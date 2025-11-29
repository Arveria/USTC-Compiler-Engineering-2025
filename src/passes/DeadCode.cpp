#include "DeadCode.hpp"
#include "Instruction.hpp"
#include "Function.hpp"
#include "logging.hpp"
#include <memory>
#include <vector>
#include <deque>


// 处理流程：两趟处理，mark 标记有用变量，sweep 删除无用指令
void DeadCode::run() {
    bool changed{};
    func_info->run();
    do {
        changed = false;
        for (auto &F : m_->get_functions()) {
            auto func = &F;
            if (func->is_declaration()) {
                continue;
            }
            std::cerr << "DCE: Processing function: " << func->get_name() << std::endl;
            // 打印Mem2Reg后的IR状态
            for (auto &bb : func->get_basic_blocks()) {
                for (auto &ins : bb.get_instructions()) {
                    if (ins.is_call()) {
                        auto call_inst = dynamic_cast<CallInst *>(&ins);
                        if (call_inst) {
                            auto func_val = call_inst->get_operand(0);
                            auto called_func = dynamic_cast<Function *>(func_val);
                            if (called_func) {
                                std::cerr << "DCE: Found call to " << called_func->get_name() 
                                         << " (is_declaration=" << called_func->is_declaration() << ")" << std::endl;
                            }
                        }
                    }
                }
            }
            mark(func);
            changed |= sweep(func);
            changed |= clear_basic_blocks(func);
        }
    } while (changed);
    LOG_INFO << "dead code pass erased " << ins_count << " instructions";
}

bool DeadCode::clear_basic_blocks(Function *func) {
    bool changed = 0;
    std::vector<BasicBlock *> to_erase;
    for (auto &bb1 : func->get_basic_blocks()) {
        auto bb = &bb1;
        // 只能删除未被entry block可达的基本块，并且不是entry block本身
        // 同时要确保基本块没有任何前驱
        if(bb->get_pre_basic_blocks().empty() && bb != func->get_entry_block()) {
            // 检查基本块是否有指令，如果没有指令，可以安全删除
            if(bb->empty()) {
                to_erase.push_back(bb);
                changed = 1;
            } else {
                // 如果基本块有指令但没有terminator，说明有问题，不应该删除
                // 但我们应该确保基本块有terminator
                if(!bb->is_terminated()) {
                    // 基本块没有terminator，这是不应该发生的
                    // 保留它，不删除
                    continue;
                }
            }
        }
    }
    for (auto &bb : to_erase) {
        bb->erase_from_parent();
        delete bb;
    }
    return changed;
}

void DeadCode::mark(Function *func) {
    // 重置标记
    marked.clear();
    work_list.clear();
    
    // 第一步：标记所有关键指令
    for (auto &bb : func->get_basic_blocks()) {
        for (auto &ins : bb.get_instructions()) {
            auto instr = &ins;
            bool critical = is_critical(instr);
            if (instr->is_call()) {
                auto call_inst = dynamic_cast<CallInst *>(instr);
                if (call_inst) {
                    auto func_val = call_inst->get_operand(0);
                    auto func = dynamic_cast<Function *>(func_val);
                    bool is_pure = func ? func_info->is_pure_function(func) : false;
                    bool is_decl = func ? func->is_declaration() : false;
                    std::cerr << "DCE: Checking call instruction: " << (func ? func->get_name() : "null")
                             << " is_declaration=" << is_decl
                             << " is_pure=" << is_pure
                             << " critical=" << critical << std::endl;
                    if (!critical && func && func->is_declaration()) {
                        std::cerr << "ERROR: Declaration function call not marked as critical!" << std::endl;
                    }
                }
            }
            if (critical) {
                work_list.push_back(instr);
            }
        }
    }
    
    // 第二步：使用worklist算法，从已标记的指令出发，标记其操作数
    while (!work_list.empty()) {
        auto ins = work_list.front();
        work_list.pop_front();
        
        if (marked.count(ins) && marked[ins]) {
            continue; // 已经标记过
        }
        
        marked[ins] = true;
        
        // 标记该指令的所有操作数（如果操作数是Instruction）
        for (unsigned i = 0; i < ins->get_num_operand(); i++) {
            auto operand = ins->get_operand(i);
            auto operand_ins = dynamic_cast<Instruction *>(operand);
            if (operand_ins) {
                if (!marked.count(operand_ins) || !marked[operand_ins]) {
                    work_list.push_back(operand_ins);
                }
            }
        }
    }
}

void DeadCode::mark(Instruction *ins) {
    // 如果已经标记过，直接返回
    if (marked.count(ins) && marked[ins]) {
        return;
    }
    // 标记该指令
    marked[ins] = true;
    // 标记该指令的所有操作数（如果操作数是Instruction）
    for (unsigned i = 0; i < ins->get_num_operand(); i++) {
        auto operand = ins->get_operand(i);
        auto operand_ins = dynamic_cast<Instruction *>(operand);
        if (operand_ins) {
            mark(operand_ins);
        }
    }
}

bool DeadCode::sweep(Function *func) {
    // TODO: 删除无用指令
    // 提示：
    // 1. 遍历函数的基本块，删除所有未被标记的指令
    // 2. 删除指令后，可能会导致其他指令的操作数变为无用，因此需要再次遍历函数的基本块
    // 3. 如果删除了指令，返回true，否则返回false
    // 4. 注意：删除指令时，需要先删除操作数的引用，然后再删除指令本身
    // 5. 删除指令时，需要注意指令的顺序，不能删除正在遍历的指令
    std::vector<Instruction *> wait_del{};

    // 1. 收集所有未被标记的指令（除了terminator）
    for (auto &bb : func->get_basic_blocks()) {
        // 确保基本块不为空
        if (bb.empty()) {
            continue;
        }
        
        // 检查基本块是否有terminator
        if (!bb.is_terminated()) {
            // 如果基本块没有terminator，这是不应该发生的
            // 保留所有指令，不删除
            continue;
        }
        
        for (auto &ins : bb.get_instructions()) {
            auto instr = &ins;
            // 注意：绝对不能删除terminator指令，即使它未被标记
            // 因为每个基本块必须有一个terminator
            if (instr->isTerminator()) {
                continue;
            }
            // 如果指令未被标记（即不是关键指令），则加入删除列表
            bool is_marked = marked.count(instr) && marked[instr];
            if (!is_marked) {
                wait_del.push_back(instr);
            }
        }
    }

    // 2. 执行删除
    for (auto ins : wait_del) {
        // 再次检查，确保不是terminator
        if (ins->isTerminator()) {
            continue;
        }
        // 删除指令的操作数引用
        ins->remove_all_operands();
        // 从基本块中删除指令（erase_instr会调用析构函数，不需要手动delete）
        auto bb = ins->get_parent();
        if (bb) {
            bb->erase_instr(ins);
            // erase_instr会调用指令的析构函数，所以不需要手动delete
        }
        // 增加删除计数
        ins_count++;
    }
    
    return !wait_del.empty(); // changed
}

bool DeadCode::is_critical(Instruction *ins) {
    // 关键指令不能被删除：
    // 1. ret指令：控制流终点，必须保留
    if (ins->is_ret()) {
        return true;
    }
    // 2. br指令：控制流分支，必须保留
    if (ins->is_br()) {
        return true;
    }
    // 3. store指令：有副作用，必须保留
    if (ins->is_store()) {
        return true;
    }
    // 4. call非纯函数：有副作用，必须保留
    if (ins->is_call()) {
        auto call_inst = dynamic_cast<CallInst *>(ins);
        if (call_inst) {
            // 从operand(0)获取被调用的函数
            auto func_val = call_inst->get_operand(0);
            auto func = dynamic_cast<Function *>(func_val);
            if (func) {
                // 声明函数（如output, input）默认不是纯函数，必须保留
                if (func->is_declaration()) {
                    return true;
                }
                // 检查FuncInfo中是否标记为纯函数
                // 如果函数不在map中，默认不是纯函数（安全起见）
                if (!func_info->is_pure_function(func)) {
                    return true;
                }
            }
        }
    }
    // 5. 如果指令有uses（被其他指令使用），则关键
    if (!ins->get_use_list().empty()) {
        return true;
    }
    return false;
}

void DeadCode::sweep_globally() {
    std::vector<Function *> unused_funcs;
    std::vector<GlobalVariable *> unused_globals;
    for (auto &f_r : m_->get_functions()) {
        if (f_r.get_use_list().size() == 0 and f_r.get_name() != "main")
            unused_funcs.push_back(&f_r);
    }
    for (auto &glob_var_r : m_->get_global_variable()) {
        if (glob_var_r.get_use_list().size() == 0)
            unused_globals.push_back(&glob_var_r);
    }
    // changed |= unused_funcs.size() or unused_globals.size();
    for (auto func : unused_funcs)
        m_->get_functions().erase(func);
    for (auto glob : unused_globals)
        m_->get_global_variable().erase(glob);
}
