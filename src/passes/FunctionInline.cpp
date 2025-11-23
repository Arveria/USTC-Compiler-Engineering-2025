#include "../../include/passes/FunctionInline.hpp"
#include "../../include/lightir/Function.hpp"

#include "BasicBlock.hpp"
#include "Instruction.hpp"
#include "Value.hpp"
#include "logging.hpp"
#include <cassert>
#include <utility>
#include <vector>

void FunctionInline::run() { inline_all_functions(); }

void FunctionInline::inline_all_functions() {
    
    std::set<Function *> recursive_func;
    for (auto &func : m_->get_functions()) {
        for (auto &bb : func.get_basic_blocks()) {
            for (auto &inst : bb.get_instructions()) {
                if (inst.is_call()) {
                    auto call = &inst;
                    auto func1 = static_cast<Function *>(call->get_operand(0));
                    if (func1 == &func) {
                        recursive_func.insert(func1);
                        break;
                    }
                }
            }
        }
    }
    for (auto &func : m_->get_functions()) {
        if (outside_func.find(func.get_name()) != outside_func.end()) {
            continue;
        }
    a1:
        for (auto &bb : func.get_basic_blocks()) {
            for (auto &inst : bb.get_instructions()) {
                if (inst.is_call()) {
                    auto call = &inst;
                    auto func1 = static_cast<Function *>(call->get_operand(0));
                    if (func1 == &func) {
                        continue;
                    }
                    if (recursive_func.find(func1) != recursive_func.end())
                        continue;
                    if (outside_func.find(func1->get_name()) !=
                        outside_func.end())
                        continue;
                    if(func1->get_basic_blocks().size() >=6){
                        continue;
                    }
                    inline_function(call, func1);
                    goto a1;
                }
            }
        }
    }
}

void FunctionInline::inline_function(Instruction *call, Function *origin) {
    std::map<Value *, Value *> v_map;
    std::vector<BasicBlock *> bb_list;
    std::vector<Instruction *> ret_list; // 记录函数所有出口
    for (auto &arg : origin->get_args()) {
        v_map.insert(std::make_pair(static_cast<Value *>(&arg),
                                    call->get_operand(arg.get_arg_no() + 1)));
    }
    auto call_bb = call->get_parent();
    auto call_func = call_bb->get_parent();
    std::vector<BasicBlock *> ret_void_bbs;
    for (auto &bb : origin->get_basic_blocks()) {
        auto bb_new =
            BasicBlock::create(call_func->get_parent(), "", call_func);
        v_map.insert(std::make_pair(static_cast<Value *>(&bb),
                                    static_cast<Value *>(bb_new)));
        bb_list.push_back(bb_new);
        for (auto &inst : bb.get_instructions()) {
            if (inst.is_ret() && origin->get_return_type()->is_void_type()) {
                ret_void_bbs.push_back(bb_new);
                continue;
            }
            if (inst.is_phi()) {
                ;
            }
            
            Instruction *inst_new ;
            if (inst.is_call()) {
                auto call = static_cast<CallInst *>(&inst);
                auto func = static_cast<Function *>(call->get_operand(0));
                // 
                inst_new = new CallInst(func, {call->get_operands().begin() + 1, call->get_operands().end()}, bb_new);
            }
            else inst_new = inst.clone(bb_new);
            // 
            if (inst.is_phi())
                bb_new->add_instr_begin(inst_new);
            v_map.insert(std::make_pair(static_cast<Value *>(&inst),
                                        static_cast<Value *>(inst_new)));
            if (inst.is_ret()) {
                ret_list.push_back(inst_new);
            }
        }
    }
    for (auto bb : bb_list) {
        for (auto &inst : bb->get_instructions()) {
            for (int i = 0; i < inst.get_num_operand(); i++) {
                if (inst.is_phi()) {
                    ;
                }
                auto op = inst.get_operand(i);
                if (v_map.find(op) != v_map.end()) {
                    inst.set_operand(i, v_map[op]);
                }
            }
        }
    }
    Value *ret_val = nullptr; // 返回值
    bool is_terminated = false;
    auto bb_new = BasicBlock::create(call_func->get_parent(), "", call_func);
    if (!origin->get_return_type()->is_void_type()) {
        // 
        if (ret_list.size() == 1) {
            auto ret = ret_list.front();
            ret_val = ret->get_operand(0);
            auto ret_bb = ret->get_parent();
            ret_bb->remove_instr(ret);
            BranchInst::create_br(bb_new, ret_bb);
        } else {
            // TODO: 处理多个返回值的情况
            // 提示：
            // 1. 需要创建一个新的基本块(bb_phi)用于存放phi指令
            // 2. 对于每个返回指令：
            //    - 记录其所在的基本块
            //    - 移除返回指令
            //    - 添加跳转到bb_phi的分支指令
            // 3. 创建phi指令：
            //    - 设置正确的返回类型
            //    - 为每个返回路径添加phi对
            // 4. 将phi指令添加到bb_phi
            // 5. 设置返回值
            // 6. 将bb_phi添加到基本块列表
            // 7. 添加从bb_phi到bb_new的跳转
        }
    } else {
        assert(ret_void_bbs.size() > 0);
        for (auto bb : ret_void_bbs) {
            BranchInst::create_br(bb_new, bb);
        }
    }
    std::vector<Instruction *> del_list;
    // 
    // 
    BranchInst* br = nullptr;
    for (auto &inst : call_bb->get_instructions()) {
    // 
        if (!is_terminated) {
            // 如果前一个基本块还没遇到这条跳转指令
            if (&(inst) == call) {
                
                
                br = BranchInst::create_br(bb_list.front(), call_bb);
                // bb_1->add_instruction(br);
                // call_bb->insert_before(&inst, br);
                // inst.replace_all_use_with(br);
                if (!origin->get_return_type()->is_void_type()) {
                    // 
                    // auto temp = call->get_use_list().begin();
                    call->replace_all_use_with(ret_val);
                    // 
                    // 

                }
                // call_bb->remove_instr(call);
                // del_list.push_back(call);
                is_terminated = true;
            }
        } else {
            // call_bb->remove_instr(&inst);
            if(dynamic_cast<BranchInst*>(&inst) == br){
                continue;
            }
            del_list.push_back(&inst);
        }
    }
    // 
    call_bb->remove_instr(call);
    origin->remove_use(call, 0);
    // 
    for (auto inst : del_list) {
        
        call_bb->remove_instr(inst);
        bb_new->add_instruction(inst);
        inst->set_parent(bb_new);
    }

    // 
    // br->set_parent(call_bb);
    // 
    origin->reset_bbs();
    // 
    call_func->reset_bbs();
    
    return;
}