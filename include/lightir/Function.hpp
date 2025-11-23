#pragma once

#include "BasicBlock.hpp"
#include "Type.hpp"
#include "User.hpp"

#include <cassert>
#include <cstddef>
#include <iterator>
#include <list>
#include <llvm/ADT/ilist.h>
#include <llvm/ADT/ilist_node.h>
#include <map>
#include <memory>

class Module;
class Argument;
class Type;
class FunctionType;

class Function : public Value, public llvm::ilist_node<Function> {
  public:
    Function(const Function &) = delete;
    Function(FunctionType *ty, const std::string &name, Module *parent);
    ~Function() = default;
    static Function *create(FunctionType *ty, const std::string &name,
                            Module *parent);

    FunctionType *get_function_type() const;
    Type *get_return_type() const;

    void add_basic_block(BasicBlock *bb);

    unsigned get_num_of_args() const;
    unsigned get_num_basic_blocks() const;

    Module *get_parent() const;

    void remove(BasicBlock *bb);
    BasicBlock *get_entry_block() { return &*basic_blocks_.begin(); }

    llvm::ilist<BasicBlock> &get_basic_blocks() { return basic_blocks_; }
    std::list<Argument> &get_args() { return arguments_; }

    bool is_declaration() { return basic_blocks_.empty(); }

    void set_instr_name();
    std::string print();

    void reset_bbs(){
    for(auto &bb: basic_blocks_){
        bb.reset();
    }
    for(auto &bb : basic_blocks_){
        auto inst = &((bb.get_instructions().back()));
            if(inst->is_br()){
                auto br = static_cast<BranchInst*>(inst);
                if(br->is_cond_br()){
                    auto true_bb = static_cast<BasicBlock*>(br->get_operand(1));
                    auto false_bb = static_cast<BasicBlock*>(br->get_operand(2));
                    assert(true_bb->get_parent() == this);
                    assert(false_bb->get_parent() == this);
                    bb.add_succ_basic_block(true_bb);
                    bb.add_succ_basic_block(false_bb);
                    true_bb->add_pre_basic_block(&bb);
                    false_bb->add_pre_basic_block(&bb);
                }
                else{
                    auto succ_bb = static_cast<BasicBlock*>(br->get_operand(0));
                    assert(succ_bb->get_parent() == this);
                    bb.add_succ_basic_block(succ_bb);
                    succ_bb->add_pre_basic_block(&bb);
                }
            }
            // else{
            //     std::cout << print();
            // }
        
    }
}

  private:
    llvm::ilist<BasicBlock> basic_blocks_;
    std::list<Argument> arguments_;
    Module *parent_;
    unsigned seq_cnt_; // print use
};

// Argument of Function, does not contain actual value
class Argument : public Value {
  public:
    Argument(const Argument &) = delete;
    explicit Argument(Type *ty, const std::string &name = "",
                      Function *f = nullptr, unsigned arg_no = 0)
        : Value(ty, name), parent_(f), arg_no_(arg_no) {}
    virtual ~Argument() {}

    inline const Function *get_parent() const { return parent_; }
    inline Function *get_parent() { return parent_; }

    /// For example in "void foo(int a, float b)" a is 0 and b is 1.
    unsigned get_arg_no() const {
        assert(parent_ && "can't get number of unparented arg");
        return arg_no_;
    }

    virtual std::string print() override;

  private:
    Function *parent_;
    unsigned arg_no_; // argument No.
};
