#include "Dominators.hpp"
#include "Function.hpp"
#include <fstream>
#include <vector>

void Dominators::run() {
    for(auto &f1 : m_->get_functions()) {
        auto f = &f1;
        if(f->is_declaration())
            continue;
        run_on_func(f);
    }
}

void Dominators::run_on_func(Function *f) {
    dom_post_order_.clear();
    dom_dfs_order_.clear();
    for(auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        idom_.insert({bb, nullptr});
        dom_frontier_.insert({bb, {}});
        dom_tree_succ_blocks_.insert({bb, {}});
    }
    create_reverse_post_order(f);
    create_idom(f);
    create_dominance_frontier(f);
    create_dom_tree_succ(f);
    create_dom_dfs_order(f);
}

BasicBlock *Dominators::intersect(BasicBlock *b1, BasicBlock *b2) {
    while (b1 != b2) {
        while (get_post_order(b1) < get_post_order(b2)) {
            b1 = get_idom(b1);
        }
        while (get_post_order(b2) < get_post_order(b1)) {
            b2 = get_idom(b2);
        }
    }
    return b1;
}

void Dominators::create_reverse_post_order(Function *f) {
    BBSet visited;
    dfs(f->get_entry_block(), visited);
}

void Dominators::dfs(BasicBlock *bb, std::set<BasicBlock *> &visited) {
    visited.insert(bb);
    for (auto &succ : bb->get_succ_basic_blocks()) {
        if (visited.find(succ) == visited.end()) {
            dfs(succ, visited);
        }
    }
    post_order_vec_.push_back(bb);
    post_order_.insert({bb, post_order_.size()});
}

void Dominators::create_idom(Function *f) {
    // 分析得到 f 中各个基本块的 idom
    idom_[f->get_entry_block()] = f->get_entry_block();
    bool changed;
    do {
        changed = false;
        for (auto it = post_order_vec_.rbegin(); it != post_order_vec_.rend();
             it++) {
            auto bb = *it;
            if (bb == f->get_entry_block())
                continue;
            if (bb->get_pre_basic_blocks().empty())
                continue;
            BasicBlock *first_pred = bb->get_pre_basic_blocks().front();
            BasicBlock *new_idom = first_pred;
            for (auto &pred : bb->get_pre_basic_blocks()) {
                if (pred == first_pred)
                    continue;
                if (get_idom(pred) != nullptr) {
                    new_idom = intersect(pred, new_idom);
                }
            }
            if (new_idom != get_idom(bb)) {
                changed = true;
                idom_[bb] = new_idom;
            }
        }
    } while (changed);
}

void Dominators::create_dominance_frontier(Function *f) {
    // 分析得到 f 中各个基本块的支配边界集合
    for (auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        if (bb->get_pre_basic_blocks().size() >= 2) {
            for (auto &pred : bb->get_pre_basic_blocks()) {
                auto runner = pred;
                while (runner != get_idom(bb)) {
                    dom_frontier_[runner].insert(bb);
                    runner = get_idom(runner);
                }
            }
        }
    }

}

void Dominators::create_dom_tree_succ(Function *f) {
    // 分析得到 f 中各个基本块的支配树后继
    for (auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        if (get_idom(bb) != nullptr && get_idom(bb) != bb) {
            dom_tree_succ_blocks_[get_idom(bb)].insert(bb);
        }
    }
}

void Dominators::create_dom_dfs_order(Function *f) {
    // 分析得到 f 中各个基本块的支配树上的dfs序L,R
    unsigned int order = 0;
    std::function<void(BasicBlock *)> dfs = [&](BasicBlock *bb) {
        dom_tree_L_[bb] = ++ order;
        dom_dfs_order_.push_back(bb);
        for (auto &succ : dom_tree_succ_blocks_[bb]) {
            dfs(succ);
        }
        dom_tree_R_[bb] = order;
    };
    dfs(f->get_entry_block());
    dom_post_order_ =
        std::vector(dom_dfs_order_.rbegin(), dom_dfs_order_.rend());
}

void Dominators::print_idom(Function *f) {
    f->get_parent()->set_print_name();
    int counter = 0;
    std::map<BasicBlock *, std::string> bb_id;
    for (auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        if (bb->get_name().empty())
            bb_id[bb] = "bb" + std::to_string(counter);
        else
            bb_id[bb] = bb->get_name();
        counter++;
    }
    printf("Immediate dominance of function %s:\n", f->get_name().c_str());
    for (auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        std::string output;
        output = bb_id[bb] + ": ";
        if (get_idom(bb)) {
            output += bb_id[get_idom(bb)];
        } else {
            output += "null";
        }
        printf("%s\n", output.c_str());
    }
}

void Dominators::print_dominance_frontier(Function *f) {
    f->get_parent()->set_print_name();
    int counter = 0;
    std::map<BasicBlock *, std::string> bb_id;
    for (auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        if (bb->get_name().empty())
            bb_id[bb] = "bb" + std::to_string(counter);
        else
            bb_id[bb] = bb->get_name();
        counter++;
    }
    printf("Dominance Frontier of function %s:\n", f->get_name().c_str());
    for (auto &bb1 : f->get_basic_blocks()) {
        auto bb = &bb1;
        std::string output;
        output = bb_id[bb] + ": ";
        if (get_dominance_frontier(bb).empty()) {
            output += "null";
        } else {
            bool first = true;
            for (auto df : get_dominance_frontier(bb)) {
                if (first) {
                    first = false;
                } else {
                    output += ", ";
                }
                output += bb_id[df];
            }
        }
        printf("%s\n", output.c_str());
    }
}

void Dominators::dump_cfg(Function *f)
{
    f->get_parent()->set_print_name();
    if(f->is_declaration())
        return;
    std::vector<std::string> edge_set;
    bool has_edges = false;
    for (auto &bb : f->get_basic_blocks()) {
        auto succ_blocks = bb.get_succ_basic_blocks();
        if(!succ_blocks.empty())
            has_edges = true;
        for (auto succ : succ_blocks) {
            edge_set.push_back('\t' + bb.get_name() + "->" + succ->get_name() + ";\n");
        }
    }
    std::string digraph = "digraph G {\n";
    if (!has_edges && !f->get_basic_blocks().empty()) {
        // 如果没有边且至少有一个基本块，添加一个自环以显示唯一的基本块
        auto &bb = f->get_basic_blocks().front();
        digraph += '\t' + bb.get_name() + ";\n";
    } else {
        for (auto &edge : edge_set) {
            digraph += edge;
        }
    }
    digraph += "}\n";
    std::ofstream file_output;
    file_output.open(f->get_name() + "_cfg.dot", std::ios::out);
    file_output << digraph;
    file_output.close();
    std::string dot_cmd = "dot -Tpng " + f->get_name() + "_cfg.dot" + " -o " + f->get_name() + "_cfg.png";
    std::system(dot_cmd.c_str());
}

void Dominators::dump_dominator_tree(Function *f)
{
    f->get_parent()->set_print_name();
    if(f->is_declaration())
        return;

    std::vector<std::string> edge_set;
    bool has_edges = false; // 用于检查是否有边存在

    for (auto &b : f->get_basic_blocks()) {
        if (idom_.find(&b) != idom_.end() && idom_[&b] != &b) {
            edge_set.push_back('\t' + idom_[&b]->get_name() + "->" + b.get_name() + ";\n");
            has_edges = true; // 如果存在支配边，标记为 true
        }
    }

    std::string digraph = "digraph G {\n";

    if (!has_edges && !f->get_basic_blocks().empty()) {
        // 如果没有边且至少有一个基本块，直接添加该块以显示它
        auto &b = f->get_basic_blocks().front();
        digraph += '\t' + b.get_name() + ";\n";
    } else {
        for (auto &edge : edge_set) {
            digraph += edge;
        }
    }

    digraph += "}\n";

    std::ofstream file_output;
    file_output.open(f->get_name() + "_dom_tree.dot", std::ios::out);
    file_output << digraph;
    file_output.close();

    std::string dot_cmd = "dot -Tpng " + f->get_name() + "_dom_tree.dot" + " -o " + f->get_name() + "_dom_tree.png";
    std::system(dot_cmd.c_str());
}