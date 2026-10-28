#include "kernel/inclosure.h"
#include <iostream>
#include <stdexcept>
#include <fstream>
#include <string>

static void require(bool p, char const * message) {
    if (!p) throw std::runtime_error(message);
}

struct yielding_task : lean::organism_task {
    size_t calls=0,limit=2;
    size_t components() const override {return 8;}
    std::vector<unsigned> source_tokens() const override {return {};}
    bool closed() const override {return false;}
    bool should_yield() const override {return calls>=limit;}
    std::string snapshot() const override {return "{}";}
    lean::organism_task_observation advance(size_t component) override {
        ++calls;return {component,lean::sixteen3_none(),false,"{}",{}};
    }
};

int main(int argc, char ** argv) {
    using namespace lean;
    {
        dialetheic_organism interrupted(sixteen3::from_mask(8)), uninterrupted(sixteen3::from_mask(8));
        auto partial=std::make_shared<yielding_task>(), complete=std::make_shared<yielding_task>();
        complete->limit=100;interrupted.attach_task(partial);uninterrupted.attach_task(complete);
        interrupted.step();
        require(interrupted.history().size()==2 && interrupted.growth_pending(),"yield must retain unfinished growth");
        require(interrupted.pending_rule()==2 && interrupted.pending_rule_count()==6,"yield lost the exact rule continuation");
        interrupted.step();
        require(partial->calls==2 && interrupted.history().size()==2,"yielded task executed more work");
        partial->limit=100;interrupted.step();uninterrupted.step();
        require(!interrupted.growth_pending() && partial->calls==complete->calls,"resume repeated or omitted a task operation");
        require(interrupted.continuation()==uninterrupted.continuation(),"resume consumed another frontier item");
        require(interrupted.frontier()==uninterrupted.frontier(),"resume changed the retained frontier");
        require(interrupted.history().size()==uninterrupted.history().size(),"resume changed action count");
        for(size_t i=0;i<interrupted.history().size();++i){
            auto const & a=interrupted.history()[i];auto const & b=uninterrupted.history()[i];
            require(a.tip==b.tip && a.rule==b.rule && a.before==b.before && a.after==b.after,
                    "resumed action differs from uninterrupted execution");
        }
        for(size_t i=0;i<64;++i)require(interrupted.clock().cells[i]==uninterrupted.clock().cells[i],
                                      "resume changed the carried clock");
        std::cout<<"retained_growth_yield_resume=verified\n";
    }
    unsigned c_fixed=0,p_fixed=0;
    for(unsigned mask=0;mask<16;++mask){
        auto x=sixteen3::from_mask(mask);
        require(x.conflation().conflation()==x,"conflation must be involutive");
        require(x.reentry_permutation().reentry_permutation()==x,"P1 must be involutive");
        c_fixed+=x.conflation()==x;p_fixed+=x.reentry_permutation()==x;
        for(unsigned other=0;other<16;++other){
            auto y=sixteen3::from_mask(other);
            if(x.le_i(y))require(y.conflation().le_i(x.conflation()),"conflation reverses information order");
        }
    }
    require(c_fixed==4 && p_fixed==4,"re-entry fixed point counts");
    unsigned chain[]={0,1,3,7,15};
    for(unsigned i=0;i<5;++i){
        auto x=sixteen3::from_mask(chain[i]);
        require(x.conflation().mask()==chain[4-i],"C-palindromic native ascent");
        require(x.hasT==(i>=2),"TF designation precedes glut");
    }
    if (argc == 2) {
        std::ifstream oracle(argv[1]);
        require(static_cast<bool>(oracle), "canonical Lean oracle missing");
        std::string kind;
        unsigned rows = 0;
        while (oracle >> kind) {
            unsigned x, y;
            oracle >> x >> y;
            if (kind == "lattice") {
                auto a = sixteen3::from_mask(x), b = sixteen3::from_mask(y);
                sixteen3 results[] = {a.join_i(b), a.meet_i(b), a.join_t(b), a.meet_t(b), a.join_f(b), a.meet_f(b)};
                for (auto const & result : results) {
                    unsigned expected;
                    oracle >> expected;
                    require(result.mask() == expected, "native operation disagrees with canonical Lean");
                }
                bool t, f, i;
                oracle >> std::boolalpha >> t >> f >> i;
                require(a.le_t(b) == t && a.le_f(b) == f && a.le_i(b) == i,
                        "native order disagrees with canonical Lean");
            } else {
                require(kind == "evidence", "unexpected Lean oracle row");
                unsigned band, bor;
                oracle >> band >> bor;
                organism_evidence a(x & 1, x & 2), b(y & 1, y & 2);
                auto and_result = a.conjunction(b), or_result = a.disjunction(b);
                require((and_result.truth + 2u * and_result.falsity) == band &&
                        (or_result.truth + 2u * or_result.falsity) == bor,
                        "native evidence disagrees with canonical Lean FDE");
            }
            require(static_cast<bool>(oracle), "incomplete canonical Lean oracle row");
            ++rows;
        }
        require(rows == 272, "canonical Lean oracle coverage incomplete");
        std::cout << "canonical_Lean_rows=" << rows << '\n';
    }
    unsigned changed_actions = 0;
    unsigned changed_program_actions = 0;
    unsigned changed_frontier_actions = 0;
    unsigned learned_probes = 0;
    unsigned self_model_changed_actions = 0;
    unsigned judgment_changed_outputs = 0, changed_generators_executed = 0;
    for (unsigned source = 0; source < 16; ++source) {
        dialetheic_organism live(sixteen3::from_mask(source));
        dialetheic_organism frozen(sixteen3::from_mask(source));
        dialetheic_organism no_model(sixteen3::from_mask(source));
        for (unsigned round = 0; round < 12; ++round) {
            live.step();
            frozen.step(false);
            no_model.step(true, false);
        }
        require(live.source() == sixteen3::from_mask(source), "source changed");
        require(live.body().boundary == sixteen3::from_mask(8), "enclosing B changed");
        require(live.body().interior == sixteen3_all(), "root articulation unfinished");
        require(live.body().articulation.size() == 5, "inner stages lost");
        unsigned stages[] = {0, 1, 3, 7, 15};
        for (unsigned i = 0; i < 5; ++i)
            require(live.body().articulation[i].mask() == stages[i], "wrong inner articulation");
        require(live.history().size() == frozen.history().size(), "control boundary mismatch");
        for (size_t i = 0; i < live.history().size(); ++i) {
            auto const & action = live.history()[i];
            require(action.machinery_before.apply(action.before) == action.after,
                    "action not executed by retained machinery");
            require(action.change == witnessed(action.before != action.after), "change witness mismatch");
            require(action.after == live.tips()[i + 1].state, "child state lost");
            auto const & child = live.tips()[i + 1];
            require(child.body->source == live.source(), "child lost source");
            require(child.body->articulation.size() == 5, "child lost articulation");
            if (action.after != frozen.history()[i].after) ++changed_actions;
            if (action.after != frozen.rules()[action.rule].apply(action.before)) ++changed_program_actions;
            if (action.tip != frozen.history()[i].tip) ++changed_frontier_actions;
            learned_probes += action.model_probes.size();
            if (action.after != no_model.history()[i].after) ++self_model_changed_actions;
            auto initial_judgment = execute_judgment(
                {organism_judge_op::change, organism_judge_op::novelty, organism_judge_op::band},
                {action.change, action.novelty, action.fidelity, action.model_agreement});
            if (!(initial_judgment.value == action.judgment.value)) ++judgment_changed_outputs;
            if (action.generator_before.size() > 2 && action.change.falsity)
                ++changed_generators_executed;
            require(action.judgment.trace.size() == action.judge_before.size(),
                    "judgment program was not executed instruction by instruction");
        }
        require(live.tips()[1].body == live.body().children[0], "nested body copied");
        bool nested_growth = false;
        for (size_t i = 1; i < live.tips().size(); ++i)
            nested_growth = nested_growth || !live.tips()[i].body->children.empty();
        require(nested_growth, "returned children did not keep growing");
        bool held = false;
        for (auto const & rule : live.rules()) held = held || (rule.experience.truth && rule.experience.falsity);
        std::cout << "source=" << source << " actions=" << live.history().size()
                  << " tips=" << live.tips().size() << " held_experience=" << held << '\n';
    }
    require(changed_actions != 0, "feedback never changed subsequent mathematical actions");
    require(changed_program_actions != 0, "rewritten programs never changed an action on its actual input");
    require(changed_frontier_actions != 0, "judgments never changed frontier choice");
    require(learned_probes != 0, "learned model never generated an observation");
    require(self_model_changed_actions != 0, "self-model never changed subsequent mathematical actions");
    require(judgment_changed_outputs != 0, "rewritten judge never changed an actual judgment");
    require(changed_generators_executed != 0, "rewritten generator was never consumed");
    organism_evidence n, t(true, false), f(false, true);
    auto b = t.join(f);
    require(b.truth && b.falsity && !n.truth && !n.falsity, "N/B collapsed");
    require(b.negate() == b && n.negate() == n, "Belnap negation mismatch");
    require(n.conjunction(b) == f && n.disjunction(b) == t, "FDE N/B operations mismatch");
    organism_clock clock;
    for (unsigned ticks = 1; ticks <= 32; ++ticks) {
        clock.tick();
        for (size_t i = 0; i < clock.cells.size(); ++i) {
            bool digit = i < 6 && ((ticks >> i) & 1);
            require(clock.cells[i] == witnessed(digit), "FDE clock definite arithmetic mismatch");
        }
    }
    clock.cells[0] = b;
    clock.tick();
    require(clock.cells[0] == b, "FDE clock erased contradictory arithmetic input");
    std::cout << "feedback_changed_actions=" << changed_actions
              << " program_changed_actions=" << changed_program_actions
              << " frontier_changed_actions=" << changed_frontier_actions
              << " learned_model_probes=" << learned_probes
              << " self_model_changed_actions=" << self_model_changed_actions
              << " judgment_changed_outputs=" << judgment_changed_outputs
              << " changed_generators_executed=" << changed_generators_executed << '\n';
}
