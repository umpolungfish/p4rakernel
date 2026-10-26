/* Native nested Prima Logica execution over the kernel SIXTEEN_3 carrier. */
#pragma once
#include "kernel/sixteen3.h"
#include <vector>
#include <stdexcept>
#include <memory>
#include <string>

namespace lean {

/** The enclosing singleton B is distinct from its complete interior. */
struct inclosure {
    sixteen3 boundary = sixteen3::from_mask(8);
    sixteen3 interior;
    std::vector<sixteen3> articulation{sixteen3_none()};
    sixteen3 source;
    std::vector<std::shared_ptr<inclosure>> children;
    std::vector<sixteen3> observations;

    /** Canonical PrimaLogica.wind, including its action on non-chain states. */
    static sixteen3 wind(sixteen3 const & s) {
        if (!s.hasN) return s.join_i(sixteen3::from_mask(1));
        if (!s.hasT) return s.join_i(sixteen3::from_mask(2));
        if (!s.hasF) return s.join_i(sixteen3::from_mask(4));
        if (!s.hasB) return s.join_i(sixteen3::from_mask(8));
        return s;
    }

    void distinguish() {
        auto next = wind(interior);
        if (next != interior) {
            interior = next;
            articulation.push_back(next);
        }
    }

    /** Return contains the actual child, its distinctions and observations.
        Joining a child into B alone would erase these distinctions. */
    void receive(std::shared_ptr<inclosure> child) {
        if (!child || child->boundary != sixteen3::from_mask(8) || child->interior != sixteen3_all())
            throw std::invalid_argument("inclosure return requires its complete interior and B boundary");
        children.push_back(std::move(child));
    }

    void articulate() {
        while (interior != sixteen3_all()) distinguish();
    }
};

/** Independent Belnap support rails. Boolean storage is the kernel's native
    representation; neither rail is derived by negating the other. */
struct organism_evidence {
    bool truth = false;
    bool falsity = false;
    organism_evidence() = default;
    organism_evidence(bool t, bool f) : truth(t), falsity(f) {}
    organism_evidence join(organism_evidence const & y) const {
        return {truth || y.truth, falsity || y.falsity};
    }
    organism_evidence negate() const { return {falsity, truth}; }
    organism_evidence conjunction(organism_evidence const & y) const {
        return {truth && y.truth, falsity || y.falsity};
    }
    organism_evidence disjunction(organism_evidence const & y) const {
        return {truth || y.truth, falsity && y.falsity};
    }
    sixteen3 singleton() const {
        if (truth && falsity) return sixteen3::from_mask(8);
        if (truth) return sixteen3::from_mask(2);
        if (falsity) return sixteen3::from_mask(4);
        return sixteen3::from_mask(1);
    }
    bool operator==(organism_evidence const & y) const {
        return truth == y.truth && falsity == y.falsity;
    }
};

/** Each order has its own evidence, in each direction. */
struct order_observation {
    std::array<organism_evidence, 3> forward;
    std::array<organism_evidence, 3> backward;
};
inline organism_evidence witnessed(bool p) { return {p, !p}; }
inline organism_evidence evidence_xor(organism_evidence a, organism_evidence b) {
    return a.conjunction(b.negate()).disjunction(a.negate().conjunction(b));
}
struct organism_sum {
    organism_evidence value;
    organism_evidence carry;
};
inline organism_sum evidence_add(organism_evidence a, organism_evidence b, organism_evidence c) {
    auto ab = evidence_xor(a, b);
    return {evidence_xor(ab, c), a.conjunction(b).disjunction(ab.conjunction(c))};
}
/** The executed instruction clock is a native FDE word. Structural container
    addresses stay separate from this mathematical arithmetic. */
struct organism_clock {
    std::array<organism_evidence, 64> cells;
    organism_evidence overflow;
    organism_clock() { cells.fill({false, true}); }
    void tick() {
        organism_evidence carry(true, false), zero(false, true);
        for (auto & cell : cells) {
            auto sum = evidence_add(cell, zero, carry);
            cell = sum.value;
            carry = sum.carry;
        }
        overflow = overflow.join(carry);
    }
};
inline order_observation observe_order(sixteen3 const & x, sixteen3 const & y) {
    return {{{witnessed(x.le_t(y)), witnessed(x.le_f(y)), witnessed(x.le_i(y))}},
            {{witnessed(y.le_t(x)), witnessed(y.le_f(x)), witnessed(y.le_i(x))}}};
}

enum class organism_op { join_i, meet_i, join_t, meet_t, join_f, meet_f, negation };
struct organism_neural_observation {
    organism_op op;
    sixteen3 input;
    sixteen3 operand;
    sixteen3 expected;
    sixteen3 proposal_before;
    sixteen3 proposal_after;
    std::array<double, 4> rails_before;
    std::array<double, 4> rails_after;
    double optimizer_before;
    double optimizer_after;
    std::array<organism_evidence, 4> membership_evidence;
};
struct organism_learner {
    virtual ~organism_learner() = default;
    virtual organism_neural_observation act(organism_op, sixteen3, sixteen3, sixteen3) = 0;
    virtual std::string snapshot() const = 0;
    virtual void bind_source(std::vector<unsigned> const &) {}
    virtual void observe_task(unsigned, sixteen3) {}
    virtual void observe_task_context(unsigned component, sixteen3 feedback,
                                      std::vector<unsigned> const &) { observe_task(component, feedback); }
};
struct organism_task_observation {
    size_t component;
    sixteen3 feedback;
    bool closed;
    std::string state;
    std::vector<unsigned> learning_context{};
};
struct organism_task {
    virtual ~organism_task() = default;
    virtual size_t components() const = 0;
    virtual std::vector<unsigned> source_tokens() const = 0;
    virtual organism_task_observation advance(size_t) = 0;
    virtual bool closed() const = 0;
    virtual std::string snapshot() const = 0;
};
struct organism_instruction {
    organism_op op;
    sixteen3 operand;
    sixteen3 apply(sixteen3 const & x) const {
        switch (op) {
        case organism_op::join_i: return x.join_i(operand);
        case organism_op::meet_i: return x.meet_i(operand);
        case organism_op::join_t: return x.join_t(operand);
        case organism_op::meet_t: return x.meet_t(operand);
        case organism_op::join_f: return x.join_f(operand);
        case organism_op::meet_f: return x.meet_f(operand);
        case organism_op::negation: return {x.hasN, x.hasF, x.hasT, x.hasB};
        }
        throw std::logic_error("invalid native organism instruction");
    }
};

/** Programs are retained compositions of the native corpus's LatticeOp
    and lifted FDE negation (CombinatoryReentry.lean). */
struct organism_rule {
    std::vector<organism_instruction> program;
    organism_evidence experience;
    organism_evidence fidelity;
    std::array<std::vector<sixteen3>, 16> prediction;
    sixteen3 apply(sixteen3 x) const {
        for (auto const & instruction : program) x = instruction.apply(x);
        return x;
    }
};

/** Carried judgment programs use the canonical FDE operations. Reads name
    independent observations; the stack retains every intermediate judgment. */
enum class organism_judge_op { change, novelty, fidelity, model, band, bor, join, negate };
struct organism_judge_context {
    organism_evidence change, novelty, fidelity, model;
};
struct organism_judgment {
    organism_evidence value;
    std::vector<organism_evidence> trace;
};
inline organism_judgment execute_judgment(std::vector<organism_judge_op> const & program,
                                         organism_judge_context const & context) {
    std::vector<organism_evidence> stack;
    organism_judgment result;
    for (auto op : program) {
        switch (op) {
        case organism_judge_op::change: stack.push_back(context.change); break;
        case organism_judge_op::novelty: stack.push_back(context.novelty); break;
        case organism_judge_op::fidelity: stack.push_back(context.fidelity); break;
        case organism_judge_op::model: stack.push_back(context.model); break;
        case organism_judge_op::negate:
            if (stack.empty()) throw std::logic_error("judgment negation has no operand");
            stack.back() = stack.back().negate(); break;
        default: {
            if (stack.size() < 2) throw std::logic_error("judgment operation has missing operands");
            auto right = stack.back(); stack.pop_back();
            auto left = stack.back();
            stack.back() = op == organism_judge_op::band ? left.conjunction(right) :
                           op == organism_judge_op::bor ? left.disjunction(right) : left.join(right);
            break;
        }
        }
        result.trace.push_back(stack.back());
    }
    if (stack.size() != 1) throw std::logic_error("judgment program has an open operand stack");
    result.value = stack.back();
    return result;
}
struct organism_action {
    size_t tip;
    size_t rule;
    sixteen3 before;
    sixteen3 after;
    organism_rule machinery_before;
    organism_rule machinery_after;
    order_observation observation;
    organism_evidence change;
    organism_evidence novelty;
    std::vector<sixteen3> prediction_before;
    organism_evidence model_agreement;
    std::vector<order_observation> model_probes;
    organism_clock cost_before;
    organism_clock cost_after;
    std::vector<organism_neural_observation> neural_operations;
    organism_evidence fidelity;
    std::vector<organism_judge_op> judge_before, judge_after;
    organism_judgment judgment;
    std::vector<organism_op> generator_before, generator_after;
    std::vector<size_t> model_ancestry;
    std::vector<organism_task_observation> task_operations;
};
struct organism_tip {
    size_t parent;
    sixteen3 state;
    std::shared_ptr<inclosure> body;
    organism_evidence attention{true, false};
};

/** One resident body. Indices and counters are structural addresses and run
    boundaries. Mathematical values and judgments never become scalar scores. */
class dialetheic_organism {
    sixteen3 m_source;
    std::shared_ptr<inclosure> m_body = std::make_shared<inclosure>();
    std::vector<organism_rule> m_rules;
    std::vector<organism_tip> m_tips;
    std::vector<organism_action> m_history;
    std::vector<size_t> m_frontier{0};
    organism_clock m_clock;
    std::shared_ptr<organism_learner> m_learner;
    std::shared_ptr<organism_task> m_task;
    std::vector<organism_judge_op> m_judge{
        organism_judge_op::change, organism_judge_op::novelty, organism_judge_op::band};
    std::vector<organism_op> m_generator{organism_op::join_i, organism_op::negation};
    size_t m_continuation = 0;
public:
    explicit dialetheic_organism(sixteen3 source) : m_source(source) {
        for (auto op : {organism_op::join_i, organism_op::meet_i,
                        organism_op::join_t, organism_op::meet_t,
                        organism_op::join_f, organism_op::meet_f}) {
            organism_rule rule;
            rule.program.push_back({op, source});
            m_rules.push_back(rule);
        }
        m_body->source = source;
        m_tips.push_back({0, sixteen3_none(), m_body, {true, false}});
    }
    void attach(std::shared_ptr<organism_learner> learner) {
        if (!m_history.empty()) throw std::invalid_argument("attach learner before organism growth");
        m_learner = std::move(learner);
        if (m_task && m_learner) m_learner->bind_source(m_task->source_tokens());
    }
    void attach_task(std::shared_ptr<organism_task> task) {
        if (!m_history.empty()) throw std::invalid_argument("attach task before organism growth");
        m_task = std::move(task);
        if (m_learner && m_task) m_learner->bind_source(m_task->source_tokens());
    }

    /** The designated truth and falsity rails drive separate arms. B executes
        both arms and N leaves an open continuation. History is never cleared. */
    void grow(size_t tip, bool feedback = true, bool model_feedback = true) {
        if (tip >= m_tips.size()) throw std::out_of_range("organism tip");
        auto before = m_tips[tip].state;
        auto rule_count = m_rules.size();
        for (size_t r = 0; r < rule_count; ++r) {
            auto old_rule = m_rules[r];
            auto judge_before = m_judge;
            auto generator_before = m_generator;
            auto clock_before = m_clock;
            auto after = before;
            std::vector<organism_neural_observation> neural_operations;
            std::vector<organism_task_observation> task_operations;
            organism_evidence fidelity(true, false);
            for (auto const & instruction : old_rule.program) {
                auto expected = instruction.apply(after);
                if (m_learner) {
                    auto neural = m_learner->act(instruction.op, after, instruction.operand, expected);
                    fidelity = fidelity.conjunction(witnessed(neural.proposal_after == expected));
                    after = neural.proposal_after;
                    neural_operations.push_back(std::move(neural));
                } else {
                    after = expected;
                }
                m_clock.tick();
            }
            if (m_task && !m_task->closed()) {
                // The learned register and current rule select a real port
                // of the retained task. Its result enters this same body.
                size_t component = (after.mask() + r) % m_task->components();
                auto task = m_task->advance(component);
                if (m_learner) m_learner->observe_task_context(component, task.feedback, task.learning_context);
                after = after.join_i(task.feedback);
                task_operations.push_back(std::move(task));
            }
            auto obs = observe_order(before, after);
            auto change = witnessed(before != after);
            bool seen = false;
            for (auto const & prior : m_tips) seen = seen || prior.state == after;
            auto novelty = witnessed(!seen);
            auto revised = old_rule;
            revised.experience = old_rule.experience.join(change);
            revised.fidelity = old_rule.fidelity.join(fidelity);
            organism_evidence agreement;
            std::vector<order_observation> model_probes;
            std::vector<size_t> model_ancestry;
            for (size_t index = 0; index < m_history.size(); ++index) {
                auto const & prior = m_history[index];
                if (prior.rule != r || prior.before != before) continue;
                // The self-model compares this lineage's earlier actions on
                // this same input. Program and neural-clock ancestry remain
                // attached to each observation, including across revisions.
                model_probes.push_back(observe_order(prior.after, after));
                agreement = agreement.join(witnessed(prior.after == after));
                model_ancestry.push_back(index);
            }
            auto & alternatives = revised.prediction[before.mask()];
            bool predicted = false;
            for (auto const & value : alternatives) predicted = predicted || value == after;
            if (!predicted) alternatives.push_back(after);
            auto judgment = execute_judgment(judge_before, {change, novelty, fidelity, agreement});
            // A witnessed stationary action prompts a native composition.
            // Its complete earlier program remains in this action's ancestry.
            if (feedback && (change.falsity || fidelity.falsity)) {
                auto operand = inclosure::wind(old_rule.program.back().operand);
                for (auto op : generator_before)
                    revised.program.push_back({op, op == organism_op::meet_i ? after :
                                                  op == organism_op::negation ? sixteen3_none() : operand});
                // Predictions are indexed by the actual executable program.
                // The old program and its complete model remain in history.
                revised.prediction = {};
            }
            // A corroborated self-prediction becomes an executable native
            // projector. Subsequent contexts actually pass through that
            // learned return. Its originating context stays in history.
            if (feedback && model_feedback && agreement.truth) {
                revised.program.push_back({organism_op::meet_i, after});
                revised.prediction = {};
                bool contains_projector = false;
                for (auto op : m_generator) contains_projector = contains_projector || op == organism_op::meet_i;
                if (!contains_projector) m_generator.push_back(organism_op::meet_i);
                bool observes_model = false;
                for (auto op : m_judge) observes_model = observes_model || op == organism_judge_op::model;
                if (!observes_model) {
                    m_judge.push_back(organism_judge_op::model);
                    m_judge.push_back(organism_judge_op::bor);
                }
            }
            if (feedback && fidelity.falsity) {
                bool observes_fidelity = false;
                for (auto op : m_judge) observes_fidelity = observes_fidelity || op == organism_judge_op::fidelity;
                if (!observes_fidelity) {
                    m_judge.push_back(organism_judge_op::fidelity);
                    m_judge.push_back(organism_judge_op::join);
                }
            }
            if (feedback) m_rules[r] = revised;
            auto child = std::make_shared<inclosure>();
            child->source = m_source;
            child->observations = {before, after, change.singleton(), novelty.singleton()};
            for (auto const & e : obs.forward) child->observations.push_back(e.singleton());
            for (auto const & e : obs.backward) child->observations.push_back(e.singleton());
            for (auto const & neural : neural_operations) {
                child->observations.push_back(neural.expected);
                child->observations.push_back(neural.proposal_after);
                for (auto const & e : neural.membership_evidence)
                    child->observations.push_back(e.singleton());
            }
            for (auto const & e : judgment.trace) child->observations.push_back(e.singleton());
            for (auto const & task : task_operations) child->observations.push_back(task.feedback);
            child->articulate();
            m_tips[tip].body->receive(child);
            // Both success and refutation can yield continuations. Their
            // evidence remains independent on the actual resulting tip.
            auto attention = feedback ? judgment.value : organism_evidence(true, false);
            // An observed model disagreement also opens a falsity arm.
            if (feedback && model_feedback && agreement.falsity)
                attention = attention.join({false, true});
            if (feedback && fidelity.falsity) attention = attention.join({false, true});
            m_tips.push_back({tip, after, std::move(child), attention});
            m_frontier.push_back(m_tips.size() - 1);
            m_history.push_back({tip, r, before, after, old_rule, m_rules[r], obs,
                                 change, novelty, old_rule.prediction[before.mask()],
                                 agreement, model_probes, clock_before, m_clock, neural_operations, fidelity,
                                 judge_before, m_judge, judgment, generator_before, m_generator, model_ancestry,
                                 task_operations});
            m_body->distinguish();
            if (m_task && m_task->closed()) {m_body->articulate();return;}
        }
    }

    /** Resume the body's stored frontier. No external branch-choice schedule. */
    void step(bool feedback = true, bool model_feedback = true) {
        if (m_task && m_task->closed()) return;
        // Designated truth directs growth first. Refuted tips remain in the
        // body and receive exploratory work when no truth-supported tip waits.
        // B participates in either pass, and N stays open in the frontier.
        for (unsigned arm = 0; arm < 2; ++arm) {
            for (size_t i = 0; i < m_frontier.size(); ++i) {
                auto attention = m_tips[m_frontier[i]].attention;
                if (arm == 0 ? attention.truth : attention.falsity) {
                    size_t tip = m_frontier[i];
                    m_frontier.erase(m_frontier.begin() + i);
                    ++m_continuation;
                    grow(tip, feedback, model_feedback);
                    return;
                }
            }
        }
    }
    sixteen3 source() const { return m_source; }
    inclosure const & body() const { return *m_body; }
    size_t continuation() const { return m_continuation; }
    std::vector<size_t> const & frontier() const { return m_frontier; }
    organism_clock const & clock() const { return m_clock; }
    std::string learner_snapshot() const { return m_learner ? m_learner->snapshot() : "null"; }
    std::string task_snapshot() const { return m_task ? m_task->snapshot() : "null"; }
    bool task_closed() const { return m_task && m_task->closed(); }
    std::vector<organism_judge_op> const & judge_program() const { return m_judge; }
    std::vector<organism_op> const & generator_program() const { return m_generator; }
    std::vector<organism_tip> const & tips() const { return m_tips; }
    std::vector<organism_rule> const & rules() const { return m_rules; }
    std::vector<organism_action> const & history() const { return m_history; }
};
}
