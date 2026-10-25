#include "kernel/inclosure.h"
#include "kernel/organism_vgi.h"
#include "kernel/organism_factor.h"
#include "runtime/io.h"
#include "runtime/object.h"
#include <mutex>
#include <sstream>

namespace lean {
namespace {
struct organism_handle {
    std::mutex lock;
    dialetheic_organism body;
    explicit organism_handle(sixteen3 source) : body(source) {}
};
lean_external_class * g_organism_class = nullptr;
void destroy_organism(void * p) { delete static_cast<organism_handle *>(p); }
void visit_organism(void *, b_obj_arg) {}
organism_handle & get_organism(b_obj_arg o) {
    return *static_cast<organism_handle *>(lean_get_external_data(o));
}
void evidence(std::ostream & s, organism_evidence e) {
    s << "[" << e.truth << "," << e.falsity << "]";
}
void clock(std::ostream & s, organism_clock const & value) {
    s << "{\"cells\":[";
    for (size_t i = 0; i < value.cells.size(); ++i) {
        if (i) s << ",";
        evidence(s, value.cells[i]);
    }
    s << "],\"overflow\":"; evidence(s, value.overflow); s << "}";
}
void orders(std::ostream & s, order_observation const & observation) {
    s << "[";
    for (size_t k = 0; k < 3; ++k) {
        if (k) s << ",";
        s << "["; evidence(s, observation.forward[k]);
        s << ","; evidence(s, observation.backward[k]); s << "]";
    }
    s << "]";
}
void program(std::ostream & s, organism_rule const & rule) {
    s << "[";
    bool separator = false;
    for (auto const & instruction : rule.program) {
        if (separator) s << ",";
        separator = true;
        s << "[" << static_cast<unsigned>(instruction.op) << "," << instruction.operand.mask() << "]";
    }
    s << "]";
}
void predictions(std::ostream & s, organism_rule const & rule) {
    s << "[";
    for (size_t x = 0; x < rule.prediction.size(); ++x) {
        if (x) s << ",";
        s << "[";
        for (size_t y = 0; y < rule.prediction[x].size(); ++y) {
            if (y) s << ",";
            s << rule.prediction[x][y].mask();
        }
        s << "]";
    }
    s << "]";
}
template<typename T> void operations(std::ostream & s, std::vector<T> const & values) {
    s << "[";
    for (size_t i = 0; i < values.size(); ++i) { if (i) s << ","; s << static_cast<unsigned>(values[i]); }
    s << "]";
}
std::string snapshot(dialetheic_organism const & o) {
    std::ostringstream s;
    s << std::setprecision(17);
    s << "{\"schema\":\"native-inclosure-v1\",\"source\":" << o.source().mask()
      << ",\"continuation\":" << o.continuation() << ",\"frontier\":[";
    for (size_t i = 0; i < o.frontier().size(); ++i) {
        if (i) s << ",";
        s << o.frontier()[i];
    }
    s << "],\"clock\":"; clock(s, o.clock());
    s << ",\"judge_program\":"; operations(s, o.judge_program());
    s << ",\"generator_program\":"; operations(s, o.generator_program());
    s << ",\"nodes\":[";
    for (size_t i = 0; i < o.tips().size(); ++i) {
        if (i) s << ",";
        auto const & tip = o.tips()[i];
        s << "{\"id\":" << i << ",\"parent\":" << tip.parent
          << ",\"state\":" << tip.state.mask() << ",\"boundary\":" << tip.body->boundary.mask()
          << ",\"source\":" << tip.body->source.mask() << ",\"interior\":" << tip.body->interior.mask()
          << ",\"attention\":";
        evidence(s, tip.attention);
        s << ",\"articulation\":[";
        for (size_t j = 0; j < tip.body->articulation.size(); ++j) {
            if (j) s << ",";
            s << tip.body->articulation[j].mask();
        }
        s << "],\"observations\":[";
        for (size_t j = 0; j < tip.body->observations.size(); ++j) {
            if (j) s << ",";
            s << tip.body->observations[j].mask();
        }
        s << "]}";
    }
    s << "],\"rules\":[";
    for (size_t i = 0; i < o.rules().size(); ++i) {
        if (i) s << ",";
        auto const & rule = o.rules()[i];
        s << "{\"program\":"; program(s, rule);
        s << ",\"experience\":"; evidence(s, rule.experience);
        s << ",\"fidelity\":"; evidence(s, rule.fidelity);
        s << ",\"prediction\":"; predictions(s, rule);
        s << "}";
    }
    s << "],\"learner\":" << o.learner_snapshot() << ",\"task\":" << o.task_snapshot() << ",\"actions\":[";
    for (size_t i = 0; i < o.history().size(); ++i) {
        if (i) s << ",";
        auto const & action = o.history()[i];
        s << "{\"tip\":" << action.tip << ",\"rule\":" << action.rule
          << ",\"before\":" << action.before.mask() << ",\"after\":" << action.after.mask()
          << ",\"change\":"; evidence(s, action.change);
        s << ",\"novelty\":"; evidence(s, action.novelty);
        s << ",\"fidelity\":"; evidence(s, action.fidelity);
        s << ",\"judge_before\":"; operations(s, action.judge_before);
        s << ",\"judge_after\":"; operations(s, action.judge_after);
        s << ",\"judgment\":"; evidence(s, action.judgment.value);
        s << ",\"judgment_trace\":[";
        for (size_t k = 0; k < action.judgment.trace.size(); ++k) {
            if (k) s << ",";
            evidence(s, action.judgment.trace[k]);
        }
        s << "],\"generator_before\":"; operations(s, action.generator_before);
        s << ",\"generator_after\":"; operations(s, action.generator_after);
        s << ",\"program_before\":"; program(s, action.machinery_before);
        s << ",\"program_after\":"; program(s, action.machinery_after);
        s << ",\"experience_before\":"; evidence(s, action.machinery_before.experience);
        s << ",\"experience_after\":"; evidence(s, action.machinery_after.experience);
        s << ",\"prediction_before\":"; predictions(s, action.machinery_before);
        s << ",\"prediction_after\":"; predictions(s, action.machinery_after);
        s << ",\"model_agreement\":"; evidence(s, action.model_agreement);
        s << ",\"model_ancestry\":[";
        for (size_t k = 0; k < action.model_ancestry.size(); ++k) {
            if (k) s << ",";
            s << action.model_ancestry[k];
        }
        s << "]";
        s << ",\"model_probes\":[";
        for (size_t k = 0; k < action.model_probes.size(); ++k) {
            if (k) s << ",";
            orders(s, action.model_probes[k]);
        }
        s << "],\"cost_before\":"; clock(s, action.cost_before);
        s << ",\"cost_after\":"; clock(s, action.cost_after);
        s << ",\"neural_operations\":[";
        for (size_t k = 0; k < action.neural_operations.size(); ++k) {
            if (k) s << ",";
            auto const & n = action.neural_operations[k];
            s << "{\"op\":" << static_cast<unsigned>(n.op)
              << ",\"input\":" << n.input.mask() << ",\"operand\":" << n.operand.mask()
              << ",\"expected\":" << n.expected.mask() << ",\"proposal_before\":" << n.proposal_before.mask()
              << ",\"proposal_after\":" << n.proposal_after.mask()
              << ",\"optimizer_before\":" << n.optimizer_before
              << ",\"optimizer_after\":" << n.optimizer_after << ",\"rails_before\":[";
            for (size_t j = 0; j < 4; ++j) { if (j) s << ","; s << n.rails_before[j]; }
            s << "],\"rails_after\":[";
            for (size_t j = 0; j < 4; ++j) { if (j) s << ","; s << n.rails_after[j]; }
            s << "],\"membership_evidence\":[";
            for (size_t j = 0; j < 4; ++j) { if (j) s << ","; evidence(s, n.membership_evidence[j]); }
            s << "]}";
        }
        s << "]";
        s << ",\"order_observations\":"; orders(s, action.observation);
        s << ",\"task_operations\":[";
        for(size_t k=0;k<action.task_operations.size();++k){
            if(k)s<<",";
            auto const & task=action.task_operations[k];
            s<<"{\"component\":"<<task.component<<",\"feedback\":"<<task.feedback.mask()
             <<",\"closed\":"<<(task.closed?"true":"false")<<",\"retained_state\":"<<task.state<<"}";
        }
        s<<"]";
        s << "}";
    }
    s << "]}";
    return s.str();
}
}

void initialize_inclosure() {
    g_organism_class = lean_register_external_class(destroy_organism, visit_organism);
}

extern "C" LEAN_EXPORT obj_res lean_organism_create(b_obj_arg source) {
    auto value = sixteen3(cnstr_get_uint8(source, 0), cnstr_get_uint8(source, 1),
                         cnstr_get_uint8(source, 2), cnstr_get_uint8(source, 3));
    return io_result_mk_ok(alloc_external(g_organism_class, new organism_handle(value)));
}

extern "C" LEAN_EXPORT obj_res lean_organism_step(b_obj_arg handle) {
    auto & organism = get_organism(handle);
    std::lock_guard<std::mutex> guard(organism.lock);
    organism.body.step();
    return io_result_mk_ok(box(0));
}

extern "C" LEAN_EXPORT obj_res lean_organism_attach_vgi(b_obj_arg handle, b_obj_arg path) {
    auto & organism = get_organism(handle);
    std::lock_guard<std::mutex> guard(organism.lock);
    try {
        organism.body.attach(std::make_shared<vgi_organism_learner>(string_cstr(path)));
        return io_result_mk_ok(box(0));
    } catch (std::exception const & error) {
        return io_result_mk_error(error.what());
    }
}

extern "C" LEAN_EXPORT obj_res lean_organism_snapshot(b_obj_arg handle) {
    auto & organism = get_organism(handle);
    std::lock_guard<std::mutex> guard(organism.lock);
    return io_result_mk_ok(mk_string(snapshot(organism.body)));
}
extern "C" LEAN_EXPORT obj_res lean_organism_attach_factor(b_obj_arg handle,b_obj_arg source,b_obj_arg path) {
    auto & organism=get_organism(handle);
    std::lock_guard<std::mutex> guard(organism.lock);
    try {
        organism.body.attach_task(std::make_shared<organism_factor_task>(string_cstr(source),string_cstr(path)));
        return io_result_mk_ok(box(0));
    } catch(std::exception const & error){return io_result_mk_error(error.what());}
}
extern "C" LEAN_EXPORT obj_res lean_organism_task_closed(b_obj_arg handle) {
    auto & organism=get_organism(handle);
    std::lock_guard<std::mutex> guard(organism.lock);
    return io_result_mk_ok(box(organism.body.task_closed()));
}
}
