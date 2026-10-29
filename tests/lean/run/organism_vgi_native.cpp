#include "kernel/organism_vgi.h"
#include <iostream>

static void require(bool p, char const * message) {
    if (!p) throw std::runtime_error(message);
}
int main(int argc, char ** argv) {
    using namespace lean;
    require(argc == 2, "supply the bound VGI organism adapter");
    auto learner = std::make_shared<vgi_organism_learner>(argv[1]);
    auto frozen = std::make_shared<vgi_organism_learner>(argv[1], false);
    auto initial = frozen->snapshot();
    require(initial == learner->snapshot(), "comparison learners start differently");
    dialetheic_organism body(sixteen3::from_mask(8));
    dialetheic_organism control(sixteen3::from_mask(8));
    body.attach(learner);
    control.attach(frozen);
    body.step();
    require(initial == frozen->snapshot(), "organisms share mutable VGI weights or memory");
    control.step();
    for (unsigned i = 1; i < 4; ++i) { body.step(); control.step(); }
    unsigned operations = 0, corrected = 0, learned_actions = 0, different_actions = 0;
    unsigned held_coordinates = 0;
    for (size_t i = 0; i < body.history().size(); ++i) {
        auto const & action = body.history()[i];
        auto carried = action.before;
        require(action.neural_operations.size() == action.machinery_before.program.size(),
                "neural mechanism did not execute each program instruction");
        for (size_t j = 0; j < action.neural_operations.size(); ++j) {
            auto const & neural = action.neural_operations[j];
            require(neural.input == carried, "neural operation lost the executing state");
            require(neural.expected == action.machinery_before.program[j].apply(carried),
                    "neural observation lost native oracle binding");
            require(neural.optimizer_after == neural.optimizer_before + 1,
                    "full-network update did not execute");
            for (unsigned bit = 0; bit < 4; ++bit) {
                auto e = witnessed((neural.proposal_after.mask() >> bit) & 1).join(
                         witnessed((neural.expected.mask() >> bit) & 1));
                require(neural.membership_evidence[bit] == e, "paired membership evidence lost");
                require(body.tips()[i + 1].body->observations[10 + 6 * j + 2 + bit] == e.singleton(),
                        "contradictory coordinate evidence lost in nested return");
                if (e.truth && e.falsity) ++held_coordinates;
            }
            if (neural.proposal_before != neural.proposal_after) ++corrected;
            carried = neural.proposal_after;
            ++operations;
        }
        require(carried == action.after, "neural return did not become the carried action result");
        if (action.fidelity.falsity)
            require(action.machinery_after.program.size() > action.machinery_before.program.size(),
                    "observed neural disagreement did not revise executing machinery");
        if (action.after != action.machinery_before.apply(action.before)) ++learned_actions;
        if (action.after != control.history()[i].after) ++different_actions;
    }
    require(operations && learned_actions, "neural computation never changed mathematical production");
    require(different_actions, "online learning never changed later actions against its frozen control");
    require(held_coordinates, "neural/native contradictory support was never retained");
    require(body.body().interior == sixteen3_all() && body.body().boundary == sixteen3::from_mask(8),
            "neural execution lost the B-to-B construction");
    std::cout << "{\"status\":\"passed\",\"neural_operations\":" << operations
              << ",\"changed_proposals\":" << corrected << ",\"neural_action_returns\":" << learned_actions
              << ",\"learning_changed_actions\":" << different_actions
              << ",\"held_coordinates\":" << held_coordinates << "}\n";
}
