from typing import Tuple

from programs.analysis.predicate_abstraction import predicate_abstraction, abstraction_to_ltl
from programs.analysis.refinement import safety_refinement, liveness_refinement, use_liveness_refinement
from programs.program import Program
from programs.synthesis import ltl_synthesis
from programs.synthesis.ltl_synthesis import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from programs.synthesis.mealy_machine import MealyMachine
from programs.util import symbol_table_from_program, create_nuxmv_model_for_compatibility_checking, \
    there_is_mismatch_between_monitor_and_strategy, \
    parse_nuxmv_ce_output_finite, reduce_up_to_iff, \
    concretize_and_ground_transitions, add_prev_suffix, label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import neg, G, F, implies, conjunct, disjunct_formula_set, X, disjunct
from prop_lang.variable import Variable


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool) -> Tuple[bool, Program]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        ltl_text = ltl_text.replace('"', "")
        in_acts_syfco = syfco_ltl_in(tlsf_path)
        out_acts_syfco = syfco_ltl_out(tlsf_path)

    ltl = string_to_ltl(ltl_text)
    in_acts = [e for e in aut.env_events + aut.out_events]
    out_acts = [e for e in aut.con_events]

    if [] != [x for x in in_acts_syfco if x not in in_acts] + [x for x in in_acts if x not in in_acts_syfco]:
        raise Exception("TLSF file has different input variables than the program.")

    if [] != [x for x in out_acts_syfco if x not in out_acts] + [x for x in out_acts if x not in out_acts_syfco]:
        raise Exception("TLSF file has different output variables than the program.")

    in_acts += [Variable(e) for e in aut.states]

    return abstract_synthesis_loop(aut, ltl, in_acts, out_acts, docker)


def abstract_synthesis_loop(program: Program, ltl: Formula, in_acts: [Variable], out_acts: [Variable], docker: str) -> \
        Tuple[bool, MealyMachine]:
    symbol_table = symbol_table_from_program(program)

    state_predicates = []
    rankings = []
    transition_predicates = []

    program_nuxmv_model = program.to_nuXmv_with_turns()
    mon_events = program.out_events \
                 + [Variable(s) for s in program.states]

    while True:
        abstract_program = predicate_abstraction(program, state_predicates, transition_predicates, symbol_table)
        print(abstract_program.to_dot())

        pred_list = state_predicates + transition_predicates
        abstraction = abstraction_to_ltl(abstract_program, state_predicates, transition_predicates)
        print(", ".join(map(str, abstraction)))

        pred_name_dict = {p: label_pred(p) for p in pred_list}
        pred_acts = [pred_name_dict[v] for v in pred_name_dict.keys()]

        predicate_constraints = []
        i = 0
        while i < len(state_predicates):
            pred = pred_name_dict[pred_list[i]]
            not_pred = pred_name_dict[pred_list[i + 1]]
            predicate_constraints += [G(neg(conjunct(pred, not_pred)))]
            i += 2
        while i < len(pred_list):
            dec = pred_name_dict[pred_list[i]]
            not_dec = pred_name_dict[pred_list[i + 1]]
            inc = pred_name_dict[pred_list[i + 2]]
            not_inc = pred_name_dict[pred_list[i + 3]]
            predicate_constraints += [X(G(neg(conjunct(dec, not_dec))))]
            predicate_constraints += [X(G(neg(conjunct(inc, not_inc))))]
            predicate_constraints += [X(G(disjunct_formula_set([conjunct(dec, not_inc), conjunct(inc, not_dec), conjunct(not_dec, not_inc)])))]

            predicate_constraints += [implies(G(F(dec)), G(F(inc)))]
            i += 4

        assumptions = predicate_constraints + abstraction

        (real, mm) = ltl_synthesis.ltl_synthesis(assumptions,
                                                 [ltl],
                                                 in_acts + pred_acts,
                                                 out_acts,
                                                 docker)

        mealy = mm.to_nuXmv_with_turns(mon_events, state_predicates, transition_predicates)

        print(mm.to_dot(pred_list))
        controller_projected_on_program = mm.project_controller_on_program(program, abstract_program, pred_list,
                                                                           symbol_table)

        print(controller_projected_on_program.to_dot())

        if real:
            return True, controller_projected_on_program
        else:
            system = create_nuxmv_model_for_compatibility_checking(program_nuxmv_model, mealy, mon_events, pred_list)
            there_is_mismatch, out = there_is_mismatch_between_monitor_and_strategy(system, False)

            if not there_is_mismatch:
                for t in controller_projected_on_program.con_transitions + controller_projected_on_program.env_transitions:
                    ok = False
                    for tt in controller_projected_on_program.con_transitions + controller_projected_on_program.env_transitions:
                        if t.tgt[0] == tt.src[0] and set(t.tgt[1]) == set(tt.src[1]):
                            ok = True
                            break

                    if not ok:
                        raise Exception(
                            "I have no idea what's gone wrong. The counterstrategy has no outgoing transition from this monitor state: " + str(t.tgt[0]) + ", " + ", ".join([str(p) for p in t.tgt[1]]))

                # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
                return False, controller_projected_on_program
            else:
                ce, transition_indices_and_state = parse_nuxmv_ce_output_finite(out)
                transitions = program.env_transitions + program.con_transitions
                transitions_without_stutter = [transitions[int(t)] for t, _ in transition_indices_and_state if
                                               t != '-1']

                use_liveness, counterexample_loop = use_liveness_refinement(ce, symbol_table)

                if not use_liveness:
                    new_preds = safety_refinement(ce, transitions_without_stutter, symbol_table, program)
                    print(", ".join([str(p) for p in new_preds]))
                    if new_preds == []:
                        raise Exception("No new state predicates identified.")

                    new_all_preds = {x.simplify() for x in new_preds}
                    new_all_preds = reduce_up_to_iff(state_predicates, list(new_all_preds), symbol_table)

                    if len(new_all_preds) == len(state_predicates):
                        raise Exception(
                            "New state predicates (" + ", ".join([str(p) for p in new_preds]) + ") are a subset of "
                                                                                                "previous predicates.")

                    state_predicates = list(new_all_preds)

                if use_liveness:
                    last_transition = transitions_without_stutter[len(transitions_without_stutter) - 1]

                    desired_env_props = []
                    desired_prog_props = []

                    # use mismatch_ce_state to identify which program transitions the env wanted to take
                    mismatch_ce_state = ce[len(ce) - 1]
                    for key in mismatch_ce_state.keys():
                        if "mon_" in key and key.replace("mon_", "") in map(str, program.states):
                            if mismatch_ce_state[key] == "TRUE":
                                desired_prog_props.append(Variable(key.replace("mon_", "")))
                            else:
                                desired_prog_props.append(neg(Variable(key.replace("mon_", ""))))
                        elif key in map(str, program.env_events):
                            if mismatch_ce_state[key] == "TRUE":
                                desired_env_props.append(Variable(key))
                            else:
                                desired_env_props.append(neg(Variable(key)))

                    # identify the loop in the monitor exercised by the counterexample
                    loop_before_exit = concretize_and_ground_transitions(program, counterexample_loop)
                    # transitions_to_close_loop = grounded_desired_prog_trans

                    ranking, invars = liveness_refinement(symbol_table,
                                                          program,
                                                          loop_before_exit,
                                                          last_transition.condition)
                    rankings.append((ranking, invars))
                    if len(invars) > 0:
                        raise NotImplementedError(
                            "Ranking function comes with invar, what shall we do here? " + ranking + "\n" + ", ".join(
                                [str(invar) for invar in invars]))

                    new_transition_predicates = [x for r, _ in rankings for x in
                                                 [BiOp(add_prev_suffix(program, r), ">", r),
                                                  neg(BiOp(add_prev_suffix(program, r), ">", r)),
                                                  BiOp(add_prev_suffix(program, r), "<", r),
                                                  neg(BiOp(add_prev_suffix(program, r), "<", r))]]

                    print(", ".join([str(p) for p in new_transition_predicates]))
                    if new_transition_predicates == []:
                        raise Exception("No new transition predicates identified.")

                    new_all_trans_preds = {x.simplify() for x in new_transition_predicates}
                    new_all_trans_preds = reduce_up_to_iff(transition_predicates, list(new_all_trans_preds),
                                                           symbol_table)

                    if len(new_all_trans_preds) == len(transition_predicates):
                        raise Exception("I did something wrong, "
                                        "it turns out the new transition predicates "
                                        "(" + ", ".join(
                            [str(p) for p in new_transition_predicates]) + ") are a subset of "
                                                                           "previous predicates.")
                    # important to add this, since later on assumptions depend on position of predicates in list
                    transition_predicates += new_transition_predicates
