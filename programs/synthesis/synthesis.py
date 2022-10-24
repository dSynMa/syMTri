from typing import Tuple

from programs.abstraction.predicate_abstraction import predicate_abstraction, abstraction_to_ltl
from programs.abstraction.refinement import safety_refinement, liveness_refinement, use_liveness_refinement
from programs.program import Program
from programs.synthesis import ltl_synthesis
from programs.synthesis.ltl_synthesis import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from programs.synthesis.mealy_machine import MealyMachine
from programs.typed_valuation import TypedValuation
from programs.util import symbol_table_from_program, create_nuxmv_model_for_compatibility_checking, \
    there_is_mismatch_between_monitor_and_strategy, \
    parse_nuxmv_ce_output_finite, reduce_up_to_iff, \
    add_prev_suffix, label_pred, ground_predicate_on_bool_vars, \
    concretize_transitions, ground_transitions_and_flatten
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import neg, G, F, implies, conjunct, X, true
from prop_lang.variable import Variable


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool) -> Tuple[bool, Program]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if " Error\"" in ltl_text:
            raise Exception("Error parsing " + tlsf_path + " see syfco error:\n" + ltl_text)
        ltl_text = ltl_text.replace('"', "")
        in_acts_syfco = syfco_ltl_in(tlsf_path)
        out_acts_syfco = syfco_ltl_out(tlsf_path)

    ltl = string_to_ltl(ltl_text)

    if isinstance(ltl, BiOp) and (ltl.op == "->" or ltl.op == "=>"):
        ltl_assumptions = ltl.left
        ltl_guarantees = ltl.right
    else:
        ltl_assumptions = true()
        ltl_guarantees = ltl

    in_acts = [e for e in aut.env_events + aut.out_events]
    out_acts = [e for e in aut.con_events]

    if [] != [x for x in in_acts_syfco if x not in in_acts] + [x for x in in_acts if x not in in_acts_syfco]:
        raise Exception("TLSF file has different input variables than the program.")

    if [] != [x for x in out_acts_syfco if x not in out_acts] + [x for x in out_acts if x not in out_acts_syfco]:
        raise Exception("TLSF file has different output variables than the program.")

    in_acts += [Variable(e) for e in aut.states]

    return abstract_synthesis_loop(aut, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker)


def abstract_synthesis_loop(program: Program, ltl_assumptions: Formula, ltl_guarantees: Formula, in_acts: [Variable],
                            out_acts: [Variable], docker: str) -> \
        Tuple[bool, MealyMachine]:
    # TODO add check that monitor is deterministic under given ltl assumptions
    eager = False

    symbol_table = symbol_table_from_program(program)
    ltl = implies(ltl_assumptions, ltl_guarantees).simplify()

    state_predicates = []
    rankings = []
    transition_predicates = []

    program_nuxmv_model = program.to_nuXmv_with_turns()
    mon_events = program.out_events \
                 + [Variable(s) for s in program.states]

    while True:
        abstract_program = predicate_abstraction(program, state_predicates, transition_predicates, symbol_table, True)
        print(abstract_program.to_dot())

        pred_list = state_predicates + transition_predicates
        abstraction = abstraction_to_ltl(abstract_program, state_predicates, transition_predicates)
        print(", ".join(map(str, abstraction)))

        pred_name_dict = {p: label_pred(p, pred_list) for p in pred_list}
        pred_acts = [pred_name_dict[v] for v in pred_name_dict.keys()]

        predicate_constraints = []
        i = 0
        while i < len(transition_predicates):
            dec = pred_name_dict[transition_predicates[i]]
            inc = pred_name_dict[transition_predicates[i + 1]]
            predicate_constraints += [X(G(neg(conjunct(dec, inc))))]

            predicate_constraints += [implies(G(F(dec)), G(F(inc)))]
            i += 2

        assumptions = predicate_constraints + abstraction

        (real, mm) = ltl_synthesis.ltl_synthesis(assumptions,
                                                 [ltl],
                                                 in_acts + pred_acts,
                                                 out_acts,
                                                 docker)

        mealy = mm.to_nuXmv_with_turns(program.states, program.out_events, state_predicates, transition_predicates)

        print(mm.to_dot(pred_list))

        symbol_table_preds = {str(label_pred(v, pred_list)):TypedValuation(str(label_pred(v, pred_list)), "bool", true()) for v in pred_list}
        symbol_table_prevs = {tv.name+"_prev":TypedValuation(tv.name+"_prev", tv.type, tv.value) for tv in program.valuation}
        controller_projected_on_program = mm.project_controller_on_program(program, abstract_program, state_predicates,
                                                                           transition_predicates, symbol_table | symbol_table_preds)

        print(controller_projected_on_program.to_dot())

        system = create_nuxmv_model_for_compatibility_checking(program_nuxmv_model, mealy, mon_events, pred_list)
        contradictory, there_is_mismatch, out = there_is_mismatch_between_monitor_and_strategy(system, real, False, ltl_assumptions, ltl_guarantees)

        if contradictory:
            raise Exception("I have no idea what's gone wrong. Strix thinks the previous mealy machine is a " +
                            ("controller" if real else "counterstrategy") + ", but nuxmv thinks it is non consistent with the monitor.")

        if not there_is_mismatch:
            for t in controller_projected_on_program.con_transitions + controller_projected_on_program.env_transitions:
                ok = False
                for tt in controller_projected_on_program.con_transitions + controller_projected_on_program.env_transitions:
                    if t.tgt == tt.src:
                        ok = True
                        break

                if not ok:
                    print(
                        "Warning: Model checking says counterstrategy is fine, but something has gone wrong with projection "
                        "onto the predicate abstraction, and I have no idea why. "
                        "The " + ("controller" if real else "counterstrategy") + " has no outgoing transition from this monitor state: "
                        + ", ".join([str(p) for p in list(t.tgt)]))
            if real:
                return True, controller_projected_on_program
            else:
                # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
                return False, controller_projected_on_program

        else:
            ce, transition_indices_and_state = parse_nuxmv_ce_output_finite(out)
            transitions_without_stutter = concretize_transitions(program, transition_indices_and_state)
            print("Counterexample is:\n" + "\n".join(
                [str(t[0]) + " var values: " + ", ".join([str(v) + "=" + t[1][str(v)] for v in t[0].condition.variablesin()]) for
                 ts in transitions_without_stutter for t in ts]))

            use_liveness, counterexample_loop, entry_predicate = use_liveness_refinement(ce, program, symbol_table)

            if use_liveness:
                ranking, invars = liveness_step(program, counterexample_loop, symbol_table, entry_predicate)
                rankings.append((ranking, invars))
                new_transition_predicates = [x for r, _ in rankings for x in
                                             [BiOp(add_prev_suffix(program, r), ">", r),
                                              BiOp(add_prev_suffix(program, r), "<", r)
                                              ]]

                print(", ".join([str(p) for p in new_transition_predicates]))
                if new_transition_predicates == []:
                    # raise Exception("No new transition predicates identified.")
                    print("No transition predicates identified. So will try safety refinement.")
                    use_liveness = False

                new_all_trans_preds = {x.simplify() for x in new_transition_predicates}
                new_all_trans_preds = reduce_up_to_iff(transition_predicates, list(new_all_trans_preds),
                                                       symbol_table | symbol_table_prevs)

                if len(new_all_trans_preds) == len(transition_predicates):
                    print("I did something wrong, "
                                    "it turns out the new transition predicates "
                                    "(" + ", ".join(
                        [str(p) for p in new_transition_predicates]) + ") are a subset of "
                                                                       "previous predicates.\n"
                                                                       "Counterexample was:\n" + "\n".join(
                        [str(t[0]) for ts in transitions_without_stutter for t in ts]))
                    print("I will try safety refinement instead.")
                    use_liveness = False
                # important to add this, since later on assumptions depend on position of predicates in list
                transition_predicates += new_transition_predicates

            if eager or not use_liveness:
                new_preds = safety_refinement(ce, transitions_without_stutter, symbol_table, program)
                print(", ".join([str(p) for p in new_preds]))
                if new_preds == []:
                    raise Exception("No new state predicates identified.")

                new_all_preds = {x.simplify() for x in new_preds}
                new_all_preds = reduce_up_to_iff(state_predicates,
                                                 list(new_all_preds),
                                                 symbol_table
                                                 | {str(v): TypedValuation(str(v), symbol_table[str(v).removesuffix("_prev")].type, "true")
                for p in new_all_preds
                for v in p.variablesin()
                if str(v).endswith("prev")}) # TODO symbol_table needs to be updated with prevs

                if len(new_all_preds) == len(state_predicates):
                    raise Exception(
                        "New state predicates (" + ", ".join([str(p) for p in new_preds]) + ") are a subset of "
                                                                                            "previous predicates.\n"
                                                                                            "Counterexample was:\n" + "\n".join(
                            [str(t[0]) + "\n var values: " + ", ".join([str(v) + "=" + t[1][str(v)] for v in set(t[0].condition.variablesin() + [v for v in list(t[1].keys()) if str(v).startswith("mon_")] + [v for v in program.env_events + program.con_events])]) for ts in transitions_without_stutter for t in ts])
                   )

                state_predicates = list(new_all_preds)


def liveness_step(program, counterexample_loop, symbol_table, entry_predicate):
    # ground transitions in the counterexample loop
    # on the environment and controller events in the counterexample
    loop_before_exit = ground_transitions_and_flatten(program, counterexample_loop[:-1])
    exit_transitions = ground_transitions_and_flatten(program, [counterexample_loop[-1]])

    entry_predicate_grounded = ground_predicate_on_bool_vars(program, entry_predicate,
                                                             counterexample_loop[0][-1][1]).simplify()

    ranking, invars = liveness_refinement(symbol_table,
                                          program,
                                          entry_predicate_grounded,
                                          loop_before_exit,
                                          exit_transitions)
    if len(invars) > 0:
        raise NotImplementedError(
            "Ranking function comes with invar, what shall we do here? " + ranking + "\n" + ", ".join(
                [str(invar) for invar in invars]))

    return ranking, invars

