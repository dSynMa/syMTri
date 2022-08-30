from typing import Tuple

from programs.analysis.predicate_abstraction import predicate_abstraction, abstraction_to_ltl
from programs.analysis.refinement import safety_refinement, liveness_refinement
from programs.program import Program
from programs.synthesis.mealy_machine import MealyMachine
from programs.util import symbol_table_from_program, create_nuxmv_model_for_compatibility_checking, \
    use_liveness_refinement, label_pred_according_to_index, create_nuxmv_model, mismatch_between_monitor_strategy, \
    parse_nuxmv_ce_output_finite, reduce_up_to_iff
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import implies, conjunct_formula_set
from prop_lang.variable import Variable
from strix import strix_adapter
from strix.strix_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool) -> Tuple[bool, Program]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        ltl_text = ltl_text.replace('"', "")
        # TODO use below for sanity checking of monitor variables
        in_acts = syfco_ltl_in(tlsf_path)
        out_acts = syfco_ltl_out(tlsf_path)

    ltl = string_to_ltl(ltl_text)
    in_acts = [e for e in aut.env_events + aut.out_events] + [e for e in aut.states]
    out_acts = [e for e in aut.con_events]
    # TODO validate in_acts, out_acts against those from TLSF
    return abstract_synthesis_loop(aut, ltl, in_acts, out_acts, docker)


def abstract_synthesis_loop(program: Program, ltl: Formula, in_acts: [Variable], out_acts: [Variable], docker: str) -> \
        Tuple[bool, MealyMachine]:
    symbol_table = symbol_table_from_program(program)

    preds = set()
    liveness_assumptions = []

    program_nuxmv_model = program.to_nuXmv_with_turns()
    mon_events = program.out_events \
                 + [Variable(s) for s in program.states]

    while True:
        pred_list = list(preds)
        abstract_monitor = predicate_abstraction(program, pred_list, symbol_table)
        print(abstract_monitor.to_dot())
        abstraction = abstraction_to_ltl(abstract_monitor, pred_list)
        print(abstraction)
        abstract_problem = implies(conjunct_formula_set([abstraction] + liveness_assumptions), ltl)

        pred_acts = [Variable("pred_" + str(i)) for i in range(0, len(preds))]
        pred_var_list = [label_pred_according_to_index(p, pred_list) for p in pred_list]

        (real, mm) = strix_adapter.strix(abstract_problem, in_acts + pred_acts, out_acts, docker)

        mealy = mm.to_nuXmv_with_turns(mon_events + pred_var_list)
        print(mm.to_dot())
        system = create_nuxmv_model_for_compatibility_checking(program_nuxmv_model, mealy, mon_events, pred_list)
        there_is_a_mismatch, out = mismatch_between_monitor_strategy(system)

        if real:
            # sanity check
            if there_is_a_mismatch:
                raise Exception("Controller does not conform to monitor.")

            return (real, mm)
        else:
            if there_is_a_mismatch:
                # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
                return False, mm
            else:
                ce, transition_indices = parse_nuxmv_ce_output_finite(out)
                transitions = program.env_transitions + program.con_transitions
                transitions_without_stutter = [transitions[int(t)] for t in transition_indices if t != '-1']

                use_liveness = use_liveness_refinement(ce, symbol_table)
                force_liveness = False

                if not use_liveness:
                    new_preds = safety_refinement(ce, transitions_without_stutter, symbol_table, program)
                    print(new_preds)
                    if new_preds == []:
                        raise Exception("No predicates identified, use liveness instead?")

                    new_all_preds = {x.simplify() for x in new_preds}
                    new_all_preds = reduce_up_to_iff(preds, list(new_all_preds), symbol_table)

                    if len(new_all_preds) == len(preds):
                        print("New predicates (" + ", ".join([str(p) for p in new_preds]) + ") are subset of "
                                                                                            "previous predicates, attempting liveness instead.")
                        force_liveness = True

                    preds = new_all_preds

                if use_liveness or force_liveness:
                    success, new_formula = liveness_refinement(create_nuxmv_model(program_nuxmv_model),
                                                               transitions_without_stutter[
                                                                   len(transitions_without_stutter) - 1])
                    if not success:
                        raise NotImplementedError(
                            "Counterstrategy is trying to stay in a loop in a monitor that involves an infinite-state variable. "
                            "The current heuristics are not enough to prove this impossible.")
                    else:
                        liveness_assumptions.append(new_formula)
