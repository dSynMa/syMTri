from itertools import chain
from typing import Tuple

from click._compat import raw_input
from pysmt.shortcuts import And
from programs.analysis.smt_checker import SMTChecker

from parsing.string_to_ltl import string_to_ltl
from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from programs.abstraction.predicate_abstraction import PredicateAbstraction
from programs.abstraction.refinement import safety_refinement, liveness_refinement, use_liveness_refinement
from programs.program import Program
from programs.synthesis import ltl_synthesis
from programs.synthesis.ltl_synthesis import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from programs.synthesis.mealy_machine import MealyMachine
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import create_nuxmv_model_for_compatibility_checking, \
    there_is_mismatch_between_monitor_and_strategy, \
    parse_nuxmv_ce_output_finite, reduce_up_to_iff, \
    add_prev_suffix, label_pred, \
    concretize_transitions, ce_state_to_predicate_abstraction_trans, \
    check_for_nondeterminism_last_step, ground_transitions, keep_bool_preds, function_is_of_natural_type, \
    ground_predicate_on_vars
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.util import neg, G, F, implies, conjunct, true, conjunct_formula_set, dnf, is_tautology
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()

def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool, project_on_abstraction=True) -> Tuple[bool, Program]:
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

    in_acts = [e for e in aut.env_events]
    out_acts = [e for e in aut.con_events]
    prog_acts = aut.out_events

    if any(x for x in in_acts + prog_acts if x not in in_acts_syfco):
        raise Exception("TLSF file has different input variables than the program.")

    if any(x for x in out_acts if x not in out_acts_syfco):
        raise Exception("TLSF file has different output variables than the program.")

    return abstract_synthesis_loop(aut, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker, project_on_abstraction=project_on_abstraction)


def abstract_synthesis_loop(program: Program, ltl_assumptions: Formula, ltl_guarantees: Formula, in_acts: [Variable],
                            out_acts: [Variable], docker: str, project_on_abstraction=False) -> \
        Tuple[bool, MealyMachine]:
    # TODO add check that monitor is deterministic under given ltl assumptions
    eager = False
    keep_only_bool_interpolants = True
    use_explicit_loops_abstraction = False
    no_analysis_just_user_input = False
    choose_predicates = False
    conservative_with_state_predicates = False

    state_predicates = [Variable(p.name) for p in program.valuation if p.type == "bool"]
    rankings = []
    transition_predicates = []
    transition_predicates_invars = {}

    in_acts += [Variable("inloop"), Variable("notinloop")]
    transition_fairness = []
    predicate_abstraction = PredicateAbstraction(program)

    while True:
        symbol_table = predicate_abstraction.program.symbol_table
        predicate_abstraction.add_predicates(state_predicates,
                                                transition_predicates,
                                                symbol_table,
                                                True)
        symbol_table["inloop"] = TypedValuation("inloop", "bool", True)
        symbol_table["notinloop"] = TypedValuation("notinloop", "bool", True)

        mon_events = predicate_abstraction.program.out_events \
                     + [Variable(s) for s in predicate_abstraction.program.states]
        ## Compute abstraction
        print(predicate_abstraction.abstraction.to_dot())

        pred_list = state_predicates + transition_predicates

        abstraction, ltl_to_program_transitions = predicate_abstraction.abstraction_to_ltl()
        print(", ".join(map(str, abstraction)))

        pred_name_dict = {p: label_pred(p, pred_list) for p in pred_list}
        state_pred_label_to_formula = {label_pred(p, pred_list): p for p in state_predicates}
        state_pred_label_to_formula |= {neg(label_pred(p, pred_list)): neg(p) for p in state_predicates}
        pred_acts = [pred_name_dict[v] for v in pred_name_dict.keys()]

        # should be computed incrementally
        # transition_fairness = []
        safety_predicate_constraints = []
        i = 0
        while i < len(transition_predicates):
            dec = pred_name_dict[transition_predicates[i]]
            inc = pred_name_dict[transition_predicates[i + 1]]
            safety_predicate_constraints += [(G(neg(conjunct(dec, inc))))]

            invar_vars = [pred_name_dict[p] for p in transition_predicates_invars[rankings[i % 2][0]]]
            invar_formula = conjunct_formula_set(invar_vars)

            transition_fairness += [implies(G(F(conjunct(invar_formula, dec))), G(F(inc)))]
            i += 2


        assumptions = [ltl_assumptions] + transition_fairness + safety_predicate_constraints + abstraction
        guarantees = [ltl_guarantees]

        (real, mm) = ltl_synthesis.ltl_synthesis(assumptions,
                                                 guarantees,
                                                 in_acts + mon_events + pred_acts,
                                                 out_acts,
                                                 docker)

        ## checking for mismatch
        mealy = mm.to_nuXmv_with_turns(predicate_abstraction.program.states, predicate_abstraction.program.out_events, state_predicates, transition_predicates)

        print(mm.to_dot(pred_list))

        symbol_table_preds = {
            str(label_pred(v, pred_list)): TypedValuation(str(label_pred(v, pred_list)), "bool", true()) for v in
            pred_list}
        symbol_table_prevs = {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                              program.valuation}

        system = create_nuxmv_model_for_compatibility_checking(program, mealy, mon_events, pred_list, False, False)
        contradictory, there_is_mismatch, out = there_is_mismatch_between_monitor_and_strategy(system, real, False,
                                                                                               ltl_assumptions,
                                                                                               ltl_guarantees)
        ## end checking for mismatch

        ## deal with if there is nothing wrong
        if not there_is_mismatch or contradictory:
            print("No mismatch found between " + (
                "strategy" if real else "counterstrategy") + " and program when excluding traces for which the monitor has a non-deterministic choice.")
            print("Trying for when the monitor has a non-deterministic choice..")
            system = create_nuxmv_model_for_compatibility_checking(program, mealy, mon_events, pred_list, True, True, False)
            contradictory, there_is_mismatch, out = there_is_mismatch_between_monitor_and_strategy(system, real, False,
                                                                                                   ltl_assumptions,
                                                                                                   ltl_guarantees)

            if contradictory:
                raise Exception("I have no idea what's gone wrong. Strix thinks the previous mealy machine is a " +
                                (
                                    "controller" if real else "counterstrategy") + ", but nuxmv thinks it is non consistent with the monitor.\n"
                                                                                   "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division.")

            if not there_is_mismatch:
                print("No mismatch found between " + (
                    "strategy" if real else "counterstrategy") + " and program even when including traces for which the monitor has a non-deterministic choice.")

                print("Looking for mismatches in predicates.")

                system = create_nuxmv_model_for_compatibility_checking(program, mealy, mon_events, pred_list, True,
                                                                       True, False)
                contradictory, there_is_mismatch, out = there_is_mismatch_between_monitor_and_strategy(system, real,
                                                                                                       False,
                                                                                                       ltl_assumptions,
                                                                                                       ltl_guarantees)
                if not there_is_mismatch:
                    print("No mismatch found.")

                    ## Finished
                    if project_on_abstraction:
                        print("Computing projection of controller onto predicate abstraction..")
                        controller_projected_on_program = mm.project_controller_on_program(program, predicate_abstraction,
                                                                                           symbol_table | symbol_table_preds)

                        for t in controller_projected_on_program.con_transitions + controller_projected_on_program.env_transitions:
                            ok = False
                            for tt in controller_projected_on_program.con_transitions + controller_projected_on_program.env_transitions:
                                if t.tgt == tt.src:
                                    ok = True
                                    break

                            if not ok:
                                print(controller_projected_on_program.to_dot())

                                raise Exception(
                                    "Warning: Model checking says counterstrategy is fine, but something has gone wrong with projection "
                                    "onto the predicate abstraction, and I have no idea why. "
                                    "The " + (
                                        "controller" if real else "counterstrategy") + " has no outgoing transition from this monitor state: "
                                    + ", ".join([str(p) for p in list(t.tgt)]))
                        result = controller_projected_on_program.to_dot()
                    else:
                        result = mm.to_dot(pred_list)

                    if real:
                        return True, result
                    else:
                        # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
                        return False, result

        print(out)
        ## Compute mismatch trace
        ce, transition_indices_and_state = parse_nuxmv_ce_output_finite(
            len(program.env_transitions) + len(program.con_transitions), out)
        transitions_without_stutter_monitor_took, pred_state = concretize_transitions(program, program, transition_indices_and_state, False)

        if pred_state is not None:
            agreed_on_transitions = transitions_without_stutter_monitor_took
            disagreed_on_state = pred_state
            disagreed_on_state_dict = disagreed_on_state[1]

            write_counterexample_state(program, agreed_on_transitions, disagreed_on_state)

        else:
            agreed_on_transitions = transitions_without_stutter_monitor_took[:-1]
            # disagreed_on_transitions = []
            monitor_actually_took = transitions_without_stutter_monitor_took[-1]

            mon_state, con_state, env_state = ce[-4], ce[-3], ce[-2]
            last_desired_env_con_env_trans: [(Transition, Transition)] = ce_state_to_predicate_abstraction_trans(
                ltl_to_program_transitions, symbol_table | symbol_table_preds, mon_state, con_state, env_state,
                program.env_events, program.con_events)
            if len(monitor_actually_took) == 1:
                (tran, state) = monitor_actually_took[0]
                if tran in program.con_transitions:
                    disagreed_on_transitions = (list(set(
                        t.with_condition(t.condition) for i in range(len(last_desired_env_con_env_trans)) for t in
                        last_desired_env_con_env_trans[i][0])), state)
                elif tran in program.env_transitions:
                    disagreed_on_transitions = (list(set(
                        t.with_condition(t.condition) for i in range(len(last_desired_env_con_env_trans)) for t in
                        last_desired_env_con_env_trans[i][1])), state)
                else:
                    raise Exception("I don't know what kind of transition this is: " + str(tran))
            else:
                con_trans, con_state = monitor_actually_took[0]
                env_trans, env_state = monitor_actually_took[1]
                all_with_matching_con_trans = [i for i in range(len(last_desired_env_con_env_trans)) for t in
                                               last_desired_env_con_env_trans[i][0] if t == con_trans]
                if len(all_with_matching_con_trans) == 0:
                    monitor_actually_took = monitor_actually_took[:-1]
                    disagreed_on_transitions = (list(
                        set([t.with_condition(t.condition) for i in range(len(last_desired_env_con_env_trans)) for t in
                             last_desired_env_con_env_trans[i][0]])), con_state)
                else:
                    agreed_on_transitions += [[monitor_actually_took[0]]]
                    monitor_actually_took = monitor_actually_took[1:]
                    disagreed_on_transitions = (list(
                        set([t.with_condition(t.condition) for i in all_with_matching_con_trans for t in
                             last_desired_env_con_env_trans[i][1]])), env_state)

                disagreed_on_state_dict = disagreed_on_transitions[1]

            write_counterexample(program, agreed_on_transitions, disagreed_on_transitions, monitor_actually_took)
            check_for_nondeterminism_last_step(monitor_actually_took[0][1], predicate_abstraction.program, False, None)


        ## end compute mismatch trace

        ## check if should use liveness or not
        try:
            counterstrategy_states = [key for ce_state in ce for key, v in ce_state.items()
                                      if key.startswith("st_") and ce_state["turn"] == "env" and v == "TRUE"]
            print("Counterstrategy states before environment step: " + ", ".join(counterstrategy_states))
            last_counterstrategy_state = counterstrategy_states[-1]
            use_liveness, counterexample_loop, entry_valuation, entry_predicate, pred_mismatch \
                = use_liveness_refinement(program, agreed_on_transitions,
                                          disagreed_on_state_dict,
                                          last_counterstrategy_state,
                                          symbol_table, state_pred_label_to_formula)
        except Exception as e:
            print("WARNING: " + str(e))
            print("I will try to use safety instead.")
            use_liveness = False

        ## do liveness refinement
        if use_liveness:
            if no_analysis_just_user_input:
                finished = False
                while not finished:
                    try:
                        text = raw_input("Any suggestions of ranking functions?")
                        rankings = list(map(string_to_math_expression, text.split(",")))
                        finished = True
                    except Exception as e:
                        pass

                invars = []
                transition_predicates += list(chain.from_iterable([[BiOp(add_prev_suffix(program, r), ">", r), BiOp(add_prev_suffix(program, r), "<", r)] for r in rankings]))
            else:
                try:
                    if pred_mismatch:  # counterexample_loop[-1][1]["compatible_predicates"] == "FALSE":
                        exit_trans = counterexample_loop[-1][0]
                        exit_trans_state = counterexample_loop[-1][1]
                        loop = counterexample_loop[:-1]
                    else:
                        loop = counterexample_loop
                        exit_trans = monitor_actually_took[0][0]
                        exit_trans_state = monitor_actually_took[0][1]

                        # TODO this isn't the real exit trans, it's a good approximation for now, but it may be a just
                        #  an explicit or implicit stutter transition
                        exit_condition = exit_trans.condition
                        ranking, invars, sufficient_entry_condition, exit_predicate = \
                            liveness_step(program, loop, symbol_table,
                                            entry_valuation, entry_predicate,
                                            exit_condition,
                                            exit_trans_state)

                    # TODO in some cases we can use ranking abstraction as before:
                    #  -DONE if ranking function is a natural number
                    #  -if ranking function does not decrease outside the loop
                    #  -DONE if supporting invariant ensures ranking function is bounded below

                    if ranking is not None:# and function_is_of_natural_type(ranking, invars, symbol_table):
                        print("Found: " + str(ranking))
                        if choose_predicates:
                            finished = False
                            while not finished:
                                try:
                                    text = raw_input("Press enter to use suggested ranking function, "
                                                     "otherwise suggest one ranking function to use instead, with a list of invars after (all separated with ',').")
                                    if text.strip(" ") == "":
                                        finished = true
                                    else:
                                        split = text.split(",")
                                        ranking = string_to_math_expression(text[0])
                                        invars = list(map(string_to_prop, split[1:]))

                                        finished = True
                                except Exception as e:
                                    pass

                        if not function_is_of_natural_type(ranking, invars, symbol_table):
                            wellfounded_invar = MathExpr(BiOp(ranking, ">=", Value(0)))
                            invars.append(wellfounded_invar)
                        # invar_formula = conjunct_formula_set(invars)
                        state_predicates += invars #TODO should be adding them separately
                        new_transition_predicates = [BiOp(add_prev_suffix(program, ranking), ">", ranking),
                                                      # conjunct(invar_formula, BiOp(add_prev_suffix(program, ranking), "<", ranking))
                                                      BiOp(add_prev_suffix(program, ranking), "<", ranking)
                                                      ]
                        transition_predicates_invars[ranking] = invars
                        rankings.append((ranking, invars))

                        new_all_trans_preds = {x.simplify() for x in new_transition_predicates}
                        new_all_trans_preds = reduce_up_to_iff(transition_predicates, list(new_all_trans_preds),
                                                               symbol_table | symbol_table_prevs)

                        if len(new_all_trans_preds) == len(transition_predicates):
                            print("I did something wrong, "
                                  "it turns out the new transition predicates "
                                  "(" + ", ".join(
                                [str(p) for p in new_transition_predicates]) + ") are a subset of "
                                                                               "previous predicates.")
                            print("I will try safety refinement instead.")
                            use_liveness = False
                        # important to add this, since later on assumptions depend on position of predicates in list
                        transition_predicates += new_transition_predicates
                    elif use_explicit_loops_abstraction:
                        # if [t for (t, _) in counterexample_loop] in [loop_body for (_, loop_body, _) in predicate_abstraction.loops]:
                        #     print("The loop is already in the predicate abstraction.")
                        new_safety_preds = predicate_abstraction.make_explicit_terminating_loop(sufficient_entry_condition,
                                                                                                [t for (t, _) in loop],
                                                                                                [exit_trans],
                                                                                                exit_predicate)
                        program = predicate_abstraction.program
                        symbol_table = predicate_abstraction.program.symbol_table
                        state_predicates = state_predicates + list(new_safety_preds)

                        transition_fairness = [implies(G(F(Variable("inloop"))), G(F((Variable("notinloop")))))]
                    else:
                        print("I will try safety refinement instead.")
                        use_liveness = False

                except Exception as e:
                    print(e)
                    print("I will try safety refinement instead.")
                    use_liveness = False
        ## do safety refinement
        if eager or not use_liveness:
            if no_analysis_just_user_input:
                finished = False
                while not finished:
                    try:
                        text = raw_input("Any suggestions of state predicates?")
                        new_preds = list(map(string_to_prop, text.split(",")))
                        finished = True
                    except Exception as e:
                        pass
            else:
                if pred_state is not None:
                    pred_formula = conjunct_formula_set([state_pred_label_to_formula[p] for p in pred_state[0]])
                    new_preds = safety_refinement(ce, agreed_on_transitions + [[(disagreed_on_transitions[0][0], disagreed_on_transitions[1])]], ([pred_formula], pred_state[1]), symbol_table, program, use_dnf=True)
                else:
                    new_preds = safety_refinement(ce, agreed_on_transitions, ([t.condition for t in disagreed_on_transitions[0]], disagreed_on_transitions[1]), symbol_table, program, use_dnf=False)
                print("Found: " + ", ".join([str(p) for p in new_preds]))
                if len(new_preds) == 0:
                    e = Exception("No state predicates identified.")
                    print("No state predicates identified.")
                    print("Trying again by putting interpolant B in DNF form and checking each disjunct separately. This may take some time...")
                    if pred_state is not None:
                        pred_formula = conjunct_formula_set([state_pred_label_to_formula[p] for p in pred_state[0]])
                        new_preds = safety_refinement(ce, agreed_on_transitions + [[(disagreed_on_transitions[0][0], disagreed_on_transitions[1])]],
                                                      ([pred_formula], pred_state[1]), symbol_table, program, use_dnf=True)
                    else:
                        new_preds = safety_refinement(ce, agreed_on_transitions, (
                        [t.condition for t in disagreed_on_transitions[0]], disagreed_on_transitions[1]), symbol_table,
                                                      program, use_dnf=True)
                    print("Found: " + ", ".join([str(p) for p in new_preds]))
                    check_for_nondeterminism_last_step(monitor_actually_took[0][1], predicate_abstraction.program, True, e)
                    print("Could not find a new state predicate..")

                    finished = False
                    while not finished:
                        try:
                            text = raw_input("Any suggestions of state predicates?")
                            new_preds = list(map(string_to_prop, text.split(",")))
                            finished = True
                        except Exception as e:
                            pass


            new_all_preds = {x.simplify() for x in new_preds}
            new_all_preds = reduce_up_to_iff(state_predicates,
                                             list(new_all_preds),
                                             symbol_table
                                             | {str(v): TypedValuation(str(v),
                                                                       symbol_table[str(v).removesuffix("_prev")].type,
                                                                       "true")
                                                for p in new_all_preds
                                                for v in p.variablesin()
                                                if str(v).endswith(
                                                     "prev")})  # TODO symbol_table needs to be updated with prevs

            if len(new_all_preds) == len(state_predicates):
                e = Exception(
                    "New state predicates (" + ", ".join([str(p) for p in new_preds]) + ") are a subset of "
                                                                                        "previous predicates."
                )
                check_for_nondeterminism_last_step(monitor_actually_took[0][1], predicate_abstraction.program, True, e)
                print("For debugging:\nComputing projection of controller onto predicate abstraction..")
                controller_projected_on_program = mm.project_controller_on_program(program, predicate_abstraction,
                                                                                   symbol_table | symbol_table_preds)

                print(controller_projected_on_program.to_dot())
                raise e

            if choose_predicates:
                finished = False
                while not finished:
                    try:
                        text = raw_input("Press enter to use suggested state predicates, otherwise write the state predicates to proceed with in a comma-separated list.")
                        if text.strip(" ") == "":
                            finished = True
                        else:
                            new_all_preds = list(map(string_to_prop, text.split(",")))
                            finished = True
                    except Exception as e:
                        pass
            else:
                if keep_only_bool_interpolants:
                    bool_interpolants = [p for p in new_preds if
                                         p not in state_predicates and p in new_all_preds and 0 == len(
                                             [v for v in p.variablesin() if
                                              symbol_table[str(v)].type != "bool" and symbol_table[
                                                  str(v)].type != "boolean"])]
                    if len(bool_interpolants) > 0:
                        new_all_preds = [p for p in new_all_preds if p in bool_interpolants or p in state_predicates]
                if conservative_with_state_predicates:
                    # TODO some heuristics to choose state preds

                    # when coming after a ranking refinement, only get interpolants that are in some way related to exit condition
                    new_all_preds = new_all_preds

            print("Using: " + ", ".join([str(p) for p in new_all_preds if p not in state_predicates]))

            state_predicates = list(new_all_preds)


def liveness_step(program, counterexample_loop, symbol_table, entry_valuation, entry_predicate,
                  exit_condition, exit_prestate):
    # ground transitions in the counterexample loop
    # on the environment and controller events in the counterexample\

    #TODO ground everything on all variable values that are not updated by transitions
    bool_vars = [v for v in symbol_table.keys() if symbol_table[v].type == "bool" or symbol_table[v].type == "boolean"]

    # first ground on bool vars

    entry_valuation_grounded = ground_predicate_on_vars(program, entry_valuation,
                                                             counterexample_loop[0][1], bool_vars, symbol_table).simplify()
    entry_predicate_grounded = ground_predicate_on_vars(program,
                                                             entry_predicate,
                                                             counterexample_loop[0][1], bool_vars, symbol_table).simplify()

    exit_predicate_grounded = ground_predicate_on_vars(program, exit_condition,
                                                            exit_prestate, bool_vars, symbol_table).simplify()

    if isinstance(exit_predicate_grounded, Value) or\
         is_tautology(exit_predicate_grounded, symbol_table, smt_checker):
         # in this case the exit is really happening before the last transition
         # TODO this shouldn't be happening, we should be identifying the real exit transition/condition
         loop_before_exit = ground_transitions(program, counterexample_loop, bool_vars, symbol_table)
    else:
         # then discover which variables are related to the variables updated in the loop
        updated_in_loop_vars = [str(act.left) for t, _ in counterexample_loop for act in t.action]
        dnf_exit_pred = dnf(exit_predicate_grounded)
        disjuncts_in_exit_pred = [dnf_exit_pred] if not isinstance(dnf_exit_pred, BiOp) or not dnf_exit_pred.op.startswith("&") else dnf_exit_pred.sub_formulas_up_to_associativity()

        relevant_vars = [str(v) for f in disjuncts_in_exit_pred for v in f.variablesin() if any(v for v in f.variablesin() if str(v) in updated_in_loop_vars)]
        irrelevant_vars = [v for v in symbol_table.keys() if v not in relevant_vars]

        entry_predicate_grounded = ground_predicate_on_vars(program,
                                                                 entry_predicate_grounded,
                                                                 counterexample_loop[0][1], irrelevant_vars, symbol_table).simplify()

        exit_predicate_grounded = ground_predicate_on_vars(program, exit_predicate_grounded,
                                                                exit_prestate, irrelevant_vars, symbol_table).simplify()

        loop_before_exit = ground_transitions(program, counterexample_loop, irrelevant_vars + bool_vars, symbol_table)

    sufficient_entry_condition = None
    try:
        ranking, invars = liveness_refinement(symbol_table,
                                              program,
                                              true(),
                                              loop_before_exit,
                                              exit_predicate_grounded)
        sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
    except:
        try:
            ranking, invars = liveness_refinement(symbol_table,
                                                  program,
                                                  entry_predicate_grounded.simplify(),
                                                  loop_before_exit,
                                                  exit_predicate_grounded)
            sufficient_entry_condition = entry_predicate
        except:
            ranking, invars = liveness_refinement(symbol_table,
                                                  program,
                                                  entry_valuation_grounded.simplify(),
                                                  loop_before_exit,
                                                  exit_predicate_grounded)
            sufficient_entry_condition = entry_valuation

    # if invars != None and len(invars) > 0:
    #     print(
    #         "Ranking function comes with invar, what shall we do here? " + ranking + "\n" + ", ".join(
    #             [str(invar) for invar in invars]) + ".")

    if not smt_checker.check(And(*neg(exit_predicate_grounded).to_smt(symbol_table))):
        for grounded_t in loop_before_exit:
            if smt_checker.check(And(*neg(grounded_t.condition).to_smt(symbol_table))):
                exit_predicate_grounded = neg(grounded_t.condition.simplify())
                break

    return ranking, invars, sufficient_entry_condition, exit_predicate_grounded


def write_counterexample(program,
                         agreed_on_transitions: [(Transition, dict)],
                         disagreed_on_transitions: ([Transition], dict),
                         monitor_actually_took: [([Transition], [Transition])]):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for ts in agreed_on_transitions for (t, s) in ts]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print(str(trans) + " var values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))

    print("Environment wanted to take one of these:")

    state = disagreed_on_transitions[1]
    vs = []
    for trans in disagreed_on_transitions[0]:
        vs += set(trans.condition.variablesin()
                  + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                  + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                  + [v for v in program.env_events + program.con_events])
        print(str(trans))
    print("with state: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))

    print("Monitor actually took:")
    print(str(monitor_actually_took[0][0]))


def write_counterexample_state(program,
                         agreed_on_transitions: [(Transition, dict)],
                         disagreed_on_state: ([Formula], dict)):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for ts in agreed_on_transitions for (t, s) in ts]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print(str(trans) + " var values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))

    print("Environment wanted predicate state to be:")

    print(", ".join([str(p) for p in disagreed_on_state[0]]))

    print("Monitor however has state:")
    print(", ".join([v + " = " + k for v,k in disagreed_on_state[1].items()]))
