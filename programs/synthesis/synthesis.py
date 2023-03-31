from itertools import chain
from typing import Tuple

from Config import env, con
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
    there_is_mismatch_between_program_and_strategy, \
    parse_nuxmv_ce_output_finite, reduce_up_to_iff, \
    add_prev_suffix, label_pred, \
    concretize_transitions, ground_transitions, keep_bool_preds, function_is_of_natural_type, \
    ground_predicate_on_vars
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.util import neg, G, F, implies, conjunct, disjunct, true, conjunct_formula_set, dnf, is_tautology, \
    related_to, iff, X, expand_LTL_to_env_con_steps, UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()

def synthesize(program: Program, ltl_text: str, tlsf_path: str, docker: bool, project_on_abstraction=False) -> Tuple[bool, Program]:
    # if not program.deterministic:
    #     raise Exception("We do not handle non-deterministic programs yet.")

    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if " Error\"" in ltl_text:
            raise Exception("Error parsing " + tlsf_path + " see syfco error:\n" + ltl_text)
        ltl_text = ltl_text.replace('"', "")
        in_acts_syfco = syfco_ltl_in(tlsf_path)
        out_acts_syfco = syfco_ltl_out(tlsf_path)
    else:
        in_acts_syfco = []
        out_acts_syfco = []

    ltl = string_to_ltl(ltl_text)

    if isinstance(ltl, BiOp) and (ltl.op == "->" or ltl.op == "=>"):
        ltl_assumptions = ltl.left
        ltl_guarantees = ltl.right
    else:
        ltl_assumptions = true()
        ltl_guarantees = ltl

    in_acts = [e for e in program.env_events]
    out_acts = [e for e in program.con_events]
    prog_acts = program.out_events

    if tlsf_path is not None:
        if any(x for x in in_acts + prog_acts if x not in in_acts_syfco):
            raise Exception("TLSF file has different input variables than the program.")

        if any(x for x in out_acts if x not in out_acts_syfco):
            raise Exception("TLSF file has different output variables than the program.")

    return abstract_synthesis_loop(program, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker, project_on_abstraction=project_on_abstraction)


def abstract_synthesis_loop(program: Program, ltl_assumptions: Formula, ltl_guarantees: Formula, in_acts: [Variable],
                            out_acts: [Variable], docker: str, project_on_abstraction=False, debug=False) -> \
        Tuple[bool, MealyMachine]:
    eager = False
    keep_only_bool_interpolants = False
    use_explicit_loops_abstraction = False
    no_analysis_just_user_input = False
    choose_predicates = False
    conservative_with_state_predicates = False
    prefer_lasso_counterexamples = True
    minimal_state_predicates = False
    controller_transition_explicit = True

    old_state_predicates = set()
    state_predicates = []
    rankings = {}
    old_transition_predicates = set()
    transition_predicates = []
    # ranking_invars = {}

    predicate_abstraction = PredicateAbstraction(program)
    init_abs, trans_abs = predicate_abstraction.initialise()

    while True:
        state_predicates = [p for p in state_predicates if not (isinstance(p, UniOp) and p.op == "!")]
        state_predicates += [p.right for p in state_predicates if isinstance(p, UniOp) and p.op == "!"]

        symbol_table = predicate_abstraction.program.symbol_table

        pred_list = list(state_predicates) + list(transition_predicates)

        #transition_predicates_prev = [add_prev_suffix(t) for t in transition_predicates]
        pred_name_dict = {p: label_pred(p, pred_list) for p in pred_list}
        pred_name_dict_with_negs = pred_name_dict | {neg(p): neg(label_pred(p, pred_list)) for p in pred_list}
        state_pred_label_to_formula = {label_pred(p, pred_list): p for p in state_predicates + transition_predicates}# + transition_predicates_prev}
        state_pred_label_to_formula |= {neg(label_pred(p, pred_list)): neg(p) for p in state_predicates + transition_predicates}# + transition_predicates_prev}
        pred_acts = [pred_name_dict[v] for v in pred_name_dict.keys()]

        new_state_preds = [s for s in state_predicates if s not in old_state_predicates]
        new_trans_preds = [t for t in transition_predicates if t not in old_transition_predicates]
        if len(new_state_preds + new_trans_preds) > 0:
            if False:
                for s in new_state_preds:
                    predicate_abstraction.add_predicates([s], [], True)
                for t in new_trans_preds:
                    predicate_abstraction.add_predicates([], [t], True)
            else:
                init_abs, trans_abs = predicate_abstraction.add_predicates(new_state_preds, new_trans_preds, pred_name_dict_with_negs, True)
        else:
            pass
            # abstraction = predicate_abstraction.add_predicates([true()], [], True)

        # predicate_abstraction.compute_with_predicates(state_predicates, transition_predicates, True)

        old_state_predicates |= {s for s in state_predicates if s not in old_state_predicates}
        old_transition_predicates |= {t for t in transition_predicates if t not in old_transition_predicates}
        symbol_table["inloop"] = TypedValuation("inloop", "bool", True)
        symbol_table["notinloop"] = TypedValuation("notinloop", "bool", True)

        program_out_vars = predicate_abstraction.program.out_events
        program_state_vars = [Variable(s) for s in predicate_abstraction.program.states]

        program_out_and_states_vars = program_out_vars + program_state_vars
        ## Compute abstraction
        # print(predicate_abstraction.abstraction.to_dot())


        # should be computed incrementally
        # transition_fairness = []
        # i = 0
        # while i < len(transition_predicates):
        #     dec = pred_name_dict[transition_predicates[i]]
        #     inc = pred_name_dict[transition_predicates[i + 1]]
        #     # dec_prev = pred_name_dict[add_prev_suffix(transition_predicates[i])]
        #     # inc_prev = pred_name_dict[add_prev_suffix(transition_predicates[i + 1])]
        #     # safety_predicate_constraints += [(G(neg(conjunct(dec, inc))))]
        #
        #     invar_vars = [pred_name_dict[p] for p in ranking_invars[rankings[i // 2]]]
        #     invar_formula = conjunct_formula_set(invar_vars)
        #
        #     transition_fairness += [implies(G(F(conjunct(invar_formula, dec))), G(F((disjunct(inc, neg(invar_formula)))))).simplify()]
        #     # transition_fairness += [implies(G(F(conjunct(invar_formula, disjunct(dec, dec_prev)))), G(F(disjunct(inc, inc_prev))))]
        #     i += 2


        symbol_table_preds = {
            str(label_pred(v, pred_list)): TypedValuation(str(label_pred(v, pred_list)), "bool", true()) for v in
            pred_list}
        symbol_table_prevs = {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                              program.valuation}

        # abstraction = predicate_abstraction.abstraction_to_ltl(symbol_table_preds
        #                                                                                    | {str(o): TypedValuation(str(o), "bool", None) for o in mon_events + list(program.states) + program.env_events + program.con_events},
        #                                                                                    simplified=True)
        # print(", ".join(map(str, abstraction)))



        at_least_and_at_most_one_state = UniOp("G",
                                               conjunct_formula_set(
                                                   [iff(Variable(str(q)),
                                                         conjunct_formula_set([neg(Variable(str(r))) for r in
                                                                                program.states
                                                                               if
                                                                               r != q]))
                                                    for q in program.states])).to_nuxmv()

        pure_env_in_acts = [p for p in in_acts if p not in program_out_vars]

        program_abstraction = ([init_abs, trans_abs] + \
                              [a for _, _, A, _ in rankings.values() for a in A] + \
                              [at_least_and_at_most_one_state])

        original_assumptions = ([expand_LTL_to_env_con_steps(ltl_assumptions, pure_env_in_acts)])

        env_turn_assumptions = ([env, G(implies(env, X(con))), G(implies(con, X(env))),
                       G(implies(env, (conjunct_formula_set([iff(p, X(p)) for p in pure_env_in_acts]))))] )

        guarantees = ([expand_LTL_to_env_con_steps(ltl_guarantees, pure_env_in_acts)] + \
                     [G(implies(con, (conjunct_formula_set([iff(p, X(p)) for p in out_acts]))))])

        controller_rankings = conjunct_formula_set([g for _, _, _, G in rankings.values() for g in G])

        if len([g for _, _, _, G in rankings.values() for g in G]) > 0:
            print()

        # env is making controller_rankings FALSE
        # formula = conjunct(controller_rankings,
        #                   implies(conjunct(env_turn_assumptions, conjunct(program_abstraction, original_assumptions)), (guarantees)))

        (real, mm) = ltl_synthesis.ltl_synthesis([], original_assumptions + env_turn_assumptions + program_abstraction,
                                                 guarantees,
                                                 pure_env_in_acts + [env] + [e for E, _, _, _ in rankings.values() for e in E],
                                                 program_out_vars,
                                                 program_state_vars + pred_acts,
                                                 out_acts + [c for _, C, _, _ in rankings.values() for c in C],
                                                 docker)

        if real and not debug:
            print("Realizable")
            print(mm.to_dot(pred_list))
            if project_on_abstraction:
                return True, mm.project_controller_on_program((
                    "strategy" if real else "counterstrategy"),
                    program, predicate_abstraction,
                    symbol_table | symbol_table_preds)
            else:
                # mm = mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(predicate_abstraction, program)
                return True, mm.to_dot(pred_list)

        print(mm.to_dot(pred_list))
        # if controller_transition_explicit:
        #     mm = mm.fill_in_predicates_at_controller_states_label_tran_preds_appropriately(predicate_abstraction, program)
        #     print(mm.to_dot(pred_list))

        ## checking for mismatch
        mealy = mm.to_nuXmv_with_turns(predicate_abstraction.program.states, predicate_abstraction.program.out_events,
                                       state_predicates, transition_predicates)

        # try looking for a lasso mismatch first
        strategy_states = sorted(["(" + str(s).split(" : ")[0] + " & " + str(s).split(" : ")[0] + "_seen_more_than_once)" for s in mealy.vars if str(s).startswith("st_")])
        lasso_mismatch = "(" + " | ".join(strategy_states) + ")"

        if prefer_lasso_counterexamples:
            mismatch_condition = lasso_mismatch
        else:
            mismatch_condition = None

        system = create_nuxmv_model_for_compatibility_checking(program, mealy, program_out_and_states_vars, pred_list,
                                                               not program.deterministic, not program.deterministic,
                                                               predicate_mismatch=True,
                                                               prefer_lassos=prefer_lasso_counterexamples,
                                                               controller_transition_explicit=controller_transition_explicit)
        print(system)
        contradictory, there_is_mismatch, out = there_is_mismatch_between_program_and_strategy(system, real, False,
                                                                                               ltl_assumptions,
                                                                                               ltl_guarantees, mismatch_condition)

        if not there_is_mismatch or contradictory:
            system = create_nuxmv_model_for_compatibility_checking(program, mealy, program_out_and_states_vars, pred_list,
                                                                   not program.deterministic, not program.deterministic,
                                                                   predicate_mismatch=True,
                                                               prefer_lassos=prefer_lasso_counterexamples,
                                                               controller_transition_explicit=controller_transition_explicit)
            contradictory, there_is_mismatch, out = there_is_mismatch_between_program_and_strategy(system, real, False,
                                                                                                   ltl_assumptions,
                                                                                                   ltl_guarantees)
        ## end checking for mismatch

        ## deal with if there is nothing wrong
        if not there_is_mismatch or contradictory:
            # TODO do this only when program has non-determinism
            # print("No mismatch found between " + (
            #     "strategy" if real else "counterstrategy") + " and program when excluding traces for which the program has a non-deterministic choice.")
            # print("Trying for when the program has a non-deterministic choice..")
            # system = create_nuxmv_model_for_compatibility_checking(program, mealy, mon_events, pred_list, True, True, False)
            # contradictory, there_is_mismatch, out = there_is_mismatch_between_program_and_strategy(system, real, False,
            #                                                                                        ltl_assumptions,
            #                                                                                        ltl_guarantees)

            if contradictory:
                raise Exception("I have no idea what's gone wrong. Strix thinks the previous mealy machine is a " +
                                (
                                    "controller" if real else "counterstrategy") + ", but nuxmv thinks it is non consistent with the program.\n"
                                                                                   "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division.")

            if not there_is_mismatch:
                # print("No mismatch found between " + (
                #     "strategy" if real else "counterstrategy") + " and program even when including traces for which the program has a non-deterministic choice.")

                # print("Looking for mismatches in predicates.")
                # # TODO check that we are dealing well with how transition predicates are bookmarkerd now, could get false predicate mismatches
                # system = create_nuxmv_model_for_compatibility_checking(program, mealy, mon_events, pred_list, True,
                #                                                        True, predicate_mismatch=True)
                # contradictory, there_is_mismatch, out = there_is_mismatch_between_program_and_strategy(system, real,
                #                                                                                        False,
                #                                                                                        ltl_assumptions,
                #                                                                                        ltl_guarantees)
                if not there_is_mismatch:
                    print("No mismatch found.")

                    ## Finished
                    if project_on_abstraction:
                        print("Computing projection of " + (
                    "strategy" if real else "counterstrategy") + " onto predicate abstraction..")
                        controller_projected_on_program = mm.project_controller_on_program((
                                                                                    "strategy" if real else "counterstrategy"),
                                                                                           program, predicate_abstraction,
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
                                        "controller" if real else "counterstrategy") + " has no outgoing transition from this program state: "
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
        ce, transition_indices_and_state, incompatible_state = \
            parse_nuxmv_ce_output_finite(len(program.env_transitions) + len(program.con_transitions), out)
        transitions_without_stutter_program_took, env_desired_abstract_state, program_taken_transition = \
            concretize_transitions(program, program, transition_indices_and_state, False,
                                   predicate_abstraction.abstraction, state_pred_label_to_formula,
                                   incompatible_state)

        # if env_desired_abstract_state is None:
        #     transitions_without_stutter_program_took, env_desired_abstract_state = \
        #         concretize_transitions(program, program, transition_indices_and_state, False,
        #                                predicate_abstraction.abstraction, state_pred_label_to_formula,
        #                                incompatible_state)

        # if pred_state is not None:
        agreed_on_transitions = transitions_without_stutter_program_took
        # removing transition predicates for now
        disagreed_on_state = ([p for p in env_desired_abstract_state[0] if not any(v for v in p.variablesin() if "_prev" in str(v))], env_desired_abstract_state[1])

        write_counterexample_state(program, agreed_on_transitions, disagreed_on_state)
        # _, abstract_trans = predicate_abstraction.allowed_in_abstraction([t[0] for t in transitions_without_stutter_program_took])
        # TODO handle this
        abstract_trans = []
        print("Abstract trans:\n" + "\n--\n".join(["\nor ".join(map(str, ats)) for ats in abstract_trans]))

        ## end compute mismatch trace

        ## check if should use liveness or not
        try:
            counterstrategy_states = [key for ce_state in ce for key, v in ce_state.items()
                                      if key.startswith("st_") and (ce_state["turn"] in ["env", "con"]) and "_seen" not in key and v == "TRUE"]
            print("Counterstrategy states before environment step: " + ", ".join(counterstrategy_states))
            last_counterstrategy_state = counterstrategy_states[-1]
            use_liveness, counterexample_loop, entry_valuation, entry_predicate, pred_mismatch, loop_in_cs \
                = use_liveness_refinement(program, agreed_on_transitions,
                                          disagreed_on_state, program_taken_transition,
                                          last_counterstrategy_state,
                                          symbol_table | symbol_table_prevs, state_pred_label_to_formula)
        except Exception as e:
            print("WARNING: " + str(e))
            print("I will try to use safety instead.")
            use_liveness = False

        ## do liveness refinement
        if use_liveness:
            if no_analysis_just_user_input:
                finished = False
                new_rankings = []
                while not finished:
                    try:
                        text = raw_input("Any suggestions of ranking functions?")
                        new_rankings = list(map(string_to_math_expression, text.split(",")))
                        finished = True
                    except Exception as e:
                        pass

                invars = []
                transition_predicates += list(chain.from_iterable([[BiOp(add_prev_suffix(r), ">", r),
                                                                    BiOp(add_prev_suffix(r), "<", r)]
                                                                   for r in new_rankings]))

                for ranking in new_rankings:
                    invars = []
                    if not function_is_of_natural_type(ranking, invars, symbol_table):
                        wellfounded_invar = MathExpr(BiOp(ranking, ">=", Value(0)))
                        state_predicates += invars
                        invars += [wellfounded_invar]
                    ranking_invars[ranking] = invars
                    state_predicates += invars
                    rankings.append(ranking)

            else:
                try:
                    # if pred_mismatch:  # counterexample_loop[-1][1]["compatible_predicates"] == "FALSE":
                    # exit_trans = counterexample_loop[-1][0]
                    exit_trans_state = disagreed_on_state[1]
                    loop = counterexample_loop
                    # else:
                    #     loop = counterexample_loop
                    #     exit_trans = program_actually_took[0]
                    #     exit_trans_state = program_actually_took[1]

                    # TODO this isn't the real exit trans, it's a good approximation for now, but it may be a just
                    #  an explicit or implicit stutter transition
                    mismatch_desired_state = conjunct_formula_set([p for p in disagreed_on_state[0]])
                    exit_condition = mismatch_desired_state #neg(mismatch_desired_state) if loop_in_cs else mismatch_desired_state
                    ranking, invars, sufficient_entry_condition, exit_predicate = \
                        liveness_step(program, loop, symbol_table | symbol_table_prevs,
                                        entry_valuation, entry_predicate,
                                        exit_condition,
                                        exit_trans_state)

                    # TODO in some cases we can use ranking abstraction as before:
                    #  -DONE if ranking function is a natural number
                    #  -if ranking function does not decrease or increase outside the loop
                    #  -DONE if supporting invariant ensures ranking function is bounded below

                    if ranking is not None:# and function_is_of_natural_type(ranking, invars, symbol_table):
                        print("Found ranking function: " + str(ranking))
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
                            invars += [wellfounded_invar]
                            # invars.append(wellfounded_invar)

                        # mismatch_predicate_state = [Variable(p) for p in disagreed_on_state[1].keys() if p.startswith("_pred") and disagreed_on_state[1][p] == "TRUE"]
                        # mismatch_predicate_state += [neg(Variable(p)) for p in disagreed_on_state[1].keys() if p.startswith("_pred") and disagreed_on_state[1][p] == "FALSE"]
                        new_env_variables, new_con_variables, new_transition_predicates, new_state_predicates, new_assumptions, new_guarantees =\
                            predicate_abstraction.loop_abstraction(sufficient_entry_condition,
                                                                   counterexample_loop,
                                                                   mismatch_desired_state,
                                                                   ranking,
                                                                   conjunct_formula_set(invars),
                                                                   disagreed_on_state[1],
                                                                   program_taken_transition)

                        # new_transition_predicates = [BiOp(add_prev_suffix(ranking), ">", ranking),
                        #                               # conjunct(invar_formula, BiOp(add_prev_suffix(ranking), "<", ranking))
                        #                               BiOp(add_prev_suffix(ranking), "<", ranking)
                        #                               ]

                        new_all_trans_preds = {x.simplify() for x in new_transition_predicates} | {x for x in transition_predicates}
                        new_all_trans_preds = reduce_up_to_iff(transition_predicates, list(new_all_trans_preds),
                                                               symbol_table | symbol_table_prevs)

                        if len(new_state_predicates) != 0:
                            # ranking_invars[ranking] = []
                            rankings[ranking] = (new_env_variables, new_con_variables, new_assumptions, new_guarantees)
                            state_predicates += invars + new_state_predicates
                            transition_predicates += new_transition_predicates
                            pass
                        elif not len(new_all_trans_preds) == len(transition_predicates)\
                                or (ranking in ranking_invars.keys() and set(ranking_invars[ranking]) != set(invars)):
                            # important to add this, since later on assumptions depend on position of predicates in list
                            # ranking_invars[ranking] = invars
                            rankings[ranking] = (new_env_variables, new_con_variables, new_assumptions, new_guarantees)
                            state_predicates += invars
                            transition_predicates += new_transition_predicates
                        else:
                            print("The new transition predicates "
                                  "(" + ", ".join(
                                [str(p) for p in new_transition_predicates]) + ") are a subset of "
                                                                               "previous predicates.")
                            print("Safety refinement should do the trick here instead. I'll do that.")
                            use_liveness = False
                            # print("I will try safety refinement instead.")
                            # use_liveness = False

                            # if use_explicit_loops_abstraction:
                            #     print("I will try to make the loop and its exit explicit instead.")
                            #     # if [t for (t, _) in counterexample_loop] in [loop_body for (_, loop_body, _) in predicate_abstraction.loops]:
                            #     #     print("The loop is already in the predicate abstraction.")
                            #     new_safety_preds = predicate_abstraction.make_explicit_terminating_loop(sufficient_entry_condition,
                            #                                                                             [t for (t, _) in loop],
                            #                                                                             disagreed_on_state,
                            #                                                                             exit_predicate)
                            #     program = predicate_abstraction.program
                            #     symbol_table = predicate_abstraction.program.symbol_table
                            #     state_predicates = state_predicates + list(new_safety_preds)
                            #
                            #     transition_predicates += [Variable("inloop"), Variable("loop")]
                            #     in_acts += [Variable("inloop"), Variable("notinloop")]
                            #     rankings.append(Variable("loop"))
                            #     ranking_invars[Variable("loop")] = []
                            # else:
                            #     print("I will try safety refinement instead.")
                            #     use_liveness = False
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
                        if len(text.strip(" ")) == 0:
                            finished = True
                        else:
                            new_preds = set(map(string_to_prop, text.split(",")))
                            finished = True
                    except Exception as e:
                        pass
            else:
                pred_formula = conjunct_formula_set([p for p in disagreed_on_state[0]])
                new_preds = safety_refinement(ce, agreed_on_transitions, ([pred_formula], disagreed_on_state[1]),
                                              abstract_trans, symbol_table | symbol_table_prevs, program, use_dnf=True)

                print("Found state predicates: " + ", ".join([str(p) for p in new_preds]))
                if len(new_preds) == 0:
                    e = Exception("No state predicates identified.")
                    print("No state predicates identified.")
                    print("I will try using the values of variables instead..")
                    vars_mentioned_in_preds = {v for p in new_preds for v in p.variablesin()}
                    new_preds |= {BiOp(v, "=", Value(state[str(v)])) for v in vars_mentioned_in_preds for state
                                         in
                                         [st for (_, st) in agreed_on_transitions + [disagreed_on_state[1]]]}

            new_all_preds = {x.simplify() for x in new_preds | {p for p in state_predicates if p not in old_state_predicates}}
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
                # check_for_nondeterminism_last_step(program_actually_took[1], predicate_abstraction.program, True)
                print(
                    "New state predicates (" + ", ".join([str(p) for p in new_preds]) + ") are a subset of "
                                                                                        "previous predicates."
                )
                print("I will try using the values of variables instead..")
                vars_mentioned_in_preds = {v for p in new_preds for v in p.variablesin()}
                new_all_preds = {BiOp(v, "=", Value(state[str(v)]))
                                     for v in vars_mentioned_in_preds
                                     for state in [st for (_, st) in agreed_on_transitions + [disagreed_on_state]]}
                new_all_preds |= {p for p in state_predicates if p not in old_state_predicates} #ranking invars may have been added
                new_all_preds = reduce_up_to_iff(state_predicates,
                                                 list(new_all_preds),
                                                 symbol_table
                                                 | {str(v): TypedValuation(str(v),
                                                                           symbol_table[
                                                                               str(v).removesuffix("_prev")].type,
                                                                           "true")
                                                    for p in new_all_preds
                                                    for v in p.variablesin()
                                                    if str(v).endswith(
                                                         "prev")})  # TODO symbol_table needs to be updated with prevs
                if len(new_all_preds) == len(state_predicates):
                    raise Exception("No new state predicates identified.")

                # print("For debugging:\nComputing projection of counterstrategy onto predicate abstraction..")
                # controller_projected_on_program = mm.project_controller_on_program("counterstrategy", program, predicate_abstraction,
                #                                                                    symbol_table | symbol_table_preds)
                #
                # print(controller_projected_on_program.to_dot())
                # raise e

            if choose_predicates:
                finished = False
                while not finished:
                    try:
                        text = raw_input("Press enter to use suggested state predicates, otherwise write the state predicates to proceed with in a comma-separated list.")
                        if text.strip(" ") == "":
                            finished = True
                        else:
                            new_all_preds = set(map(string_to_prop, text.split(",")))
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
                    new_preds = [p for p in new_all_preds if p not in state_predicates]
                    if len(new_preds) == 0:
                        raise Exception("No new state predicates identified.")
                    #get the number of variables associated with each predicates
                    ordered_according_to_no_of_vars_used = [[p for p in new_preds if len(p.variablesin()) == n] for n in range(1, len(program.valuation) + 1)]
                    ordered_according_to_no_of_vars_used = [ps for ps in ordered_according_to_no_of_vars_used if len(ps) > 0]
                    new_all_preds = state_predicates + (ordered_according_to_no_of_vars_used[0] if len(ordered_according_to_no_of_vars_used) > 0 else [])

            print("Using: " + ", ".join([str(p) for p in new_all_preds if p not in state_predicates]))

            state_predicates = list(new_all_preds)


def liveness_step(program, counterexample_loop, symbol_table, entry_valuation, entry_predicate,
                  exit_condition, exit_prestate, expand_termination_argument=False):
    # ground transitions in the counterexample loop
    # on the environment and controller events in the counterexample\

    invars = []
    #TODO consider if sometimes bool vals are needed or not
    bool_vars = [v for v in symbol_table.keys() if symbol_table[v].type == "bool" or symbol_table[v].type == "boolean"]

    # first ground on bool vars

    entry_valuation_grounded = ground_predicate_on_vars(program, entry_valuation,
                                                             counterexample_loop[0][1], bool_vars, symbol_table).simplify()
    entry_predicate_grounded = ground_predicate_on_vars(program,
                                                             entry_predicate,
                                                             counterexample_loop[0][1], bool_vars, symbol_table).simplify()

    exit_predicate_grounded = ground_predicate_on_vars(program, exit_condition,
                                                            exit_prestate, bool_vars, symbol_table).simplify()
    dnf_exit_pred = dnf(exit_predicate_grounded, symbol_table)
    disjuncts_in_exit_pred = [dnf_exit_pred] if not isinstance(dnf_exit_pred, BiOp) or not dnf_exit_pred.op.startswith(
        "|") else dnf_exit_pred.sub_formulas_up_to_associativity()

    if isinstance(exit_predicate_grounded, Value) or\
         is_tautology(exit_predicate_grounded, symbol_table, smt_checker):
         # in this case the exit is really happening before the last transition
         # TODO this shouldn't be happening, we should be identifying the real exit transition/condition
         loop_before_exit = ground_transitions(program, counterexample_loop, bool_vars, symbol_table)
         irrelevant_vars = []
         disjuncts_in_exit_pred_grounded = disjuncts_in_exit_pred
    else:
         # then discover which variables are related to the variables updated in the loop
         # TODO may also need to look at the guards of the transitions in the loop
        updated_in_loop_vars = [str(act.left) for t, _ in counterexample_loop for act in t.action if act.left != act.right]

        relevant_vars = [str(v) for f in disjuncts_in_exit_pred for v in f.variablesin() if any(v for v in f.variablesin() if str(v) in updated_in_loop_vars)]
        irrelevant_vars = [v for v in symbol_table.keys() if v not in relevant_vars]

        entry_predicate_grounded = ground_predicate_on_vars(program,
                                                                 entry_predicate_grounded,
                                                                 counterexample_loop[0][1], irrelevant_vars, symbol_table).simplify()

        disjuncts_in_exit_pred_grounded = [ground_predicate_on_vars(program, e,
                                                                exit_prestate, irrelevant_vars, symbol_table).simplify() for e in disjuncts_in_exit_pred]

        loop_before_exit = ground_transitions(program, counterexample_loop, irrelevant_vars + bool_vars, symbol_table)

    sufficient_entry_condition = None

    conditions = [(true(), True), (entry_predicate_grounded.simplify(), True), (entry_valuation_grounded, False)]

    ranking = None
    for (cond, add_natural_conditions) in conditions:
        for exit_pred in disjuncts_in_exit_pred_grounded:
            try:
                ranking, invars = liveness_refinement(symbol_table,
                                                      program,
                                                      cond,
                                                      loop_before_exit,
                                                      exit_pred,
                                                      add_natural_conditions)
                if ranking is None:
                    continue
                sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
                break
            except:
                continue

        if ranking is None:
            continue

        break

    if ranking is not None:
        # analyse ranking function for suitability and re-try
        if not isinstance(exit_predicate_grounded, Value) or\
             is_tautology(exit_predicate_grounded, symbol_table, smt_checker):
            # for each variable in ranking function, check if they are related in the exit condition, or transitively so
            updated_in_loop_vars = [str(act.left) for t in loop_before_exit for act in t.action if act.left != act.right]

            vars_in_ranking = ranking.variablesin()# + [Variable(v) for v in updated_in_loop_vars]

            dnf_exit_pred = dnf(exit_predicate_grounded, symbol_table)
            disjuncts_in_exit_pred = [dnf_exit_pred] if not isinstance(dnf_exit_pred, BiOp) or not dnf_exit_pred.op.startswith("&") else dnf_exit_pred.sub_formulas_up_to_associativity()

            # compute related
            related_dict = {v:set() for v in (vars_in_ranking + [Variable(v) for v in updated_in_loop_vars])}
            for disjunct in disjuncts_in_exit_pred:
                for v in (vars_in_ranking + [Variable(v) for v in updated_in_loop_vars]):
                    related_dict[v] |= related_to(v, disjunct)

            # check if the ranking function relates variables that are related in entry condition
            if [] != [v for v in vars_in_ranking if v not in related_dict[vars_in_ranking[0]]]:
                print("The ranking function discovered does not relate variables that are related in the exit condition.")
                all_updated_vars_mentioned_in_ranking = {v for v in vars_in_ranking if str(v) in updated_in_loop_vars}
                print("Refining the loop code to focus on: " + ", ".join([str(v) for v in all_updated_vars_mentioned_in_ranking]) + "...")
                all_extra_vars = [v for v in vars_in_ranking
                                  if not any(v in related_dict[vv] for vv in all_updated_vars_mentioned_in_ranking)]

                # ground on these extra vars
                entry_valuation_grounded = ground_predicate_on_vars(program, entry_valuation,
                                                                    counterexample_loop[0][1], all_extra_vars,
                                                                    symbol_table).simplify()

                entry_predicate_grounded = ground_predicate_on_vars(program,
                                                                    entry_predicate_grounded,
                                                                    counterexample_loop[0][1], all_extra_vars,
                                                                    symbol_table).simplify()

                disjuncts_in_exit_pred_grounded = [ground_predicate_on_vars(program, e,
                                                                            exit_prestate, all_extra_vars,
                                                                            symbol_table).simplify() for e in
                                                   disjuncts_in_exit_pred_grounded]

                loop_before_exit = ground_transitions(program, counterexample_loop, irrelevant_vars + bool_vars + all_extra_vars,
                                                      symbol_table)

                conditions = [(true(), True),
                              (entry_predicate_grounded.simplify(), True),
                              (entry_valuation_grounded, False)]

                ranking = None
                for (cond, add_natural_conditions) in conditions:
                    for exit_pred in disjuncts_in_exit_pred_grounded:
                        try:
                            ranking, invars = liveness_refinement(symbol_table,
                                                                  program,
                                                                  cond,
                                                                  loop_before_exit,
                                                                  exit_pred,
                                                                  add_natural_conditions)
                            if ranking is None:
                                continue
                            sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
                            break
                        except:
                            continue

                    if ranking is None:
                        continue
                    sufficient_entry_condition = keep_bool_preds(entry_predicate, symbol_table)
                    break

        if not smt_checker.check(And(*neg(exit_predicate_grounded).to_smt(symbol_table))):
            for grounded_t in loop_before_exit:
                if smt_checker.check(And(*neg(grounded_t.condition).to_smt(symbol_table))):
                    exit_predicate_grounded = neg(grounded_t.condition.simplify())
                    break
        return ranking, invars, sufficient_entry_condition, exit_predicate_grounded
    else:
        return None, None, None, None



def write_counterexample(program,
                         agreed_on_transitions: [(Transition, dict)],
                         # disagreed_on_transitions: ([Transition], dict),
                         program_actually_took: [(Transition, dict)]):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print(("env: " if "env" == state["turn"] else "con: ") + str(trans) + "\nvar values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]) + "\n")

    # print("Environment wanted to take one of these:")

    # state = disagreed_on_transitions[1]
    # vs = []
    # for trans in disagreed_on_transitions[0]:
    #     vs += set(trans.condition.variablesin()
    #               + [v for v in list(state.keys()) if str(v).startswith("mon_")]
    #               + [v for v in list(state.keys()) if str(v).startswith("pred_")]
    #               + [v for v in program.env_events + program.con_events])
    #     print(str(trans))
    # print("with state: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]))
    #
    # print("Program actually took:")
    print("Environment did not want to take:")

    print(("env: " if "env" == program_actually_took[1]["turn"] else "con: ") + str(program_actually_took[0]))
    vs = []
    vs += set(program_actually_took[0].condition.variablesin()
              + [v for v in list(program_actually_took[1].keys()) if str(v).startswith("mon_")]
              + [v for v in list(program_actually_took[1].keys()) if str(v).startswith("pred_")]
              + [v for v in program.env_events + program.con_events])
    print("with state: " + ", ".join([str(v) + "=" + program_actually_took[1][str(v)] for v in vs]))


def write_counterexample_state(program,
                         agreed_on_transitions: [(Transition, dict)],
                         disagreed_on_state: ([Formula], dict)):
    print("Mismatch:")
    print("Agreed on transitions:")
    for trans, state in ([(t, s) for (t, s) in agreed_on_transitions]):
        vs = set(trans.condition.variablesin()
                 + [v for v in list(state.keys()) if str(v).startswith("mon_")]
                 + [v for v in list(state.keys()) if str(v).startswith("pred_")]
                 + [v for v in program.env_events + program.con_events])

        print(("env: " if "env" == state["turn"] else "con: ") + str(trans) + "\nvar values: " + ", ".join([str(v) + "=" + state[str(v)] for v in vs]) + "\n")

    print("Environment wanted state to satisfy:")

    print(", ".join([str(p) for p in disagreed_on_state[0]]))

    print("Program however has state:")
    print(", ".join([v + " = " + k for v,k in disagreed_on_state[1].items()]))
