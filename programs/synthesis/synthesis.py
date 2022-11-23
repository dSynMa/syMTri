from typing import Tuple, List, Any
from dataclasses import dataclass


from parsing.string_to_ltl import string_to_ltl
from programs.abstraction.predicate_abstraction import predicate_abstraction, abstraction_to_ltl
from programs.abstraction.refinement import safety_refinement, liveness_refinement, use_liveness_refinement
from programs.program import Program
from programs.synthesis import ltl_synthesis
from programs.synthesis.ltl_synthesis import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from programs.synthesis.mealy_machine import MealyMachine
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import symbol_table_from_program, create_nuxmv_model_for_compatibility_checking, \
    there_is_mismatch_between_monitor_and_strategy, \
    parse_nuxmv_ce_output_finite, reduce_up_to_iff, \
    add_prev_suffix, label_pred, ground_predicate_on_bool_vars, \
    concretize_transitions, ce_state_to_predicate_abstraction_trans, \
    check_for_nondeterminism_last_step, ground_transitions
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import neg, G, F, implies, conjunct, X, true, Value
from prop_lang.variable import Variable


class Predicates:
    # TODO turn into a dataclass
    def __init__(self, state, transition) -> None:
        self.state_predicates = state
        self.transition_predicates = transition

    def pred_list(self):
        yield from self.state_predicates
        yield from self.transition_predicates

    def symbol_table_preds(self):
        def str_label(v):
            return str(label_pred(v, self.list()))

        return {
            str_label(v): TypedValuation(str_label(v), "bool", true())
            for v in self.list(all)}


@dataclass
class Inputs:
    program: Program
    ltl_assumptions: Formula
    ltl_guarantees: Formula
    in_acts: List[Variable]
    out_acts: List[Variable]

    def ltl(self):
        return implies(self.ltl_assumptions, self.ltl_guarantees).simplify()

    def mon_events(self):
        return self.program.out_events + [Variable(s) for s in self.program.states]

    def symbol_table_prevs(self):
        def _prev(name):
            return f"{name}_prev"
        return {
            _prev(tv.name): TypedValuation(_prev(tv.name), tv.type, tv.value) 
            for tv in self.program.valuation}


def setup_synthesis(aut: Program, ltl_text: str, tlsf_path: str) -> Tuple[Formula | Value, Formula | BiOp, List, List]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        if " Error\"" in ltl_text:
            raise Exception(f"Error parsing {tlsf_path}, see syfco error:\n{ltl_text}")
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
    inputs = Inputs(aut, ltl_assumptions, ltl_guarantees, in_acts, out_acts)

    return inputs


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool) -> Tuple[bool, Program]:
    ltl_assumptions, ltl_guarantees, in_acts, out_acts, inputs = setup_synthesis(
        aut, ltl_text, tlsf_path
    )
    return abstract_synthesis_loop(aut, ltl_assumptions, ltl_guarantees, in_acts, out_acts, docker, inputs)


def compute_abstraction(p: Predicates, inp: Inputs, docker: str, notebook=False) -> Tuple[bool, MealyMachine, Any, Any]:
    # ltl_assumptions: Formula,
    # ltl_guarantees: Formula,
    # in_acts: List[Variable],
    # out_acts: List[Variable],
    # state_predicates, transition_predicates,
    (
        abstract_program,
        env_to_program_transitions,
        con_to_program_transitions
    ) = predicate_abstraction(
        inp.program,
        p.state_predicates,
        p.transition_predicates,
        inp.program.symbol_table,
        True)

    abstraction, ltl_to_program_transitions = abstraction_to_ltl(
        abstract_program, env_to_program_transitions,
        con_to_program_transitions, p.state_predicates,
        p.transition_predicates)

    if not notebook:
        print(", ".join(map(str, abstraction)))

    pred_name_dict = {p: label_pred(p, p.list_all()) for p in p.pred_list()}
    pred_acts = [pred_name_dict[v] for v in pred_name_dict.keys()]

    # TODO should be computed incrementally
    predicate_constraints = []
    i = 0
    while i < len(p.transition_predicates):
        dec = pred_name_dict[p.transition_predicates[i]]
        inc = pred_name_dict[p.transition_predicates[i + 1]]
        predicate_constraints += [X(G(neg(conjunct(dec, inc))))]

        predicate_constraints += [implies(G(F(dec)), G(F(inc)))]
        i += 2

    (real, mm) = ltl_synthesis.ltl_synthesis(
        predicate_constraints + abstraction,  # assumptions
        [inp.ltl()],  # ltl formula
        inp.in_acts + pred_acts,
        inp.out_acts,
        docker)
    if not notebook:
        print(mm.to_dot(p.pred_list()))
    return real, mm, abstract_program, ltl_to_program_transitions


@dataclass
class Counterexample:
    program: Program
    ce: Any
    agreed_on: list
    disagreed_on: list
    monitor_actually_took: Any


def check_mismatch(p: Predicates,
                   mm: MealyMachine, real,
                   inp: Inputs, abstract_program,
                   ltl_to_program_transitions):
    mealy = mm.to_nuXmv_with_turns(inp.program.states, inp.program.out_events, p.state_predicates, p.transition_predicates)
    system = create_nuxmv_model_for_compatibility_checking(inp.program, mealy, inp.mon_events(), p.pred_list(), False)
    contradictory, there_is_mismatch, out = there_is_mismatch_between_monitor_and_strategy(system, real, False, inp.ltl_assumptions, inp.ltl_guarantees)
    whatsitsname = "controller" if real else "counterstrategy"

    ## deal with if there is nothing wrong
    if not there_is_mismatch or contradictory:
        print("No mismatch found between " + (
            "strategy" if real else "counterstrategy") + " and program when excluding traces for which the monitor has a non-deterministic choice.")
        print("Trying for when the monitor has a non-deterministic choice..")
        system = create_nuxmv_model_for_compatibility_checking(inp.program, mealy, inp.mon_events(), p.pred_list(), True)
        contradictory, there_is_mismatch, out = \
            there_is_mismatch_between_monitor_and_strategy(
                system, real, False, inp.ltl_assumptions, inp.ltl_guarantees)

        if contradictory:
            raise Exception(
                f"I have no idea what's gone wrong. Strix thinks the previous mealy machine is a {whatsitsname}, "
                "but nuXmv thinks it is non consistent with the monitor.\n"
                "This may be a problem with nuXmv, e.g., it does not seem to play well with integer division.")

        if not there_is_mismatch:
            print(
                f"No mismatch found between {whatsitsname} and program "
                "even when including traces for which the monitor has a "
                "non-deterministic choice.\n"
                "Computing projection of controller onto predicate abstraction...")

            ## Finished
            controller_projected_on_program = mm.project_controller_on_program(
                inp.program, abstract_program,
                p.state_predicates,
                p.transition_predicates,
                inp.program.symbol_table | inp.symbol_table_preds())

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
                        f"The {whatsitsname} has no outgoing transition from this monitor state: "
                        ", ".join([str(p) for p in list(t.tgt)]))
            if not there_is_mismatch:
                # Quit early
                return None, real, controller_projected_on_program, out
       
        ## Compute mismatch trace
        ce, transition_indices_and_state = parse_nuxmv_ce_output_finite(
            len(inp.program.env_transitions) + len(inp.program.con_transitions), out)
        transitions_without_stutter_monitor_took = concretize_transitions(inp.program, transition_indices_and_state)
        last_desired_env_con_env_trans: List[Tuple[Transition, Transition]] = ce_state_to_predicate_abstraction_trans(
            ltl_to_program_transitions, inp.program.symbol_table | p.symbol_table_preds, ce[-4], ce[-3], ce[-2])

        agreed_on_transitions = transitions_without_stutter_monitor_took[:-1]
        disagreed_on_transitions = []
        monitor_actually_took = transitions_without_stutter_monitor_took[-1]

        if len(monitor_actually_took) == 1:
            (tran, state) = monitor_actually_took[0]
            if tran in inp.program.con_transitions:
                disagreed_on_transitions += (list(set(
                    t.with_condition(t.condition) for i in range(len(last_desired_env_con_env_trans)) for t in
                    last_desired_env_con_env_trans[i][0])), state)
            elif tran in inp.program.env_transitions:
                disagreed_on_transitions += (list(set(
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
                disagreed_on_transitions += (list(
                    set([t.with_condition(t.condition) for i in range(len(last_desired_env_con_env_trans)) for t in
                         last_desired_env_con_env_trans[i][0]])), con_state)
            else:
                agreed_on_transitions += [[monitor_actually_took[0]]]
                monitor_actually_took = monitor_actually_took[1:]
                disagreed_on_transitions += (list(
                    set([t.with_condition(t.condition) for i in all_with_matching_con_trans for t in
                         last_desired_env_con_env_trans[i][1]])), env_state)

        cex = Counterexample(inp.program, ce, agreed_on_transitions, disagreed_on_transitions, monitor_actually_took)

        write_counterexample(inp.program, agreed_on_transitions, disagreed_on_transitions, monitor_actually_took)
        check_for_nondeterminism_last_step(monitor_actually_took[0][1], inp.program, False, None)
        ## end compute mismatch trace
        return cex, real, controller_projected_on_program, out


def try_liveness(inp: Inputs,
                 preds: Predicates,
                 cex: Counterexample,
                 rankings: list,
                 force: bool = False,
                 only_suggest: bool = False) -> tuple:
    try:
        state_pred_label_to_formula = {
            label_pred(p, preds.pred_list()): p
            for p in preds.state_predicates}
        last_counterstrategy_state = [
            key for key, v in cex.ce[-1].items()
            if key.startswith("st_") and v == "TRUE"][0]
        (
            use_liveness,
            counterexample_loop,
            entry_predicate,
            entry_predicate_in_terms_of_preds
        ) = use_liveness_refinement(
            inp.program, cex.agreed_on_transitions,
            cex.disagreed_on_transitions, last_counterstrategy_state,
            cex.monitor_actually_took, inp.program.symbol_table,
            state_pred_label_to_formula)
    except Exception as e:
        print("WARNING: " + str(e))
        print("I will try to use safety instead.")
        return False

    if only_suggest:
        # This may be useful in interactive mode
        return use_liveness

    if use_liveness or force:
        try:
            ranking, invars = liveness_step(
                inp.program, counterexample_loop, inp.program.symbol_table,
                entry_predicate, entry_predicate_in_terms_of_preds,
                cex.monitor_actually_took[0])

            # rankings.append((ranking, invars)) todo in main loop
            new_transition_predicates = [
                x for r, _ in rankings
                for x in [
                    BiOp(add_prev_suffix(inp.program, r), ">", r),
                    BiOp(add_prev_suffix(inp.program, r), "<", r)]]

            if new_transition_predicates == []:
                # raise Exception("No new transition predicates identified.")
                print("No transition predicates identified. So will try safety refinement.")
                use_liveness = False

            print("Found: " + ", ".join([str(p) for p in new_transition_predicates]))

            new_all_trans_preds = {x.simplify() for x in new_transition_predicates}
            new_all_trans_preds = reduce_up_to_iff(
                preds.transition_predicates, list(new_all_trans_preds),
                inp.program.symbol_table | inp.symbol_table_prevs())

            if len(new_all_trans_preds) == len(preds.transition_predicates):
                fmt_tr_preds = ", ".join([str(p) for p in new_transition_predicates])
                print(
                    "I did something wrong, "
                    "it turns out the new transition predicates "
                    f"({fmt_tr_preds})"
                    "are a subset of previous predicates.\n"
                    "I will try safety refinement instead.")
                use_liveness = False
                # important to add this, since later on assumptions depend on position of predicates in list
                preds.transition_predicates += new_transition_predicates

            return True
        except Exception as e:
            print(e)
            print("I will try safety refinement instead.")
            return False


def abstract_synthesis_loop(program: Program, ltl_assumptions: Formula, ltl_guarantees: Formula, in_acts: [Variable],
                            out_acts: [Variable], docker: str, inp: Inputs) -> \
        Tuple[bool, MealyMachine]:

    # TODO add check that monitor is deterministic under given ltl assumptions
    eager = False
    keep_only_bool_interpolants = True

    symbol_table = program.symbol_table

    state_predicates = []
    rankings = []
    transition_predicates = []

    mon_events = inp.program.out_events + [Variable(s) for s in inp.program.states]

    while True:

        preds = Predicates(state_predicates, transition_predicates, program)

        # Compute abstraction
        (
            real, mm, abstract_program, ltl_to_program_transitions
        ) = compute_abstraction(
            preds, ltl_assumptions, ltl_guarantees, in_acts, out_acts, "")

        # try getting a counterexaample
        (
            cex, real, controller_projected_on_program, out
        ) = check_mismatch(preds, mm, real, inp, abstract_program, ltl_to_program_transitions)

        if cex is None:
            if real:
                return True, controller_projected_on_program
            else:
                # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
                return False, controller_projected_on_program

        use_liveness = try_liveness(inp, preds, cex, rankings, force=False, only_suggest=False)

        ## do safety refinement
        if eager or not use_liveness:
            new_preds = safety_refinement(ce, agreed_on_transitions, disagreed_on_transitions, symbol_table, program, use_dnf=False)
            print("Found: " + ", ".join([str(p) for p in new_preds]))
            if len(new_preds) == 0:
                e = Exception("No state predicates identified.")
                print("No state predicates identified.")
                print("Trying again by putting interpolant B in DNF form and checking each disjunct separately. This may take some time...")
                new_preds = safety_refinement(ce, agreed_on_transitions, disagreed_on_transitions, symbol_table, program, use_dnf=True)
                print("Found: " + ", ".join([str(p) for p in new_preds]))
                check_for_nondeterminism_last_step(monitor_actually_took[0][1], program, True, e)
                raise e

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
                check_for_nondeterminism_last_step(monitor_actually_took[0][1], program, True, e)
                print("For debugging:\nComputing projection of controller onto predicate abstraction..")
                controller_projected_on_program = mm.project_controller_on_program(program, abstract_program,
                                                                                   state_predicates,
                                                                                   transition_predicates,
                                                                                   symbol_table | symbol_table_preds)

                print(controller_projected_on_program.to_dot())
                raise e

            if keep_only_bool_interpolants:
                bool_interpolants = [p for p in new_preds if
                                     p not in state_predicates and p in new_all_preds and 0 == len(
                                         [v for v in p.variablesin() if
                                          symbol_table[str(v)].type != "bool" and symbol_table[
                                              str(v)].type != "boolean"])]
                if len(bool_interpolants) > 0:
                    new_all_preds = [p for p in new_all_preds if p in bool_interpolants or p in state_predicates]
            print("Using: " + ", ".join([str(p) for p in new_all_preds if p not in state_predicates]))

            state_predicates = list(new_all_preds)


def liveness_step(program, counterexample_loop, symbol_table, entry_predicate, entry_predicate_in_terms_of_preds,
                  exit_transition):
    # ground transitions in the counterexample loop
    # on the environment and controller events in the counterexample
    loop_before_exit = ground_transitions(program, counterexample_loop)

    entry_predicate_grounded = ground_predicate_on_bool_vars(program, entry_predicate,
                                                             counterexample_loop[0][1]).simplify()
    entry_predicate_in_terms_of_preds_grounded = ground_predicate_on_bool_vars(program,
                                                                               entry_predicate_in_terms_of_preds,
                                                                               counterexample_loop[0][1]).simplify()

    exit_predicate_grounded = ground_predicate_on_bool_vars(program, exit_transition[0].condition,
                                                            exit_transition[1]).simplify()

    ranking, invars = liveness_refinement(symbol_table,
                                          program,
                                          entry_predicate_grounded, entry_predicate_in_terms_of_preds_grounded,
                                          loop_before_exit,
                                          exit_predicate_grounded)
    if len(invars) > 0:
        raise NotImplementedError(
            "Ranking function comes with invar, what shall we do here? " + ranking + "\n" + ", ".join(
                [str(invar) for invar in invars]))

    return ranking, invars


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
