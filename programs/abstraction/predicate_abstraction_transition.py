from itertools import chain, combinations
import re

from func_timeout import func_timeout
from pysmt.shortcuts import And, Not, TRUE

from parsing.string_to_prop_logic import string_to_prop
from programs.abstraction.abstract_state import AbstractState
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import label_preds, add_prev_suffix, stutter_transitions, \
    stutter_transition, symbol_table_from_program, safe_update_set_vals, safe_update_list_vals
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    implies, G, X, true, false, disjunct, simplify_formula_without_math, cnf
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()


class PredicateAbstraction:
    def __init__(self, program: Program):
        self.state_predicates = []
        self.transition_predicates = []

        self.con_to_program_transitions = None
        self.env_to_program_transitions = None

        self.con_program_transitions_to_abstract = None
        self.env_program_transitions_to_abstract = None

        self.state_to_env_transitions = None
        self.state_to_con_transitions = None

        self.abstraction = None
        self.program = program
        self.cache = {}
        self.f_cache = {}
        self.loop_counter = 0
        self.loops = []

        self.env_partitions = {}
        self.con_partitions = {}


    def getFromCache(self, f: Formula):
        if f in self.cache.keys():
            return self.cache[f]
        else:
            Ps = set()
            Ps.add(frozenset())
            return Ps

    def getFromFCache(self, con_turn_flag, t, E):
        if (t, E) in self.f_cache.keys():
            return self.f_cache[(con_turn_flag, t, E)]
        else:
            return None

    def meaning_within(self, f: Formula, predicates: [Formula], symbol_table):
        Ps = self.getFromCache(f)
        return meaning_within_incremental(f, Ps, predicates, symbol_table)

    def initialise(self):
        print("Initialising predicate abstraction.")
        program = self.program
        init_st = program.initial_state
        init_conf = conjunct_typed_valuation_set(program.valuation)
        env_transitions = set()
        con_transitions = set()
        current_states = set()

        orig_env_transitions, orig_con_transitions = program.complete_transitions()

        symbol_table = self.program.symbol_table

        env_to_program_transitions = {}
        con_to_program_transitions = {}

        new_env_program_transitions_to_abstract = {}
        new_con_program_transitions_to_abstract = {}

        # initial transitions rule
        for t in orig_env_transitions:
            # TODO when program is deterministic re-use info about Es that satisfy other transitions
            if t.src == program.initial_state:
                vars_in_cond = t.condition.variablesin()
                env_vars_in_cond = [e for e in vars_in_cond if e in program.env_events]
                env_powerset = powerset_complete(env_vars_in_cond)
                #TODO what happens when len(env_vars_in_cond) == 0?

                #gather all sets that satisfy the guard
                guarded = conjunct(init_conf, t.condition)
                satisfying_env_behaviour = [E for E in env_powerset if smt_checker.check(And(*conjunct_formula_set(E | {guarded}).to_smt(symbol_table)))]
                abstract_guard = disjunct_formula_set([conjunct_formula_set(E) for E in satisfying_env_behaviour])
                abstract_guard_cnf = cnf(abstract_guard, symbol_table)
                abstract_guard_simplified = simplify_formula_without_math(abstract_guard, symbol_table)

                next_state = t.tgt
                current_states.add(next_state)

                new_output = set(t.output)
                new_output |= {neg(o) for o in program.out_events if o not in t.output}
                new_output = list(new_output)

                abs_t = Transition(init_st, abstract_guard, [], new_output, next_state)
                safe_update_list_vals(env_to_program_transitions, abs_t, [t])
                safe_update_set_vals(new_env_program_transitions_to_abstract, t, {abs_t})
                env_transitions.add(abs_t)

                key = str(abs_t.src) + str(
                    conjunct_formula_set(sorted(abs_t.output, key=lambda x: str(x)))) + str(
                    abs_t.tgt)
                if key in self.env_partitions.keys():
                    self.env_partitions[key].append(abs_t)
                else:
                    self.env_partitions[key] = [abs_t]

        con_turn_flag = True

        done_states_env = set()
        done_states_con = set()

        while len(current_states) != 0:
            next_states = set()

            if con_turn_flag:
                transition_set = orig_con_transitions
                events = program.con_events
            else:
                transition_set = orig_env_transitions
                events = program.env_events

            new_transitions = set()

            for q in current_states:
                q_transitions = {t for t in transition_set if str(t.src) == str(q)}
                for t in q_transitions:
                    vars_in_cond = t.condition.variablesin()
                    env_vars_in_cond = [e for e in vars_in_cond if e in events]

                    env_powerset = powerset_complete(env_vars_in_cond)

                    satisfying_behaviour = [E for E in env_powerset if smt_checker.check(
                        And(*conjunct_formula_set(E | {t.condition}).to_smt(symbol_table)))]
                    abstract_guard = disjunct_formula_set([conjunct_formula_set(E) for E in satisfying_behaviour])

                    next_state = t.tgt
                    new_output = set(t.output)
                    new_output |= {neg(o) for o in program.out_events if o not in t.output}
                    new_output = list(new_output)

                    abs_t = Transition(q, abstract_guard, [], new_output, next_state)

                    new_transitions.add(abs_t)

                    if con_turn_flag:
                        safe_update_list_vals(con_to_program_transitions, abs_t, [t])
                        safe_update_set_vals(new_con_program_transitions_to_abstract, t, {abs_t})

                        key = str(abs_t.src) + str(
                            conjunct_formula_set(sorted(abs_t.output, key=lambda x: str(x)))) + str(
                            abs_t.tgt)
                        if key in self.con_partitions.keys():
                            self.con_partitions[key].append(abs_t)
                        else:
                            self.con_partitions[key] = [abs_t]
                    else:
                        safe_update_list_vals(env_to_program_transitions, abs_t, [t])
                        safe_update_set_vals(new_env_program_transitions_to_abstract, t, {abs_t})

                        key = str(abs_t.src) + str(
                            conjunct_formula_set(sorted(abs_t.output, key=lambda x: str(x)))) + str(
                            abs_t.tgt)
                        if key in self.env_partitions.keys():
                            self.env_partitions[key].append(abs_t)
                        else:
                            self.env_partitions[key] = [abs_t]

                    if con_turn_flag and next_state not in done_states_env:
                        next_states.add(next_state)
                    elif not con_turn_flag and next_state not in done_states_con:
                        next_states.add(next_state)

            if con_turn_flag:
                done_states_con.update(current_states)
                con_transitions.update(new_transitions)
            else:
                done_states_env.update(current_states)
                env_transitions.update(new_transitions)

            current_states = next_states

            con_turn_flag = not con_turn_flag

        states = {s for t in (env_transitions | con_transitions) for s in
                  {t.src, t.tgt}}  # done_states_env | done_states_con

        # For debugging
        for t in env_transitions:
            good = False
            for x in con_transitions:
                if t.tgt == x.src:
                    good = True
                    break
            if not good:
                raise Exception("Predicate abstraction has state, " + str(t.tgt) + ", without output transitions.\n"
                                                                                   "" + "\n".join(
                    map(str, orig_env_transitions + orig_con_transitions)))

        for t in con_transitions:
            good = False
            for x in env_transitions:
                if t.tgt == x.src:
                    good = True
                    break
            if not good:
                raise Exception("Predicate abstraction has state, " + str(t.tgt) + ", without output transitions.")

        self.env_to_program_transitions = env_to_program_transitions
        self.con_to_program_transitions = con_to_program_transitions
        self.env_program_transitions_to_abstract = new_env_program_transitions_to_abstract
        self.con_program_transitions_to_abstract = new_con_program_transitions_to_abstract

        self.state_to_env_transitions = {s: [t for t in env_transitions if t.src == s] for s in states}
        self.state_to_con_transitions = {s: [t for t in con_transitions if t.src == s] for s in states}

        self.abstraction = Program("pred_abst_" + program.name, states | {init_st}, init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events, False)

    def add_predicates(self, new_state_predicates: [Formula], new_transition_predicates: [Formula], simplified: bool):
        if len(new_state_predicates) + len(new_transition_predicates) == 0:
            return
        print("Adding predicates to predicate abstraction:")
        print("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")
        print("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")
        program = self.program
        init_st = program.initial_state
        init_conf = conjunct_typed_valuation_set(program.valuation)
        env_transitions = set()
        con_transitions = set()

        orig_env_transitions, orig_con_transitions = program.complete_transitions()

        symbol_table = self.program.symbol_table

        symbol_table = symbol_table | {(str(key) + "_prev"): value for key, value in
                                                      symbol_table.items()}\
                                    | {(str(key) + "_prev" + "_prev"): value for key, value in
                                       symbol_table.items()}

        self.state_predicates += new_state_predicates
        self.transition_predicates += new_transition_predicates

        # TODO we are not doing this incrementally...
        predicates = self.state_predicates + self.transition_predicates
        new_predicates = new_state_predicates + new_transition_predicates

        new_env_to_program_transitions = {}
        new_con_to_program_transitions = {}

        new_env_program_transitions_to_abstract = {}
        new_con_program_transitions_to_abstract = {}

        new_state_to_env_transitions = {}
        new_state_to_con_transitions = {}

        new_env_partitions = {}
        new_con_partitions = {}

        done_states = set()

        # current states will be pairs of old states and a set of sets of predicates
        init_preds = set()
        for p in new_state_predicates:
            if smt_checker.check(And(*(conjunct(init_conf, p).to_smt(symbol_table)))):
                init_preds |= {p}
            else:
                init_preds |= {neg(p)}

        current_states = {(True, init_st, frozenset(init_preds))}

        while len(current_states) > 0:
            next_states = set()
            for (env_turn, st, new_Ps) in current_states:
                done_states.add((env_turn, st, new_Ps))
                for abstract_trans in (self.state_to_env_transitions[st]
                                            if env_turn else self.state_to_con_transitions[st]):
                    # TODO some of the new abstract transitions may be redundant
                    # partition program_trans according to whether their actions mention variables related to the new predicates or not
                    print(len(self.env_to_program_transitions[abstract_trans]
                                            if env_turn else self.con_to_program_transitions[abstract_trans]))
                    for program_trans in (self.env_to_program_transitions[abstract_trans]
                                            if env_turn else self.con_to_program_transitions[abstract_trans]):

                        if isinstance(abstract_trans.src, AbstractState):
                            state = conjunct_formula_set(st.predicates)
                        else:
                            state = init_conf

                        pre_smt_formula = conjunct_formula_set({state, program_trans.condition} | new_Ps)

                        # TODO events will be in DNF, here need to get all disjuncts, get all those that satisfy guard, and move on with them
                        if isinstance(abstract_trans.condition, BiOp) and abstract_trans.condition.op[0] == "|":
                            events = disjunct_formula_set([E for E in abstract_trans.condition.sub_formulas_up_to_associativity()
                                      if smt_checker.check(And(*(conjunct(pre_smt_formula, E).to_smt(symbol_table))))])
                            pre_smt_formula = conjunct(pre_smt_formula, events)
                        else:
                            events = abstract_trans.condition


                        smt_formula = And(*pre_smt_formula.to_smt(symbol_table))

                        if smt_checker.check(smt_formula):
                            prev_condition = add_prev_suffix(pre_smt_formula)

                            complete_action = program.complete_action_set(program_trans.action)
                            prev_action = [BiOp(act.left, "=", add_prev_suffix(act.right)) for act in
                                           complete_action]

                            f = conjunct_formula_set(list(prev_action) + [prev_condition] + abstract_trans.tgt.predicates)

                            if not smt_checker.check(And(*f.to_smt(symbol_table))):
                                continue
                            else:
                                if f in self.cache.keys():
                                    next_Ps = self.cache[f]
                                else:
                                    next_Ps = self.meaning_within(f, new_predicates, symbol_table)
                                    self.cache[f] = next_Ps
                                for next_P in next_Ps:
                                    if len(next_P) != len(new_state_predicates) + len(new_transition_predicates):
                                        raise Exception("Something went wrong")
                                    if env_turn:
                                        new_output = set(program_trans.output)
                                        new_output |= {neg(o) for o in program.out_events if o not in program_trans.output}
                                        new_output = list(new_output)
                                    else:
                                        new_output = []

                                    if isinstance(abstract_trans.src, AbstractState):
                                        new_abs_src = AbstractState(abstract_trans.src.state,
                                                                    set(abstract_trans.src.predicates) | set(new_Ps))
                                    else:
                                        new_abs_src = abstract_trans.src
                                    new_abs_tgt = AbstractState(abstract_trans.tgt.state, set(abstract_trans.tgt.predicates) | next_P)

                                    if not smt_checker.check(And(*conjunct_formula_set(set(abstract_trans.tgt.predicates) | next_P).to_smt(symbol_table))):
                                        raise Exception("Something went wrong")

                                    new_abstract_trans = Transition(new_abs_src, events, [], new_output, new_abs_tgt)

                                    next = (not env_turn, abstract_trans.tgt, frozenset(next_P))
                                    if next not in done_states | current_states:
                                        next_states |= {next}

                                    if env_turn:
                                        try:
                                            env_transitions |= {new_abstract_trans}
                                        except Exception as e:
                                            print(e)
                                            raise e
                                        safe_update_set_vals(new_env_to_program_transitions, new_abstract_trans, {program_trans})
                                        safe_update_set_vals(new_env_program_transitions_to_abstract, program_trans, {new_abstract_trans})

                                        # safe_update_list_vals(new_program_env_to_abs_transitions, program_trans, [abs_t])
                                        safe_update_set_vals(new_state_to_env_transitions, new_abstract_trans.src, {new_abstract_trans})

                                        key = str(new_abstract_trans.src) + str(
                                            conjunct_formula_set(sorted(new_abstract_trans.output, key=lambda x: str(x)))) + str(
                                            new_abstract_trans.tgt)
                                        if key in new_env_partitions.keys():
                                            new_env_partitions[key].append(new_abstract_trans)
                                        else:
                                            new_env_partitions[key] = [new_abstract_trans]
                                    else:
                                        con_transitions |= {new_abstract_trans}
                                        safe_update_set_vals(new_con_to_program_transitions, new_abstract_trans, {program_trans})
                                        safe_update_set_vals(new_con_program_transitions_to_abstract, program_trans, {new_abstract_trans})
                                        # safe_update_list_vals(new_program_con_to_abs_transitions, program_trans, [abs_t])
                                        safe_update_set_vals(new_state_to_con_transitions, new_abstract_trans.src, {new_abstract_trans})

                                        key = str(new_abstract_trans.src) + str(
                                            conjunct_formula_set(sorted(new_abstract_trans.output, key=lambda x: str(x)))) + str(
                                            new_abstract_trans.tgt)
                                        if key in new_con_partitions.keys():
                                            new_con_partitions[key].append(new_abstract_trans)
                                        else:
                                            new_con_partitions[key] = [new_abstract_trans]

                                    # trans_from_here.add(abs_t)
            current_states = next_states

        states = {s for t in (env_transitions | con_transitions) for s in
                  {t.src, t.tgt}}  # done_states_env | done_states_con

        # For debugging
        for t in env_transitions:
            good = False
            for x in con_transitions:
                if t.tgt == x.src:
                    good = True
                    break
            if not good:
                raise Exception("Predicate abstraction has state, " + str(t.tgt) + ", without output transitions.\n"
                                                                                   "" + "\n".join(
                    map(str, orig_env_transitions + orig_con_transitions)))

        for t in con_transitions:
            good = False
            for x in env_transitions:
                if t.tgt == x.src:
                    good = True
                    break
            if not good:
                raise Exception("Predicate abstraction has state, " + str(t.tgt) + ", without output transitions.")

        self.env_to_program_transitions = new_env_to_program_transitions
        self.con_to_program_transitions = new_con_to_program_transitions

        self.env_program_transitions_to_abstract = new_env_program_transitions_to_abstract
        self.con_program_transitions_to_abstract = new_con_program_transitions_to_abstract

        self.state_to_env_transitions = {s: [t for t in env_transitions if t.src == s] for s in states}
        self.state_to_con_transitions = {s: [t for t in con_transitions if t.src == s] for s in states}

        self.env_partitions = new_env_partitions
        self.con_partitions = new_con_partitions

        self.abstraction = Program("pred_abst_" + program.name, states | {init_st}, init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events, False)

    def add_transition_predicates(self, new_transition_predicates: [Formula], simplified: bool):
        raise Exception("Not implemented yet")
        if len(new_transition_predicates) == 0:
            return
        print("Adding transition predicates to predicate abstraction:")
        print("preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")
        program = self.program
        init_st = program.initial_state
        init_conf = conjunct_typed_valuation_set(program.valuation)
        env_transitions = set()
        con_transitions = set()

        orig_env_transitions, orig_con_transitions = program.complete_transitions()

        symbol_table = self.program.symbol_table

        symbol_table = symbol_table | {(str(key) + "_prev"): value for key, value in
                                                      symbol_table.items()}\
                                    | {(str(key) + "_prev" + "_prev"): value for key, value in
                                       symbol_table.items()}

        self.transition_predicates += new_transition_predicates

        new_env_to_program_transitions = {}
        new_con_to_program_transitions = {}

        new_env_program_transitions_to_abstract = {}
        new_con_program_transitions_to_abstract = {}

        new_state_to_env_transitions = {}
        new_state_to_con_transitions = {}

        done_states = set()

        # current states will be pairs of old states and a set of sets of predicates
        current_states = {(True, init_st, frozenset({neg(p) for p in new_transition_predicates}))}

        while len(current_states) > 0:
            next_states = set()
            for (env_turn, st, new_Ps) in current_states:
                done_states.add((env_turn, st, new_Ps))
                for abstract_trans in (self.state_to_env_transitions[st]
                                            if env_turn else self.state_to_con_transitions[st]):
                    for program_trans in (self.env_to_program_transitions[abstract_trans]
                                            if env_turn else self.con_to_program_transitions[abstract_trans]):
                        events = abstract_trans.condition
                        if isinstance(abstract_trans.src, AbstractState):
                            state = conjunct_formula_set(abstract_trans.src.predicates)
                        else:
                            state = init_conf
                        pre_smt_formula = conjunct_formula_set({events, state, program_trans.condition} | new_Ps)
                        smt_formula = And(*pre_smt_formula.to_smt(symbol_table))

                        if smt_checker.check(smt_formula):
                            prev_condition = add_prev_suffix(pre_smt_formula)

                            complete_action = program.complete_action_set(program_trans.action)
                            prev_action = [BiOp(act.left, "=", add_prev_suffix(act.right)) for act in
                                           complete_action]

                            f = conjunct_formula_set(list(prev_action) + [prev_condition] + abstract_trans.tgt.predicates)

                            if not smt_checker.check(And(*f.to_smt(symbol_table))):
                                continue
                            else:
                                if f in self.cache.keys():
                                    next_Ps = self.cache[f]
                                else:
                                    next_Ps = self.meaning_within(f, new_predicates, symbol_table)
                                    self.cache[f] = next_Ps
                                for next_P in next_Ps:
                                    if len(next_P) != len(new_state_predicates) + len(new_transition_predicates):
                                        raise Exception("Something went wrong")
                                    if env_turn:
                                        new_output = set(program_trans.output)
                                        new_output |= {neg(o) for o in program.out_events if o not in program_trans.output}
                                        new_output = list(new_output)
                                    else:
                                        new_output = []

                                    if isinstance(abstract_trans.src, AbstractState):
                                        new_abs_src = AbstractState(abstract_trans.src.state,
                                                                    set(abstract_trans.src.predicates) | set(new_Ps))
                                    else:
                                        new_abs_src = abstract_trans.src
                                    new_abs_tgt = AbstractState(abstract_trans.tgt.state, set(abstract_trans.tgt.predicates) | next_P)

                                    if not smt_checker.check(And(*conjunct_formula_set(set(abstract_trans.tgt.predicates) | next_P).to_smt(symbol_table))):
                                        raise Exception("Something went wrong")

                                    new_abstract_trans = Transition(new_abs_src, events, [], new_output, new_abs_tgt)

                                    next = (not env_turn, abstract_trans.tgt, frozenset(next_P))
                                    if next not in done_states | current_states:
                                        next_states |= {next}

                                    if env_turn:
                                        env_transitions |= {new_abstract_trans}
                                        safe_update_set_vals(new_env_to_program_transitions, new_abstract_trans, {program_trans})
                                        safe_update_set_vals(new_env_program_transitions_to_abstract, program_trans, {new_abstract_trans})

                                        # safe_update_list_vals(new_program_env_to_abs_transitions, program_trans, [abs_t])
                                        safe_update_set_vals(new_state_to_env_transitions, new_abstract_trans.src, {new_abstract_trans})
                                    else:
                                        con_transitions |= {new_abstract_trans}
                                        safe_update_set_vals(new_con_to_program_transitions, new_abstract_trans, {program_trans})
                                        safe_update_set_vals(new_con_program_transitions_to_abstract, program_trans, {new_abstract_trans})
                                        # safe_update_list_vals(new_program_con_to_abs_transitions, program_trans, [abs_t])
                                        safe_update_set_vals(new_state_to_con_transitions, new_abstract_trans.src, {new_abstract_trans})

                                    # trans_from_here.add(abs_t)
            current_states = next_states

        states = {s for t in (env_transitions | con_transitions) for s in
                  {t.src, t.tgt}}  # done_states_env | done_states_con

        # For debugging
        for t in env_transitions:
            good = False
            for x in con_transitions:
                if t.tgt == x.src:
                    good = True
                    break
            if not good:
                raise Exception("Predicate abstraction has state, " + str(t.tgt) + ", without output transitions.\n"
                                                                                   "" + "\n".join(
                    map(str, orig_env_transitions + orig_con_transitions)))

        for t in con_transitions:
            good = False
            for x in env_transitions:
                if t.tgt == x.src:
                    good = True
                    break
            if not good:
                raise Exception("Predicate abstraction has state, " + str(t.tgt) + ", without output transitions.")

        self.env_to_program_transitions = new_env_to_program_transitions
        self.con_to_program_transitions = new_con_to_program_transitions

        self.env_program_transitions_to_abstract = new_env_program_transitions_to_abstract
        self.con_program_transitions_to_abstract = new_con_program_transitions_to_abstract

        self.state_to_env_transitions = {s: [t for t in env_transitions if t.src == s] for s in states}
        self.state_to_con_transitions = {s: [t for t in con_transitions if t.src == s] for s in states}

        self.abstraction = Program("pred_abst_" + program.name, states | {init_st}, init_st, [],
                                   env_transitions, con_transitions, program.env_events,
                                   program.con_events, program.out_events, False)

    def allowed_in_abstraction(self, path: [Transition]):
        if len(path) == 0:
            return True

        abstract_trans: [[Transition]] = []
        # assuming env-con alternation in path
        current_abstract_states = {self.abstraction.initial_state}
        current_t_index = 0

        env_turn = True

        while True:
            current_t = path[current_t_index]
            if env_turn:
                tentative_abstract_ts = self.env_program_transitions_to_abstract[current_t]
            else:
                tentative_abstract_ts = self.con_program_transitions_to_abstract[current_t]
            abstract_ts = [t for t in tentative_abstract_ts if t.src in current_abstract_states]
            if len(abstract_ts) == 0:
                return False, abstract_trans
            else:
                current_abstract_states = {t.tgt for t in abstract_ts}
                abstract_trans += [abstract_ts]
                current_t_index += 1
                if current_t_index == len(path):
                    return True, abstract_trans
                else:
                    env_turn = not env_turn

    def allowed_in_abstraction_with_new_pred(self, path : [Transition], new_predicate):
        if len(path) == 0:
            return True

        abstract_trans : [[Transition]] = []
        # assuming env-con alternation in path
        current_abstract_states = {self.abstraction.initial_state}
        current_t_index = 0

        env_turn = True

        while True:
            current_t = path[current_t_index]
            if env_turn:
                tentative_abstract_ts = self.env_program_transitions_to_abstract[current_t]
            else:
                tentative_abstract_ts = self.con_program_transitions_to_abstract[current_t]
            abstract_ts = [t for t in tentative_abstract_ts if t.src in current_abstract_states]
            if len(abstract_ts) == 0:
                return False, abstract_trans
            else:
                current_abstract_states = {t.tgt for t in abstract_ts}
                abstract_trans += [abstract_ts]
                current_t_index += 1
                if current_t_index == len(path):
                    return True, abstract_trans
                else:
                    env_turn = not env_turn

    def make_explicit_terminating_loop(self, entry_condition, loop_body: [Transition], exit_transs: [Transition],
                                       exit_predicate):
        self.loops += [(entry_condition, loop_body, exit_transs)]
        new_env = []
        new_env += self.program.env_transitions
        new_con = []
        new_con += self.program.con_transitions
        entry_trans = loop_body[0]
        start = 0

        entry_trans_is_con = entry_trans in self.program.con_transitions
        if entry_trans_is_con:
            entry_trans = stutter_transition(self.program, entry_trans.src, True)
        else:
            start = 1

        old_to_new_env_transitions = {t: {t} for t in
                                      self.program.env_transitions + stutter_transitions(self.program, True)}
        old_to_new_con_transitions = {t: {t} for t in
                                      self.program.con_transitions + stutter_transitions(self.program, False)}

        update_from_to = lambda _action, _from, _to: ([v for v in _action if v.left != _from]
                                                      + [BiOp(_from, ":=", disjunct(v.right, _to)) for v in _action if
                                                         v.left == _from]) \
            if any(v for v in _action if v.left == _from) \
            else _action + [BiOp(_from, ":=", _to)]

        entered_loop = Variable("loop" + str(self.loop_counter) + "_1")

        env_turn = entry_trans in old_to_new_env_transitions.keys()

        env_turn = not env_turn

        # TODO: find unique suffix
        step = 1
        i_t = start
        abstract_state_formula = true()
        symbol_table = symbol_table_from_program(self.program)

        loop_seq_vars = {entered_loop}

        for loop_seq_var in loop_seq_vars:
            symbol_table |= {(str(loop_seq_var) + "_" + str(step)): TypedValuation(
                (str(loop_seq_var) + "_" + str(step)), "bool", false())}

        while i_t < len(loop_body):
            if env_turn:
                if loop_body[i_t] not in old_to_new_env_transitions.keys():
                    step_t = stutter_transition(self.program, loop_body[i_t].src, True)
                else:
                    step_t = loop_body[i_t]
                    i_t += 1

                src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
                tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

                loop_seq_vars |= {src_state, tgt_state}

                for loop_seq_var in loop_seq_vars:
                    symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                        (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

                for k, v in symbol_table_from_program(self.program).items():
                    symbol_table |= {
                        (str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                    symbol_table |= {
                        (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step + 1), v.type, v.value)}

                ts_renamed = set()
                for t in old_to_new_env_transitions[step_t]:
                    t_renamed = Transition(t.src, t.condition,
                                           update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                          false()), t.output,
                                           t.tgt)
                    ts_renamed |= {t_renamed}
                    new_env += [t_renamed]

                    abstract_state_formula = conjunct(abstract_state_formula, t.condition.replace(
                        lambda var: Variable(var.name + "_" + str(step))))
                    abstract_state_formula = conjunct(abstract_state_formula,
                                                      conjunct_formula_set([BiOp(a.left.replace(
                                                          lambda var: Variable(var.name + "_" + str(step + 1))),
                                                                                 "=", a.right.replace(
                                                              lambda var: Variable(var.name + "_" + str(step))))
                                                                            for a in self.program.complete_action_set(
                                                              t.action)]))

                    alternate_trans_exit = [tt for tt in old_to_new_env_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_exit:
                        old_to_new_env_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(ttt.action, src_state, false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_env_transitions[tt]}

                        alternate_trans_stay = [tt for tt in old_to_new_env_transitions.keys()
                                                if t != tt and tt.src == t.src
                                                and not smt_checker.check(And(*conjunct(
                                neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                abstract_state_formula).to_smt(symbol_table)))]

                        for tt in alternate_trans_stay:
                            old_to_new_env_transitions[tt] = {
                                Transition(ttt.src, ttt.condition,
                                           update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                          false()),
                                           ttt.output, ttt.tgt)
                                for ttt in old_to_new_env_transitions[tt]}
                old_to_new_env_transitions[step_t] = ts_renamed

            elif not env_turn:
                if loop_body[i_t] not in old_to_new_con_transitions.keys():
                    step_t = stutter_transition(self.program, loop_body[i_t].src, False)
                else:
                    step_t = loop_body[i_t]
                    i_t += 1

                src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
                tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

                loop_seq_vars |= {src_state, tgt_state}

                for loop_seq_var in loop_seq_vars:
                    symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                        (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

                for k, v in symbol_table_from_program(self.program).items():
                    symbol_table |= {
                        (str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                    symbol_table |= {
                        (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}

                loop_seq_vars |= {src_state, tgt_state}

                ts_renamed = set()
                for t in old_to_new_con_transitions[step_t]:
                    t_renamed = Transition(t.src, t.condition,
                                           update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                          false()),
                                           t.output, t.tgt)
                    ts_renamed |= {t_renamed}
                    new_con += [t_renamed]

                    abstract_state_formula = conjunct(abstract_state_formula, t.condition.replace(
                        lambda var: Variable(var.name + "_" + str(step))))
                    abstract_state_formula = conjunct(abstract_state_formula,
                                                      conjunct_formula_set([BiOp(a.left.replace(
                                                          lambda var: Variable(var.name + "_" + str(step + 1))),
                                                                                 "=", a.right.replace(
                                                              lambda var: Variable(var.name + "_" + str(step))))
                                                                            for a in self.program.complete_action_set(
                                                              t.action)]))

                    alternate_trans_exit = [tt for tt in old_to_new_con_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_exit:
                        old_to_new_con_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(ttt.action, src_state, false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_con_transitions[tt]}

                        alternate_trans_stay = [tt for tt in old_to_new_con_transitions.keys()
                                                if t != tt and tt.src == t.src
                                                and not smt_checker.check(And(*conjunct(
                                neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                abstract_state_formula).to_smt(symbol_table)))]

                        for tt in alternate_trans_stay:
                            old_to_new_con_transitions[tt] = {
                                Transition(ttt.src, ttt.condition,
                                           update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                          false()),
                                           ttt.output, ttt.tgt)
                                for ttt in old_to_new_con_transitions[tt]}
                old_to_new_con_transitions[step_t] = ts_renamed

            # loop_states |= {Variable(t.src + "loop" +  str(self.loop_counter) + "_" + str(step)), Variable(t.tgt + "loop" +  str(self.loop_counter) + "_" + str(step + 1))}

            env_turn = not env_turn
            step += 1

        exit_trans_is_con = any(exit_trans
                                for exit_trans in exit_transs
                                if exit_trans not in old_to_new_env_transitions.keys())

        if env_turn and exit_trans_is_con:
            stutter_t = stutter_transition(self.program, exit_transs[0].src, True)

            src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
            tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

            loop_seq_vars |= {src_state, tgt_state}

            for loop_seq_var in loop_seq_vars:
                symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                    (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

            for k, v in symbol_table_from_program(self.program).items():
                symbol_table |= {(str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                symbol_table |= {
                    (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step + 1), v.type, v.value)}

            ts_renamed = set()
            for t in old_to_new_env_transitions[stutter_t]:
                t_renamed = Transition(t.src, t.condition,
                                       update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                      false()),
                                       t.output, t.tgt)
                ts_renamed |= {t_renamed}
                new_env += [t_renamed]

                abstract_state_formula = conjunct(abstract_state_formula,
                                                  t.condition.replace(lambda var: Variable(var.name + "_" + str(step))))
                abstract_state_formula = conjunct(abstract_state_formula,
                                                  conjunct_formula_set([BiOp(a.left.replace(
                                                      lambda var: Variable(var.name + "_" + str(step + 1))),
                                                      "=", a.right.replace(
                                                          lambda var: Variable(var.name + "_" + str(step))))
                                                      for a in
                                                      self.program.complete_action_set(t.action)]))

                alternate_trans_exit = [tt for tt in old_to_new_env_transitions.keys()
                                        if t != tt and tt.src == t.src
                                        and smt_checker.check(
                        And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                      abstract_state_formula).to_smt(symbol_table)))]

                for tt in alternate_trans_exit:
                    old_to_new_env_transitions[tt] = {
                        Transition(ttt.src, ttt.condition,
                                   update_from_to(ttt.action, src_state, false()),
                                   ttt.output, ttt.tgt)
                        for ttt in old_to_new_env_transitions[tt]}

                    alternate_trans_stay = [tt for tt in old_to_new_env_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and not smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_stay:
                        old_to_new_env_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                      false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_env_transitions[tt]}
            old_to_new_env_transitions[stutter_t] = ts_renamed

            step += 1
            env_turn = not env_turn
        elif not env_turn and not exit_trans_is_con:
            stutter_t = stutter_transition(self.program, exit_transs[0].src, False)

            src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))
            tgt_state = Variable("loop" + str(self.loop_counter) + "_" + str(step + 1))

            loop_seq_vars |= {src_state, tgt_state}

            for loop_seq_var in loop_seq_vars:
                symbol_table |= {(str(loop_seq_var) + "_" + str(step + 1)): TypedValuation(
                    (str(loop_seq_var) + "_" + str(step + 1)), "bool", false())}

            for k, v in symbol_table_from_program(self.program).items():
                symbol_table |= {(str(k) + "_" + str(step)): TypedValuation(v.name + "_" + str(step), v.type, v.value)}
                symbol_table |= {
                    (str(k) + "_" + str(step + 1)): TypedValuation(v.name + "_" + str(step + 1), v.type, v.value)}

            ts_renamed = set()
            for t in old_to_new_con_transitions[stutter_t]:
                t_renamed = Transition(t.src, t.condition,
                                       update_from_to(update_from_to(t.action, tgt_state, src_state), src_state,
                                                      false()),
                                       t.output, t.tgt)
                ts_renamed |= {t_renamed}
                new_env += [t_renamed]

                abstract_state_formula = conjunct(abstract_state_formula,
                                                  t.condition.replace(lambda var: Variable(var.name + "_" + str(step))))
                abstract_state_formula = conjunct(abstract_state_formula,
                                                  conjunct_formula_set([BiOp(a.left.replace(
                                                      lambda var: Variable(var.name + "_" + str(step + 1))),
                                                      "=", a.right.replace(
                                                          lambda var: Variable(var.name + "_" + str(step))))
                                                      for a in
                                                      self.program.complete_action_set(t.action)]))

                alternate_trans_exit = [tt for tt in old_to_new_con_transitions.keys()
                                        if t != tt and tt.src == t.src
                                        and smt_checker.check(
                        And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                      abstract_state_formula).to_smt(symbol_table)))]

                for tt in alternate_trans_exit:
                    old_to_new_con_transitions[tt] = {
                        Transition(ttt.src, ttt.condition,
                                   update_from_to(ttt.action, src_state, false()),
                                   ttt.output, ttt.tgt)
                        for ttt in old_to_new_con_transitions[tt]}

                    alternate_trans_stay = [tt for tt in old_to_new_con_transitions.keys()
                                            if t != tt and tt.src == t.src
                                            and not smt_checker.check(
                            And(*conjunct(neg(tt.condition.replace(lambda var: Variable(var.name + "_" + str(step)))),
                                          abstract_state_formula).to_smt(symbol_table)))]

                    for tt in alternate_trans_stay:
                        old_to_new_con_transitions[tt] |= {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(update_from_to(ttt.action, tgt_state, src_state), src_state,
                                                      false()),
                                       ttt.output, ttt.tgt)
                            for ttt in old_to_new_con_transitions[tt]}
            old_to_new_con_transitions[stutter_t] = ts_renamed
            step += 1
            env_turn = not env_turn

        for exit_trans0 in exit_transs:
            src_state = Variable("loop" + str(self.loop_counter) + "_" + str(step))

            if env_turn:
                # assert exit_trans == entry_trans
                # assert len(exit_transs) == 1

                tgt_state = Variable("loop" + str(self.loop_counter) + "_1")
                loop_seq_vars |= {src_state, tgt_state}

                exit_trans_renamed = set()
                for exit_trans in old_to_new_env_transitions[exit_trans0]:
                    t = Transition(exit_trans.src, exit_trans.condition,
                                   update_from_to(exit_trans.action, src_state, false()),
                                   exit_trans.output, exit_trans.tgt)
                    exit_trans_renamed |= {t}

                    alternate_trans = [tt for tt in old_to_new_env_transitions.keys() if
                                       exit_trans != tt and exit_trans.src == tt.src]

                    for tt in alternate_trans:
                        old_to_new_env_transitions[tt] = \
                            {Transition(ttt.src, ttt.condition,
                                        update_from_to(update_from_to(ttt.action, tgt_state,
                                                                      conjunct(neg(exit_predicate), src_state)),
                                                       src_state, false()),
                                        ttt.output, ttt.tgt) for ttt in old_to_new_env_transitions[tt]}
                old_to_new_env_transitions[exit_trans0] = exit_trans_renamed

            else:
                tgt_state = Variable("loop" + str(self.loop_counter) + "_0")
                loop_seq_vars |= {src_state, tgt_state}

                exit_trans_renamed = set()
                for exit_trans in old_to_new_con_transitions[exit_trans0]:
                    t = Transition(exit_trans.src, exit_trans.condition,
                                   update_from_to(exit_trans.action, src_state, false()),
                                   exit_trans.output, exit_trans.tgt)
                    exit_trans_renamed |= {t}

                    alternate_trans = [tt for tt in old_to_new_con_transitions.keys() if
                                       exit_trans != tt and exit_trans.src == tt.src]

                    for tt in alternate_trans:
                        old_to_new_con_transitions[tt] = {
                            Transition(ttt.src, ttt.condition,
                                       update_from_to(update_from_to(ttt.action, tgt_state,
                                                                     conjunct(neg(exit_predicate), src_state)),
                                                      src_state,
                                                      false()),
                                       ttt.output, ttt.tgt) for ttt in old_to_new_con_transitions[tt]}
                old_to_new_con_transitions[exit_trans0] = exit_trans_renamed

        if not env_turn:
            src_state = Variable("loop" + str(self.loop_counter) + "_0")
            tgt_state = Variable("loop" + str(self.loop_counter) + "_1")

            loop_seq_vars |= {src_state, tgt_state}

            ts = []
            for entry_trans1 in old_to_new_env_transitions[entry_trans]:
                t = Transition(entry_trans1.src, entry_trans1.condition,
                               update_from_to(update_from_to(entry_trans1.action, tgt_state, src_state), src_state,
                                              false()),
                               entry_trans1.output, entry_trans1.tgt)
                ts += [t]

                alternate_trans = [tt for tt in old_to_new_env_transitions.keys() if
                                   t != tt and t.src == tt.src]

                for tt in alternate_trans:
                    old_to_new_env_transitions[tt] = [
                        Transition(ttt.src, ttt.condition,
                                   update_from_to(ttt.action, src_state, false()),
                                   ttt.output, ttt.tgt) for ttt in old_to_new_env_transitions[tt]]

            old_to_new_env_transitions[entry_trans] = set(ts)

        if entry_trans in old_to_new_env_transitions.keys():
            entry_transs = list(old_to_new_env_transitions[entry_trans])[0]
            entry_trans_renamed = Transition(entry_transs.src, entry_transs.condition,
                                             update_from_to(entry_transs.action, entered_loop,
                                                            conjunct(entry_condition,
                                                                     neg(disjunct_formula_set(loop_seq_vars)))),
                                             entry_transs.output, entry_transs.tgt)

            old_to_new_env_transitions[entry_trans] = {entry_trans_renamed}
        else:
            entry_transs = list(old_to_new_con_transitions[entry_trans])[0]
            entry_trans_renamed = Transition(entry_transs.src, entry_transs.condition,
                                             update_from_to(entry_transs.action, entered_loop,
                                                            conjunct(entry_condition,
                                                                     neg(disjunct_formula_set(loop_seq_vars)))),
                                             entry_transs.output, entry_transs.tgt)

            old_to_new_con_transitions[entry_trans] = {entry_trans_renamed}

        new_program = Program(self.program.name, self.program.states,
                              self.program.initial_state,
                              self.program.valuation + [TypedValuation(v.name, "bool", false()) for v in loop_seq_vars],
                              [v for V in old_to_new_env_transitions.values() for v in V],
                              [v for V in old_to_new_con_transitions.values() for v in V],
                              self.program.env_events, self.program.con_events, self.program.out_events)
        self.program = new_program
        print(self.program.to_dot())
        self.loop_counter += 1

        return loop_seq_vars

    def simplified_transitions_abstraction(self):
        new_env_transitions = self.merge_transitions(self.env_partitions, self.abstraction.env_transitions,
                                                                            self.program.symbol_table,
                                                                            self.env_to_program_transitions)
        new_con_transitions = self.merge_transitions(self.con_partitions, self.abstraction.con_transitions,
                                                                            self.program.symbol_table,
                                                                            self.con_to_program_transitions)

        return Program("pred_abst_" + self.abstraction.name, self.abstraction.states, self.abstraction.initial_state, [],
                                   new_env_transitions, new_con_transitions, self.abstraction.env_events,
                                   self.abstraction.con_events, self.abstraction.out_events, False)

    def abstraction_to_ltl(self, symbol_table, simplified=True):
        predicates = self.state_predicates + self.transition_predicates

        # simplify
        if simplified:
            new_env_transitions = self.merge_transitions(self.env_partitions, self.abstraction.env_transitions,
                                                                                     self.program.symbol_table,
                                                                                     self.env_to_program_transitions)
            new_con_transitions = self.merge_transitions(self.con_partitions, self.abstraction.con_transitions,
                                                                                     self.program.symbol_table,
                                                                                     self.con_to_program_transitions)
        else:
            new_env_transitions = self.abstraction.env_transitions
            # env_to_program_transitions = self.env_to_program_transitions
            new_con_transitions = self.abstraction.con_transitions
            # con_to_program_transitions = self.con_to_program_transitions

        ltl_to_program_transitions = {}

        init_transitions = [t for t in new_env_transitions if t.src == self.abstraction.initial_state]
        init_cond_formula_sets = []
        # ltl_to_program_transitions["init"] = {}
        for t in init_transitions:
            cond = conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
                            conjunct_formula_set(
                                sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
                            )
            init_cond_formula_sets.append(cond)
            # safe_update_list_vals(ltl_to_program_transitions["init"], cond, env_to_program_transitions[t])

        init_cond_formula = disjunct_formula_set(init_cond_formula_sets)

        init_cond = init_cond_formula.to_nuxmv()

        states = [Variable(s.state) for s in self.abstraction.states if s != self.abstraction.initial_state] + \
                 [Variable(self.abstraction.initial_state)]
        states = set(states)

        at_least_and_at_most_one_state = UniOp("G",
                                               conjunct_formula_set(
                                                   [BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
                                                                                         states
                                                                                         if
                                                                                         r != q]))
                                                    for q in states if "loop" not in str(q)])).to_nuxmv()

        not_init_env_transitions = [t for t in new_env_transitions if
                                    t.src != self.abstraction.initial_state]

        not_init_con_transitions = [t for t in new_con_transitions if
                                    t.src != self.abstraction.initial_state]

        matching_pairs = {}

        # for every state that is not the initial state: s
        # for each controller transition from that state: t
        # get the set of all env transitions that can happen immediately after: ets
        # and match s with the pair of condition of t and ets
        #
        # at the end, every state s is associated with a list of conditions
        # and the associated env transitions that can happen after
        for s in self.abstraction.states:
            if s is not self.abstraction.initial_state:
                for t in not_init_con_transitions:
                    if t.src == s:
                        ets = []
                        for et in not_init_env_transitions:
                            if et.src == t.tgt:
                                ets.append(et)
                            else:
                                pass
                        if s in matching_pairs.keys():
                            matching_pairs[s] += [(t, ets)]
                        else:
                            matching_pairs[s] = [(t, ets)]
                    else:
                        pass

        remove_loop_stuff = lambda state: state  # re.split("loop", state)[0]
        con_env_transitions = []
        for c_s, cond_ets in matching_pairs.items():
            now_state_preds = [p for p in c_s.predicates if
                               p in (self.state_predicates + [neg(p) for p in self.state_predicates])]
            now = conjunct(Variable(c_s.state),
                           conjunct_formula_set(sorted(label_preds(now_state_preds, predicates),
                                                       key=lambda x: str(x))))
            next = []
            for (ct, ets) in cond_ets:
                cond = ct.condition
                now_next = []
                for et in ets:
                    bookeeping_tran_preds = label_preds(tran_and_state_preds_after_con_env_step(et),
                                                        predicates)

                    next_here = conjunct(conjunct_formula_set([Variable(et.tgt.state), et.condition] + et.output),
                                         conjunct_formula_set(sorted(bookeeping_tran_preds, key=lambda x: str(x)))
                                         )
                    # try:
                    #     next_here_cnf = func_timeout(3, cnf, [next_here_cnf, symbol_table])
                    #     if len(str(next_here_cnf)) < len(str(next_here)):
                    #         next_here = next_here_cnf
                    # except:
                    #     pass

                    now_next += [(next_here)]

                    # try:
                    #     if now not in ltl_to_program_transitions.keys():
                    #         ltl_to_program_transitions[now] = {}
                    #      safe_update_list_vals(ltl_to_program_transitions[now], (cond, next_here),
                    #                  [(con_to_program_transitions[ct],
                    #                    env_to_program_transitions[et])])
                    # except Exception as e:
                    #     print(str(e))
                    #     raise e
                # If cond (which is the about the current state) is just True (i.e., it s negation is unsat)
                # then just ignore it
                if isinstance(cond, Value) and cond.is_true():
                    next += [X(disjunct_formula_set(sorted(set(now_next), key=lambda x: str(x))))]
                else:
                    next_disjuncts = disjunct_formula_set(sorted(set(now_next), key=lambda x: str(x)))
                    try:
                        next_disjuncts_cnf = func_timeout(3, cnf, [next_disjuncts, symbol_table])
                        if len(str(next_disjuncts_cnf)) < len(str(next_disjuncts)):
                            next_disjuncts = next_disjuncts_cnf
                    except:
                        pass

                    next += [conjunct(cond, X(next_disjuncts))]

            next = sorted(set(next), key=lambda x: str(x))

            con_env_transitions += [G(implies(now, disjunct_formula_set(next))).to_nuxmv()]

        # TODO this set is only needed when we have transition predicates
        transition_cond = sorted(set(con_env_transitions), key=lambda x: str(x))

        return [init_cond, at_least_and_at_most_one_state] + transition_cond#, ltl_to_program_transitions

    def merge_transitions(self, partitions, transitions: [Transition], symbol_table, to_program_transitions):
        new_transitions = []
        # new_to_program_transitions = {}

        # partition the transitions into classes where in each class each transition has the same outputs and source and end state
        # partitions = dict()
        for key in partitions.keys():
            trans_here = partitions[key]
            conditions = disjunct_formula_set(sorted([t.condition for t in trans_here], key=lambda x: str(x)))
            conditions_simplified = simplify_formula_without_math(conditions, symbol_table)
            # conditions_smt = conditions.to_smt(symbol_table)
            # # If negation is unsat
            # if not smt_checker.check(Not(And(*conditions_smt))):
            #     conditions_simplified_fnode = TRUE()
            # else:
            #     conditions_simplified_fnode = conditions_smt[0].simplify()
            ## simplify when doing disjunct, after lex ordering
            ## also, may consider when enumerating possible event sets starting with missing some evetns and seeing how many transitions they match, if only then can stop adding to it
            try:
                new_tran = Transition(trans_here[0].src, conditions_simplified, [],
                                      # string_to_prop(str(conditions_simplified_fnode)), [],
                                      trans_here[0].output,
                                      trans_here[0].tgt)
                new_transitions.append(new_tran)

            except Exception as e:
                raise e
        return new_transitions

def meaning_within_incremental(f: Formula, previous_preds: [[Formula]], new_preds: [Formula], symbol_table):
    Ps = previous_preds

    for new_pred in new_preds:
        Pss = set()
        for ps in Ps:
            if smt_checker.check(And(*conjunct_formula_set(ps | {f, new_pred}).to_smt(symbol_table))):
                Pss.add(frozenset(ps | {new_pred}))

                if smt_checker.check(And(*conjunct_formula_set(ps | {f, neg(new_pred)}).to_smt(symbol_table))):
                    Pss.add(frozenset(ps | {neg(new_pred)}))
            else:
                Pss.add(frozenset(ps | {neg(new_pred)}))
        Ps = Pss

    return Ps


def meaning_within_incremental_one_step(f: Formula, previous_preds: [[Formula]], new_pred: Formula, symbol_table):
    Ps = set()

    for ps in previous_preds:
        if smt_checker.check(And(*conjunct_formula_set(ps | {f, new_pred}).to_smt(symbol_table))):
            Ps.add(ps | {new_pred})
            if smt_checker.check(And(*conjunct_formula_set(ps | {f, neg(new_pred)}).to_smt(symbol_table))):
                Ps.add(ps | {neg(new_pred)})
        else:
            Ps.add(ps | {neg(new_pred)})

    return Ps


def powerset_complete(S: set):
    positive_subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))
    complete_subsets = list()
    for ps in positive_subsets:
        real_ps = set(ps)
        negative = {neg(s) for s in S if (s) not in real_ps}
        complete = set(real_ps).union(negative)
        complete_subsets.append(frozenset(complete))

    return complete_subsets


def powerset(S: set):
    subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))

    return sorted(list(map(set, subsets)), key=lambda x: len(x))




def tran_and_state_preds_after_con_env_step(env_trans: Transition):
    if True:
        src_tran_preds = [p for p in env_trans.src.predicates
                          if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]
        tgt_tran_preds = [p for p in env_trans.tgt.predicates
                          if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]

        pos = {p for p in (src_tran_preds + tgt_tran_preds) if not isinstance(p, UniOp)}
        all_neg = {p for p in (src_tran_preds + tgt_tran_preds) if isinstance(p, UniOp)}
        neg = {p for p in all_neg if p.right not in pos}

        state_preds = [p for p in env_trans.tgt.predicates
                      if [] == [v for v in p.variablesin() if v.name.endswith("_prev")]]

        return list(pos | neg) + state_preds
