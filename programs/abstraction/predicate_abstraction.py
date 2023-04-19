import time
from itertools import chain, combinations
from multiprocessing import Process, Queue

from func_timeout import func_timeout
from pysmt.shortcuts import And, Not, TRUE
from joblib import Parallel, delayed

from Config import env, con
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import label_preds, add_prev_suffix, stutter_transitions, \
    stutter_transition, symbol_table_from_program, safe_update_set_vals, safe_update_list_vals, transition_formula, \
    reduce_up_to_iff, label_pred, stringify_pred, stringify_formula
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    implies, G, X, true, false, disjunct, simplify_formula_without_math, cnf, iff, is_tautology, sat, \
    keep_only_vars, dnf, partially_evaluate, is_dnf, abstract_out_conjunctions_of_atoms, depth_of_formula, \
    abstract_out_disjunctions_of_atoms, atomic_predicates, F, type_constraints, U, W
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()

queue = Queue()
timeout = -1

def run_with_timeout(f, arg, timeout):
    if timeout == -1:
        return f(arg)
    else:
        p1 = Process(target=dnfguard, name=f.__name__, args=arg)
        p1.start()
        p1.join(timeout=10)
        if p1.exitcode is None:
            p1.terminate()
            return None
        else:
            return queue.get()

def dnfguard(d_and_guard):
    dnfed = dnf(d_and_guard, simplify=False)
    print(str(dnfed))
    queue.put(dnfed)


class PredicateAbstraction:
    def __init__(self, program: Program):
        self.transition_state_tags = {}
        self.transition_unaffected_tags = {}
        self.transition_constant_tags = {}
        self.transition_tran_tags = {}
        self.con_tags = {}
        self.pred_transition_invars = {}
        self.formula_to_trans = {}
        self.formula_to_formula_without_identity_actions = {}
        self.abstract_effect_invars = {}
        self.abstract_effect_constant = {}
        self.abstract_effect = {}

        self.init_program_trans = None
        self.abstract_guard_con = None
        self.abstract_guard_con_disjuncts = None
        self.abstract_guard_env = None
        self.abstract_guard_env_disjuncts = None
        self.state_predicates = []
        self.transition_predicates = []
        self.loops = []

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

    def abstract_program_transition_env(self, env_trans : Transition):
        if env_trans.tgt == "won":
            print()
        disjuncts, formula = self.abstract_guard(env_trans.condition, self.program.env_events)
        return env_trans, disjuncts, formula

    def abstract_program_transition_con(self, con_trans: Transition):
            disjuncts, formula = self.abstract_guard(con_trans.condition, self.program.con_events)
            return con_trans, disjuncts, formula

    def abstract_program_transitions(self):
        orig_env_transitions, orig_con_transitions = self.program.complete_transitions()

        self.abstract_guard_env = {}
        self.abstract_guard_con = {}
        self.abstract_guard_env_disjuncts = {}
        self.abstract_guard_con_disjuncts = {}

        self.init_program_trans = []

        results_env = Parallel(n_jobs=10)(delayed(self.abstract_program_transition_env)(t) for t in orig_env_transitions)
        init_conf = MathExpr(conjunct_typed_valuation_set(self.program.valuation))
        self.init_program_trans = [t.add_condition(init_conf) for t in orig_env_transitions if t.src == self.program.initial_state]
        results_init = Parallel(n_jobs=10)(delayed(self.abstract_program_transition_env)(t) for t in self.init_program_trans)
        results_con = Parallel(n_jobs=10)(delayed(self.abstract_program_transition_con)(t) for t in orig_con_transitions)

        for t, disjuncts, formula in results_env + results_init:
            self.abstract_guard_env[t] = formula
            self.abstract_guard_env_disjuncts[t] = disjuncts
            self.abstract_effect[t] = {E: [[]] for _, E in disjuncts}

        for t, disjuncts, formula in results_con:
            self.abstract_guard_con[t] = formula
            self.abstract_guard_con_disjuncts[t] = disjuncts
            self.abstract_effect[t] = {E: [[]] for _, E in disjuncts}

        self.all_program_trans = orig_env_transitions + orig_con_transitions + self.init_program_trans

    def abstract_guard_explicitly(self, guard, events):
        vars_in_cond = guard.variablesin()
        events_in_cond = [e for e in vars_in_cond if e in events]
        powerset = powerset_complete(events_in_cond)

        int_disjuncts_only_events = [E for E in powerset if
                                     smt_checker.check(
                                         And(*conjunct_formula_set(E | {guard}).to_smt(self.program.symbol_table)))]

        satisfying_behaviour = int_disjuncts_only_events
        dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
        disjuncts = []
        for E in satisfying_behaviour:
            if not E:
                logger.info("empty E " + str(guard))
            guard_E = guard.replace(lambda x: true() if x in E else false() if neg(x) in E else x)
            guard_E_simplified = simplify_formula_with_math(guard_E, self.program.symbol_table)
            disjuncts.append((guard_E_simplified, E))
        return disjuncts, dnfed

    def abstract_guard(self, guard: Formula, events, use_set_method=True):
        if use_set_method:
            return self.abstract_guard_explicitly(guard, events)

        guard_without_math = guard.replace_math_exprs(0)
        # when there is a disjunction, instead of resolving vars to false, resolve them to a var 'program_choice'
        # then, if there is a disjunct with just program_choice in it, it denotes the transition may be activated
        # regardless of what the env does with env vars
        guard_with_only_events0 = keep_only_vars(guard_without_math[0], events, make_program_choices_explicit=True).simplify()
        guard_with_only_events = simplify_formula_without_math(guard_with_only_events0)
        abstract_out_disjunctions = abstract_out_disjunctions_of_atoms(guard_with_only_events)
        new_abstract_out_disjunctions = {}
        for var, disjunct in abstract_out_disjunctions[1].items():
            if isinstance(disjunct, BiOp) and disjunct.op[0] == "|":
                disjuncts = set(disjunct.sub_formulas_up_to_associativity())
                if Variable("program_choice") in disjuncts:
                    disjuncts.remove(Variable("program_choice"))
                    disjuncts.add(conjunct_formula_set([neg(d) for d in disjuncts]))
                new_abstract_out_disjunctions[var] = disjunct_formula_set(disjuncts)
            else:
                if not disjunct == Variable("program_choice"):
                    new_abstract_out_disjunctions[var] = disjunct

        guard_with_only_events = abstract_out_disjunctions[0].replace(lambda x: x if str(x) not in new_abstract_out_disjunctions.keys()
                                                                            else new_abstract_out_disjunctions[str(x)])
        guard_with_only_events = guard_with_only_events.replace(BiOp(Variable("program_choice"), ":=", Value("TRUE")))
        # TODO need to timeout and give up on this dnfing sometimes too
        # dnf_guard_with_only_events = dnf(guard_with_only_events, simplify=False)
        val = dnf(guard_with_only_events)

        if val is None:
            print("Giving up on dnfing, and using explicit method.")
            use_set_method = True
            vars_in_cond = guard.variablesin()
            events_in_cond = [e for e in vars_in_cond if e in events]
            powerset = powerset_complete(events_in_cond)

            int_disjuncts_only_events = [E for E in powerset if
                                         smt_checker.check(And(*conjunct_formula_set(E | {guard}).to_smt(self.program.symbol_table)))]

        else:
            dnf_guard_with_only_events = val

            if Variable("program_choice") in dnf_guard_with_only_events.variablesin():
                print()
            int_disjuncts_only_events = set()
            if isinstance(dnf_guard_with_only_events, BiOp) and dnf_guard_with_only_events.op[0] == "|":
                for d in dnf_guard_with_only_events.sub_formulas_up_to_associativity():
                    if isinstance(d, BiOp) and d.op[0] == "&":
                        atoms = d.sub_formulas_up_to_associativity()
                        contradictions = [a for a in d.variablesin() if a in atoms and neg(a) in atoms]
                        basic_atoms = [a for a in atoms if isinstance(a, Variable) and a not in contradictions
                                       or isinstance(a, UniOp) and a.right not in contradictions]
                        new_conjuncts = [basic_atoms]
                        while len(contradictions) > 0:
                            next_conjuncts = []
                            for at in new_conjuncts:
                                next_conjuncts.append(at + [contradictions[0]])
                                next_conjuncts.append(at + [neg(contradictions[0])])
                            contradictions.pop(0)
                            new_conjuncts = next_conjuncts
                        unique_new_conjuncts = frozenset({frozenset(dd) for dd in new_conjuncts})
                        for dd in unique_new_conjuncts:
                            int_disjuncts_only_events.add(dd)
                    else:
                        int_disjuncts_only_events.add(frozenset({d}))
            else:
                if isinstance(dnf_guard_with_only_events, BiOp) and dnf_guard_with_only_events.op[0] == "&":
                        atoms = dnf_guard_with_only_events.sub_formulas_up_to_associativity()
                        contradictions = [a for a in dnf_guard_with_only_events.variablesin() if a in atoms and neg(a) in atoms]
                        basic_atoms = [a for a in atoms if isinstance(a, Variable) and a not in contradictions
                                       or isinstance(a, UniOp) and a.right not in contradictions]
                        new_conjuncts = [basic_atoms]
                        while len(contradictions) > 0:
                            next_conjuncts = set(new_conjuncts)
                            for at in new_conjuncts:
                                next_conjuncts.add(at + [contradictions[0]])
                                next_conjuncts.add(at + [neg(contradictions[0])])
                            contradictions.pop(0)
                            new_conjuncts = next_conjuncts
                        unique_new_conjuncts = frozenset({frozenset(dd) for dd in new_conjuncts})
                        for dd in unique_new_conjuncts:
                            int_disjuncts_only_events.add(dd)
                else:
                    int_disjuncts_only_events.add(frozenset({dnf_guard_with_only_events}))

            if len(int_disjuncts_only_events) > 1 and frozenset({Value("TRUE")}) in int_disjuncts_only_events:
                int_disjuncts_only_events.remove(frozenset({Value("TRUE")}))
            event_guard = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
            if not is_tautology(implies(guard, event_guard), self.program.symbol_table):
                disjuncts_to_add = set()
                for d in int_disjuncts_only_events:
                    for dd in d:
                        disjuncts_to_add |= {frozenset({neg(dd).simplify()})}
                for d in disjuncts_to_add:
                    int_disjuncts_only_events.add(d)

            put_math_back = lambda f,d: f.replace(lambda v : d[str(v)] if str(v) in d.keys() else v)

            int_disjuncts = set()
            for d in int_disjuncts_only_events:
                new_guard = partially_evaluate(guard, [v for v in d if isinstance(v, Variable)],
                                               [v.right for v in d if isinstance(v, UniOp) and v.op[0] == "!"] +
                                               [e for e in events if e not in d and neg(e) not in d],
                                            self.program.symbol_table)
                if isinstance(new_guard, Value) and new_guard.is_false():
                    continue
                d_and_guard_without_atomic_conjunctions, conj_dict = abstract_out_conjunctions_of_atoms(new_guard, {})
                d_and_guard_without_math = d_and_guard_without_atomic_conjunctions.replace_math_exprs(0)
                d_and_guard = d_and_guard_without_math[0]
                # dnf is exponential, so if more than 8 variables we give up and just compute all possible combinations of events
                # TODO consider also a timeout, and/or anlayse if d_and_guard is already in dnf form
                # TODO this will mostly happen for the implicit stutter transitions,
                #  so if we leave them for last, we can collect all the info from the smaller transitions
                if is_dnf(d_and_guard):
                    dnf_d_and_guard = d_and_guard
                else:
                    if len(d_and_guard.variablesin()) > 8 and depth_of_formula(d_and_guard) > 3:
                        print("Giving up on dnfing, and using explicit method.")
                        use_set_method = True
                        break
                    val = dnf(d_and_guard)

                    if val is None:
                        print("Giving up on dnfing, and using explicit method.")
                        use_set_method = True
                        break
                    else:
                        dnf_d_and_guard = val

                new_d = d
                if isinstance(dnf_d_and_guard, BiOp) and dnf_d_and_guard.op[0] == "|":
                    collect_disjuncts = set()
                    for dd in dnf_d_and_guard.sub_formulas_up_to_associativity():
                        dd_with_math = put_math_back(dd, conj_dict | d_and_guard_without_math[1])
                        if sat(conjunct(guard, dd_with_math), self.program.symbol_table):
                            collect_disjuncts.add(dd_with_math)
                    if len(collect_disjuncts) > 0:
                        int_disjuncts.add((disjunct_formula_set(collect_disjuncts), new_d))
                else:
                    d_with_math = put_math_back(dnf_d_and_guard, conj_dict | d_and_guard_without_math[1])
                    if sat(conjunct(guard, d_with_math), self.program.symbol_table):
                        int_disjuncts.add((d_with_math, new_d))

        if not use_set_method:
            dnfed = disjunct_formula_set([conjunct_formula_set(d) for _, d in int_disjuncts])
            print(str(guard) + " -> " + str(dnfed))
            return int_disjuncts, dnfed
        else:
            satisfying_behaviour = int_disjuncts_only_events
            dnfed = disjunct_formula_set([conjunct_formula_set(d) for d in int_disjuncts_only_events])
            print(str(guard) + " -> " + str(dnfed))

            return [(conjunct(guard, conjunct_formula_set(E)), E) for E in satisfying_behaviour], dnfed

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

    def prune_predicate_sets(self):
        new_abstract_effect = {}
        for t in self.abstract_guard_env.keys():
            if t in self.init_program_trans:
                new_abstract_effect[t] = self.abstract_effect[t]
            else:
                new_abstract_effect[t] = {}
                t_f = transition_formula(t)
                prev_trans = [tt for tt in self.abstract_guard_con.keys() if tt.tgt == t.src]

                prev_pred_states = set()
                for tt in prev_trans:
                    tt_f = transition_formula(tt)
                    tt_prev_pred_state = set()
                    for _, effects in self.abstract_effect[tt].items():
                        effects_tt_prev_pred_states = [Ps for Ps in effects.keys()]
                        if len(self.abstract_effect_constant[tt_f]) > 0:
                            effects_tt_prev_pred_states = [Ps | {c for c in self.abstract_effect_constant[tt_f]} for Ps in effects_tt_prev_pred_states]
                        if len(self.abstract_effect_invars[tt_f]) > 0:
                            invar_powersets = powerset_complete(self.abstract_effect_invars[tt_f])
                            effects_tt_prev_pred_states = [Ps | P for P in invar_powersets for Ps in effects_tt_prev_pred_states]
                        tt_prev_pred_state |= set(effects_tt_prev_pred_states)
                    prev_pred_states |= tt_prev_pred_state

                current_pred_states = [Ps for _, effects in self.abstract_effect[t].items() for Pss in effects.values() for Ps in Pss]
                if len(self.abstract_effect_constant[t_f]) > 0:
                    invar_powersets = powerset_complete(self.abstract_effect_constant[t_f])
                    current_pred_states = [Ps + list(P) for P in invar_powersets for Ps in current_pred_states]
                if len(self.abstract_effect_invars[t_f]) > 0:
                    invar_powersets = powerset_complete(self.abstract_effect_invars[t_f])
                    current_pred_states = [Ps + list(P) for P in invar_powersets for Ps in current_pred_states]

                pruned_current_pred_states = [Ps for Ps in current_pred_states if set(Ps) in prev_pred_states]
                pruned_current_pred_states = [[p for p in Ps
                                               if p not in self.abstract_effect_constant[t_f] and
                                               p not in self.abstract_effect_invars[t_f] and
                                               negate(p) not in self.abstract_effect_constant[t_f] and
                                               negate(p) not in self.abstract_effect_invars[t_f]]
                                              for Ps in pruned_current_pred_states]

                for E, effects in self.abstract_effect[t].items():
                    new_abstract_effect[t][E] = {}
                    for nextPs in effects.keys():
                        newPss = [Ps for Ps in effects[nextPs] if Ps in pruned_current_pred_states]
                        if len(newPss) > 0:
                            new_abstract_effect[t][E][nextPs] = newPss
                    if len(new_abstract_effect[t][E]) == 0:
                        del new_abstract_effect[t][E]

        for t in self.abstract_guard_con.keys():
            new_abstract_effect[t] = {}
            t_f = transition_formula(t)
            prev_trans = [tt for tt in self.abstract_guard_env.keys() if tt.tgt == t.src]

            prev_pred_states = set()
            for tt in prev_trans:
                tt_f = transition_formula(tt)
                tt_prev_pred_state = set()
                for _, effects in self.abstract_effect[tt].items():
                    effects_tt_prev_pred_states = [Ps for Ps in effects.keys()]
                    if len(self.abstract_effect_constant[tt_f]) > 0:
                        effects_tt_prev_pred_states = [Ps | {c for c in self.abstract_effect_constant[tt_f]} for Ps
                                                       in effects_tt_prev_pred_states]
                    if len(self.abstract_effect_invars[tt_f]) > 0:
                        invar_powersets = powerset_complete(self.abstract_effect_invars[tt_f])
                        effects_tt_prev_pred_states = [Ps | P for P in invar_powersets for Ps in
                                                       effects_tt_prev_pred_states]
                    tt_prev_pred_state |= set(effects_tt_prev_pred_states)
                prev_pred_states |= tt_prev_pred_state

            current_pred_states = [Ps for _, effects in self.abstract_effect[t].items() for Pss in effects.values()
                                   for Ps in Pss]
            if len(self.abstract_effect_constant[t_f]) > 0:
                invar_powersets = powerset_complete(self.abstract_effect_constant[t_f])
                current_pred_states = [Ps + list(P) for P in invar_powersets for Ps in current_pred_states]
            if len(self.abstract_effect_invars[t_f]) > 0:
                invar_powersets = powerset_complete(self.abstract_effect_invars[t_f])
                current_pred_states = [Ps + list(P) for P in invar_powersets for Ps in current_pred_states]

            pruned_current_pred_states = [Ps for Ps in current_pred_states if set(Ps) in prev_pred_states]
            pruned_current_pred_states = [[p for p in Ps
                                           if p not in self.abstract_effect_constant[t_f] and
                                           p not in self.abstract_effect_invars[t_f] and
                                           negate(p) not in self.abstract_effect_constant[t_f] and
                                           negate(p) not in self.abstract_effect_invars[t_f]]
                                          for Ps in
                                          pruned_current_pred_states]

            for E, effects in self.abstract_effect[t].items():
                new_abstract_effect[t][E] = {}
                for nextPs in effects.keys():
                    newPss = [Ps for Ps in effects[nextPs] if Ps in pruned_current_pred_states]
                    if len(newPss) > 0:
                        new_abstract_effect[t][E][nextPs] = newPss
                if len(new_abstract_effect[t][E]) == 0:
                    del new_abstract_effect[t][E]

        self.abstract_effect = new_abstract_effect

    def loop_abstraction(self,
                         entry_condition,
                         loop_body,
                         exit_predicate_state : Formula,
                         ranking_function: MathExpr,
                         invars: Formula,
                         disagreed_on_program_state : dict,
                         program_taken_transition : Transition):
        #ASSUMPTION: the loop body has been pre-processes to keep only actions that affect the ranking function
        # as in synthesis.liveness_step
        #
        # if there are only decreases of the ranking function in the loop body, then just GF rf_dec -> GF rf_inc is enough
        # if there are also increases, then need to specialise to the actions that affect the rf in the loop body

        new_env_variables = []
        new_con_variables = []
        new_state_predicates = []
        new_transition_predicates = []
        new_guarantees = []
        new_assumptions = []

        # first check who wanted to remain in the loop
        # last_mm_state = [st for st in disagreed_on_program_state.keys() if st.startswith("st_") and "seen" not in st and disagreed_on_program_state[st] == "TRUE"][0]
        env_wanted_to_remain_in_loop = program_taken_transition[0] != loop_body[0][0] #any(True for _, dict in loop_body if dict[last_mm_state] == "TRUE")

        # # check if the actual predicate state of the program appears already in the loop body (counterexample_loop)
        # actual_program_true_preds = [p for p in disagreed_on_program_state.keys() if
        #                              str(p).startswith("pred_") and disagreed_on_program_state[p] == "TRUE"]
        # actual_program_false_preds = [neg(p) for p in disagreed_on_program_state.keys() if
        #                               str(p).startswith("pred_") and disagreed_on_program_state[p] == "FALSE"]
        # actual_program_predicate_state = conjunct_formula_set(
        #     actual_program_true_preds + actual_program_false_preds, sort=True)
        #
        # for _, dict in loop_body:
        #     true_preds = [p for p in dict.keys() if
        #                   str(p).startswith("pred_") and dict[p] == "TRUE"]
        #     false_preds = [neg(p) for p in dict.keys() if
        #                    str(p).startswith("pred_") and dict[p] == "FALSE"]
        #     predicate_state = conjunct_formula_set(true_preds + false_preds, sort=True)
        #     if predicate_state == actual_program_predicate_state:
        #         env_wanted_to_remain_in_loop = False
        #         break

        rf_dec = BiOp(add_prev_suffix(ranking_function), ">", ranking_function)
        rf_inc = BiOp(add_prev_suffix(ranking_function), "<", ranking_function)
        rf_stutter = BiOp(ranking_function, "=", add_prev_suffix(ranking_function))

        #entry_condition can be of three types:
        # (1) true
        # (2) a conjunction of known state predicates
        # (3) a valuation,
        #TODO in the latter two cases we will want to try and expand the entry_condition
        # for now, we add predicates in the entry_condition that are not already present as new state predicates
        entry_predicates = atomic_predicates(entry_condition)
        entry_predicates = [p for p in entry_predicates if not(isinstance(p, Value) and (p.is_true() or p.is_false()))]
        # TODO check if can be expressed with current predicates, with meaning_within
        # entry_predicates = reduce_up_to_iff(entry_predicates, self.state_predicates, self.program.symbol_table)

        # now computing the transition predicates
        # check whether given the loop invariants, and the type constrains of the variables,
        # an action is associated with an increase or decrease or it could be either

        only_dec = False
        action_sequence = []
        for t, _ in loop_body:
            actions = []
            for act in t.action:
                if act.left != act.right:
                    action_formula = BiOp(act.left, "=", add_prev_suffix(act.right))
                    type_constraint = type_constraints(action_formula, self.program.symbol_table)

                    if sat(conjunct_formula_set([rf_dec, type_constraint, action_formula, invars, add_prev_suffix(invars)]), self.program.symbol_table):
                        if not sat(conjunct_formula_set([rf_inc, type_constraint, action_formula, invars, add_prev_suffix(invars)]), self.program.symbol_table):
                            only_dec = True

                    actions.append(action_formula)
            if len(actions) > 0:
                action_sequence.append(conjunct_formula_set(actions, sort=True))
        if only_dec and env_wanted_to_remain_in_loop:
            new_assumptions += [implies(G(F(conjunct(stringify_pred(rf_dec), invars))), G(F(disjunct(stringify_pred(rf_inc), neg(invars)))))]
            new_transition_predicates += [rf_dec, rf_inc]
        else:
            new_state_predicates += list(entry_predicates) + list(set(action_sequence))
            new_transition_predicates += action_sequence + [rf_stutter]
            action_sequence = [stringify_pred(p) for p in action_sequence]

            in_loop = Variable("inloop_" + str(len(self.loops)))
            loop_index = len(self.loops)

            new_env_variables += [in_loop]
            # building abstract loop constraints
            safety = []
            # initially not in loop
            safety.append(neg(in_loop))

            # entry into abstract loop
            if str(entry_condition).lower() == "true":
                entering_loop = conjunct(neg(in_loop), X(action_sequence[0]))
            else:
                entering_loop = conjunct(neg(in_loop), entry_condition)
                not_entering_loop = conjunct(neg(in_loop), neg(entry_condition))

                safety.append(G(implies(not_entering_loop, X(neg(in_loop)))))

            if len(action_sequence) > 1:
                steps = []
                for i in range(len(action_sequence[1:])):
                    steps.append(Variable("step_" + str(loop_index) + "_" + str(i + 1)))

                new_env_variables += steps

                safety.append(conjunct_formula_set(neg(s) for s in steps))
                # being in one step implies not being in the other steps
                safety.append(conjunct_formula_set(
                    [G(implies(s, neg(disjunct_formula_set([not_s for not_s in steps if not_s != s]))))
                              for s in steps]))
                safety.append(G(implies(entering_loop, X(conjunct(in_loop, steps[0])))))

                looping_steps = steps + [steps[0]]
                # stepping through loop
                for i in range(1, len(looping_steps)):
                    now = conjunct(looping_steps[i-1], X(action_sequence[i-1]))
                    safety.append(G(implies(now, X(conjunct(in_loop, looping_steps[i])))))

                    # stutter
                    now_stutter = conjunct(looping_steps[i-1], X(stringify_pred(rf_stutter)))
                    safety.append(G(implies(now_stutter, X(conjunct(in_loop, looping_steps[i-1])))))

                    # other action
                    now_other_change = conjunct(looping_steps[i-1], X(conjunct(neg(action_sequence[i-1]), neg(stringify_pred(rf_stutter)))))
                    safety.append(G(implies(now_other_change, X(neg(in_loop)))))

                if not env_wanted_to_remain_in_loop:
                    # TODO allow_exit needs to allow the environment to choose a certain predicate state (the exit condition)
                    controller_choice = Variable("allow_exit_" + str(len(self.loops)))
                    new_con_variables.append(controller_choice)

                    # at last step, controller can choose to disallow the environment from exiting the loop
                    controller_disallows_exit = conjunct(conjunct(in_loop, steps[-1]), neg(controller_choice))

                    safety.append(G(implies(controller_disallows_exit, X(in_loop))))

                    # to reduce size of game, only allowing controller to set choice variable when at the last step
                    new_guarantees.append(G(implies(neg(steps[-1]), neg(controller_disallows_exit))))

                    new_guarantees.append(G((implies(steps[-1], F(conjunct(env, disjunct(neg(in_loop), controller_choice)))))))
                    new_guarantees.append(G((implies(steps[-1], F(conjunct(con, disjunct(neg(in_loop), controller_choice)))))))
                    # new_guarantees.append(implies(G(F(in_loop)), G(F(neg(in_loop)))))
                else:
                    new_assumptions += [implies(G(F(in_loop)), G(F(neg(in_loop))))]
            else:
                safety.append(G(implies(entering_loop, X(in_loop))))

                now = conjunct(in_loop, X(action_sequence[0]))
                safety.append(G(implies(now, X(in_loop))))

                # stutter
                now_stutter = conjunct(in_loop, X(stringify_pred(rf_stutter)))
                safety.append(G(implies(now_stutter, X(in_loop))))

                # other action
                now_other_change = conjunct(in_loop, X(W(stringify_pred(rf_stutter), conjunct(neg(action_sequence[0]), neg(stringify_pred(rf_stutter))))))
                safety.append(G(implies(now_other_change, X(neg(in_loop)))))

                if not env_wanted_to_remain_in_loop:
                    controller_choice = Variable("allow_exit_" + str(len(self.loops)))
                    new_con_variables.append(controller_choice)

                    # at last step, controller can choose to disallow the environment from exiting the loop
                    controller_disallows_exit = conjunct(in_loop, neg(controller_choice))

                    exit_condition = stringify_formula(exit_predicate_state)
                    safety.append(G(implies(controller_disallows_exit, X(conjunct(in_loop, neg(exit_condition))))))
                    new_state_predicates += [p for p in atomic_predicates(exit_predicate_state)]

                    # to reduce size of game, only allowing controller to set choice variable when at the last step
                    # new_guarantees.append(G(implies(neg(in_loop), X(neg(controller_choice)))))

                    new_guarantees.append(G((implies(in_loop, disjunct(G(con), F(conjunct(env, controller_choice)))))))
                    new_guarantees.append(G((implies(in_loop, disjunct(G(env), F(conjunct(con, controller_choice)))))))
                else:
                    new_assumptions += [implies(G(F(in_loop)), G(F(neg(in_loop))))]

            new_assumptions += safety

            self.loops.append((entry_condition, loop_body, ranking_function))

        return new_env_variables, new_con_variables, new_transition_predicates, new_state_predicates, new_assumptions, new_guarantees

    def initialise(self, debug=True):
        print("Initialising predicate abstraction.")

        self.abstract_program_transitions()

        # Formula -> (P -> [P])
        for t in self.all_program_trans:
            disjuncts = self.abstract_guard_env_disjuncts[t] if t in self.abstract_guard_env_disjuncts.keys() else self.abstract_guard_con_disjuncts[t]

            formula = transition_formula(t)
            self.formula_to_trans[formula] = t
            self.transition_state_tags[formula] = {frozenset({d}): [[]] for d in disjuncts}
            self.transition_tran_tags[formula] = {frozenset({d}): [[]] for d in disjuncts}
            self.transition_unaffected_tags[formula] = set()
            self.transition_constant_tags[formula] = set()
            self.pred_transition_invars[formula] = set()
            self.abstract_effect_invars[formula] = []
            self.abstract_effect_constant[formula] = []
            self.abstract_effect[t] = {E:{frozenset(): [[]]} for _, E in disjuncts}

        # construct transition ltl
        init_transitions = [conjunct_formula_set([self.abstract_guard_env[t], Variable(t.tgt)] + t.output)
                                for t in self.init_program_trans]

        init_transition_ltl = disjunct_formula_set([conjunct(phi, X(phi)) for phi in init_transitions])

        transition_ltl = []
        for env_trans in self.abstract_guard_env.keys():
            if env_trans in self.init_program_trans: continue
            now = conjunct_formula_set([env, Variable(env_trans.src), self.abstract_guard_env[env_trans]])
            next = X(conjunct_formula_set([Variable(env_trans.tgt)] + env_trans.output))
            transition_ltl += [conjunct(now, next)]

        for con_trans in self.abstract_guard_con.keys():
            now = conjunct_formula_set([con, Variable(con_trans.src), self.abstract_guard_con[con_trans]])

            next = X(conjunct_formula_set([Variable(con_trans.tgt)] + [(neg(o)) for o in self.program.out_events]))
            transition_ltl += [conjunct(now, next)]

        ltl = conjunct(init_transition_ltl, X(G(disjunct_formula_set(transition_ltl))))

        print(ltl)
        return init_transition_ltl, X(G(disjunct_formula_set(transition_ltl)))

    def add_predicates(self, new_state_predicates: [Formula], new_transition_predicates: [Formula], pred_name_dict : dict, simplified: bool):
        if len(new_state_predicates) + len(new_transition_predicates) == 0:
            return

        # TODO maybe Nir's idea is better
        # T : 2^{P \cup Q} -> 2^2^{P \cup Q}

        print("Adding predicates to predicate abstraction:")
        print("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")
        print("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")


        print("Tagging abstract transitions with predicates..")
        start = time.time()
        for p in new_state_predicates + new_transition_predicates:
            for t in self.all_program_trans:
                self.compute_abstract_effect_with_p(t, t in self.abstract_guard_env.keys(), p)

        end = time.time()
        print(end - start)

        # start = time.time()
        # self.prune_predicate_sets()
        # end = time.time()
        # print(end - start)

        self.state_predicates += new_state_predicates
        self.transition_predicates += new_transition_predicates

        rename_pred = lambda p: pred_name_dict[p] if p in pred_name_dict.keys() else p

        init_transitions = []
        for t in self.init_program_trans:
            for E, effect in self.abstract_effect[t].items():
                if len(effect.keys()) > 1:
                    raise Exception("init transition " + str(t) + " has more than one possible effect")
                elif len(effect.keys()) == 1:
                    E_effects = [rename_pred(p) for p in list(effect.keys())[0]]
                else:
                    E_effects = []
                E_effects += [neg(rename_pred(p)) for p in self.abstract_effect_invars[transition_formula(t)]]
                E_effects += [rename_pred(p) for p in self.abstract_effect_constant[transition_formula(t)]]
                if len(E_effects) == 0:
                    raise Exception("init transition " + str(t) + " has no effect")
                init_transitions += [conjunct_formula_set(E_effects + [Variable(t.tgt)] + list(E) + t.output)]

        init_transition_ltl = disjunct_formula_set([conjunct(phi, X(phi)) for phi in init_transitions])

        transition_ltl = []
        for env_trans in self.abstract_guard_env.keys():
            # exclude initial transitions
            if env_trans in self.init_program_trans: continue

            t_formula = transition_formula(env_trans)
            now = conjunct_formula_set([env, Variable(env_trans.src)])

            invar_preds_effects = []

            if t_formula in self.abstract_effect_invars.keys():
                invar_preds_effects += [iff(pred_name_dict[p], X(pred_name_dict[p])) for p in self.abstract_effect_invars[t_formula]]

            if t_formula in self.abstract_effect_constant.keys():
                invar_preds_effects += [X(pred_name_dict[p]) for p in self.abstract_effect_constant[t_formula]]

            invar_preds_formula = conjunct_formula_set(invar_preds_effects)
            pred_effects = []

            for E, effect in self.abstract_effect[env_trans].items():
                E_effects = []
                for next_pred_state, pred_states in effect.items():
                    E_now = disjunct_formula_set(
                        [conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states])
                    E_now_simplified = simplify_formula_without_math(E_now)

                    E_next = X(conjunct_formula_set([rename_pred(p) for p in next_pred_state]))
                    E_effects += [conjunct(E_now_simplified, E_next)]
                pred_effects += [conjunct(conjunct_formula_set(E), disjunct_formula_set(E_effects))]

            pred_effect_formula = disjunct_formula_set(pred_effects)
            output_formula = conjunct_formula_set([X(o) for o in env_trans.output])
            effect_formula = conjunct(conjunct(pred_effect_formula, invar_preds_formula), output_formula)

            next = conjunct(effect_formula, X(conjunct_formula_set([Variable(env_trans.tgt)])))
            transition_ltl += [conjunct(now, next)]

        for con_trans in self.abstract_guard_con.keys():
            t_formula = transition_formula(con_trans)
            now = conjunct_formula_set([con, Variable(con_trans.src)])

            invar_preds_effects = []

            if t_formula in self.abstract_effect_invars.keys():
                invar_preds_effects += [iff(pred_name_dict[p], X(pred_name_dict[p])) for p in self.abstract_effect_invars[t_formula]]

            if t_formula in self.abstract_effect_constant.keys():
                invar_preds_effects += [X(pred_name_dict[p]) for p in self.abstract_effect_constant[t_formula]]

            invar_preds_formula = conjunct_formula_set(invar_preds_effects)

            pred_effects = []

            for E, effect in self.abstract_effect[con_trans].items():
                E_effects = []
                for next_pred_state, pred_states in effect.items():
                    E_now = disjunct_formula_set(
                                            [conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states])
                    E_now_simplified = simplify_formula_without_math(E_now)

                    E_next = X(conjunct_formula_set([rename_pred(p) for p in next_pred_state]))
                    E_effects += [conjunct(E_now_simplified, E_next)]
                pred_effects += [conjunct(conjunct_formula_set(E), disjunct_formula_set(E_effects))]
            pred_effect_formula = disjunct_formula_set(pred_effects)
            output_formula = conjunct_formula_set([X(neg(o)) for o in self.program.out_events])
            effect_formula = conjunct(conjunct(pred_effect_formula, invar_preds_formula), output_formula)

            next = conjunct(effect_formula, X(conjunct_formula_set([Variable(con_trans.tgt)])))
            transition_ltl += [conjunct(now, next)]

        ltl = conjunct(init_transition_ltl, X(G(disjunct_formula_set(transition_ltl))))

        print(ltl)
        return init_transition_ltl, X(G(disjunct_formula_set(transition_ltl)))

    def add_predicates_old(self, new_state_predicates: [Formula], new_transition_predicates: [Formula], pred_name_dict : dict, simplified: bool):
        if len(new_state_predicates) + len(new_transition_predicates) == 0:
            return

        # TODO maybe Nir's idea is better
        # T : 2^{P \cup Q} -> 2^2^{P \cup Q}

        print("Adding predicates to predicate abstraction:")
        print("state preds: [" + ", ".join(list(map(str, new_state_predicates))) + "]")
        print("trans preds: [" + ", ".join(list(map(str, new_transition_predicates))) + "]")


        print("Tagging abstract transitions with predicates..")
        start = time.time()
        for p in new_state_predicates + new_transition_predicates:
            self.transition_state_tags, self.transition_unaffected_tags, self.transition_constant_tags  = \
                self.tag_transitions_with_state_preds(self.transition_state_tags,
                                                      self.transition_unaffected_tags,
                                                      self.transition_constant_tags,
                                                      p)
            # self.con_tags, con_pred_invars = self.tag_transitions(self.con_tags, p)

        end = time.time()
        print(end - start)

        start = time.time()

        program = self.program
        init_st = program.initial_state
        init_conf = conjunct_typed_valuation_set(program.valuation)
        env_transitions = set()
        con_transitions = set()

        self.state_predicates += new_state_predicates
        self.transition_predicates += new_transition_predicates

        rename_pred = lambda p: pred_name_dict[p] if p in pred_name_dict.keys() else p

        init_preds = set()
        for p in self.state_predicates + self.transition_predicates:
            if smt_checker.check(And(*(conjunct(init_conf, p).to_smt(self.program.symbol_table)))):
                init_preds |= {p}
            else:
                init_preds |= {neg(p)}

        init_transitions = []
        for t in self.init_program_trans:
            t_formula = transition_formula(t)
            abstract_guard = self.abstract_guard_env[t]
            abstract_guard_disjuncts = self.abstract_guard_env_disjuncts[t]
            effects = []

            if t_formula in self.transition_constant_tags.keys():
                constants = self.transition_constant_tags[t_formula]
                effects += [pred_name_dict[p] for p in constants]
            else:
                constants = {}

            if t_formula in self.transition_unaffected_tags.keys():
                invars = self.transition_unaffected_tags[t_formula]
                effects += [pred_name_dict[p] for p in invars if p in init_preds]
                effects += [neg(pred_name_dict[p]) for p in invars if neg(p) in init_preds]
            else:
                invars = {}

            init_pred_state = frozenset(p for p in init_preds if p not in invars | constants and neg(p).simplify() not in constants)

            if t_formula in self.transition_state_tags.keys():
                for disjunct in abstract_guard_disjuncts:
                    predicate_effect = self.transition_state_tags[t_formula]
                    init_pred_state_with_disjunct = frozenset(init_pred_state | {disjunct})
                    if init_pred_state_with_disjunct not in predicate_effect.keys():
                        raise Exception("")
                    init_predicate_effect = disjunct_formula_set(conjunct_formula_set([rename_pred(p) for p in ps])
                                                                 for ps in predicate_effect[init_pred_state_with_disjunct])

                    effects += [(init_predicate_effect)]
            init_transitions += [conjunct_formula_set(effects + [Variable(t.tgt), abstract_guard] + t.output)]

        init_transition_ltl = disjunct_formula_set([conjunct(phi, X(phi)) for phi in init_transitions])

        transition_ltl = []
        for env_trans in self.abstract_guard_env.keys():
            abstract_guard_disjuncts = self.abstract_guard_env_disjuncts[env_trans]

            if env_trans in self.init_program_trans: continue
            now = conjunct_formula_set([env, Variable(env_trans.src), self.abstract_guard_env[env_trans]])
            t_formula = transition_formula(env_trans)

            effects = []
            if t_formula in self.transition_constant_tags.keys():
                effects += [X(pred_name_dict[p]) for p in self.transition_constant_tags[t_formula]]

            if t_formula in self.transition_unaffected_tags.keys():
                effects += [iff(pred_name_dict[p], X(pred_name_dict[p])) for p in self.transition_unaffected_tags[t_formula]]

            if t_formula in self.transition_state_tags.keys():
                predicate_effect = self.transition_state_tags[t_formula]
                inv_effects = {}
                for k, v in predicate_effect.items():
                    new_v = disjunct_formula_set([conjunct_formula_set([rename_pred(p) for p in ps]) for ps in v])
                    inv_effects[new_v] = inv_effects.get(new_v, []) + [k]

                effects += [implies(disjunct_formula_set([conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states]),
                                    X(next_pred_states))
                                                             for next_pred_states, pred_states in inv_effects.items()]

                # effects += [implies(conjunct_formula_set([pred_name_dict[p] for p in pred_state]),
                #                     X(disjunct_formula_set([conjunct_formula_set([pred_name_dict[p] for p in ps]) for ps in next_pred_states])))
                #                                              for pred_state, next_pred_states in predicate_effect.items()]

            effect_formula = conjunct_formula_set([X(o) for o in env_trans.output] + effects)

            next = conjunct(effect_formula, X(conjunct_formula_set([Variable(env_trans.tgt)])))
            transition_ltl += [conjunct(now, next)]

        for con_trans in self.abstract_guard_con.keys():
            now = conjunct_formula_set([con, Variable(con_trans.src), self.abstract_guard_con[con_trans]])

            t_formula = transition_formula(con_trans)

            effects = []
            if t_formula in self.transition_constant_tags.keys():
                effects += [X(pred_name_dict[p]) for p in self.transition_constant_tags[t_formula]]

            if t_formula in self.transition_unaffected_tags.keys():
                effects += [iff(pred_name_dict[p], X(pred_name_dict[p])) for p in self.transition_unaffected_tags[t_formula]]

            if t_formula in self.transition_state_tags.keys():
                predicate_effect = self.transition_state_tags[t_formula]
                inv_effects = {}
                for k, v in predicate_effect.items():
                    new_v = disjunct_formula_set([conjunct_formula_set([rename_pred(p) for p in ps]) for ps in v])
                    inv_effects[new_v] = inv_effects.get(new_v, []) + [k]

                effects += [implies(disjunct_formula_set([conjunct_formula_set([rename_pred(p) for p in pred_state]) for pred_state in pred_states]),
                                    X(next_pred_states))
                                                             for next_pred_states, pred_states in inv_effects.items()]

                # effects += [implies(conjunct_formula_set([pred_name_dict[p] for p in pred_state]),
                #                     X(disjunct_formula_set([conjunct_formula_set([pred_name_dict[p] for p in ps]) for ps in next_pred_states])))
                #                                              for pred_state, next_pred_states in predicate_effect.items()]

            effects += [X(neg(o)) for o in self.program.out_events]
            effect_formula = conjunct_formula_set(effects)

            next = conjunct(effect_formula, X(conjunct_formula_set([Variable(con_trans.tgt)])))
            transition_ltl += [conjunct(now, next)]

        ltl = conjunct(init_transition_ltl, X(G(disjunct_formula_set(transition_ltl))))

        print(ltl)
        return init_transition_ltl, X(G(disjunct_formula_set(transition_ltl)))

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
                tentative_abstract_ts = self.abstract_guard_env[current_t]
            else:
                tentative_abstract_ts = self.abstract_guard_con[current_t]
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

    def abstraction_to_ltl(self, symbol_table, simplified=True):
        predicates = self.state_predicates + self.transition_predicates

        new_env_transitions = self.abstraction.env_transitions
        # env_to_program_transitions = self.env_to_program_transitions
        new_con_transitions = self.abstraction.con_transitions
        # con_to_program_transitions = self.con_to_program_transitions

        ltl_to_program_transitions = {}

        init_transitions = [t for t in new_env_transitions if t.src == self.abstraction.initial_state]
        init_cond_formula_sets = []
        # ltl_to_program_transitions["init"] = {}
        for t in init_transitions:
            cond = conjunct(conjunct_formula_set([Variable(t.tgt), t.condition] + t.output),
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


def powerset_complete(SS: set):
    if not isinstance(SS, set):
        S = set(SS)
    else:
        S = SS
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
