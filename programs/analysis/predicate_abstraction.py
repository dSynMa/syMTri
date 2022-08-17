from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set
from itertools import chain, combinations

from prop_lang.variable import Variable

smt_checker = SMTChecker()


def meaning_within(f: Formula, predicates: [Formula], symbol_table):
    Ps = set()
    Ps.add(set())

    for p in predicates:
        Pss = set()
        for ps in Ps:
            if smt_checker.check(conjunct_formula_set(ps + {f, p}), symbol_table):
                Pss.add(ps + {p})
            else:
                Ps.add(ps + {neg(p)})
        Ps = Pss

    return Ps


def meaning_within_incremental(f: Formula, previous_preds: [[Formula]], new_pred: Formula, symbol_table):
    Ps = set()

    for ps in previous_preds:
        if smt_checker.check(conjunct_formula_set(ps + {f, new_pred}), symbol_table):
            Ps.add(ps + {new_pred})
        else:
            Ps.add(ps + {neg(new_pred)})

    return Ps


def subsets_as_lists(S: set):
    return chain.from_iterable(combinations(list(S), r) for r in range(len(S) + 1))


def predicate_abstraction(program: Program, predicates: [Formula], symbol_table):
    env_sublists = subsets_as_lists(program.env_events)
    con_sublists = subsets_as_lists(program.con_events)

    init_st = program.initial_state
    init_conf = conjunct_typed_valuation_set(program.valuation)
    env_transitions = set()
    con_transitions = set()
    current_states = set()
    done_states = set()

    # initial transitions rule
    # TODO this should only be computed once, if predicate set updated it can be done incrementally
    for t in program.env_transitions:
        if t.src is program.initial_state:
            for E in env_sublists:
                events = conjunct_formula_set(E)
                state = conjunct(init_conf, events)
                guarded = conjunct(state, t.condition)
                smt = guarded.to_smt(symbol_table)
                if smt_checker.check(smt, symbol_table):
                    action_formula = conjunct_formula_set(set(t.action))
                    next_valuation = conjunct(action_formula, init_conf)
                    next_preds = {p for p in predicates if smt_checker.check(conjunct(p, next_valuation), symbol_table)}
                    next_state = (t.tgt, next_preds)
                    current_states.add(next_state)
                    env_transitions.add(Transition(init_st, events, [], [], next_state))

    con_turn_flag = True
    for_renaming = [BiOp(v, ":=", Variable(v.name + "_prev")) for v in [tv.name for tv in program.valuation]]

    done_states.add(program.initial_state)

    while len(current_states) is not 0:
        next_states = set()

        if con_turn_flag:
            transition_set = program.con_transitions
            events_sublists = con_sublists
        else:
            transition_set = program.event_transitions
            events_sublists = env_sublists

        new_transitions = set()

        for q, P in current_states:
            # TODO precompute mapping from states to transitions
            q_transitions = {t for t in transition_set if t.src is q}
            for Evs in events_sublists:
                context_P = conjunct_formula_set(P)
                context_Evs = conjunct_formula_set(Evs)
                context = conjunct(context_P, context_Evs)
                for t in q_transitions:
                    guard_in_context = conjunct(t.condition, context)
                    if smt_checker.check(guard_in_context, symbol_table):
                        prev_condition = t.condition.replace(for_renaming)
                        prev_action = [BiOp(act.left, "=", act.right.replace(for_renaming)) for act in t.action]
                        f = conjunct_formula_set(
                            set(prev_action).union({prev_condition, context_P.replace(for_renaming), context_Evs}))
                        next_Ps = meaning_within(f, predicates, symbol_table)
                        for next_P in next_Ps:
                            next_state = (t.tgt, next_P)
                            if next_state not in done_states.union(current_states):
                                next_states.add(next_state)
                            new_transitions.add(Transition((q, P), context_Evs, [], [], next_state))

        if con_turn_flag:
            con_transitions.update(new_transitions)
        else:
            env_transitions.update(new_transitions)

        done_states.update(current_states)
        current_states = next_states
        con_turn_flag = not con_turn_flag
    return Program("pred_abst_" + program.name, done_states, [], env_transitions, con_transitions, program.env_events,
                   program.con_events, program.mon_events)


def abstraction_to_ltl(pred_abstraction: Program):
    init_transitions = [t for t in pred_abstraction.env_transitions]
    init_cond = disjunct_formula_set(
        [conjunct_formula_set({Variable(t.src), t.condition, t.tgt[1]}) for t in init_transitions])

    at_least_one_state = UniOp("G", disjunct_formula_set([Variable(q[0]) for q in pred_abstraction.states]))

    at_most_one_state = UniOp("G", conjunct_formula_set([BiOp(Variable(q[0]), "=>", conjunct_formula_set([neg(r[0])
                                                                                                          for r in
                                                                                                          pred_abstraction.states
                                                                                                          if
                                                                                                          r[0] is not q[
                                                                                                              0]]))
                                                         for q in pred_abstraction.states]))

    matching_pairs = [(ct, et)
                      for ct in pred_abstraction.con_transitions
                      for et in pred_abstraction.env_transitions
                      if ct.tgt is et.src]

    con_env_transitions = disjunct_formula_set([conjunct_formula_set([Variable(ct.src[0]),
                                                                      conjunct_formula_set(ct.src[1]),
                                                                      ct.condition,
                                                                      UniOp("X",
                                                                            conjunct_formula_set([Variable(et.tgt[0]),
                                                                                                  et.condition,
                                                                                                  conjunct_formula_set(
                                                                                                      et.tgt[1])]))])
                                                for (ct, et) in matching_pairs])

    transition_cond = UniOp("G", con_env_transitions)

    return conjunct_formula_set([init_cond, at_least_one_state, at_most_one_state, transition_cond])


# Use this for testing
def abstraction_to_ltl_with_turns(pred_abstraction: Program):
    init_transitions = [t for t in pred_abstraction.env_transitions]
    init_cond = conjunct(Variable("env"), disjunct_formula_set(
        [conjunct_formula_set({Variable(t.src), t.condition, t.tgt[1]}) for t in init_transitions]))

    at_least_one_state = UniOp("G", disjunct_formula_set([Variable(q[0]) for q in pred_abstraction.states]))

    at_most_one_state = UniOp("G", conjunct_formula_set([BiOp(Variable(q[0]), "=>", conjunct_formula_set([neg(r[0])
                                                                                                          for r in
                                                                                                          pred_abstraction.states
                                                                                                          if
                                                                                                          r[0] is not q[
                                                                                                              0]]))
                                                         for q in pred_abstraction.states]))

    con_transitions = conjunct(neg(Variable("env")), disjunct_formula_set([conjunct_formula_set([Variable(ct.src[0]),
                                                                                                 conjunct_formula_set(
                                                                                                     ct.src[1]),
                                                                                                 ct.condition,
                                                                                                 UniOp("X",
                                                                                                       conjunct_formula_set(
                                                                                                           [Variable(
                                                                                                               ct.tgt[
                                                                                                                   0]),
                                                                                                            conjunct_formula_set(
                                                                                                                ct.tgt[
                                                                                                                    1])]))])
                                                                           for ct in pred_abstraction.con_transitions]))

    env_transitions = conjunct(Variable("env"), disjunct_formula_set([conjunct_formula_set([Variable(et.src[0]),
                                                                                            conjunct_formula_set(
                                                                                                et.src[1]),
                                                                                            et.condition,
                                                                                            UniOp("X",
                                                                                                  conjunct_formula_set([
                                                                                                                           Variable(
                                                                                                                               et.tgt[
                                                                                                                                   0]),
                                                                                                                           conjunct_formula_set(
                                                                                                                               et.tgt[
                                                                                                                                   1])]))])
                                                                      for et in pred_abstraction.env_transitions]))

    transition_cond = UniOp("G", disjunct_formula_set(con_transitions, env_transitions))

    return conjunct_formula_set([init_cond, at_least_one_state, at_most_one_state, transition_cond])
