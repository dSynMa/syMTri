from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import label_preds_according_to_index
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    disjunct
from itertools import chain, combinations

from prop_lang.variable import Variable

smt_checker = SMTChecker()


def meaning_within(f: Formula, predicates: [Formula], symbol_table):
    Ps = set()
    Ps.add(frozenset())

    for p in predicates:
        Pss = set()
        for ps in Ps:
            if smt_checker.check(conjunct_formula_set(ps | {f, p}).to_smt(symbol_table)):
                Pss.add(frozenset(ps | {p}))
            else:
                Pss.add(frozenset(ps | {neg(p)}))
        Ps = Pss

    return Ps


def meaning_within_incremental(f: Formula, previous_preds: [[Formula]], new_pred: Formula, symbol_table):
    Ps = set()

    for ps in previous_preds:
        if smt_checker.check(conjunct_formula_set(ps | {f, new_pred}).to_smt(symbol_table)):
            Ps.add(ps | {new_pred})
        else:
            Ps.add(ps | {neg(new_pred)})

    return Ps


def powerset(S: set):
    positive_subsets = chain.from_iterable(combinations(S, r) for r in range(len(S) + 1))
    complete_subsets = set()
    for ps in positive_subsets:
        real_ps = set(ps)
        negative = {neg(s) for s in S if (s) not in real_ps}
        complete = set(real_ps).union(negative)
        complete_subsets.add(frozenset(complete))

    return complete_subsets


def predicate_abstraction(program: Program, predicates: [Formula], symbol_table) -> Program:
    env_sublists = powerset(program.env_events)
    con_sublists = powerset(program.con_events)

    init_st = program.initial_state
    init_conf = conjunct_typed_valuation_set(program.valuation)
    env_transitions = set()
    con_transitions = set()
    current_states = set()

    orig_env_transitions, orig_con_transitions = program.complete_transitions()

    for_renaming = [BiOp(Variable(v), ":=", Variable(v + "_prev")) for v in [tv.name for tv in program.valuation]]
    symbol_table_with_prev_vars = symbol_table | {key + "_prev": value for key, value in symbol_table.items()}

    # initial transitions rule
    # TODO this should only be computed once, if predicate set updated it can be done incrementally
    for t in orig_env_transitions:
        if t.src == program.initial_state:
            for E in env_sublists:
                events = conjunct_formula_set(E)
                state = conjunct(init_conf, events)
                guarded = conjunct(state, t.condition)
                smt = guarded.to_smt(symbol_table)
                if smt_checker.check(smt):
                    relabelled_actions = [BiOp(b.left, "=", b.right.replace(for_renaming)) for b in t.action]
                    action_formula = conjunct_formula_set(relabelled_actions)
                    next_valuation = conjunct(action_formula, init_conf)
                    next_preds = {p for p in predicates if
                                  smt_checker.check(conjunct(p, next_valuation).to_smt(symbol_table_with_prev_vars))}
                    next_state = (t.tgt, frozenset(next_preds))
                    current_states.add(next_state)

                    new_output = set(t.output)
                    new_output |= {neg(o) for o in program.out_events if o not in t.output}
                    new_output = list(new_output)
                    env_transitions.add(Transition(init_st, events, [], new_output, next_state))

    con_turn_flag = True

    done_states_env = set()
    done_states_con = set()

    done_states_env.add(program.initial_state)

    while len(current_states) != 0:
        next_states = set()

        if con_turn_flag:
            transition_set = orig_con_transitions
            events_sublists = con_sublists
        else:
            transition_set = orig_env_transitions
            events_sublists = env_sublists

        new_transitions = set()

        for q, P in current_states:
            # TODO precompute mapping from states to transitions
            q_transitions = {t for t in transition_set if t.src == q}
            for Evs in events_sublists:
                context_P = conjunct_formula_set(P)
                context_Evs = conjunct_formula_set(Evs)
                context = conjunct(context_P, context_Evs)
                for t in q_transitions:
                    guard_in_context = conjunct(t.condition, context).to_smt(symbol_table)
                    if smt_checker.check(guard_in_context):
                        prev_condition = t.condition.replace(for_renaming)
                        prev_action = [BiOp(act.left, "=", act.right.replace(for_renaming)) for act in t.action]
                        f = conjunct_formula_set(
                            set(prev_action).union({prev_condition, context_P.replace(for_renaming), context_Evs}))
                        next_Ps = meaning_within(f, predicates, symbol_table_with_prev_vars)
                        for next_P in next_Ps:
                            next_state = (t.tgt, next_P)
                            if con_turn_flag and next_state not in done_states_env:
                                next_states.add(next_state)
                            elif not con_turn_flag and next_state not in done_states_con:
                                next_states.add(next_state)

                            new_output = set(t.output)
                            new_output |= {neg(o) for o in program.out_events if o not in t.output}
                            new_output = list(new_output)
                            new_transitions.add(Transition((q, P), context_Evs, [], new_output, next_state))

        if con_turn_flag:
            done_states_con.update(current_states)
            con_transitions.update(new_transitions)
        else:
            done_states_env.update(current_states)
            env_transitions.update(new_transitions)

        current_states = next_states

        con_turn_flag = not con_turn_flag

    return Program("pred_abst_" + program.name, done_states_env | done_states_con, program.initial_state, [],
                   env_transitions,
                   con_transitions, program.env_events,
                   program.con_events, program.out_events)


# Use this for testing
def abstraction_to_ltl_with_turns(pred_abstraction: Program):
    init_transitions = [t for t in pred_abstraction.env_transitions if t.src == pred_abstraction.initial_state]
    init_cond = disjunct_formula_set(
        [conjunct_formula_set({Variable(pred_abstraction.initial_state),
                               t.condition}  # the target state of transition, and the environment proposition guard
                              | {UniOp("X", out) for out in t.output}
                              | {UniOp("X", p) for p in t.tgt[1]}  # the predicate set associate with target state
                              | {UniOp("X", Variable(t.tgt[0]))})  # the monitor props associated with transition
         for t in init_transitions]).to_nuxmv()

    # wrapping states in Variable object
    states = [Variable(s[0]) for s in pred_abstraction.states if s != pred_abstraction.initial_state] \
             + [Variable(pred_abstraction.initial_state)]

    at_least_one_state = UniOp("G", disjunct_formula_set([q for q in states])).to_nuxmv()

    at_most_one_state = UniOp("G", conjunct_formula_set([BiOp(q, "=>", conjunct_formula_set([neg(r) for r in
                                                                                             states
                                                                                             if
                                                                                             r != q]))
                                                         for q in states])).to_nuxmv()

    # the non initial transitions
    not_init_env_transitions = [t for t in pred_abstraction.env_transitions if t.src != pred_abstraction.initial_state]

    not_init_con_transitions = [t for t in pred_abstraction.con_transitions if t.src != pred_abstraction.initial_state]

    # if it's the controller's turn, then the monitor observes what the controller did, and moves in the next step
    con_transitions = conjunct(BiOp(Variable("turn"), "=", Variable("con")),
                               disjunct_formula_set([conjunct_formula_set(ct.src[1]  # are these predicates true
                                                                          | {Variable(ct.src[0]),  # am i in this state
                                                                             ct.condition,  # did the controller do this
                                                                             UniOp("X",
                                                                                   # then i move in the next state like thi
                                                                                   conjunct_formula_set(
                                                                                       {Variable(ct.tgt[0])}
                                                                                       | ct.tgt[1]))})
                                                     for ct in not_init_con_transitions]))

    # if it's the environment's turn, then the monitor observes what the environment did, and moves in the next step
    env_transitions = conjunct(BiOp(Variable("turn"), "=", Variable("env")),
                               disjunct_formula_set(
                                   [conjunct_formula_set(et.src[1]
                                                         | {Variable(et.src[0]),
                                                            et.condition,
                                                            UniOp("X",
                                                                  conjunct_formula_set({Variable(et.tgt[0])}
                                                                                       | et.tgt[1]))}
                                                         | {UniOp("X", out) for out in et.output})
                                    for et in not_init_env_transitions]))

    predicates = [p for s in pred_abstraction.states for p in s[1] if s is not pred_abstraction.initial_state]

    mon_transition = conjunct(BiOp(Variable("turn"), "=", Variable("mon")),
                              conjunct_formula_set({BiOp(s, "<->", UniOp("X", s)) for s in states}
                                                   | {BiOp(p, "<->", UniOp("X", p)) for p in predicates}))

    transition_cond = UniOp("G", disjunct_formula_set([con_transitions, env_transitions, mon_transition])).to_nuxmv()

    return conjunct_formula_set([init_cond, at_least_one_state, at_most_one_state, transition_cond])


def abstraction_to_ltl(pred_abstraction: Program, predicates: [Formula]):
    init_transitions = [t for t in pred_abstraction.env_transitions if t.src == pred_abstraction.initial_state]
    init_cond = disjunct_formula_set(
        {conjunct_formula_set({Variable(t.tgt[0]), t.condition}
                              | label_preds_according_to_index(t.tgt[1], predicates)
                              | set(t.output)) for t in init_transitions}
    ).to_nuxmv()

    states = [Variable(s[0]) for s in pred_abstraction.states if s != pred_abstraction.initial_state] + [
        Variable(pred_abstraction.initial_state)]

    at_least_one_state = UniOp("G", disjunct_formula_set([q for q in states])).to_nuxmv()

    at_most_one_state = UniOp("G", conjunct_formula_set([BiOp(q, "=>", conjunct_formula_set([neg(r) for r in
                                                                                             states
                                                                                             if
                                                                                             r != q]))
                                                         for q in states])).to_nuxmv()

    not_init_env_transitions = [t for t in pred_abstraction.env_transitions if t.src != pred_abstraction.initial_state]

    not_init_con_transitions = [t for t in pred_abstraction.con_transitions if t.src != pred_abstraction.initial_state]

    matching_pairs = [(ct, et)
                      for ct in not_init_con_transitions
                      for et in not_init_env_transitions
                      if ct.tgt == et.src]

    con_env_transitions = disjunct_formula_set([
        conjunct_formula_set(label_preds_according_to_index(ct.src[1], predicates)
                             | {Variable(ct.src[0]), ct.condition}
                             | {UniOp("X",
                                      conjunct_formula_set(label_preds_according_to_index(et.tgt[1], predicates)
                                                           | {Variable(et.tgt[0]), et.condition}
                                                           | {out for out in et.output}))})
        for (ct, et) in matching_pairs])

    transition_cond = UniOp("G", con_env_transitions).to_nuxmv()

    return conjunct_formula_set([init_cond, at_least_one_state, at_most_one_state, transition_cond])
