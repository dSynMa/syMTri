from itertools import chain, combinations

from pysmt.shortcuts import And

from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import label_preds_according_to_index, add_prev_suffix
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    implies, G, X
from prop_lang.variable import Variable

smt_checker = SMTChecker()


def meaning_within(f: Formula, predicates: [Formula], symbol_table):
    Ps = set()
    Ps.add(frozenset())

    # remove negations from set
    predicates_without_negs = []
    for p in predicates:
        if neg(p) not in predicates_without_negs:
            predicates_without_negs.append(p)

    for p in predicates_without_negs:
        Pss = set()
        for ps in Ps:
            if smt_checker.check(And(*conjunct_formula_set(ps | {f, p}).to_smt(symbol_table))):
                Pss.add(frozenset(ps | {p}))

                if smt_checker.check(And(*conjunct_formula_set(ps | {f, neg(p)}).to_smt(symbol_table))):
                    Pss.add(frozenset(ps | {neg(p)}))
            else:
                Pss.add(frozenset(ps | {neg(p)}))
        Ps = Pss

    return Ps


def meaning_within_incremental_one_step(f: Formula, previous_preds: [[Formula]], new_pred: Formula,
                                        predicates: [Formula], symbol_table):
    Ps = set()

    for ps in previous_preds:
        if smt_checker.check(And(*conjunct_formula_set(ps | {f, new_pred}).to_smt(symbol_table))):
            Ps.add(ps | {new_pred})
            if smt_checker.check(And(*conjunct_formula_set(ps | {f, neg(new_pred)}).to_smt(symbol_table))):
                Ps.add(ps | {neg(new_pred)})
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


def predicate_abstraction(program: Program, state_predicates: [Formula], transition_predicates: [Formula], symbol_table) -> Program:
    env_sublists = powerset(program.env_events)
    con_sublists = powerset(program.con_events)

    init_st = program.initial_state
    init_conf = conjunct_typed_valuation_set(program.valuation)
    env_transitions = set()
    con_transitions = set()
    current_states = set()

    orig_env_transitions, orig_con_transitions = program.complete_transitions()

    symbol_table_with_prev_vars = symbol_table | {key + "_prev": value for key, value in symbol_table.items()}

    predicates = state_predicates + transition_predicates
    # initial transitions rule
    # TODO this should only be computed once, if predicate set updated it can be done incrementally
    for t in orig_env_transitions:
        if t.src == program.initial_state:
            for E in env_sublists:
                events = conjunct_formula_set(E)
                state = conjunct(init_conf, events)
                guarded = conjunct(state, t.condition)
                smt = And(*guarded.to_smt(symbol_table))
                if smt_checker.check(smt):
                    complete_action = program.complete_action_set(t.action)
                    relabelled_actions = [BiOp(b.left, "=", add_prev_suffix(program, b.right)) for b in complete_action]
                    action_formula = conjunct_formula_set(relabelled_actions)
                    next_valuation = conjunct(action_formula, add_prev_suffix(program, init_conf))
                    next_preds = {p for p in predicates if
                                  smt_checker.check(
                                      And(*conjunct(p, next_valuation).to_smt(symbol_table_with_prev_vars)))}
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
                    guard_in_context = And(*conjunct(t.condition, context).to_smt(symbol_table_with_prev_vars))
                    if smt_checker.check(guard_in_context):
                        context_P_without_prevs = conjunct_formula_set([p for p in P if [] == [v for v in p.variablesin() if v.name.endswith("_prev")]])
                        prev_condition = add_prev_suffix(program, t.condition)
                        complete_action = program.complete_action_set(t.action)
                        prev_action = [BiOp(act.left, "=", add_prev_suffix(program, act.right)) for act in complete_action]
                        f = conjunct_formula_set(
                            set(prev_action).union({prev_condition, add_prev_suffix(program, context_P_without_prevs), context_Evs}))
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

    return Program("pred_abst_" + program.name, done_states_env | done_states_con | {init_st}, init_st, [],
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


def complete_and_label_pred_sets(pred_set, full_preds):
    X = label_preds_according_to_index(pred_set, full_preds)
    # Y = {neg(label_pred_according_to_index(p, full_preds)) for p in full_preds if p not in set(pred_set)}
    return X # | Y


def abstraction_to_ltl(pred_abstraction: Program, predicates: [Formula]):
    init_transitions = [t for t in pred_abstraction.env_transitions if t.src == pred_abstraction.initial_state]
    init_cond_formula = disjunct_formula_set(
        {conjunct(conjunct_formula_set([Variable(t.tgt[0]), t.condition] + t.output),
                  conjunct_formula_set(sorted(complete_and_label_pred_sets(t.tgt[1], predicates), key = lambda x : str(x)))
                  ) for t in init_transitions}
    )
    init_cond = init_cond_formula.to_nuxmv()

    states = [Variable(s[0]) for s in pred_abstraction.states if s != pred_abstraction.initial_state] + \
             [Variable(pred_abstraction.initial_state)]
    states = set(states)

    at_least_one_state = UniOp("G", disjunct_formula_set([q for q in states])).to_nuxmv()

    at_most_one_state = UniOp("G", conjunct_formula_set([BiOp(q, "=>", conjunct_formula_set([neg(r) for r in
                                                                                             states
                                                                                             if
                                                                                             r != q]))
                                                         for q in states])).to_nuxmv()

    not_init_env_transitions = [t for t in pred_abstraction.env_transitions if t.src != pred_abstraction.initial_state]

    not_init_con_transitions = [t for t in pred_abstraction.con_transitions if t.src != pred_abstraction.initial_state]

    matching_pairs = {}

    # for every state that is not the initial state
    for c in pred_abstraction.states:
        if c is not pred_abstraction.initial_state:
            # get all transitions from that state
            all_con_trans_from_c = [t for t in not_init_con_transitions if t.src == c]
            # get all conditions of those transitions
            all_conds = {t.condition for t in all_con_trans_from_c}
            # given a condition from a state, get all possible destinations of it
            dst_cond = {cond: [t.tgt for t in not_init_con_transitions if t.src == c and cond == t.condition] for cond in all_conds}
            matching_pairs.update({(c, cond): [et for et in not_init_env_transitions if et.src in dst_cond[cond]] for cond in dst_cond.keys()})

    con_env_transitions = []
    for (c_s, cond), ets in matching_pairs.items():
        now = conjunct(conjunct(Variable(c_s[0]),
                                conjunct_formula_set(sorted(complete_and_label_pred_sets(c_s[1], predicates), key = lambda x: str(x)))),
                       cond)
        next = []
        for et in ets:
            bookeeping_tran_preds = tran_preds_after_con_env_step(et, predicates)
            next += [
                X(conjunct(conjunct_formula_set([Variable(et.tgt[0]), et.condition] + et.output),
                           conjunct_formula_set(sorted(complete_and_label_pred_sets(bookeeping_tran_preds, predicates), key = lambda x: str(x)))
                ))]

        next = sorted(next, key=lambda x : str(x))
        con_env_transitions += [G(implies(now, disjunct_formula_set(next))).to_nuxmv()]

    transition_cond = sorted(con_env_transitions, key=lambda x : str(x))

    return [init_cond, at_least_one_state, at_most_one_state] + transition_cond


def tran_preds_after_con_env_step(env_trans : Transition, predicates: [Formula]):
    src_tran_preds = [p for p in predicates
                      if p in env_trans.src[1]
                      if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]
    tgt_tran_preds = [p for p in predicates
                      if p in env_trans.tgt[1]
                      if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]

    keep_these = []

    for p in src_tran_preds:
        if type(p) == BiOp and p.op == "<":
            if BiOp(p.left, "<", p.right) in tgt_tran_preds:
                keep_these += [p, neg(BiOp(p.left, ">", p.right))]
            elif BiOp(p.left, ">", p.right) in tgt_tran_preds:
                keep_these += [neg(BiOp(p.left, ">", p.right)), neg(BiOp(p.left, ">", p.right))]
            elif neg(BiOp(p.left, ">", p.right)) in tgt_tran_preds and neg(BiOp(p.left, "<", p.right)) in tgt_tran_preds:
                keep_these += [p]
        elif type(p) == BiOp and p.op == ">":
            if BiOp(p.left, ">", p.right) in tgt_tran_preds:
                keep_these += [p]
            elif BiOp(p.left, "<", p.right) in tgt_tran_preds:
                keep_these += [neg(BiOp(p.left, ">", p.right)), neg(BiOp(p.left, ">", p.right))]
            elif neg(BiOp(p.left, ">", p.right)) in tgt_tran_preds and neg(BiOp(p.left, "<", p.right)) in tgt_tran_preds:
                keep_these += [p, neg(BiOp(p.left, "<", p.right))]

    keep_these += [q for q in tgt_tran_preds if neg(q).simplify() not in keep_these]

    return list(set(keep_these)) \
           + [p for p in env_trans.tgt[1] if p not in tgt_tran_preds]