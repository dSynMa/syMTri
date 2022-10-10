from itertools import chain, combinations

from pysmt.shortcuts import And, Not, TRUE

from programs.analysis.abstract_state import AbstractState
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import label_preds, add_prev_suffix
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, neg, conjunct_formula_set, conjunct_typed_valuation_set, disjunct_formula_set, \
    implies, G, X
from prop_lang.value import Value
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


def predicate_abstraction(program: Program, state_predicates: [Formula], transition_predicates: [Formula], symbol_table,
                          simplified: bool) -> Program:
    init_st = program.initial_state
    init_conf = conjunct_typed_valuation_set(program.valuation)
    env_transitions = set()
    con_transitions = set()
    current_states = set()

    orig_env_transitions, orig_con_transitions = program.complete_transitions()

    symbol_table_with_prev_vars = symbol_table | {key + "_prev": value for key, value in symbol_table.items()}

    predicates = state_predicates + transition_predicates
    negation_closed_predicates = predicates + [neg(p) for p in predicates]
    # initial transitions rule
    # TODO this should only be computed once, if predicate set updated it can be done incrementally
    for t in orig_env_transitions:
        vars_in_cond = t.condition.variablesin()
        env_vars_in_cond = [e for e in vars_in_cond if e in program.env_events]
        env_powerset = powerset_complete(env_vars_in_cond)
        for E in env_powerset:
            if t.src == program.initial_state:
                events = conjunct_formula_set(E)
                state = conjunct(init_conf, events)
                guarded = conjunct(state, t.condition)
                smt = And(*guarded.to_smt(symbol_table))
                if smt_checker.check(smt):
                    complete_action = program.complete_action_set(t.action)
                    relabelled_actions = [BiOp(b.left, "=", add_prev_suffix(program, b.right)) for b in complete_action]
                    action_formula = conjunct_formula_set(relabelled_actions)
                    next_valuation = conjunct(action_formula, add_prev_suffix(program, init_conf))
                    next_preds = {p for p in negation_closed_predicates if
                                  smt_checker.check(
                                      And(*conjunct(p, next_valuation).to_smt(symbol_table_with_prev_vars)))}
                    next_state = AbstractState(t.tgt, frozenset(next_preds))
                    current_states.add(next_state)

                    new_output = set(t.output)
                    new_output |= {neg(o) for o in program.out_events if o not in t.output}
                    new_output = list(new_output)
                    env_transitions.add(Transition(init_st, events, [], new_output, next_state))

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

        for abs_st in current_states:
            q, P = abs_st.unpack()
            q_transitions = {t for t in transition_set if str(t.src) == str(q)}
            for t in q_transitions:
                vars_in_cond = t.condition.variablesin()
                env_vars_in_cond = [e for e in vars_in_cond if e in events]
                env_powerset = powerset_complete(env_vars_in_cond)
                for Evs in env_powerset:
                    # TODO precompute mapping from states to transitions
                    context_P = conjunct_formula_set(P)
                    context_Evs = conjunct_formula_set(Evs)
                    context = conjunct(context_P, context_Evs)
                    guard_in_context = And(*conjunct(t.condition, context).to_smt(symbol_table_with_prev_vars))
                    if smt_checker.check(guard_in_context):
                        context_P_without_prevs = conjunct_formula_set(
                            [p for p in P if [] == [v for v in p.variablesin() if v.name.endswith("_prev")]])
                        prev_condition = add_prev_suffix(program, t.condition)
                        complete_action = program.complete_action_set(t.action)
                        prev_action = [BiOp(act.left, "=", add_prev_suffix(program, act.right)) for act in
                                       complete_action]
                        f = conjunct_formula_set(
                            set(prev_action).union(
                                {prev_condition, add_prev_suffix(program, context_P_without_prevs), context_Evs}))
                        next_Ps = meaning_within(f, negation_closed_predicates, symbol_table_with_prev_vars)
                        for next_P in next_Ps:
                            next_state = AbstractState(t.tgt, next_P)
                            new_output = set(t.output)
                            new_output |= {neg(o) for o in program.out_events if o not in t.output}
                            new_output = list(new_output)
                            new_transitions.add(Transition(abs_st, context_Evs, [], new_output, next_state))
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

    # simplification stage
    if simplified:
        new_env_transitions = merge_transitions(env_transitions, symbol_table)
        new_con_transitions = merge_transitions(con_transitions, symbol_table)
    else:
        new_env_transitions = env_transitions
        new_con_transitions = con_transitions

    return Program("pred_abst_" + program.name, states | {init_st}, init_st, [],
                   new_env_transitions,
                   new_con_transitions, program.env_events,
                   program.con_events, program.out_events)


def merge_transitions(transitions: [Transition], symbol_table):
    new_transitions = []

    # partition the transitions into classes where in each class each transition has the same outputs and source and end state
    partitions = dict()
    for transition in transitions:
        key = str(transition.src) + str(conjunct_formula_set(sorted(transition.output, key=lambda x: str(x)))) + str(
            transition.tgt)
        if key in partitions.keys():
            partitions[key].append(transition)
        else:
            partitions[key] = [transition]
    for key in partitions.keys():
        trans_here = partitions[key]
        conditions = disjunct_formula_set(sorted([t.condition for t in trans_here], key=lambda x: str(x)))
        conditions_smt = conditions.to_smt(symbol_table)
        # If negation is unsat
        if not smt_checker.check(Not(And(*conditions_smt))):
            conditions_simplified_fnode = TRUE()
        else:
            conditions_simplified_fnode = conditions_smt[0].simplify()
        ## simplify when doing disjunct, after lex ordering
        ## also, may consider when enumerating possible event sets starting with missing some evetns and seeing how many transitions they match, if only then can stop adding to it
        try:
            # TODO using string_to_ltl here since it can deal with unbracketed combinations, e.g. a | b | c
            #  string_to_pl needs to be extended to handle this too
            new_transitions.append(
                Transition(trans_here[0].src, string_to_ltl(str(conditions_simplified_fnode)), [], trans_here[0].output,
                           trans_here[0].tgt))
        except Exception as e:
            raise e
    return new_transitions


# Use this for testing
# TODO update, this is probably not in sync with abstraction_to_ltl
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


def abstraction_to_ltl(pred_abstraction: Program, state_predicates: [Formula], transition_predicates: [Formula]):
    predicates = state_predicates + transition_predicates
    negation_closed_predicates = predicates + [neg(p) for p in predicates]

    init_transitions = [t for t in pred_abstraction.env_transitions if t.src == pred_abstraction.initial_state]
    init_cond_formula = disjunct_formula_set(
        {conjunct(conjunct_formula_set([Variable(t.tgt.state), t.condition] + t.output),
                  conjunct_formula_set(sorted(label_preds(t.tgt.predicates, predicates), key=lambda x: str(x)))
                  ) for t in init_transitions}
    )
    init_cond = init_cond_formula.to_nuxmv()

    states = [Variable(s.state) for s in pred_abstraction.states if s != pred_abstraction.initial_state] + \
             [Variable(pred_abstraction.initial_state)]
    states = set(states)

    at_least_and_at_most_one_state = UniOp("G",
                                           conjunct_formula_set([BiOp(q, "<=>", conjunct_formula_set([neg(r) for r in
                                                                                                      states
                                                                                                      if
                                                                                                      r != q]))
                                                                 for q in states])).to_nuxmv()

    not_init_env_transitions = [t for t in pred_abstraction.env_transitions if t.src != pred_abstraction.initial_state]

    not_init_con_transitions = [t for t in pred_abstraction.con_transitions if t.src != pred_abstraction.initial_state]

    matching_pairs = {}

    # for every state that is not the initial state: s
    # for each controller transition from that state: t
    # get the set of all env transitions that can happen immediately after: ets
    # and match s with the pair of condition of t and ets
    #
    # at the end, every state s is associated with a list of conditions
    # and the associated env transitions that can happen after
    for s in pred_abstraction.states:
        if s is not pred_abstraction.initial_state:
            for t in not_init_con_transitions:
                if t.src == s:
                    ets = []
                    for et in not_init_env_transitions:
                        if et.src == t.tgt:
                            ets.append(et)
                        else:
                            pass
                    if s in matching_pairs.keys():
                        matching_pairs[s] += [(t.condition, ets)]
                    else:
                        matching_pairs[s] = [(t.condition, ets)]
                else:
                    pass

    con_env_transitions = []
    for c_s, cond_ets in matching_pairs.items():
        now_state_preds = [p for p in c_s.predicates if p in (state_predicates + [neg(p) for p in state_predicates])]
        now = conjunct(Variable(c_s.state),
                       conjunct_formula_set(sorted(label_preds(now_state_preds, predicates),
                                                   key=lambda x: str(x))))
        next = []
        for (cond, ets) in cond_ets:
            now_next = []
            for et in ets:
                bookeeping_tran_preds = label_preds(tran_preds_after_con_env_step(et, negation_closed_predicates),
                                                    state_predicates + transition_predicates)
                now_next += [X(conjunct(conjunct_formula_set([Variable(et.tgt.state), et.condition] + et.output),
                                        conjunct_formula_set(sorted(bookeeping_tran_preds, key=lambda x: str(x)))
                                        ))]

            # If cond (which is the about the current state) is just True (i.e., it s negation is unsat)
            # then just ignore it
            if isinstance(cond, Value) and cond.is_true():
                next += [disjunct_formula_set(sorted(set(now_next), key=lambda x: str(x)))]
            else:
                next += [conjunct(cond, disjunct_formula_set(sorted(set(now_next), key=lambda x: str(x))))]

        next = sorted(set(next), key=lambda x: str(x))

        con_env_transitions += [G(implies(now, disjunct_formula_set(next))).to_nuxmv()]

    # TODO this set is needed when we have transition predicates
    transition_cond = sorted(set(con_env_transitions), key=lambda x: str(x))

    return [init_cond, at_least_and_at_most_one_state] + transition_cond


def tran_preds_after_con_env_step(env_trans: Transition, predicates: [Formula]):
    src_tran_preds = [p for p in predicates
                      if p in env_trans.src.predicates
                      if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]
    tgt_tran_preds = [p for p in predicates
                      if p in env_trans.tgt.predicates
                      if [] != [v for v in p.variablesin() if v.name.endswith("_prev")]]

    keep_these = []

    for p in src_tran_preds:
        if type(p) == BiOp and p.op == "<":
            if BiOp(p.left, "<", p.right) in tgt_tran_preds:
                keep_these += [p]
            elif BiOp(p.left, ">", p.right) in tgt_tran_preds:
                keep_these += [neg(BiOp(p.left, ">", p.right)), neg(BiOp(p.left, ">", p.right))]
            elif neg(BiOp(p.left, ">", p.right)) in tgt_tran_preds and neg(
                    BiOp(p.left, "<", p.right)) in tgt_tran_preds:
                keep_these += [p]
        elif type(p) == BiOp and p.op == ">":
            if BiOp(p.left, ">", p.right) in tgt_tran_preds:
                keep_these += [p]
            elif BiOp(p.left, "<", p.right) in tgt_tran_preds:
                keep_these += [neg(BiOp(p.left, ">", p.right)), neg(BiOp(p.left, ">", p.right))]
            elif neg(BiOp(p.left, ">", p.right)) in tgt_tran_preds and neg(
                    BiOp(p.left, "<", p.right)) in tgt_tran_preds:
                keep_these += [p]

    keep_these += [q for q in tgt_tran_preds if neg(q).simplify() not in keep_these] + [p for p in
                                                                                        env_trans.tgt.predicates if
                                                                                        p not in tgt_tran_preds]

    return list(set(keep_these))
