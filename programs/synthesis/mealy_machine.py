from graphviz import Digraph
from pysmt.shortcuts import And

import Config
from programs.abstraction.predicate_abstraction import tran_and_state_preds_after_con_env_step, PredicateAbstraction
from programs.analysis.nuxmv_model import NuXmvModel
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set, neg, conjunct, mutually_exclusive_rules, \
    propagate_negations, sat, simplify_formula_without_math, is_tautology, iff, \
    project_out_vars
from prop_lang.variable import Variable


class MealyMachine:
    def __init__(self, name, init_st: int, env_events, con_events, env_transitions={}, con_transitions={}):
        self.name = name
        self.init_st = str(init_st)
        self.states = {self.init_st} | {k for k in env_transitions.keys() | con_transitions.keys()}
        self.env_events = env_events
        self.con_events = con_events
        self.env_transitions = env_transitions
        self.con_transitions = con_transitions
        self.prog_state = {}
        self.counter = -1
        self.env_transition_tgt = {}
        self.con_transition_tgt = {}
        self.env_prog_state = {}
        self.con_prog_state = {}

    def add_transitions(self, controller: bool, trans_dict: dict, resolve_env_turns, env_events, con_events, prog_out, prog_preds):
        int_env_trans = {}
        int_con_trans = {}

        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            env_cond = (env_behaviour.simplify()).to_nuxmv()
            env_cond = propagate_negations(env_cond)

            env_turn = resolve_env_turns and sat(conjunct(Config.env, env_cond))
            con_turn = resolve_env_turns and sat(conjunct(Config.con, env_cond))

            if not env_turn and not con_turn:
                raise Exception(str(Config.env) + "")

            # if env_turn and con_turn:
            #     raise Exception("Environment is not setting " + str(Config.env) + " correctly: " + str((src_index, env_behaviour, tgt_index)))

            if env_turn:
                new_src = "st_" + str(src_index)
                new_tgt = "st__" + str(tgt_index)

                if new_src not in int_env_trans.keys():
                    int_env_trans[new_src] = set()

                if not controller:
                    pure_env_action = self.project_out_events(env_cond, prog_out + prog_preds + [Config.env])
                    prog_state_before_env_action = self.project_out_events(env_cond, env_events + [Config.env])

                    if new_src in self.prog_state.keys():
                        if self.prog_state[new_src] != prog_state_before_env_action:
                            if not is_tautology(iff(self.prog_state[new_src], prog_state_before_env_action)):
                                raise Exception(new_src + " already tagged by " + str(self.prog_state[new_src]) + " but now we also need to tag it by " + str(prog_state_before_env_action))

                    if prog_state_before_env_action not in self.env_prog_state.keys():
                        self.env_prog_state[prog_state_before_env_action] = [new_src]
                    else:
                        self.env_prog_state[prog_state_before_env_action].append(new_src)
                    self.prog_state[new_src] = prog_state_before_env_action

                    int_env_trans[new_src].add((pure_env_action, new_tgt))

                    if new_tgt in self.env_transition_tgt.keys():
                        self.env_transition_tgt[new_tgt].append((new_src, pure_env_action))
                    else:
                        self.env_transition_tgt[new_tgt] = [(new_src, pure_env_action)]
                else:
                    env_prog_action = self.project_out_events(env_cond, prog_out + [Config.env])
                    env_prog_action = simplify_formula_without_math(env_prog_action)
                    int_env_trans[new_src].add((env_prog_action, new_tgt))

                    if new_tgt in self.env_transition_tgt.keys():
                        self.env_transition_tgt[new_tgt].append((new_src, env_prog_action))
                    else:
                        self.env_transition_tgt[new_tgt] = [(new_src, env_prog_action)]

                self.states.add(new_src)
                self.states.add(new_tgt)

            if con_turn:
                new_src = "st__" + str(src_index)
                new_tgt = "st_" + str(tgt_index)

                if new_src not in int_con_trans.keys():
                    int_con_trans[new_src] = set()

                con_behaviour = disjunct_formula_set(trans_dict[(src_index, env_behaviour, tgt_index)])
                con_cond = (con_behaviour.simplify()).to_nuxmv()
                con_action = propagate_negations(con_cond)

                if not controller:
                    prog_state_before_con_action = self.project_out_events(propagate_negations(env_behaviour),
                                                                           env_events + [Config.env])

                    # if new_src in self.prog_state.keys():
                    #     # This will happen because env needs to consider all possible controller actions
                    #     if not is_tautology(iff(self.prog_state[new_src], prog_state_before_con_action)):
                    #         raise Exception(new_src + " already tagged by " + str(self.prog_state[new_src]) + " but now we also need to tag it by " + str(prog_state_before_con_action))
                    self.con_transition_tgt[(con_action, new_tgt)] = new_src
                    if prog_state_before_con_action not in self.con_prog_state.keys():
                        self.con_prog_state[prog_state_before_con_action] = [new_src]
                    else:
                        self.con_prog_state[prog_state_before_con_action].append(new_src)

                    self.prog_state[new_src] = prog_state_before_con_action
                    int_con_trans[new_src].add((con_action, new_tgt))

                        # raise Exception("Transition already exists: " + str((con_action, new_tgt)))

                else:
                    prog_outs = self.project_out_events(propagate_negations(env_behaviour),
                                                                           env_events + prog_preds + [Config.env]).simplify()
                    prog_outs = simplify_formula_without_math(prog_outs)
                    # con_transition_tgt[(con_action, new_tgt)] = (new_src, prog_state_before_con_action)
                    int_con_trans[new_src].add((conjunct(con_action, prog_outs), new_tgt))

                    self.con_transition_tgt[(con_action, new_tgt)] = new_src
                self.states.add(new_src)
                self.states.add(new_tgt)

        self.env_transitions = int_env_trans
        self.con_transitions = int_con_trans

        for src, tgts in self.con_transitions.items():
            for _, tgt in tgts:
                if tgt not in self.env_transitions.keys():
                    raise Exception("Controller transition to non-existing environment state: " + str((src, tgt)))

        for src, tgts in self.env_transitions.items():
            for _, tgt in tgts:
                if tgt not in self.con_transitions.keys():
                    raise Exception(
                        "Environment transition to non-existing controller state: " + str((src, tgt)))
                    # print(str(tgt) + " not in env transitions")
                    # mon = MealyMachine("", self.init_st,
                    #                    self.env_events, self.con_events, {}, {})
                    #
                    # mon.add_transitions(controller, trans_dict, resolve_env_turns, env_events,
                    #                     prog_out, prog_preds, con_events)

        # had_an_effect = True
        # while had_an_effect:
        #     had_an_effect = self.minimize_env_states()
        #     had_an_effect = had_an_effect or self.minimize_con_states()

    def minimize_env_states(self):
        had_an_effect = False
        #if env_states have the same program state and the same outgoing transitions, then merge them
        for prog_state, srcs in self.env_prog_state.items():
            tgts_map = {}
            for src, tgts in self.env_transitions.items():
                if src in srcs:
                    frozen_tgts = frozenset(tgts)
                    if frozen_tgts not in tgts_map.keys():
                        tgts_map[frozen_tgts] = [src]
                    else:
                        tgts_map[frozen_tgts].append(src)

            for _, srcs in tgts_map.items():
                if len(srcs) > 1:
                    for src in srcs[1:]:
                        self.env_transitions.pop(src)
                        self.states.remove(src)

                    all_con_transitions = self.con_transitions.items()
                    for con_src, con_tgts in all_con_transitions:
                        all_conds = []
                        new_con_tgts = set()
                        for (con_cond, env_tgt) in con_tgts:
                            if env_tgt in srcs:
                                had_an_effect = True
                                all_conds.append(con_cond)
                            else:
                                new_con_tgts.add((con_cond, env_tgt))
                        if len(all_conds) > 0:
                            self.con_transitions[con_src] = new_con_tgts
                            new_cond = disjunct_formula_set(all_conds)
                            new_cond = simplify_formula_without_math(new_cond)
                            self.con_transitions[con_src].add((new_cond, srcs[0]))
        return had_an_effect
    def minimize_con_states(self):
        had_an_effect = False
        # if con_states have the same program state and the same outgoing transitions, then merge them
        for prog_state, srcs in self.con_prog_state.items():
            tgts_map = {}
            for src, tgts in self.con_transitions.items():
                if src in srcs:
                    frozen_tgts = frozenset(tgts)
                    if frozen_tgts not in tgts_map.keys():
                        tgts_map[frozen_tgts] = [src]
                    else:
                        tgts_map[frozen_tgts].append(src)

            for _, srcs in tgts_map.items():
                if len(srcs) > 1:
                    for src in srcs[1:]:
                        self.con_transitions.pop(src)
                        self.states.remove(src)

                    all_env_transitions = self.env_transitions.items()
                    for con_src, con_tgts in all_env_transitions:
                        all_conds = []
                        new_con_tgts = set()
                        for (con_cond, env_tgt) in con_tgts:
                            if env_tgt in srcs:
                                had_an_effect = True
                                all_conds.append(con_cond)
                            else:
                                new_con_tgts.add((con_cond, env_tgt))
                        if len(all_conds) > 0:
                            self.env_transitions[con_src] = new_con_tgts
                            new_cond = disjunct_formula_set(all_conds)
                            new_cond = simplify_formula_without_math(new_cond)
                            self.env_transitions[con_src].add((new_cond, srcs[0]))
        return had_an_effect
        # #     #TODO this optimisation needs to move to minimize function, cannot do it before constructing the whole mealy machine.
        # if (con_action, new_tgt) in con_transition_tgt.keys() and \
        #         prog_state_before_con_action == self.prog_state[con_transition_tgt[(con_action, new_tgt)]]:
        #     if new_src in self.env_transition_tgt.keys():
        #         prev_env_trans = self.env_transition_tgt[new_src]
        #         self.env_transition_tgt.pop(new_src)
        #     else:
        #         prev_env_trans = []
        #
        #     old_env_tgt = new_src
        #     new_src = con_transition_tgt[(con_action, new_tgt)]
        #     new_env_trans = []
        #     for (src, env_cond_without_turn_var) in prev_env_trans:
        #         int_env_trans[src].remove((env_cond_without_turn_var, old_env_tgt))
        #         int_env_trans[src].add((env_cond_without_turn_var, new_src))
        #         new_env_trans.append((env_cond_without_turn_var, new_src))
        #
        #     if new_src in self.env_transition_tgt.keys():
        #         self.env_transition_tgt[new_src] += new_env_trans
        #     else:
        #         self.env_transition_tgt[new_src] = new_env_trans

    def project_out_events(self, env_cond: Formula, env_events: [Variable]):
        return simplify_formula_without_math(project_out_vars(env_cond, env_events))

        # in_cnf = cnf(env_cond)
        # if isinstance(in_cnf, BiOp) and in_cnf.op[0] == "&":
        #     conjuncts = in_cnf.sub_formulas_up_to_associativity()
        # else:
        #     conjuncts = [in_cnf]
        #
        # new_conjuncts = []
        # for conjunct in conjuncts:
        #     if isinstance(conjunct, BiOp) and conjunct.op[0] == "|":
        #         disjuncts = conjunct.sub_formulas_up_to_associativity()
        #     else:
        #         disjuncts = [conjunct]
        #
        #     new_disjuncts = []
        #     for disjunct in disjuncts:
        #         if not(isinstance(disjunct, Variable) and disjunct in env_events):
        #             if not(isinstance(disjunct, UniOp) and disjunct.right in env_events):
        #                 new_disjuncts.append(disjunct)
        #
        #     if len(new_disjuncts) > 0:
        #         new_conjunct = disjunct_formula_set(new_disjuncts)
        #         new_conjuncts.append(new_conjunct)
        #
        # new_formula = conjunct_formula_set(new_conjuncts)
        # alternate_new_formula = project_out_vars(env_cond, env_events)
        #
        # if not is_tautology(iff(new_formula, alternate_new_formula)):
        #     raise Exception("Formula " + str(env_cond) + " projected out " + str(env_events) + " is " + str(new_formula) + " but should be " + str(alternate_new_formula))
        # return new_formula


    def __str__(self):
        return str(self.to_dot())

    def to_dot(self, pred_list: [Formula] = None):
        to_replace = []
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace += [BiOp(pred_var, ":=", pred)]


        dot = Digraph(name="MealyMachine",
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"),  # ("rankdir", "LR"),
                                  ("ranksep", "0.8"),
                                  ("nodesep", "0.5")],
                      node_attr=[("shape", "circle")],
                      edge_attr=[("fontname", "mono")],
                      engine='dot',
                      format='svg')

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            if s in self.prog_state.keys():
                prog_state = self.prog_state[s]
                dot.node(str(s), str(prog_state))
            else:
                dot.node(str(s))

        dot.edge("init", str(self.init_st), style="solid")

        for src in self.env_transitions.keys():
            for (beh, tgt) in self.env_transitions.get(src):
                label = str(beh.replace(to_replace))
                dot.edge(str(src), str(tgt), label)

        for src in self.con_transitions.keys():
            for (beh, tgt) in self.con_transitions.get(src):
                label = str(beh.replace(to_replace))
                dot.edge(str(src), str(tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(self, mon_states, mon_out_events, state_pred_list, trans_pred_list):
        state_pred_acts = [label_pred(p, state_pred_list) for p in state_pred_list]
        trans_pred_acts = [label_pred(p, trans_pred_list) for p in trans_pred_list]
        pred_acts = state_pred_acts + trans_pred_acts

        mon_events = mon_out_events \
                     + [Variable(s) for s in mon_states]

        new_mon_events = [BiOp(m, ":=", Variable("mon_" + m.name)) for m in mon_events] \
                         + [BiOp(m, ":=", Variable(m.name)) for m in pred_acts]

        guards_acts = {}

        init_conds = []

        for (env_beh, tgt) in self.env_transitions.get(self.init_st):
            formula_set = [env_beh.replace(new_mon_events), Variable(tgt), self.prog_state[tgt].replace(new_mon_events),
                           conjunct_formula_set([neg(Variable(s)) for s in self.states if s != tgt])]
            init_conds += [conjunct_formula_set(formula_set)]

        init_cond = disjunct_formula_set(init_conds)
        for src in self.con_transitions.keys():
            for (con_behaviour, con_tgt) in self.con_transitions[src]:
                guard = "turn = mon_env & " + str(src)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()
                act = "next(" + str(con_behaviour.to_nuxmv()) + " & "\
                        + str(self.prog_state[con_tgt].replace(new_mon_events).to_nuxmv()) + " & " + str(con_tgt) + ")"
                act += " & next(" + " & ".join(["!" + s for s in self.states if s != con_tgt]) + ")"
                guards_acts[guard].append(act)
                if (con_tgt not in self.env_transitions.keys()) or len(self.env_transitions.get(con_tgt)) == 0:
                    raise Exception("Nothing to do in counter-strategy from state " + str(con_tgt))

        for src in self.env_transitions.keys():
            for (env_beh, env_tgt) in self.env_transitions.get(src):
                guard = "turn = mon_con & " + str(src)
                if guard not in guards_acts.keys():
                    guards_acts[guard] = list()

                act = conjunct_formula_set([UniOp("next", env_beh),
                                            UniOp("next", self.prog_state[env_tgt].replace(new_mon_events)),
                                            UniOp("next", Variable(env_tgt)),
                                            UniOp("next", conjunct_formula_set([neg(Variable(s)) for s in self.states if s != env_tgt]))]).to_nuxmv()
                guards_acts[guard].append(str(act))

        define = []
        transitions = []
        guard_ids = []
        i = 0
        guard_keys = list(guards_acts.keys())
        while i < len(guard_keys):
            define += [self.name + "_guard_" + str(i) + " := " + guard_keys[i]]
            define += [
                self.name + "_act_" + str(i) + " := (" + ")\n\t| \t(".join(map(str, guards_acts[guard_keys[i]])) + ")"]
            transitions.append(self.name + "_guard_" + str(i) + " & " + self.name + "_act_" + str(i))
            guard_ids.append(self.name + "_guard_" + str(i))
            i += 1

        identity = []
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["next(" + str(event) + ") = " + str(event) for event in (self.env_events + self.con_events) if
                     Variable(str(event)) not in (mon_events + pred_acts)]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # transitions.append("!(" + " | ".join(guard_ids) + ") & identity_" + self.name + "& next(mismatch)")

        vars = ["turn : {env, mon_env, con, mon_con}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [str(var) + " : boolean" for var in self.env_events if
                 str(var) not in [str(v) for v in (mon_events + pred_acts)]]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["mon_" + str(var) + " : boolean" for var in mon_events]
        vars += [str(var) + " : boolean" for var in pred_acts]

        init = [str(init_cond)]
        transitions = ["((" + ")\n\t|\t(".join(transitions) + "))"]

        identity = "((turn = env | turn = con) -> (identity_" + self.name + " & " + str(conjunct_formula_set(
            [BiOp(UniOp("next", Variable("mon_" + e.name)), "=", Variable("mon_" + e.name)) for e in
             mon_events] +
            [BiOp(UniOp("next", Variable(p.name)), "=", Variable(p.name)) for p in
             pred_acts]).to_nuxmv()) + "))"

        trans = ["(" + identity + " &\n\t\t(!(turn = env | turn = con) -> (" + ")\n\t|\t(".join(transitions) + ")))"]
        invar = []

        return NuXmvModel(self.name, set(vars), define, init, invar, trans)

    def fill_in_predicates_at_controller_states_label_tran_preds_appropriately(self, predicate_abstraction, program):
        symbol_table = program.symbol_table | {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                         program.valuation}

        new_con_transitions = {k:{} for k, _ in self.con_transitions.items()}
        new_env_transitions = {k:{} for k, _ in self.env_transitions.items()}

        smt_checker = SMTChecker()

        pred_list = predicate_abstraction.state_predicates + predicate_abstraction.transition_predicates

        replace_preds = []
        i = 0
        for p in pred_list:
            label = label_pred(p, pred_list)
            replace_preds.append(BiOp(Variable(label.name), ":=", p))
            i += 1

        at_least_one_state = disjunct_formula_set([Variable(q) for q in program.states])

        at_most_one_state = conjunct_formula_set([BiOp(Variable(q), "=>",
                                                       conjunct_formula_set([neg(Variable(r))
                                                                             for r in program.states
                                                                             if r != q]))
                                                  for q in program.states])
        current_states = []
        done_states = []

        abstraction = predicate_abstraction.abstraction

        for (m_cond, mm_tgt) in self.env_transitions[self.init_st]:
            for pa_t in abstraction.state_to_env[abstraction.initial_state]:
                formula = conjunct_formula_set(
                    [m_cond.replace(replace_preds), pa_t.condition, at_least_one_state, at_most_one_state,
                     Variable(pa_t.tgt.state)] +
                    pa_t.tgt.predicates +
                    pa_t.output).replace(replace_preds)
                formula_smt = And(*formula.to_smt(symbol_table))
                compatible = smt_checker.check(formula_smt)
                if compatible:
                    current_states.append((mm_tgt, pa_t.tgt))
                    new_env_transitions[self.init_st][(m_cond, mm_tgt)] = {}

        done_states += [(self.init_st, abstraction.initial_state)]

        # TODO this needs to be optimised
        while len(current_states) > 0:
            next_states = []
            for (mm_con_src, pa_con_src) in current_states:
                tentative_con_trans = []
                for (mm_con_cond, mm_con_tgt) in self.con_transitions[mm_con_src]:
                    # TODO this can be optimised by keeping a cache
                    for pa_con_t in abstraction.state_to_con[pa_con_src]:
                        formula = conjunct_formula_set(
                            [mm_con_cond.replace(replace_preds), pa_con_t.condition]).replace(replace_preds)
                        formula_smt = And(*formula.to_smt(symbol_table))
                        compatible = smt_checker.check(formula_smt)
                        if compatible:
                            tentative_con_trans.append((mm_con_cond, mm_con_tgt, pa_con_t))

                for (mm_con_cond, mm_con_tgt, pa_con_t) in tentative_con_trans:
                    (mm_env_src, pa_env_src) = (mm_con_tgt, pa_con_t.tgt)
                    for (mm_env_cond, mm_env_tgt) in self.env_transitions[mm_env_src]:
                        for pa_env_t in abstraction.state_to_env[pa_env_src]:
                            try:
                                f_trans_preds = tran_and_state_preds_after_con_env_step(pa_env_t)
                                formula2 = conjunct_formula_set([mm_env_cond.replace(replace_preds)] +
                                                                [pa_env_t.condition] +
                                                                pa_env_t.output +
                                                                [Variable(pa_env_t.tgt.state)] +
                                                                [at_least_one_state] +
                                                                [at_most_one_state] +
                                                                f_trans_preds)
                                formula2_smt = And(*formula2.to_smt(symbol_table))
                                compatible = smt_checker.check(formula2_smt)
                                if compatible:
                                    next_states.append((mm_env_tgt, pa_env_t.tgt))
                                    if (mm_con_cond, mm_con_tgt) not in new_con_transitions[mm_con_src].keys():
                                        new_con_transitions[mm_con_src][(mm_con_cond, mm_con_tgt)] = set()
                                    new_con_transitions[mm_con_src][(mm_con_cond, mm_con_tgt)] |= {conjunct_formula_set([Variable(pa_env_src.state)] + [label_pred(p, pred_list) for p in pa_env_t.src.predicates])}

                                    # TODO repair transition predicates
                                    new_env_transitions[mm_env_src][(mm_env_cond, mm_env_tgt)] = {}
                            except Exception as e:
                                raise e

            done_states += [str(s) for s in current_states]
            current_states = set([x for x in next_states if str(x) not in done_states])

        proper_con_transitions = {k:set() for (k, _) in new_con_transitions.items()}
        for k, dict in new_con_transitions.items():
            for (mm_con_cond, mm_con_tgt) in dict.keys():
                proper_con_transitions[k] |= {(conjunct(mm_con_cond, disjunct_formula_set(dict[(mm_con_cond, mm_con_tgt)])), (mm_con_tgt))}

        return MealyMachine(self.name, self.init_st, self.env_events, self.con_events, self.env_transitions, proper_con_transitions)

    # TODO this function needs to be optimised
    def project_controller_on_program(self, name, program, predicate_abstraction: PredicateAbstraction, symbol_table,
                                      program_on_env_side=True, mealy_machine_events_on_transitions=True):
        symbol_table |= {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                         program.valuation}

        new_env_transitions = set()
        new_con_transitions = set()

        smt_checker = SMTChecker()

        pred_list = predicate_abstraction.state_predicates + predicate_abstraction.transition_predicates

        replace_preds = []
        i = 0
        for p in pred_list:
            label = label_pred(p, pred_list)
            replace_preds.append(BiOp(Variable(label.name), ":=", p))
            i += 1

        at_least_one_state = disjunct_formula_set([Variable(q) for q in program.states])

        at_most_one_state = conjunct_formula_set([BiOp(Variable(q), "=>",
                                                       conjunct_formula_set([neg(Variable(r))
                                                                             for r in program.states
                                                                             if r != q]))
                                                  for q in program.states])
        current_states = []
        done_states = []

        # abstraction = predicate_abstraction.simplified_transitions_abstraction()
        abstraction = predicate_abstraction.abstraction

        for (m_cond, mm_tgt) in self.env_transitions[self.init_st]:
            for pa_t in abstraction.state_to_env[abstraction.initial_state]:
                formula = conjunct_formula_set(
                    [m_cond.replace(replace_preds), pa_t.condition, at_least_one_state, at_most_one_state,
                     Variable(pa_t.tgt.state)] +
                    pa_t.tgt.predicates +
                    pa_t.output)
                formula_smt = And(*formula.to_smt(symbol_table))
                compatible = smt_checker.check(formula_smt)
                if compatible:
                    new_env_transitions \
                        .add(
                        Transition((self.init_st, abstraction.initial_state),
                                   pa_t.condition if not mealy_machine_events_on_transitions else m_cond.replace(replace_preds),
                                   pa_t.action,
                                   pa_t.output, (mm_tgt, pa_t.tgt)))
                    current_states.append((mm_tgt, pa_t.tgt))

        done_states += [(self.init_st, abstraction.initial_state)]

        # TODO this needs to be optimised
        while len(current_states) > 0:
            next_states = []
            for (mm_con_src, pa_con_src) in current_states:
                tentative_con_trans = []
                for (mm_con_cond, mm_con_tgt) in self.con_transitions[mm_con_src]:
                    # TODO this can be optimised by keeping a cache
                    for pa_con_t in abstraction.state_to_con[pa_con_src]:
                        formula = conjunct_formula_set(
                            [mm_con_cond.replace(replace_preds), pa_con_t.condition])
                        formula_smt = And(*formula.to_smt(symbol_table))
                        compatible = smt_checker.check(formula_smt)
                        if compatible:
                            tentative_con_trans.append(
                                Transition((mm_con_src, pa_con_src),
                                           mm_con_cond,
                                           pa_con_t.action, pa_con_t.output,
                                           (mm_con_tgt, pa_con_t.tgt)))

                for mm_con_trans in tentative_con_trans:
                    (mm_env_src, pa_env_src) = mm_con_trans.tgt
                    for (mm_env_cond, mm_env_tgt) in self.env_transitions[mm_env_src]:
                        for pa_env_t in abstraction.state_to_env[pa_env_src]:
                            try:
                                f_trans_preds = tran_and_state_preds_after_con_env_step(pa_env_t)
                                formula2 = conjunct_formula_set([mm_env_cond.replace(replace_preds)] +
                                                                [pa_env_t.condition] +
                                                                pa_env_t.output +
                                                                [Variable(pa_env_t.tgt.state)] +
                                                                [at_least_one_state] +
                                                                [at_most_one_state] +
                                                                f_trans_preds)
                                formula2_smt = And(*formula2.to_smt(symbol_table))
                                compatible = smt_checker.check(formula2_smt)
                                if compatible:
                                    next_states.append((mm_env_tgt, pa_env_t.tgt))
                                    new_con_transitions.add(mm_con_trans)
                                    new_env_transitions.add(
                                        Transition((mm_env_src, pa_env_src),
                                                   pa_env_t.condition if not mealy_machine_events_on_transitions else mm_env_cond.replace(replace_preds),
                                                   pa_env_t.action,
                                                   pa_env_t.output, (mm_env_tgt, pa_env_t.tgt)))
                            except Exception as e:
                                raise e

            done_states += [str(s) for s in current_states]
            current_states = set([x for x in next_states if str(x) not in done_states])

        # TODO need to check that if counter-strategy, then it s complete for controller
        #  and if strategy then complete for environment

        return Program(name, [s for t in (new_con_transitions | new_env_transitions) for s in [t.src, t.tgt]],
                       (self.init_st, abstraction.initial_state),
                       program.valuation + (([TypedValuation(s, "bool", None) for s in program.states] + [TypedValuation(t.name + "_prev", t.type, t.value) for t in program.valuation]) if mealy_machine_events_on_transitions else []),
                       list(set(new_env_transitions)), list(set(new_con_transitions)),
                       abstraction.env_events, abstraction.con_events,
                       abstraction.out_events, False)

