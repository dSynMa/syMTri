from graphviz import Digraph
from pysmt.shortcuts import And

from programs.analysis.nuxmv_model import NuXmvModel
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.typed_valuation import TypedValuation
from programs.util import label_pred
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set, neg, conjunct, mutually_exclusive_rules
from prop_lang.variable import Variable


class MealyMachine:
    def __init__(self, name, init_st: int, env_events, con_events):
        self.name = name
        self.states = {"st_" + str(init_st)}
        self.init_st = "st_" + str(init_st)
        self.env_events = env_events
        self.con_events = con_events
        self.env_transitions = {}
        self.con_transitions = {}
        self.counter = -1

    def add_transitions(self, trans_dict: dict):
        int_st_index = 0
        env_interm_states = {}
        for src_index, env_behaviour, tgt_index in trans_dict.keys():
            new_src = "st_" + str(src_index)

            env_cond = (env_behaviour.simplify()).to_nuxmv()

            con_behaviour = disjunct_formula_set(trans_dict[(src_index, env_behaviour, tgt_index)])
            con_cond = (con_behaviour.simplify()).to_nuxmv()
            new_tgt = "st_" + str(tgt_index)

            if new_src not in self.env_transitions.keys():
                self.env_transitions[new_src] = set()

            if (src_index, env_behaviour) in env_interm_states.keys():
                new_intermed = env_interm_states.get((src_index, env_behaviour))
            else:
                new_intermed = "st__" + str(int_st_index)
                env_interm_states[(src_index, env_behaviour)] = new_intermed
                int_st_index += 1
                self.con_transitions[new_intermed] = set()

            if (env_cond, new_intermed) not in self.env_transitions[new_src]:
                self.env_transitions[new_src].add((env_cond, new_intermed))

            if (con_cond, new_tgt) not in self.con_transitions[new_intermed]:
                self.con_transitions[new_intermed] |= {(con_cond, new_tgt)}

            self.states.add(new_intermed)
            self.counter = self.counter - 1
            self.states.add(new_src)
            self.states.add(new_tgt)

    def to_dot(self, pred_list: [Formula]):
        to_replace = []
        if pred_list is not None:
            for pred in pred_list:
                pred_var = label_pred(pred, pred_list)
                to_replace += [BiOp(pred_var, ":=", pred)]

        dot = Digraph(name="MealyMachine",
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"), #("rankdir", "LR"),
                                  ("ranksep", "0.8"),
                                  ("nodesep", "0.5")],
                      node_attr=[("shape", "circle")],
                      edge_attr=[("fontname", "mono")],
                      engine='dot',
                      format='svg')

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
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
        init_conds = []

        for (env_beh, tgt) in self.env_transitions.get(self.init_st):
            formula_set = [env_beh.replace(new_mon_events), Variable(tgt)]
            init_conds += [conjunct_formula_set(formula_set)]

        init_cond = disjunct_formula_set(init_conds)

        guards = []
        acts = []

        for src in self.con_transitions.keys():
            for (con_behaviour, con_tgt) in self.con_transitions[src]:
                guard = "turn = con & " + str(src) + " & " \
                        + str(con_behaviour.to_nuxmv())

                if len(self.env_transitions.get(con_tgt)) == 0:
                    raise Exception("Nothing to do in counter-strategy from state " + str(con_tgt))

                for (env_beh, env_tgt) in self.env_transitions.get(con_tgt):
                    act = conjunct_formula_set([UniOp("next", env_beh.replace(new_mon_events)),
                                                UniOp("next", Variable(env_tgt))])
                    guards.append(guard)
                    acts.append(str(act))

        define = []
        transitions = []
        guard_ids = []
        i = 0
        while i < len(guards):
            define += [self.name + "_guard_" + str(i) + " := " + guards[i]]
            define += [self.name + "_act_" + str(i) + " := " + acts[i]]
            transitions.append("(" + self.name + "_guard_" + str(i) + " & " + self.name + "_act_" + str(i) + ")")
            guard_ids.append(self.name + "_guard_" + str(i))
            i += 1

        identity = []
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["next(" + str(event) + ") = " + str(event) for event in (self.env_events + self.con_events) if
                     Variable(str(event)) not in (mon_events + pred_acts)]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # transitions.append("!(" + " | ".join(guard_ids) + ") & identity_" + self.name + "& next(mismatch)")

        vars = ["turn : {env, mon, con}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [str(var) + " : boolean" for var in self.env_events if
                 str(var) not in [str(v) for v in (mon_events + pred_acts)]]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["mon_" + str(var) + " : boolean" for var in mon_events]
        vars += [str(var) + " : boolean" for var in pred_acts]

        init = [str(init_cond)]
        transitions += ["turn != con & (identity_" + self.name + " & " + str(conjunct_formula_set(
            [BiOp(UniOp("next", Variable("mon_" + e.name)), "=", Variable("mon_" + e.name)) for e in mon_events] +
            [BiOp(UniOp("next", Variable(p.name)), "=", Variable(p.name)) for p in pred_acts]).to_nuxmv()) + ")"]
        trans = ["(" + ")\n\t|\t(".join(transitions) + ")"]
        invar = mutually_exclusive_rules(self.states)
        invar += mutually_exclusive_rules(["mon_" + s for s in mon_states])
        invar += [str(disjunct_formula_set([Variable(str(s)) for s in self.states]))]
        j = 0
        while j < len(trans_pred_acts):
            invar += [str(neg(conjunct(trans_pred_acts[j], trans_pred_acts[j + 1])))]
            j += 2

        return NuXmvModel(self.name, set(vars), define, init, invar, trans)

    # TODO this function needs to be optimised
    def project_controller_on_program(self, program, predicate_abstraction: Program, pred_list, symbol_table):
        symbol_table |= {tv.name + "_prev": TypedValuation(tv.name + "_prev", tv.type, tv.value) for tv in
                         program.valuation}

        new_env_transitions = []
        new_con_transitions = []

        current_states = [(self.init_st, predicate_abstraction.initial_state)]
        done_states = []

        smt_checker = SMTChecker()

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

        while len(current_states) > 0:
            next_states = []
            for (mm_s, p_s) in current_states:
                env_states = []
                for (m_cond, m_tgt) in self.env_transitions[mm_s]:
                    for p_t in predicate_abstraction.env_transitions:
                        if p_t.src == p_s:
                            formula = conjunct_formula_set(
                                [m_cond.replace(replace_preds), p_t.condition, Variable(p_t.tgt.state),
                                 at_least_one_state,
                                 at_most_one_state] + list(p_t.tgt.predicates) + p_t.output)
                            formula = And(*formula.to_smt(symbol_table))
                            compatible = smt_checker.check(formula)
                            if compatible:
                                env_states.append((m_tgt, p_t.tgt))
                                new_env_transitions.append(p_t)

                for (m_env_tgt, p_env_tgt) in env_states:
                    for (m_cond, m_tgt) in self.con_transitions[m_env_tgt]:
                        for p_t in predicate_abstraction.con_transitions:
                            if p_t.src == p_env_tgt:
                                formula2 = conjunct_formula_set([m_cond, p_t.condition])
                                formula2 = And(*formula2.to_smt(symbol_table))
                                compatible = smt_checker.check(formula2)
                                if compatible:
                                    next_states.append((m_tgt, p_t.tgt))
                                    new_con_transitions.append(p_t)

            done_states += current_states
            current_states = set([x for x in next_states if x not in done_states])

        predicate_abstraction.new_env_transitions = new_env_transitions
        predicate_abstraction.con_transitions = new_con_transitions
        return Program("Strategy", predicate_abstraction.states, predicate_abstraction.initial_state,
                       predicate_abstraction.valuation, list(set(new_env_transitions)), list(set(new_con_transitions)),
                       predicate_abstraction.env_events, predicate_abstraction.con_events,
                       predicate_abstraction.out_events)
