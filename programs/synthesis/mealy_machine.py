from graphviz import Digraph

from programs.analysis.nuxmv_model import NuXmvModel
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, disjunct_formula_set, neg, push_negation
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

    def add_transition(self, src: int, env_behaviour: Formula, con_behaviour: Formula, tgt: int):
        new_src = "st_" + str(src)
        new_tgt = "st_" + str(tgt)
        new_intermed = "st_" + str(self.counter) + "_" + str(src) + "_" + str(tgt)

        env_cond = (env_behaviour.simplify()).to_nuxmv()
        con_cond = (con_behaviour.simplify()).to_nuxmv()

        if new_src in self.env_transitions.keys():
            self.env_transitions[new_src].append((env_cond, new_intermed))
        else:
            self.env_transitions[new_src] = [(env_cond, new_intermed)]
        assert new_intermed not in self.con_transitions.keys()
        self.con_transitions[new_intermed] = [(con_cond, new_tgt)]

        self.states.add(new_intermed)
        self.counter = self.counter - 1
        self.states.add(new_src)
        self.states.add(new_tgt)

    def to_dot(self):
        dot = Digraph(name="MealyMachine",
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"), ("rankdir", "LR"), ("ranksep", "0.8"),
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
                label = str(beh)
                dot.edge(str(src), str(tgt), label)

        for src in self.con_transitions.keys():
            for (beh, tgt) in self.con_transitions.get(src):
                label = str(beh)
                dot.edge(str(src), str(tgt), label, style="dotted")

        return dot

    def to_nuXmv_with_turns(self, mon_events):
        new_mon_events = [BiOp(m, ":=", Variable("mon_" + m.name)) for m in mon_events]
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

        identity += ["!next(" + str(event) + ")" for event in self.env_events if Variable(str(event)) not in mon_events]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # if no guard holds, then keep the same state and output no monitor events
        transitions.append("!(" + " | ".join(guard_ids) + ") & identity_" + self.name)

        vars = ["turn : {env, mon, con}"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += ["mon_" + str(var) + " : boolean" for var in mon_events]

        init = [str(init_cond)]
        trans = ["(" + ")\n\t|\t(".join(transitions) + ")"]
        trans += ["turn != con -> (identity_" + self.name + " & " + str(conjunct_formula_set([BiOp(UniOp("next", "mon_" + e.name), "=", Variable("mon_" + e.name)) for e in mon_events])) + ")"]
        invar = [str(s) + " -> " + str(conjunct_formula_set([neg(ss) for ss in self.states if ss != s])) for s in self.states]
        invar += [str(disjunct_formula_set([Variable(str(s)) for s in self.states]))]

        return NuXmvModel(self.name, vars, define, init, invar, trans)
