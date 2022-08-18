from typing import Set

from graphviz import Digraph

from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import neg, disjunct_formula_set
from prop_lang.variable import Variable


class Program:

    def __init__(self, name, sts, init_st, init_val: [TypedValuation],
                 env_transitions: [Transition], con_transitions: [Transition],
                 env_events: [Variable], con_events: [Variable], mon_events: [Variable]):
        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.local_vars = [Variable(tv.name) for tv in init_val]
        self.env_transitions = env_transitions
        self.state_to_env = lambda s: [t for t in env_transitions if t.src == s]
        self.state_to_con = lambda s: [t for t in con_transitions if t.src == s]
        # type checking
        for transition in env_transitions:
            if not all(v in env_events + self.local_vars for v in transition.condition.variablesin()):
                raise Exception("Conditions in environment transitions can only refer to environment events and "
                                "local/internal variables: " + str(transition) + ".")

            if not all(biop.left in self.local_vars for biop in transition.action):
                raise Exception("Actions in environment transitions can only set "
                                "local/internal variables: " + str(transition) + ".")
            if not all(v in env_events + self.local_vars for biop in transition.action for v in
                       biop.right.variablesin()):
                raise Exception("Actions in environment transitions can only refer to environment or "
                                "local/internal variables: " + str(transition) + ".")
            if not all(v.left in mon_events for v in transition.output):
                raise Exception("Outputs of environment transitions can only refer to monitor output variables: " + str(
                    transition) + ".")

        self.con_transitions = con_transitions
        for transition in con_transitions:
            if not all(v in con_events + self.local_vars for v in transition.condition.variablesin()):
                raise Exception("Conditions in controller transitions can only refer to controller events and "
                                "local/internal variables: " + str(transition) + ".")

            if not all(biop.left in self.local_vars for biop in transition.action):
                raise Exception("Actions in controller transitions can only set "
                                "local/internal variables: " + str(transition) + ".")
            if not all(v in con_events + self.local_vars for biop
                       in transition.action for v in biop.right.variablesin() in self.local_vars):
                raise Exception("Actions in controller transitions can only refer to environment or"
                                "local/internal variables: " + str(transition) + ".")

        self.valuation = init_val
        self.env_events = env_events
        self.con_events = con_events
        self.mon_events = mon_events

    def add_env_transition(self, src, condition: Formula, action: [BiOp], output: [BiOp], tgt):
        assert {x.left for x in output}.issubset(self.mon_events)
        self.env_transitions.append(Transition(src, condition, action, tgt))
        self.states.add(src)
        self.states.add(tgt)

    def add_con_transition(self, src, condition: Formula, action: Formula, output: [BiOp], tgt):
        assert {x.left for x in output}.issubset(self.mon_events)
        self.con_transitions.append(Transition(src, condition, action, output, tgt))
        self.states.add(src)
        self.states.add(tgt)

    def to_dot(self):
        dot = Digraph(name=self.name,
                      graph_attr=[("overlap", "scalexy"), ("splines", "true"), ("rankdir", "LR"), ("ranksep", "0.8"),
                                  ("nodesep", "0.5")],
                      node_attr=[("shape", "circle")],
                      edge_attr=[("fontname", "mono")],
                      engine='dot',
                      format='svg')

        dot.node("init", "", [("shape", "point")])
        for s in self.states:
            dot.node(str(s))

        dot.edge("init", str(self.initial_state), style="solid")

        for t in self.env_transitions:
            if t.output is None:
                outputs = ""
            else:
                outputs = str(t.output)

            label = str(t.condition) + "\n>> " + str(t.action) + "\n>> " + outputs
            dot.edge(str(t.src), str(t.tgt), label)

        for t in self.con_transitions:
            if t.output is None:
                outputs = ""
            else:
                outputs = str(t.output)

            label = str(t.condition) + "\n>> " + str(t.action) + "\n>> " + outputs
            dot.edge(str(t.src), str(t.tgt), label, "style=dotted")

        return dot

    def to_nuXmv_with_turns(self):
        guards = []
        acts = []
        for env_transition in self.env_transitions:
            guard = "env & " + env_transition.src + " & " \
                    + str(env_transition.condition.to_nuxmv())

            act = self.only_this_state_next(env_transition.tgt) \
                  + "".join([" & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv()) for act in
                             self.complete_action_set(env_transition.action)]) \
                  + "".join([" & next(" + str(assignment.left) + ") = " + str(assignment.right.to_nuxmv()) for assignment in
                             env_transition.output]) \
                  + "".join([" & !next(" + str(event) + ")" for event in self.mon_events
                             if event not in [out.left for out in env_transition.output]])
            guards.append(guard)
            acts.append(act)

        for con_transition in self.con_transitions:
            guard = "!env & " + con_transition.src + " & " \
                    + str(con_transition.condition.to_nuxmv())

            # updated_variables = [str(act.left) for act in con_transition.action]
            act = self.only_this_state_next(con_transition.tgt) \
                  + "".join([" & next(" + str(act.left) + ") = " + str(act.right.to_nuxmv()) for act in
                             self.complete_action_set(con_transition.action)]) \
                  + "".join([" & !next(" + str(event) + ")"
                             for event in self.mon_events])
            guards.append(guard)
            acts.append(act)

        define = []
        transitions = []
        guard_ids = []
        i = 0
        while i < len(guards):
            define += ["guard_" + str(i) + " := " + guards[i]]
            define += ["act_" + str(i) + " := next(env) = !env & " + acts[i]]
            transitions.append("(guard_" + str(i) + " & " + "act_" + str(i) + ")")
            guard_ids.append("guard_" + str(i))
            i += 1

        identity = ["next(env) = !env"]
        for typed_val in self.valuation:
            identity.append("next(" + str(typed_val.name) + ") = " + str(typed_val.name))
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["!next(" + str(event) + ")" for event in self.mon_events]

        define += ["identity_" + self.name + " := " + " & ".join(identity)]

        # if no guard holds, then keep the same state and output no monitor events
        transitions.append("!(" + " | ".join(guard_ids) + ") & identity_" + self.name)

        vars = ["env : boolean"]
        vars += [str(st) + " : boolean" for st in self.states]
        vars += [str(val.name) + " : " + str(val.type) for val in self.valuation]
        vars += [str(var) + " : boolean" for var in self.env_events]
        vars += [str(var) + " : boolean" for var in self.con_events]
        vars += [str(var) + " : boolean" for var in self.mon_events]

        init = [self.only_this_state(self.initial_state)]
        init += [str(val.name) + " = " + str(val.value) for val in self.valuation]
        init += ["!" + str(event) for event in self.mon_events]
        init += ["env"]
        trans = ["\n\t|\t".join(transitions)]

        return self.name, vars, define, init, trans

    def only_this_state(self, state):
        only_this_state = str(state)
        for other in self.states:
            if other != state:
                only_this_state += " & !(" + str(other) + ")"
        return only_this_state

    def only_this_state_next(self, state):
        only_this_state = "next(" + str(state) + ")"
        for other in self.states:
            if other != state:
                only_this_state += " & !next(" + str(other) + ")"
        return only_this_state

    def complete_transitions(self):
        complete_env = []
        complete_con = []

        for s in self.states:
            env_from_s = [t for t in self.env_transitions if t.src == s]
            conds_env = [t.condition for t in env_from_s]
            env_from_s += [Transition(s, neg(disjunct_formula_set(conds_env)), [], [], s)]
            complete_env += env_from_s

            con_from_s = [t for t in self.con_transitions if t.src == s]
            conds_con = [t.condition for t in con_from_s]
            con_from_s += [Transition(s, neg(disjunct_formula_set(conds_con)), [], [], s)]
            complete_con += con_from_s

        return complete_env, complete_con


    def complete_action_set(self, actions: [BiOp]):
        non_updated_vars = [tv.name for tv in self.valuation if tv.name not in [str(act.left) for act in actions]]
        return actions + [BiOp(Variable(var), "=", Variable(var)) for var in non_updated_vars]
