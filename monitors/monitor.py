from functools import reduce
from typing import Set

from graphviz import Digraph

from monitors.transition import Transition
from monitors.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import project, conjunct, neg, disjunct, G, implies, X, true
from prop_lang.value import Value
from prop_lang.variable import Variable


class Monitor:

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
                raise Exception("Actions in environment transitions can only refer to environment or"
                                "local/internal variables: " + str(transition) + ".")
            if not all(v in mon_events for v in transition.output):
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

            if transition.output is []:
                raise Exception("Controller transitions cannot have outputs: " + str(transition) + ".")

        self.valuation = init_val
        self.env_events = env_events
        self.con_events = con_events
        self.mon_events = mon_events

    def add_env_transition(self, src, condition: Formula, action: Formula, output: [Variable], tgt):
        assert output.issubset(self.mon_events)
        self.env_transitions.append(Transition(src, condition, action, output, tgt))
        self.states.add(src)
        self.states.add(tgt)

    def add_con_transition(self, src, condition: Formula, action: Formula, tgt):
        self.con_transitions.append(Transition(src, condition, action, [], tgt))
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

    def abstract_into_ltl(self):
        # TODO predicate stuff

        donothingevents = []
        for monitor_event in self.mon_events:
            donothingevents += [X(neg(monitor_event))]

        donothingevents = reduce(conjunct, donothingevents)

        init_cond_list = []
        for transition in self.state_to_env(self.initial_state):
            init_cond_list += [reduce(conjunct,
                                      [project(transition.condition, self.env_events)] +
                                      [transition.tgt] +
                                      [ev for ev in transition.output] +
                                      [neg(ev) for ev in self.mon_events if ev not in transition.output])]

        init_cond = reduce(disjunct, init_cond_list)

        transition_cond_list = []
        for state in self.states:
            state_cond_now_list = []
            state_cond_list = []
            for transition in self.state_to_con(state):
                now_condition = project(transition.condition, self.con_events)
                state_cond_now_list += [now_condition]
                next_condition_list = []
                for next_transition in self.state_to_env(transition.tgt):
                    next_condition = X(reduce(conjunct,
                                              [project(next_transition.condition, self.env_events),
                                               self.only_this_state(next_transition.tgt)] +
                                              [ev for ev in next_transition.output] +
                                              [neg(ev) for ev in self.mon_events if ev not in next_transition.output]))
                    state_cond_list += [conjunct(now_condition, next_condition)]
                    next_condition_list += [next_condition]

                state_cond_list += [reduce(conjunct,
                                           [now_condition,
                                            neg(reduce(disjunct, next_condition_list)),
                                            X(donothingevents),
                                            X(self.only_this_state(transition.tgt))])]

            if not self.state_to_con(state):
                con_stutter_now = X(true())
            else:
                con_stutter_now = neg(reduce(disjunct, state_cond_now_list))
            con_stutter_then_env_list = []
            for next_transition in self.state_to_env(state):
                next_condition = reduce(conjunct,
                                        [project(next_transition.condition, self.env_events)] + \
                                        [X(reduce(conjunct,
                                          [self.only_this_state(next_transition.tgt)] +
                                          [ev for ev in next_transition.output] +
                                          [neg(ev) for ev in self.mon_events if ev not in next_transition.output]))])
                state_cond_list += [conjunct(con_stutter_now, next_condition)]
                con_stutter_then_env_list += [next_condition]

            state_cond_list += [reduce(conjunct,
                                       [con_stutter_now,
                                        neg(reduce(disjunct, con_stutter_then_env_list)),
                                        X(donothingevents),
                                        X(self.only_this_state(state))])]
        transition_cond_list += [conjunct(state, reduce(disjunct, state_cond_list))]

        transition_cond = G(reduce(disjunct, transition_cond_list))

        return conjunct(init_cond, transition_cond)

    def __str__(self):
        text = "monitor " + self.name + " {\n"
        tagged_states = [str(self.initial_state) + " : init"] + [str(s) for s in self.states if s != self.initial_state]
        text += "\tSTATES {\n"
        text += "\t\t" + ",\n\t\t".join(tagged_states) + "\n"
        text += "\t}\n"
        text += "\tEVENTS {\n"
        text += "\t\t" + ",".join([str(e) + " : env" for e in self.env_events]) + "\n"
        text += "\t\t" + ",".join([str(m) + " : mon" for m in self.mon_events]) + "\n"
        text += "\t\t" + ",".join([str(c) + " : con" for c in self.con_events]) + "\n"
        text += "\t}" + "\n"
        text += "\tVALUATION {\n"
        text += "\t\t" + ";\n\t\t".join([str(x) for x in self.valuation]) + "\n"
        text += "\t}" + "\n"
        text += "\tENVIRONMENT TRANSITIONS {\n"
        text += "\t\t{" + "},\n\t\t{".join([str(t) for t in self.env_transitions]) + "}\n"
        text += "\t}" + "\n"
        text += "\tCONTROLLER TRANSITIONS {\n"
        text += "\t\t{" + "},\n\t\t{".join([str(t) for t in self.env_transitions]) + "}\n"
        text += "\t}" + "\n"
        text += "}"
        return text.replace("&&", "&").replace("||", "|")

    def to_nuXmv(self):

        donothingmonevents = str(reduce(conjunct, [str(event) + " = FALSE" for event in self.mon_events]))

        init_cond_list = []
        for transition in self.state_to_env(self.initial_state):
            init_cond_list += [reduce(conjunct,
                                      [transition.condition.ground(self.valuation).to_nuxmv()] +
                                      [BiOp(act.left, " = ", act.right.ground(self.valuation).to_nuxmv()) for act in self.complete_action_set(transition.action)] +
                                      [self.only_this_state(transition.tgt)] +
                                      [ev for ev in transition.output] +
                                      [neg(ev) for ev in self.mon_events if ev not in transition.output])]

        init_cond = reduce(disjunct, init_cond_list)

        transition_cond_list = []
        for state in self.states:
            state_cond_now_list = []
            state_cond_list = []
            for transition in self.state_to_con(state):
                now_condition = transition.condition.to_nuxmv()
                state_cond_now_list += [now_condition]
                next_condition_list = []
                for next_transition in self.state_to_env(transition.tgt):
                    next_conditions = ["next(" + str(reduce(conjunct,
                                            [next_transition.condition.replace(transition.action).to_nuxmv()] +
                                            [ev for ev in next_transition.output] +
                                            [neg(ev) for ev in self.mon_events if ev not in next_transition.output])) + ")"]
                    next_conditions += [" & ".join(["next(" + str(act.left) + ") = (" + str(act.right.replace(transition.action).to_nuxmv()) + ")" for act in self.complete_action_set(transition.action)])]
                    next_conditions = [x for x in next_conditions if x]

                    next_condition = " & ".join(next_conditions)

                    state_cond_list += [str(conjunct(now_condition, next_condition))]
                    next_condition_list += [next_condition]

                state_cond_list += ["\n\t & ".join([str(now_condition),
                                            "((" + ") | (".join(next_condition_list) + "))",
                                            "next(" + donothingmonevents + ")",
                                            "next(" + self.only_this_state(transition.tgt) + ")"])]

            if not self.state_to_con(state):
                con_stutter_now = true()
            else:
                con_stutter_now = neg(reduce(disjunct, state_cond_now_list))
            con_stutter_then_env_list = []
            for next_transition in self.state_to_env(state):
                next_conditions = [str(next_transition.condition.to_nuxmv()) + " & "\
                                 "next(" + str(reduce(conjunct,
                                        [self.only_this_state(next_transition.tgt)] +
                                        [ev for ev in next_transition.output] +
                                        [neg(ev) for ev in self.mon_events if ev not in next_transition.output])) + ")"]
                next_conditions += [" & ".join(["next(" + str(act.left) + ") = (" + str(act.right) + ")" for act in self.complete_action_set(next_transition.action)])]
                next_conditions = [x for x in next_conditions if x ]
                next_condition = " & ".join(next_conditions)

                # no controller transition but take an environment transition
                state_cond_list += [" & ".join([str(con_stutter_now), next_condition])]
                con_stutter_then_env_list += [next_condition]

            # no controller and no environment transition
            state_cond_list += ["\n\t & ".join([str(con_stutter_now),
                                        str(neg(reduce(disjunct, con_stutter_then_env_list))),
                                        "next(" + donothingmonevents + ")",
                                        "next(" + self.only_this_state(state) + ")"])]

            transition_cond_list += [str(state) + " & (" + ")\n\t| (".join(state_cond_list) + ")"]

        define = "DEFINE\n"

        text = "MODULE main\n"
        text += "VAR\n"
        # text += "\tstate : {" + ",".join([str(st) for st in self.states]) + "};\n"
        text += "".join(["\t" + str(st) + " : boolean" + ";\n" for st in self.states])
        text += "".join(["\t" + str(val.name) + " : " + str(val.type) + ";\n" for val in self.valuation])
        text += "".join(["\t" + str(var) + " : boolean" + ";\n" for var in self.env_events])
        text += "".join(["\t" + str(var) + " : boolean" + ";\n" for var in self.con_events])
        text += "".join(["\t" + str(var) + " : boolean" + ";\n" for var in self.mon_events])

        text += define
        text += "INIT\n"
        text += "\t" + str(init_cond)
        text += "\n"
        text += "TRANS\n"
        text += "\t(" + "\n)\t|\t(".join(transition_cond_list) + ")"

        text = text.replace("%", "mod")

        return text

    def to_nuXmv_with_turns(self):
        guards = []
        acts = []
        for env_transition in self.env_transitions:
            guard = "turn = env & " + env_transition.src + " & " \
                    + str(env_transition.condition)

            updated_variables = [str(act.left) for act in env_transition.action]
            act = self.only_this_state_next(env_transition.tgt) \
                  + "".join([" & next" + str(act).replace(" := ", ") = (") for act in self.complete_action_set(env_transition.action)]) \
                  + "".join([" & next(" + str(typed_val.name) + ") = (" + str(typed_val.name) + ")"
                             for typed_val in self.valuation if str(typed_val.name) not in updated_variables]) \
                  + "".join([" & next(" + str(event) + ") = TRUE" for event in env_transition.output]) \
                  + "".join([" & next(" + str(event) + ") = FALSE"
                             for event in self.env_events]) \
                  + "".join([" & next(" + str(event) + ") = FALSE"
                             for event in self.mon_events if event not in env_transition.output])
            guards.append(guard)
            acts.append(act)

        for con_transition in self.con_transitions:
            guard = "turn = con & " + con_transition.src + " & " \
                    + str(env_transition.condition)

            updated_variables = [str(act.left) for act in con_transition.action]
            act = self.only_this_state_next(con_transition.tgt) \
                  + "".join([" & next" + str(act).replace(" := ", ") = (") for act in self.complete_action_set(con_transition.action)]) \
                  + "".join([" & next(" + str(typed_val.name) + ") = (" + str(typed_val.name) + ")"
                             for typed_val in self.valuation if str(typed_val.name) not in updated_variables]) \
                  + "".join([" & next(" + str(event) + ") = FALSE"
                             for event in self.mon_events + self.con_events])
            guards.append(guard)
            acts.append(act)

        define = "DEFINE\n"
        transitions = []
        guard_ids = []
        i = 0
        while i < len(guards):
            define += "\tguard_" + str(i) + " := " + guards[i] + ";\n"
            define += "\tact_" + str(i) + " := " + acts[i] + ";\n"
            transitions.append("(guard_" + str(i) + " & " + "act_" + str(i) + ")")
            guard_ids.append("guard_" + str(i))
            i += 1

        identity = []
        for typed_val in self.valuation:
            identity.append("next(" + str(typed_val.name) + ") = " + str(typed_val.name))
        for st in self.states:
            identity.append("next(" + str(st) + ") = " + str(st))

        identity += ["next(" + str(event) + ") = FALSE" for event in self.mon_events]

        define += "\tidentity := " + " & ".join(identity) + ";\n"

        # if no guard holds, then keep the same state and output no monitor events
        transitions.append("!(" + " | ".join(guard_ids) + ") & identity")

        text = "MODULE main\n"
        text += "VAR\n"
        text += "\tturn : {env, con};\n"
        # text += "\tstate : {" + ",".join([str(st) for st in self.states]) + "};\n"
        text += "".join(["\t" + str(st) + " : boolean" + ";\n" for st in self.states])
        text += "".join(["\t" + str(val.name) + " : " + str(val.type) + ";\n" for val in self.valuation])
        text += "".join(["\t" + str(var) + " : boolean" + ";\n" for var in self.env_events])
        text += "".join(["\t" + str(var) + " : boolean" + ";\n" for var in self.con_events])
        text += "".join(["\t" + str(var) + " : boolean" + ";\n" for var in self.mon_events])

        text += define
        text += "INIT\n"
        text += "\t" + self.only_this_state(self.initial_state) + "\n"
        text += "".join(["\t& \t" + str(val.name) + " = " + str(val.value) + "\n" for val in self.valuation])
        text += "".join(["\t& \t" + str(event) + " = FALSE\n" for event in self.mon_events + self.con_events])
        text += "\n"
        text += "TRANS\n"
        text += "\t" + "\n\t|\t".join(transitions)

        text = text.replace("%", "mod")

        return text

    def only_this_state(self, state):
        only_this_state = str(state)
        for other in self.states:
            if other != state:
                only_this_state += " & !(" + str(other) + ")"
        return only_this_state

    def only_this_state_next(self, state):
        only_this_state = "next(" + str(state) + " )"
        for other in self.states:
            if other != state:
                only_this_state += " & !next(" + str(other) + ")"
        return only_this_state

    def complete_action_set(self, actions : [BiOp]):
        non_updated_vars = [tv.name for tv in self.valuation if tv.name not in [str(act.left) for act in actions]]
        return actions + [BiOp(Variable(var), "=", Variable(var)) for var in non_updated_vars]