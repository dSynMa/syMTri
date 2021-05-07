from typing import Set

from monitors.transition import Transition
from monitors.typed_valuation import TypedValuation
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from graphviz.dot import Digraph


class Monitor:

    def __init__(self, name, sts, init_st, init_val: [TypedValuation], flag_sts, transitions: [Transition], input_events, output_events):
        self.name = name
        self.initial_state = init_st
        self.states: Set = set(sts)
        self.flag_states = flag_sts
        self.transitions = transitions
        self.valuation = init_val
        self.input_events  = input_events
        self.output_events = output_events

    def add_transition(self, src, condition: Formula, action: Formula, output: [Atom], tgt):
        self.transitions.append(Transition(src, condition, action, output, tgt))
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

        for t in self.transitions:
            outputs = ""
            if t.output is None:
                outputs = ""
            else:
                outputs = str(t.output)

            label = str(t.condition) + "\n>> " + str(t.action) + "\n>> " + outputs
            dot.edge(str(t.src), str(t.tgt), label=label)

        return dot

    def reduce(self):
        # TODO remove states not reachable from init state

        # Remove looping transitions without actions
        without_looping_no_effect_transitions = [t for t in self.transitions if
                                                 not (t.src == t.tgt and t.action == Atom("skip"))]
        self.transitions = without_looping_no_effect_transitions

        used_states = [s for s in self.states if len([t for t in self.transitions if t.src == s or t.tgt == s]) > 0]
        self.states = used_states


    def __str__(self):
        text = "monitor " + self.name + " {\n"
        tagged_states = [str(self.initial_state) + " : init"] \
                        + [str(s) + " : flag" for s in self.flag_states] \
                        + [str(s) for s in self.states if s not in self.flag_states and s is not self.initial_state]
        text += "\tSTATES {\n"
        text += "\t\t" + ",\n\t\t".join(tagged_states)+ "\n"
        text += "\t}\n"
        text += "\tEVENTS {\n"
        text += "\t\t" + ",".join([i + " : input" for i in self.input_events] + [o + " : output" for o in self.output_events]) + "\n"
        text += "\t}" + "\n"
        text += "\tINITIAL_VALUATION {\n"
        text += "\t\t" + ";\n\t\t".join([str(x) for x in self.valuation]) + "\n"
        text += "\t}" + "\n"
        text += "\tTRANSITIONS {\n"
        text += "\t\t{" + "},\n\t\t{".join([str(t) for t in self.transitions]) + "}\n"
        text += "\t}" + "\n"
        text += "}"
        return text.replace("&&", "&").replace("||", "|")


    def to_nuXmv(self):
        guards = []
        acts = []
        for transition in self.transitions:
            guard = "state = " + transition.src + " & " + str(transition.condition)
            act = "next(state) = " + transition.tgt + "".join([" & next" + str(act).replace(" := ", ") = (") for act in transition.action])
            guards.append(guard)
            acts.append(act)

        define = "DEFINE\n"
        transitions = []
        i = 0
        while i < len(self.transitions):
            define += "\tguard_" + str(i) + " := " + guards[i] + ";\n"
            define += "\tact_" + str(i) + " := " + acts[i] + ";\n"
            transitions.append("(guard_" + str(i) + " & " + "act_" + str(i) + ")")
            i += 1

        text = "MODULE main\n"
        text += "VAR\n"
        text += "\tstate : {" + ",".join([str(st) for st in self.states]) + "};\n"
        text += "".join(["\t" + str(val.name) + " : " + str(val.type) + ";\n" for val in self.valuation])
        text += "".join(["\t" + val + " : boolean" + ";\n" for val in self.input_events])
        text += "".join(["\t" + val + " : boolean" + ";\n" for val in self.output_events])

        text += define
        text += "INIT\n"
        text += "\tstate = " + str(self.initial_state) + "\n"
        text += "".join(["\t& \t" + str(val.name) + " = " + str(val.value) + "\n" for val in self.valuation])
        text += "TRANS\n"
        text += "\t" + "\n\t|\t".join(transitions)

        return text


    def to_nuXmv_case_style(self):
        guards = []
        acts = []
        for transition in self.transitions:
            guard = "state = " + transition.src + " & " + str(transition.condition)
            act = "next(state) = " + transition.tgt + "".join([" & next" + str(act).replace(" := ", ") = (") for act in transition.action])
            guards.append(guard)
            acts.append(act)

        define = "DEFINE\n"
        transitions = []
        i = 0
        while i < len(self.transitions):
            define += "\tguard_" + str(i) + " := " + guards[i] + ";\n"
            define += "\tact_" + str(i) + " := " + acts[i] + ";\n"
            transitions.append("\t\tguard_" + str(i) + " : " + "act_" + str(i) + ";\n")
            i += 1

        text = "MODULE main\n"
        text += "VAR\n"
        text += "\tstate : {" + ",".join([str(st) for st in self.states]) + "};\n"
        text += "".join(["\t" + str(val.name) + " : " + str(val.type) + ";\n" for val in self.valuation])
        text += "".join(["\t" + val + " : boolean" + ";\n" for val in self.input_events])
        text += "".join(["\t" + val + " : boolean" + ";\n" for val in self.output_events])

        text += define
        text += "ASSIGN\n"
        text += "\tinit(state) := " + str(self.initial_state) + ";\n"
        text += "".join(["\tinit(" + str(val.name) + ") := " + str(val.value) + ";\n" for val in self.valuation])
        text += "TRANS\n"
        if len(transitions) != 0:
            text += "\tcase\n"
            text += "".join(transitions)
            text += "\tesac"

        return text