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
