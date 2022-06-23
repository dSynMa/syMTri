from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import true
from prop_lang.variable import Variable


class Transition:
    def __init__(self, src, condition: Formula, action: [BiOp], output: [Variable], tgt):
        self.src = src
        self.condition = true() if condition is None else condition
        self.action = [] if action is None else action
        self.output = output
        self.tgt = tgt

    def __str__(self) -> str:
        return self.src + " -> " + self.tgt + " {" + str(self.condition) + " $ " + "; ".join(
            [str(x) for x in self.action]) + " >> " + "[" + ", ".join([str(x) for x in self.output]) + "]" + "}"
