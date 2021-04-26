from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula


class Transition:
    def __init__(self, src, condition: Formula, action: [BiOp], output: Formula, tgt):
        self.src = src
        self.condition = Atom("true") if condition is None else condition
        self.action = [] if action is None else action
        self.output = output
        self.tgt = tgt

    def __str__(self) -> str:
        return self.src + " -> " + self.tgt + " {" + str(self.condition) + " >> " + "; ".join(
            [str(x) for x in self.action]) + " >> " + str(self.output).replace("(", "").replace(")", "") + "}"
