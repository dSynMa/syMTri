from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.util import true
from prop_lang.variable import Variable


class Transition:
    def __init__(self, src, condition: Formula, action: [BiOp], output: [Variable], tgt):
        self.src = src
        self.condition = true() if condition is None else condition
        self.action = [] if action is None else action
        self.output = sorted(output, key=lambda x: str(x))
        self.tgt = tgt

    def __str__(self) -> str:
        to_str = lambda x: str(x) if type(x) != tuple or type(x[1]) != frozenset else str(x[0]) + ", " + ', '.join(
            map(to_str, list(x[1])))

        return to_str(self.src) + " -> " + to_str(self.tgt) + " {" + str(self.condition) + " $ " + "; ".join(
            [str(x) for x in self.action]) + " >> " + "[" + ", ".join([str(x) for x in self.output]) + "]" + "}"
