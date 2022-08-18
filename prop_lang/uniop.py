from programs.typed_valuation import TypedValuation
from prop_lang.formula import Formula
from prop_lang.variable import Variable

from pysmt.shortcuts import Not, Minus, Int

class UniOp(Formula):
    def __init__(self, op: str, right: Formula):
        self.op = op
        self.right = right

    def __str__(self):
        return self.op + "(" + str(self.right) + ")"

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, UniOp):
            return self.op == other.op and self.right == other.right
        else:
            return NotImplemented

    def __hash__(self):
        return hash((self.op, self.right))

    def variablesin(self) -> [Variable]:
        return self.right.variablesin()

    def ground(self, context : [TypedValuation]):
        return UniOp(self.op, self.right.ground(context))

    def replace(self, context):
        return UniOp(self.op, self.right.replace(context))

    def to_nuxmv(self):
        return UniOp(self.op, self.right.to_nuxmv())

    def to_smt(self, symbol_table):
        if self.op == "!":
            return Not(self.right.to_smt(symbol_table))
        elif self.op == "-":
            return Minus(Int(0), self.right.to_smt(symbol_table))
        else:
            raise NotImplementedError(f"{self.op} unsupported")
