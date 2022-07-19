from programs.typed_valuation import TypedValuation
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.variable import Variable
from pysmt.shortcuts import And, Or, Implies
from pysmt.shortcuts import (
    Plus, Minus, Times, Div, BVSRem, EqualsOrIff, LE, LT, GT, GE, NotEquals
)


class BiOp(Formula):
    def __init__(self, left: Formula, op: str, right: Formula):
        self.left = left
        self.op = op
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + " " + str(self.op) + " " + str(self.right) + ")"

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, BiOp):
            return self.op == other.op and self.right == other.right and self.left == other.left
        return NotImplemented

    def variablesin(self) -> [Variable]:
        return self.left.variablesin() + self.right.variablesin()

    def ground(self, context : [TypedValuation]):
        return BiOp(self.left.ground(context), self.op, self.right.ground(context))

    def replace(self, context):
        return BiOp(self.left.replace(context), self.op, self.right.replace(context))

    def to_nuxmv(self):
        if self.op == "%":
            return UniOp("toint", BiOp(UniOp("unsigned word[8]", self.left.to_nuxmv()), "mod", UniOp("unsigned word[8]", self.right.to_nuxmv())))
        else:
            return BiOp(self.left.to_nuxmv(), self.op, self.right.to_nuxmv())

    def to_smt(self, symbol_table):
        ops = {
            "&&": And,
            "||": Or,
            "->": Implies,
            "==": EqualsOrIff,
            "!=": NotEquals,
            "<->": EqualsOrIff,
            ">": GT,
            ">=": GE,
            "<": LT,
            "<=": LE,
            "+": Plus,
            "-": Minus,
            "*": Times,
            "/": Div,
            "%": BVSRem
        }
        try:
            op = ops[self.op]
            return op(self.left.to_smt(symbol_table), self.right.to_smt(symbol_table))
        except KeyError:
            raise NotImplementedError(f"{self.op} unsupported")
