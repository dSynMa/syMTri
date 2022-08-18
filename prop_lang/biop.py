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
        assert isinstance(left, Formula)
        self.left = left
        self.op = op.strip()
        assert isinstance(right, Formula)
        self.right = right

    def __str__(self):
        return "(" + str(self.left) + " " + str(self.op) + " " + str(self.right) + ")"

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, BiOp):
            return self.op == other.op and self.right == other.right and self.left == other.left
        return NotImplemented

    def __hash__(self):
        return hash((self.left, self.op, self.right))

    def variablesin(self) -> [Variable]:
        return self.left.variablesin() + self.right.variablesin()

    def ground(self, context: [TypedValuation]):
        return BiOp(self.left.ground(context), self.op, self.right.ground(context))

    def replace(self, context):
        return BiOp(self.left.replace(context), self.op, self.right.replace(context))

    def to_nuxmv(self):
        if self.op == "%":
            return UniOp("toint", BiOp(UniOp("unsigned word[8]", self.left.to_nuxmv()), "mod",
                                       UniOp("unsigned word[8]", self.right.to_nuxmv())))
        elif self.op == "=>":
            return BiOp(self.left.to_nuxmv(), '->', self.right.to_nuxmv())
        else:
            return BiOp(self.left.to_nuxmv(), self.op, self.right.to_nuxmv())

    def to_smt(self, symbol_table):
        ops = {
            "&": And,
            "&&": And,
            "|": Or,
            "||": Or,
            "->": Implies,
            "==": EqualsOrIff,
            "=": EqualsOrIff,
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
        except KeyError:
            raise NotImplementedError(f"{self.op} unsupported")
        else:
            return op(self.left.to_smt(symbol_table), self.right.to_smt(symbol_table))
