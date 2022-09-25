from pysmt.fnode import FNode
from pysmt.shortcuts import And, Or, Implies
from pysmt.shortcuts import (
    Plus, Minus, Times, Div, BVSRem, EqualsOrIff, LE, LT, GT, GE, NotEquals
)

from programs.typed_valuation import TypedValuation
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


class BiOp(Formula):
    def __init__(self, left: Formula, op: str, right: Formula):
        assert isinstance(left, Formula)
        self.left = left
        self.op = op.strip()
        assert isinstance(right, Formula)
        self.right = right

    def __str__(self):
        return "(" + (" " + self.op + " ").join([str(c) for c in self.sub_formulas_up_to_associativity()]) + ")"

    def sub_formulas_up_to_associativity(self):
        if self.op == "&&" or self.op == "&" or self.op == "||" or self.op == "|":
            sub_formulas = []
            if not isinstance(self.left, BiOp) or self.left.op != self.op:
                sub_formulas += [self.left]
            else:
                sub_formulas += self.left.sub_formulas_up_to_associativity()
            if not isinstance(self.right, BiOp) or self.right.op != self.op:
                sub_formulas += [self.right]
            else:
                sub_formulas += self.right.sub_formulas_up_to_associativity()
        else:
            sub_formulas = [self.left, self.right]
        return sub_formulas

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

    def simplify(self):
        left = self.left.simplify()
        right = self.right.simplify()
        if self.op in ["&", "&&"]:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return left
            elif isinstance(right, Value) and right.is_true():
                return left
            elif isinstance(right, Value) and right.is_false():
                return right
        elif self.op in ["|", "||"]:
            if isinstance(left, Value) and left.is_true():
                return left
            elif isinstance(left, Value) and left.is_false():
                return right
            elif isinstance(right, Value) and right.is_true():
                return right
            elif isinstance(right, Value) and right.is_false():
                return left
        elif self.op in ["->", "=>"]:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return Value("True")
            elif isinstance(right, Value) and right.is_true():
                return Value("True")
            elif isinstance(right, Value) and right.is_false():
                return UniOp("!", left)
        elif self.op in ["<->", "<=>"]:
            if isinstance(left, Value) and left.is_true():
                return right
            elif isinstance(left, Value) and left.is_false():
                return UniOp("!", right).simplify()
            elif isinstance(right, Value) and right.is_true():
                return left
            elif isinstance(right, Value) and right.is_false():
                return UniOp("!", left).simplify()
        return self

    def ops_used(self):
        return [self.op] + self.left.ops_used() + self.right.ops_used()

    def replace(self, context):
        return BiOp(self.left.replace(context), self.op, self.right.replace(context))

    def to_nuxmv(self):
        if self.op == "%":
            return UniOp("toint", BiOp(UniOp("unsigned word[8]", self.left.to_nuxmv()), "mod",
                                       UniOp("unsigned word[8]", self.right.to_nuxmv())))
        elif self.op == "=>":
            return BiOp(self.left.to_nuxmv(), '->', self.right.to_nuxmv())
        elif self.op == "<=>":
            return BiOp(self.left.to_nuxmv(), '<->', self.right.to_nuxmv())
        elif self.op == "&&":
            return BiOp(self.left.to_nuxmv(), '&', self.right.to_nuxmv())
        elif self.op == "||":
            return BiOp(self.left.to_nuxmv(), '|', self.right.to_nuxmv())
        else:
            return BiOp(self.left.to_nuxmv(), self.op, self.right.to_nuxmv())

    def to_smt(self, symbol_table) -> (FNode, FNode):
        ops = {
            "&": And,
            "&&": And,
            "|": Or,
            "||": Or,
            "->": Implies,
            "=>": Implies,
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
        left_expr, left_invar = self.left.to_smt(symbol_table)
        right_expr, right_invar = self.right.to_smt(symbol_table)

        try:
            op = ops[self.op]
        except KeyError:
            raise NotImplementedError(f"{self.op} unsupported")
        else:
            return op(left_expr, right_expr), And(left_invar, right_invar)
