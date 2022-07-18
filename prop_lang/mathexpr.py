from typing import Any

from prop_lang.formula import Formula


class MathExpr(Formula):

    def __init__(self, f: Formula):
        self.formula = f

    def __str__(self):
        return str(self.formula)

    def __hash__(self):
        return self.name.__hash__()

    def __eq__(self, other):
        if isinstance(other, MathExpr):
            return self.f == other.formula
        else:
            return False

    def variablesin(self):
        return self.formula.variablesin()

    def ground(self, context):
        return self.formula.ground(context)

    def replace(self, context):
        return self.formula.replace(context)

    def to_nuxmv(self):
        return self.formula.to_nuxmv()

    def to_smt(self, symbol_table: Any):
        return self.formula.to_smt(symbol_table)
