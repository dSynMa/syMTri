from prop_lang.formula import Formula


class MathExpr(Formula):

    def MathExpr(self, f: Formula):
        self.formula = f

    def __str__(self):
        return str(self.name)

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
