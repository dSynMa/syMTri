from monitors.typed_valuation import TypedValuation
from prop_lang.atom import Atom


class Variable(Atom):
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return str(self.name)

    def __hash__(self):
        return self.name.__hash__()

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Variable):
            return self.name == other.name
        return NotImplemented

    def variablesin(self):
        return [self]

    def ground(self, context : [TypedValuation]):
        for val in context:
            if val.name == self.name:
                return val.value

        return self

    def replace(self, context):
        for val in context:
            if (val.op == "=" or val.op == ":=") and val.name == self.name:
                return val.value

        return self

    def to_nuxmv(self):
        return self