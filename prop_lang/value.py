from monitors.typed_valuation import TypedValuation
from prop_lang.atom import Atom
from prop_lang.variable import Variable
from pysmt.shortcuts import Int, TRUE, FALSE

class Value(Atom):
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return str(self.name)

    def __hash__(self):
        return self.name.__hash__()

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Value):
            return self.name == other.name
        return NotImplemented

    def is_true(self):
        lower = self.name.lower()
        return lower == "true" or lower == "tt"


    def is_false(self):
        lower = self.name.lower()
        return lower == "false" or lower == "ff"

    def variablesin(self) -> [Variable]:
        return []

    def ground(self, context : [TypedValuation]):
        return self

    def replace(self, context):
        return self

    def to_nuxmv(self):
        return self

    def to_smt(self, _):
        if self.is_true():
            return TRUE
        elif self.is_false():
            return FALSE
        else:
            return Int(int(self.name))
