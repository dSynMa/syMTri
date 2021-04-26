from prop_lang.formula import Formula


class Atom(Formula):
    def __init__(self, name: str):
        self.name = name

    def __str__(self):
        return str(self.name)

    def __hash__(self):
        return self.name.__hash__()

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, Atom):
            return self.name == other.name
        return NotImplemented
