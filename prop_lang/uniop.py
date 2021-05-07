from prop_lang.formula import Formula


class UniOp(Formula):
    def __init__(self, op: str, right: Formula):
        self.op = op
        self.right = right

    def __str__(self):
        return self.op + " " + str(self.right)

    def __eq__(self, other):
        """Overrides the default implementation"""
        if isinstance(other, UniOp):
            return self.op == other.op and self.right == other.right
        return NotImplemented
