from prop_lang.formula import Formula


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
