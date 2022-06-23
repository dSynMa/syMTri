from prop_lang.formula import Formula
from abc import ABC, abstractmethod


class Atom(Formula, ABC):

    def __str__(self):
        return str(self.name)

    def __hash__(self):
        return self.name.__hash__()

    @abstractmethod
    def __eq__(self, other):
        pass
