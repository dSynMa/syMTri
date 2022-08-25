from abc import ABC, abstractmethod
from typing import Any

from programs.typed_valuation import TypedValuation


class Formula(ABC):

    @abstractmethod
    def __str__(self):
        pass

    @abstractmethod
    def variablesin(self):
        pass

    @abstractmethod
    def ground(self, context: [TypedValuation]):
        pass

    @abstractmethod
    def simplified(self):
        pass

    @abstractmethod
    def ops_used(self):
        pass

    # contexts assumed to be a list of assignments
    @abstractmethod
    def replace(self, context):
        pass

    @abstractmethod
    def to_nuxmv(self):
        pass

    @abstractmethod
    def to_smt(self, symbol_table: Any):
        pass
