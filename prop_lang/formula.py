from abc import ABC, abstractmethod

from monitors.typed_valuation import TypedValuation


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

    # contexts assumed to be a list of assignments
    @abstractmethod
    def replace(self, context):
        pass

    @abstractmethod
    def to_nuxmv(self):
        pass