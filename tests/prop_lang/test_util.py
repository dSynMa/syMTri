from unittest import TestCase

from prop_lang.util import neg, disjunct, tighten_ltl, X, conjunct, G, F
from prop_lang.variable import Variable


class Test(TestCase):
    def test_tighten_ltl_0(self):
        ltl = F(Variable("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_1(self):
        ltl = G(Variable("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is not None:
            self.fail()

    def test_tighten_ltl_1(self):
        ltl = conjunct(Variable("a"), Variable("b"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_2(self):
        ltl = X(Variable("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_3(self):
        ltl = conjunct(X(Variable("a")), Variable("b"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_4(self):
        ltl = neg(Variable("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_5(self):
        ltl = neg(X(Variable("a")))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is not None:
            self.fail()

    def test_tighten_ltl_6(self):
        ltl = disjunct(X(Variable("a")), Variable("b"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()
