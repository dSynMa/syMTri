from unittest import TestCase

from prop_lang.atom import Atom
from prop_lang.util import nott, orr, tighten_ltl, next, andd, globally, eventually


class Test(TestCase):
    def test_tighten_ltl_0(self):
        ltl = eventually(Atom("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_1(self):
        ltl = globally(Atom("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is not None:
            self.fail()

    def test_tighten_ltl_1(self):
        ltl = andd(Atom("a"), Atom("b"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_2(self):
        ltl = next(Atom("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_3(self):
        ltl = andd(next(Atom("a")), Atom("b"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_4(self):
        ltl = nott(Atom("a"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()

    def test_tighten_ltl_5(self):
        ltl = nott(next(Atom("a")))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is not None:
            self.fail()

    def test_tighten_ltl_6(self):
        ltl = orr(next(Atom("a")), Atom("b"))
        tightened = tighten_ltl(ltl)
        print(tightened)
        if tightened is None:
            self.fail()
