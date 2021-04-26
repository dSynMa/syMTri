from unittest import TestCase

from prop_lang.ltl.string_to_ltl import string_to_ltl


class Test(TestCase):
    def test_string_to_ltl_0(self):
        ltl = string_to_ltl("(a & (a)")
        print(ltl)
        if ltl is not None:
            self.fail()

    def test_string_to_ltl_1(self):
        ltl = string_to_ltl("(a) & (a)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_2(self):
        ltl = string_to_ltl("G (a) & (a)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_3(self):
        ltl = string_to_ltl("G (a & a)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_3(self):
        ltl = string_to_ltl("G (A && A)")
        print(ltl)
        if ltl is None:
            self.fail()

    def test_string_to_ltl_4(self):
        ltl = string_to_ltl("F (ROOMCLEAN && (X F !INROOM) && (X F ! DOORLOCKED))")
        print(ltl)
        if ltl is None:
            self.fail()
