from unittest import TestCase

from pysmt.shortcuts import And

from parsing.string_to_prop_logic import string_to_prop
from programs.analysis.smt_checker import SMTChecker
from programs.typed_valuation import TypedValuation


class TestSMTChecker(TestCase):
    def test_to_cnf(self):
        smt_checker = SMTChecker()
        formula = string_to_prop("a & b | c")
        symbol_table = {}
        symbol_table['a'] = TypedValuation('a', "bool", None)
        symbol_table['b'] = TypedValuation('b', "bool", None)
        symbol_table['c'] = TypedValuation('c', "bool", None)
        val = smt_checker.to_cnf(And(*formula.to_smt(symbol_table)))
        print(val)
        val.serialize(10)
        self.assertTrue(val != None)
