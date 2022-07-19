import os
import shutil
import subprocess
from subprocess import check_output
from unittest import SkipTest, TestCase

from prop_lang.parsing.string_to_ltl import string_to_ltl
from pysmt.factory import SolverRedefinitionError
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import Solver, Symbol, get_env

from programs.typed_valuation import TypedValuation


class TestSmt(TestCase):

    SOLVER_NAME = "mathsat-smtlib"

    def _add_mathsat(self):
        self._check_os()

        msat_path = shutil.which("mathsat")

        # Add the solver to the environment
        env = get_env()
        try:
            env.factory.add_generic_solver(self.SOLVER_NAME, [msat_path], [QF_UFLRA])
        except SolverRedefinitionError:
            # Solver has already been registered, skip
            pass

    def _check_os(self):
        if os.name not in ("posix", "nt"):
            raise SkipTest(f"This test does not support OS '{os.name}'.")

    def __init__(self, methodName: str = ...) -> None:
        super().__init__(methodName)
        self._add_mathsat()

    def test_mathsat(self):
        """Tests that a system-wide mathsat can be found and driven by pysmt
        """
        self._check_os()
        with Solver(name=self.SOLVER_NAME) as s:
            self.assertTrue(s.is_sat(Symbol("x")))

    def _test_to_smt(self, ltl_str: str, symbols: dict, expected_sat: bool):
        self._check_os()
        ltl = string_to_ltl(ltl_str)
        smt = ltl.to_smt(symbols)
        with Solver(name=self.SOLVER_NAME) as s:
            self.assertEqual(s.is_sat(smt), expected_sat)

    def test_to_smt_0(self):
        self._test_to_smt("1 == 0", {}, False,)

    def test_to_smt_1(self):
        self._test_to_smt(
            "TO_BE || (!TO_BE)",
            {"TO_BE": TypedValuation("TO_BE", "bool", True)},
            True)

    def test_to_smt_2(self):
        self._test_to_smt(
            "TO_BE && (!TO_BE)",
            {"TO_BE": TypedValuation("TO_BE", "bool", True)},
            False)

    def test_to_smt_3(self):
        self._test_to_smt(
            "(ROOMCLEAN && (!INROOM) && (! DOORLOCKED))",
            {
                "ROOMCLEAN": TypedValuation("ROOMCLEAN", "bool", True),
                "INROOM": TypedValuation("INROOM", "bool", True),
                "DOORLOCKED": TypedValuation("DOORLOCKED", "bool", True)
            },
            True)
