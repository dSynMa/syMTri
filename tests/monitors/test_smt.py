from unittest import SkipTest, TestCase

from pysmt.shortcuts import Symbol, get_env, Solver
from pysmt.logics import QF_UFLRA
from subprocess import check_output
import os


class TestSmt(TestCase):

    def test_mathsat(self):
        """Tests that a system-wide mathsat can be found and driven by pysmt
        """

        if os.name == "posix":
            which_cmd = "which"
        elif os.name == "nt":
            which_cmd = "where"
        else:
            raise SkipTest(f"This test does not support OS '{os.name}'.")

        msat_path = check_output((which_cmd, "mathsat"), encoding="utf8")
        msat_path = msat_path.replace("\n", "")
        name = "mathsat-smtlib"

        # Add the solver to the environment
        env = get_env()
        env.factory.add_generic_solver(name, [msat_path], [QF_UFLRA])
        with Solver(name=name) as s:
            self.assertTrue(s.is_sat(Symbol("x")))
