
from pysmt.fnode import FNode
from pysmt.shortcuts import Solver, binary_interpolant, sequence_interpolant, Interpolator, get_env

from programs.util import _add_solver, _check_os


class SMTChecker:
    SOLVER_NAME = "msat"
    # SOLVER_NAME = "mathsat-smtlib"

    def __init__(self) -> None:
        pass
        get_env().factory._get_available_solvers()
        # _add_solver(self.SOLVER_NAME, "msat")

    def check(self, smt: FNode):
        with Solver(name=self.SOLVER_NAME) as s:
            return s.is_sat(smt)

    def binary_interpolant(self, A: FNode, B: FNode, logic) -> FNode:
        with Interpolator(name="msat", logic="QF_UFLRA") as s:
            return s.binary_interpolant(A, B)

    def sequence_interpolant(self, A: FNode, B: FNode, logic) -> FNode:
        # TODO
        pass