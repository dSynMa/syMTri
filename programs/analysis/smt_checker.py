import os
import shutil
from pysmt.factory import SolverRedefinitionError
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import Solver, Symbol, get_env

from prop_lang.formula import Formula


def _check_os():
    if os.name not in ("posix", "nt"):
        raise Exception(f"This test does not support OS '{os.name}'.")


def _add_solver(description, command, args=[], logics=None):
    _check_os()
    logics = logics or [QF_UFLRA]

    path = shutil.which(command)

    # Add the solver to the environment
    env = get_env()
    try:
        env.factory.add_generic_solver(description, [path, *args], logics)
    except SolverRedefinitionError:
        # Solver has already been registered, skip
        pass


class SMTChecker:
    SOLVER_NAME = "mathsat-smtlib"

    def __init__(self) -> None:
        _add_solver(self.SOLVER_NAME, "mathsat")

        _check_os()
        with Solver(name=self.SOLVER_NAME) as s:
            self.assertTrue(s.is_sat(Symbol("x")))

    def check(self, f: Formula, symbol_table: dict):
        _check_os()
        smt = f.to_smt(symbol_table)
        with Solver(name=self.SOLVER_NAME) as s:
            return s.is_sat(smt)