import pysmt
from pysmt.fnode import FNode
from pysmt.rewritings import CNFizer
from pysmt.shortcuts import Solver, Interpolator, get_env, get_unsat_core, UnsatCoreSolver, serialize, And


class SMTChecker:
    SOLVER_NAME = "msat"

    # SOLVER_NAME = "mathsat-smtlib"

    def __init__(self) -> None:
        pass
        get_env().factory._get_available_solvers()
        # _add_solver(self.SOLVER_NAME, "msat")

    def newSolver(self):
        return Solver(name=self.SOLVER_NAME)

    def check(self, smt: FNode):
        try:
            with Solver(name="msat") as s:
                return s.is_sat(smt)
        except:
            with Solver(name="z3") as s: # this is needed because msat does not support non-linear arithmetic
                return s.is_sat(smt)

    def unsatcore(self, A, B):
        with UnsatCoreSolver(logic="QF_UFLIAt", unsat_cores_mode="all") as s:
            s.add_assertion(A)
            s.add_assertion(B)
            r = s.solve()
            assert not r
            unsatcore = list(s.get_unsat_core())

            print(" , ".join(map(str, map(serialize, map(pysmt.shortcuts.simplify, (unsatcore))))))
            return And(*unsatcore[:-1]), unsatcore[-1]

    def binary_interpolant(self, A: FNode, B: FNode, logic) -> FNode:
        with Interpolator(name="msat") as s:
            return s.binary_interpolant(A, B)

    def to_cnf(self, A: FNode) -> FNode:
        val = CNFizer().convert_as_formula(A)
        return val

    def sequence_interpolant(self, A: FNode, B: FNode, logic) -> FNode:
        # TODO
        pass
