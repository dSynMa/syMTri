from pysmt.fnode import FNode

from programs.analysis.smt_checker import SMTChecker
from programs.transition import Transition
from programs.util import ce_state_to_formula, fnode_to_formula
from prop_lang.biop import BiOp
from prop_lang.util import conjunct, conjunct_formula_set, neg
from prop_lang.variable import Variable


def safety_abstraction(ce: [dict], prefix: [Transition], symbol_table) -> [FNode]:
    logic = "QF_UFLRA"  # TODO what to put here?

    smt_checker = SMTChecker()

    ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys()]
    reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in symbol_table.keys() for i in range(0, len(prefix))]

    new_symbol_table = {}
    for i in range(0, len(prefix)):
        new_symbol_table.update({key + "_" + str(i): value for key, value in symbol_table.items()})

    Cs = set()

    init_prop = ce_state_to_formula(ce[0], symbol_table).replace(ith_vars(0))

    B = conjunct(neg(prefix[len(prefix) - 1].condition).replace(ith_vars(len(prefix) - 1)), init_prop)

    for j in reversed(range(0, len(prefix))):

        # localize ith state
        path_formula_set_A = []
        for i in range(0, j + 1):
            # TODO maybe add known predicates
            path_formula_set_A += [prefix[i].condition.replace(ith_vars(i))] + \
                                  [BiOp(act.left.name + "_" + str(i + 1),
                                        "=",
                                        act.right.replace(ith_vars(i))) for act in prefix[i].action]

        path_formula_A = conjunct_formula_set(path_formula_set_A)

        path_formula_set_B = []
        for i in range(j + 1, len(prefix)):
            # TODO maybe add known predicates
            path_formula_set_B += [prefix[i].condition.replace(ith_vars(i))] + \
                                  [BiOp(act.left.name + "_" + str(i + 1),
                                        "=",
                                        act.right.replace(ith_vars(i))) for act in prefix[i].action]
        path_formula_B = conjunct_formula_set(path_formula_set_B)

        Aj = path_formula_A.to_smt(new_symbol_table)
        Bj = conjunct(B, path_formula_B).to_smt(new_symbol_table)
        Cj = smt_checker.binary_interpolant(Aj, Bj, logic)
        if Cj is None:
            raise Exception("Interpolation being checked against formulas that are not contradictory: \n" +
                            "A: " + str(Aj) +
                            "\nB: " + str(Bj))
        # if B is itself inconsistent
        if Cj.is_true():
            break

        Cs |= {fnode_to_formula(Cj).replace(reset_vars)}

    return Cs


def liveness_abstraction(program, ce: [BiOp]):
    pass
