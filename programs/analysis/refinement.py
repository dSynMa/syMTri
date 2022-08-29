from pysmt.fnode import FNode
from pysmt.shortcuts import And

from programs.analysis.model_checker import ModelChecker
from programs.analysis.smt_checker import SMTChecker
from programs.transition import Transition
from programs.util import ce_state_to_formula, fnode_to_formula
from prop_lang.biop import BiOp
from prop_lang.util import conjunct, conjunct_formula_set, neg, G, F, implies
from prop_lang.variable import Variable


def safety_refinement(ce: [dict], prefix: [Transition], symbol_table, program) -> [FNode]:
    logic = "QF_UFLRA"  # TODO what to put here?

    smt_checker = SMTChecker()

    ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys()]
    reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in symbol_table.keys() for i in range(0, len(prefix))]

    new_symbol_table = {}
    for i in range(0, len(prefix) + 1):
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
                                  [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                        "=",
                                        act.right.replace(ith_vars(i))) for act in program.complete_action_set(prefix[i].action)]

        path_formula_A = conjunct_formula_set(path_formula_set_A)

        path_formula_set_B = []
        for i in range(j + 1, len(prefix)):
            # TODO maybe add known predicates
            path_formula_set_B += [prefix[i].condition.replace(ith_vars(i))] + \
                                  [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                        "=",
                                        act.right.replace(ith_vars(i))) for act in program.complete_action_set(prefix[i].action)]
        path_formula_B = conjunct_formula_set(path_formula_set_B)

        Aj = And(*path_formula_A.to_smt(new_symbol_table))
        Bj = And(*conjunct(B, path_formula_B).to_smt(new_symbol_table))
        Cj = smt_checker.binary_interpolant(Aj, Bj, logic)
        if Cj is None:
            raise Exception("Interpolation being checked against formulas that are not contradictory: \n" +
                            "A: " + str(Aj) +
                            "\nB: " + str(Bj))
        # if B is itself inconsistent
        if Cj.is_true():
            break
        elif Cj.is_false():
            Aj = And(*conjunct(init_prop, path_formula_A).to_smt(new_symbol_table))
            Bj = And(*conjunct(B, path_formula_B).to_smt(new_symbol_table))
            Cj = smt_checker.binary_interpolant(Aj, Bj, logic)

            if Cj.is_true():
                break
            elif Cj.is_false():
                break

        Cs |= {fnode_to_formula(Cj).replace(reset_vars).simplify()}
        Cs |= {neg(fnode_to_formula(Cj).replace(reset_vars)).simplify()}

    return Cs


def liveness_refinement(program_nuxmv_model, mismatch_mon_transition):
    # get all the states in the monitor loop, model check if for all paths the monitor eventually
    # settles in these states or not

    formula = neg(implies(G(F(Variable(mismatch_mon_transition.src))), G(F(Variable(mismatch_mon_transition.tgt)))))

    model_checker = ModelChecker()
    result, ce = model_checker.check(program_nuxmv_model, formula, None)

    # if it is true that the monitor eventually always settles in these states
    if not result:
        return True, formula.right # remove the negation, since proved false
    else:
        return False, ce

