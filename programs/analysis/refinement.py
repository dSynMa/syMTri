from pysmt.fnode import FNode
from pysmt.shortcuts import And

from programs.analysis.model_checker import ModelChecker
from programs.analysis.smt_checker import SMTChecker
from programs.transition import Transition
from programs.util import ce_state_to_formula, fnode_to_formula, ground_formula_on_ce_state_with_index, \
    project_ce_state_onto_ev
from prop_lang.biop import BiOp
from prop_lang.util import conjunct, conjunct_formula_set, neg, G, F, implies
from prop_lang.value import Value
from prop_lang.variable import Variable


def safety_refinement(ce: [dict], prefix: [Transition], symbol_table, program) -> [FNode]:
    logic = "QF_UFLRA"  # TODO what to put here?

    smt_checker = SMTChecker()

    # this will be used to add intermediate variables for each monitor state
    ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys()]

    # symbol table is updated with intermediate variables (plus last one, len(prefix), for state after last transition
    new_symbol_table = {}
    for i in range(0, len(prefix) + 1):
        new_symbol_table.update({key + "_" + str(i): value for key, value in symbol_table.items()})

    # this will be used to generalise the interpolants references to intermediate variables to the original variable name
    reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in symbol_table.keys() for i in
                  range(0, len(prefix))]

    # we collect interpolants in this set
    Cs = set()

    # this characterises the variables at the initial state, we rename to name_0
    init_prop = ce_state_to_formula(ce[0], symbol_table).replace(ith_vars(0))

    # this characterise the base of the B of the interpolant problem, essentially, the initial proposition, and the
    # negation of the condition of the transition the environment did not want to take
    # B = conjunct(neg(prefix[len(prefix) - 1].condition).replace(ith_vars(len(prefix) - 1)), init_prop)

    A = []
    B = []
    C = []

    for j in reversed(range(0, len(prefix))):
        # localize jth state
        path_formula_set_A = []
        for i in range(0, j):
            path_formula_set_A += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                        "=",
                                        act.right.replace(ith_vars(i))) for act in
                                   program.complete_action_set(prefix[i].action)]

        path_formula_A = conjunct_formula_set(path_formula_set_A)

        path_formula_set_B = []
        for i in range(j, len(prefix) - 1):
            path_formula_set_B += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                       "=",
                                       act.right.replace(ith_vars(i))) for act in
                                  program.complete_action_set(prefix[i].action)]

        projected_condition = prefix[len(prefix) - 1].condition.replace(ith_vars(len(prefix) - 1))
        grounded_condition = ground_formula_on_ce_state_with_index(projected_condition,
                                                                    project_ce_state_onto_ev(ce[len(prefix) - 1],
                                                                                            program.env_events
                                                                                            + program.con_events), len(prefix) - 1)

        path_formula_set_B += [neg(grounded_condition)]

        path_formula_B = conjunct_formula_set(path_formula_set_B)

        A = [And(*conjunct(init_prop, path_formula_A).to_smt(new_symbol_table))] + A
        B = [And(*path_formula_B.to_smt(new_symbol_table))] + B

        C = [smt_checker.binary_interpolant(A[0], B[0], logic)] + C
        if C[0] is None:
            print("I think that interpolation is being checked against formulas that are not contradictory: \n" +
                  "A: " + str(A[0]) +
                  "\nB: " + str(B[0]))
            break
        # if B is itself inconsistent
        if C[0].is_true():
            break
        elif C[0].is_false():
            break

        # Cj_generalised = ground_formula_on_ce_state_with_index(fnode_to_formula(C[0]), ce[0], 0).replace(
        #     reset_vars).simplify()
        Cj_generalised = fnode_to_formula(C[0]).replace(reset_vars).simplify()
        Cs |= {Cj_generalised}
        Cs |= {neg(Cj_generalised).simplify()}

    return Cs


def liveness_refinement(program_nuxmv_model, mismatch_mon_transition):
    # TODO is this always the environment's turn or not?
    formula = implies(G(F(BiOp(BiOp(Variable("turn"), "=", Value("env")), "&", Variable(mismatch_mon_transition.src)))), G(F(Variable(mismatch_mon_transition.tgt))))

    model_checker = ModelChecker()
    result, ce = model_checker.check(program_nuxmv_model, formula, None)

    if result:
        formula_without_turn = implies(G(F(Variable(mismatch_mon_transition.src))),
                                       G(F(Variable(mismatch_mon_transition.tgt))))

        return True, formula_without_turn
    else:
        return False, ce
