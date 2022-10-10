import re

from click._compat import raw_input
from pysmt.fnode import FNode
from pysmt.shortcuts import And

from programs.analysis.ranker import Ranker
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import ce_state_to_formula, fnode_to_formula, ground_formula_on_ce_state_with_index, \
    project_ce_state_onto_ev, get_differently_value_vars, prog_transition_indices_and_state_from_ce, \
    concretize_transitions
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_prop_logic import string_to_mathexpr
from prop_lang.util import conjunct, conjunct_formula_set, neg, true, is_boolean
from prop_lang.value import Value
from prop_lang.variable import Variable


def safety_refinement(ce: [dict], prefix_pairs: [[(Transition, dict)]], symbol_table, program) -> [FNode]:
    # we collect interpolants in this set
    Cs = set()

    concurring_transitions = [x for xs in prefix_pairs[:-1] for x in xs]
    disagreed_on = prefix_pairs[len(prefix_pairs) - 1]

    # this is a hack to ensure correct behaviour when there is a mismatch with only transition (disagreed_on)
    # since interpolation requires len(concurring_transitions) to be at least one 1
    if concurring_transitions == []:
        concurring_transitions = [(Transition(program.initial_state, true(), [], [], program.initial_state), ce[0])]

    for i in range(0, len(disagreed_on)):
        for j in reversed(range(0, len(concurring_transitions) + i + 1)):
            C = interpolation(program, concurring_transitions + disagreed_on[0:i], disagreed_on[i], j, symbol_table)
            if C is None:
                print("I think that interpolation is being checked against formulas that are not contradictory.")
                break
            # if B is itself inconsistent
            if isinstance(C, Value) and C.is_true():
                break
            elif isinstance(C, Value) and C.is_false():
                break

            if isinstance(C, BiOp) and C.op[0] == "&":
                Cs |= set(C.sub_formulas_up_to_associativity())
            else:
                Cs |= {C}

    return Cs


def interpolation(program: Program, concurring_transitions: [(Transition, dict)], disagreed_on: (Transition, dict),
                  cut_point: int, symbol_table):
    assert cut_point <= len(concurring_transitions)
    assert len(concurring_transitions) > 0

    logic = "QF_UFLRA"  # TODO what to put here?
    smt_checker = SMTChecker()

    # this will be used to add intermediate variables for each monitor state
    ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys()]

    # symbol table is updated with intermediate variables (plus last one, len(prefix), for state after last transition
    new_symbol_table = {}
    for i in range(0, len(concurring_transitions) + 1):
        new_symbol_table.update({key + "_" + str(i): value for key, value in symbol_table.items()})

    # this will be used to generalise the interpolants references to intermediate variables to the original variable name
    reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in symbol_table.keys() for i in
                  range(0, len(concurring_transitions) + 1)]

    init_prop = ce_state_to_formula(concurring_transitions[0][1], symbol_table).replace(ith_vars(0))

    path_formula_set_A = []
    for i in range(0, cut_point):
        path_formula_set_A += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]

    path_formula_A = conjunct_formula_set(path_formula_set_A)

    path_formula_set_B = []
    for i in range(cut_point, len(concurring_transitions)):
        path_formula_set_B += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]

    neg_part_B = []

    disagreed_on_transition = disagreed_on[0]
    disagreed_on_state = disagreed_on[1]
    projected_condition = disagreed_on_transition.condition.replace(ith_vars(len(concurring_transitions)))
    grounded_condition = ground_formula_on_ce_state_with_index(projected_condition,
                                                               project_ce_state_onto_ev(disagreed_on_state,
                                                                                        program.env_events
                                                                                        + program.con_events),
                                                               len(concurring_transitions))
    neg_part_B += [grounded_condition]

    path_formula_set_B += [neg(conjunct_formula_set(neg_part_B).simplify())]
    path_formula_B = conjunct_formula_set(path_formula_set_B)

    A = And(*conjunct(init_prop, path_formula_A).to_smt(new_symbol_table))
    B = And(*path_formula_B.to_smt(new_symbol_table))

    C = smt_checker.binary_interpolant(A, B, logic)

    if C is not None:
        Cf = fnode_to_formula(C).replace(reset_vars).simplify()
        return Cf
    else:
        return None


def liveness_refinement(symbol_table, program, entry_predicate, unfolded_loop, exit_cond: Formula):
    # try to come up with a ranking function
    c_code = loop_to_c(symbol_table, program, entry_predicate, unfolded_loop, exit_cond)
    ranker = Ranker()
    success, ranking_function, invars = ranker.check(c_code)
    if not success:
        print("Could not find a ranking function for: \n" + c_code)
        text = raw_input("Any suggestions?")
        ranking_function, invars = string_to_mathexpr(text), []

    return ranking_function, invars


def loop_to_c(symbol_table, program: Program, entry_predicate: Formula, loop_before_exit: [Transition], exit_cond: Formula):
    # params
    param_list = ", ".join([symbol_table[str(v)].type + " " + str(v)
                            for v in {v.name for v in program.valuation}
                            if
                            not is_boolean(v, program.valuation) and v in [str(vv) for t in loop_before_exit for vv in
                                                                           (t.condition.variablesin()
                                                                            + [act.left for act in t.action]
                                                                            + [a for act in t.action for a in
                                                                               act.right.variablesin()])]])
    param_list = param_list.replace("integer", "int") \
        .replace("natural", "int") \
        .replace("nat", "int") \
        .replace("real", "double")

    init = ["if(!" + str(entry_predicate).replace(" = ", " == ").replace(" & ", " && ") + ") return;"] \
           + ["if(!(" + " && ".join([v + " >= 0 " for v in symbol_table.keys() if not v.endswith("_prev") and symbol_table[v].type in ["natural", "nat"]]) + ")) return;"]

    choices = ["if(" + str(t.condition).replace(" = ", " == ").replace(" & ", " && ") + "){"
               + ("\n\t" if len(t.action) > 0 else "")
               + "\n\t\t".join([str(act.left) + " = " + str(act.right) + ";" for act in t.action if
                                not is_boolean(act.left, program.valuation)])
               + "\n\t} else {"
               # + "\n\t} else if(!" + str(t.condition).replace(" = ", " == ").replace(" & ", " && ") + "){"
               + "\n\t\tbreak;"
               + "\n\t}"
               for t in loop_before_exit] \
              + ["if(" + str(exit_cond) + ") break;" if str(exit_cond.simplify()).lower() != "true" else ""]

    loop_code = "\n\twhile(true){\n\t" \
                + "\n\t".join(choices) \
                + "\t}"

    c_code = "#include<stdbool.h>\n\nvoid main(" + param_list + "){\n\t" + "\n\t".join(init) + loop_code + "\n}"
    c_code = c_code.replace("TRUE", "true")
    c_code = c_code.replace("True", "true")
    c_code = c_code.replace("FALSE", "false")
    c_code = c_code.replace("False", "false")

    return c_code


def use_liveness_refinement(ce: [dict], program, symbol_table):
    assert len(ce) > 0

    counterstrategy_states_con = [key for dict in ce for key, value in dict.items()
                                  if dict["turn"] == "env" and key.startswith("st_") and value == "TRUE"]

    last_state = counterstrategy_states_con[len(counterstrategy_states_con) - 2]
    if last_state in counterstrategy_states_con[:-1]:
        indices_of_prev_visits = [i for i, x in enumerate(counterstrategy_states_con[:-1]) if x == last_state]
        corresponding_ce_state = [ce[(3 * i)] for i in (indices_of_prev_visits)] + [ce[len(ce) - 2]]
        var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                           for i in range(0, len(corresponding_ce_state) - 1)]
        var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in var_differences]
        var_differences = [[v for v in vs if v in symbol_table.keys()] for vs in var_differences]
        if any([x for xs in var_differences for x in xs if
                re.match("(int(eger)?|nat(ural)?|real)", symbol_table[x].type)]):

            if not len(indices_of_prev_visits) > 0:
                raise Exception("Something weird here.")

            first_index = indices_of_prev_visits[0]
            ce_prog_init_trans = prog_transition_indices_and_state_from_ce(ce[0:first_index])
            ce_prog_init_trans_concretised = concretize_transitions(program, ce_prog_init_trans)
            ce_prog_loop_trans = prog_transition_indices_and_state_from_ce(ce[first_index + 1:])
            ce_prog_loop_tran_concretised = concretize_transitions(program, ce_prog_loop_trans)
            entry_predicate = interpolation(ce, program, ce_prog_init_trans_concretised + ce_prog_loop_tran_concretised, len(ce_prog_init_trans) + 1, symbol_table)
            return True, ce_prog_loop_trans, entry_predicate
        else:
            return False, None, None
    else:
        return False, None, None