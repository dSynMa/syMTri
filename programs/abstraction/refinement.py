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
    concretize_transitions, transition_up_to_dnf
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from parsing.string_to_prop_logic import string_to_prop
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
        up_to_dnf = transition_up_to_dnf(disagreed_on[i][0])
        for l in range(0, len(up_to_dnf)):
            for j in reversed(range(0, len(concurring_transitions) + i + 1)):
                C = interpolation(program, concurring_transitions + disagreed_on[0:i], (up_to_dnf[l], disagreed_on[i][1]), j, symbol_table)
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


def liveness_refinement(symbol_table, program, entry_predicate, unfolded_loop, exit_transitions):
    exceptions = []
    for i, exit_trans in enumerate(exit_transitions):
        try:
            # try to come up with a ranking function
            c_code = loop_to_c(symbol_table, program, entry_predicate, unfolded_loop + exit_transitions[0:i], exit_trans.condition)
            print(c_code)
            ranker = Ranker()
            success, ranking_function, invars = ranker.check(c_code)
            if not success:
                print("Could not find a ranking function for: \n" + c_code)
                text = raw_input("Any suggestions?")
                ranking_function, invars = string_to_mathexpr(text), []

            return ranking_function, invars
        except Exception as e:
            exceptions.append(e)

    raise exceptions[0]



def loop_to_c(symbol_table, program: Program, entry_predicate: Formula, loop_before_exit: [Transition],
              exit_cond: Formula):
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

    init = ["if(!(" + " && ".join([v + " >= 0 " for v in symbol_table.keys() if
                                     not v.endswith("_prev") and symbol_table[v].type in ["natural",
                                                                                          "nat"]]) + ")) return;"]

    choices = []

    for t in loop_before_exit:
        safety = str(t.condition.simplify().to_smt(symbol_table)[1]).replace(" = ", " == ").replace(" & ", " && ").replace(" | ", " || ")
        cond_simpl = str(t.condition.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ", " || ")
        acts = "\n\t\t".join([str(act.left) + " = " + str(act.right) + ";" for act in t.action if
                                    not is_boolean(act.left, program.valuation)])

        if isinstance(string_to_ltl(cond_simpl).simplify(), Value):
            if string_to_ltl(cond_simpl).simplify().is_false():
                choices += ["break;"]
            elif string_to_ltl(cond_simpl).simplify().is_true():
                choices += ["\t" + acts]
        else:
            choices += ["\tif(" + cond_simpl + ") {" + acts + "}\n\t else break;"]
        choices += ["\tif(!(" + safety + ")) break;"]

    exit_cond_simplified = str(exit_cond.simplify())\
                                       .replace(" = ", " == ")\
                                       .replace(" & ", " && ")\
                                       .replace(" | ", " || ")
    exit_cond_var_constraints = str(exit_cond.simplify().to_smt(symbol_table)[1])\
                                       .replace(" = ", " == ")\
                                       .replace(" & ", " && ")\
                                       .replace(" | ", " || ")

    #TODO check for satisfiability instead of equality of with true
    choices = ["\n\t\tif(!(" + exit_cond_var_constraints + ")) break;" if exit_cond_var_constraints.lower() != "true" else ""] + choices
    choices = ["\n\t\tif(" + exit_cond_simplified + ") break;" if exit_cond_simplified.lower() != "true" else ""] + choices

    loop_code = "\n\tdo{\n\t" \
                + "\n\t".join(choices) \
                + "\n\t} while(true);\n"

    loop_code = "\n\tif(" + str(entry_predicate.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ", " || ") \
                + "){" + loop_code + "\n\t}"

    c_code = "#include<stdbool.h>\n\nvoid main(" + param_list + "){\n\t" + "\n\t".join(init) + loop_code + "\n}"
    c_code = c_code.replace("TRUE", "true")
    c_code = c_code.replace("True", "true")
    c_code = c_code.replace("FALSE", "false")
    c_code = c_code.replace("False", "false")

    return c_code


def use_liveness_refinement_state(ce: [dict], symbol_table):
    counterstrategy_states_con = [key for dict in ce for key, value in dict.items()
                                  if dict["turn"] == "env" and key.startswith("st_") and value == "TRUE"]

    last_state = counterstrategy_states_con[len(counterstrategy_states_con) - 1]
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

            return True, first_index
        else:
            return False, None
    else:
        return False, None

def use_liveness_refinement_trans(ce: [dict], symbol_table):
    counterstrategy_trans_con = []

    for i, state in enumerate(ce):
        if ce[i]["turn"] == "con":
            true_guards = [k.replace("counterstrategy_guard_", "") for k in ce[i].keys()
                           if k.startswith("counterstrategy_guard_")
                           and ce[i][k] == "TRUE"]
            true_acts = [k.replace("counterstrategy_act_", "") for k in ce[i].keys()
                         if k.startswith("counterstrategy_act_")
                         and ce[i][k] == "TRUE"]
            trans = [i for i in true_guards if i in true_acts]
            counterstrategy_trans_con += [set(trans)]
        elif i == len(ce) - 1:
            true_guards = [k.replace("counterstrategy_guard_", "") for k in ce[i].keys()
                           if k.startswith("counterstrategy_guard_")
                           and ce[i][k] == "TRUE"]
            counterstrategy_trans_con += [set(true_guards)]

    last_trans = counterstrategy_trans_con[-1]
    if any(x for x in last_trans if any(y for y in counterstrategy_trans_con[:-1] if x in y)):
        indices_of_prev_visits = [i for i, x in enumerate(counterstrategy_trans_con[:-1]) if
                                  any(i for i in last_trans if i in x)]
        corresponding_ce_state = [ce[(i)] for i in (indices_of_prev_visits)]
        var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                           for i in range(0, len(corresponding_ce_state) - 1)]
        var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in var_differences]
        var_differences = [[v for v in vs if v in symbol_table.keys()] for vs in var_differences]
        if any([x for xs in var_differences for x in xs if
                re.match("(int(eger)?|nat(ural)?|real)", symbol_table[x].type)]):

            if not len(indices_of_prev_visits) > 0:
                raise Exception("Something weird here.")

            first_index = indices_of_prev_visits[0]

            return True, first_index
        else:
            return False, None
    else:
        return False, None


def use_liveness_refinement(ce: [dict], program, symbol_table):
    assert len(ce) > 0

    yes = False

    yes_state, first_index_state = use_liveness_refinement_state(ce, symbol_table)
    if yes_state:
        yes = True
        first_index = first_index_state
    else:
        yes_trans, first_index_trans = use_liveness_refinement_trans(ce, symbol_table)
        if yes_trans:
            yes = True
            first_index = first_index_trans

    if yes:
        ce_prog_loop_trans = prog_transition_indices_and_state_from_ce(ce[first_index + 1:])
        ce_prog_loop_tran_concretised = concretize_transitions(program, ce_prog_loop_trans)

        if first_index != 0:
            ce_prog_init_trans = prog_transition_indices_and_state_from_ce(ce[0:first_index])
            ce_prog_init_trans_concretised = concretize_transitions(program, ce_prog_init_trans)
            entry_predicate = interpolation(program,
                                            [x for xs in ce_prog_init_trans_concretised for x in xs]
                                            + [x for xs in ce_prog_loop_tran_concretised[:-1] for x in xs],
                                            ce_prog_loop_tran_concretised[len(ce_prog_loop_tran_concretised) - 1][0],
                                            first_index,
                                            symbol_table)
        else:
            entry_predicate = true()

        if entry_predicate == None:
            raise Exception("Something weird here. Entry predicate to loop is None.")

        return True, ce_prog_loop_tran_concretised, entry_predicate
    else:
        return False, None, None
