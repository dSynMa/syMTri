import re

from click._compat import raw_input
from pysmt.fnode import FNode
from pysmt.shortcuts import And

from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from programs.analysis.ranker import Ranker
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import ce_state_to_formula, fnode_to_formula, ground_formula_on_ce_state_with_index, \
    project_ce_state_onto_ev, get_differently_value_vars
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, conjunct_formula_set, neg, true, is_boolean, dnf, infinite_type
from prop_lang.value import Value
from prop_lang.variable import Variable


def safety_refinement(ce: [dict], agreed_on_transitions: [[(Transition, dict)]],
                      disagreed_on_transitions: ([Transition], dict), symbol_table, program, use_dnf=False) -> [FNode]:
    # we collect interpolants in this set
    Cs = set()

    concurring_transitions = [x for xs in agreed_on_transitions for x in xs]

    # this is a hack to ensure correct behaviour when there is a mismatch with only transition (disagreed_on)
    # since interpolation requires len(concurring_transitions) to be at least one 1
    if concurring_transitions == []:
        concurring_transitions = [(Transition(program.initial_state, true(), [], [], program.initial_state), ce[0])]

    for t in disagreed_on_transitions[0]:
        neg_t = t.with_condition(neg(t.condition))
        for j in reversed(range(0, len(concurring_transitions) + 1)):
            Css = interpolation(program, concurring_transitions, (neg_t, disagreed_on_transitions[1]), j, symbol_table, use_dnf=use_dnf)
            if Css is None:
                print("I think that interpolation is being checked against formulas that are not contradictory.")
                break
            # if B is itself inconsistent
            if len(Cs) == 1 and isinstance(list(Cs)[0], Value):
                if list(Cs)[0].is_true():
                    break
                elif list(Cs)[0].is_false():
                    break

            for C in Css:
                if isinstance(C, BiOp) and C.op[0] == "&":
                    Cs |= set(C.sub_formulas_up_to_associativity())
                elif isinstance(C, Value):
                    if C.is_true():
                        continue
                    elif C.is_false():
                        continue
                else:
                    Cs |= {C}

    return Cs


def interpolation(program: Program, concurring_transitions: [(Transition, dict)], disagreed_on: (Transition, dict),
                  cut_point: int, symbol_table, use_dnf=False):
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
    upper_bound = len(concurring_transitions)
    i = cut_point
    while i < upper_bound:
        path_formula_set_B += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]
        i += 1

    disagreed_on_transition = disagreed_on[0]
    disagreed_on_state = disagreed_on[1]
    projected_condition = disagreed_on_transition.condition.replace(ith_vars(len(concurring_transitions)))
    grounded_condition = ground_formula_on_ce_state_with_index(projected_condition,
                                                               project_ce_state_onto_ev(disagreed_on_state,
                                                                                        program.env_events
                                                                                        + program.con_events),
                                                               len(concurring_transitions))

    # some simplification before DNFing
    if isinstance(grounded_condition, BiOp) and grounded_condition.op[0] == "&":
        Bs = list(map(neg, grounded_condition.sub_formulas_up_to_associativity()))
    elif isinstance(grounded_condition, UniOp) and grounded_condition.op == "!":
        if isinstance(grounded_condition.right, BiOp) and grounded_condition.op[0] == "|":
            Bs = grounded_condition.sub_formulas_up_to_associativity()
        else:
            Bs = [grounded_condition.right]
    else:
        Bs = [neg(grounded_condition)]

    if use_dnf:
        new_Bs = []
        for b in Bs:
            after_dnf = dnf(b)
            if isinstance(after_dnf, BiOp) and after_dnf.op[0] == "|":
                new_Bs += after_dnf.sub_formulas_up_to_associativity()
            else:
                new_Bs += [after_dnf]
        Bs = new_Bs

    Cs = set()

    for BB in Bs:
        path_formula_B = conjunct_formula_set(path_formula_set_B + [BB])

        A = And(*conjunct(init_prop, path_formula_A).to_smt(new_symbol_table))
        B = And(*path_formula_B.to_smt(new_symbol_table))

        C = smt_checker.binary_interpolant(A, B, logic)

        if C is not None:
            Cf = fnode_to_formula(C).replace(reset_vars).simplify()
            Cs |= {Cf}

    if len(Cs) == 0:
        return None
    else:
        return Cs


def liveness_refinement(symbol_table, program, entry_predicate, entry_predicate_in_terms_of_preds, unfolded_loop,
                        exit_predicate_grounded):
    try:
        # try to come up with a ranking function
        c_code = loop_to_c(symbol_table, program, entry_predicate_in_terms_of_preds, unfolded_loop, exit_predicate_grounded)
        print(c_code)
        ranker = Ranker()
        try:
            success, ranking_function, invars = ranker.check(c_code)
        except:
            success = False
        if not success:
            c_code = loop_to_c(symbol_table, program, entry_predicate, unfolded_loop,
                               exit_predicate_grounded)
            print(c_code)
            ranker = Ranker()
            success, ranking_function, invars = ranker.check(c_code)
            if not success:
                print("Could not find a ranking function for: \n" + c_code)
                text = raw_input("Any suggestions?")
                ranking_function, invars = string_to_math_expression(text), []

        return ranking_function, invars
    except Exception as e:
        raise e


def loop_to_c(symbol_table, program: Program, entry_predicate: Formula, loop_before_exit: [Transition],
              exit_cond: Formula):
    # params
    params = list(set(symbol_table[str(v)].type + " " + str(v)
                      for v in {v.name for v in program.valuation} | set(entry_predicate.variablesin())
                      if
                      not is_boolean(v, program.valuation) and [str(vv) for t in loop_before_exit for vv in
                                                                (t.condition.variablesin()
                                                                 + entry_predicate.variablesin()
                                                                 + [act.left for act in t.action]
                                                                 + [a for act in t.action for a in
                                                                    act.right.variablesin()])]))
    param_list = ", ".join(params)
    param_list = param_list.replace("integer", "int") \
        .replace("natural", "int") \
        .replace("nat", "int") \
        .replace("real", "double")

    natural_conditions = [v.split(" ")[1] + " >= 0 " for v in params if
                          not v.endswith("_prev") and symbol_table[v.split(" ")[1]].type in ["natural",
                                                                                             "nat"]]
    init = ["if(!(" + " && ".join(natural_conditions) + ")) return;" if len(natural_conditions) > 0 else ""]

    choices = []

    for t in loop_before_exit:
        safety = str(t.condition.simplify().to_smt(symbol_table)[1]).replace(" = ", " == ").replace(" & ",
                                                                                                    " && ").replace(
            " | ", " || ")
        cond_simpl = str(t.condition.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ", " || ")
        acts = "\n\t\t".join([str(act.left) + " = " + str(act.right) + ";" for act in t.action if
                              not is_boolean(act.left, program.valuation)])

        if isinstance(string_to_prop(cond_simpl).simplify(), Value):
            if string_to_prop(cond_simpl).simplify().is_false():
                choices += ["break;"]
            elif string_to_prop(cond_simpl).simplify().is_true():
                choices += ["\t" + acts]
        else:
            choices += ["\tif(" + cond_simpl + ") {" + acts + "}\n\t\t else break;"]
        choices += ["\tif(!(" + safety + ")) break;"]

    exit_cond_simplified = str(exit_cond.simplify()) \
        .replace(" = ", " == ") \
        .replace(" & ", " && ") \
        .replace(" | ", " || ")
    exit_cond_var_constraints = str(exit_cond.simplify().to_smt(symbol_table)[1]) \
        .replace(" = ", " == ") \
        .replace(" & ", " && ") \
        .replace(" | ", " || ")

    # TODO check for satisfiability instead of equality of with true
    choices = [
                  "\tif(!(" + exit_cond_var_constraints + ")) break;" if exit_cond_var_constraints.lower() != "true" else ""] + choices
    choices = ["\tif(" + exit_cond_simplified + ") break;" if exit_cond_simplified.lower() != "true" else ""] + choices

    loop_code = "\n\tdo{\n\t" \
                + "\n\t".join(choices) \
                + "\n\t} while(true);\n"

    loop_code = "\n\tif(" + str(entry_predicate.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ",
                                                                                                                  " || ") \
                + "){" + loop_code + "\n\t}"

    c_code = "#include<stdbool.h>\n\nvoid main(" + param_list + "){\n\t" + "\n\t".join(init).strip() + loop_code + "\n}"
    c_code = c_code.replace("TRUE", "true")
    c_code = c_code.replace("True", "true")
    c_code = c_code.replace("FALSE", "false")
    c_code = c_code.replace("False", "false")

    return c_code


def use_liveness_refinement_state(env_con_ce: [dict], last_cs_state, symbol_table):
    previous_visits = [i for i, dict in enumerate(env_con_ce) for key, value in dict.items()
                       if key == last_cs_state and value == "TRUE"]
    if len(previous_visits) - 1 > 0: # ignoring last visit
        var_differences = []

        for i, visit in enumerate(previous_visits[:-1]):
            corresponding_ce_state = [env_con_ce[i] for i in range(visit, previous_visits[i + 1] + 1)]

            any_var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                               for i in range(0, len(corresponding_ce_state) - 1)]
            any_var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in any_var_differences]
            any_var_differences = [[v for v in vs if v in symbol_table.keys()] for vs in any_var_differences]
            any_var_differences = [[] != [v for v in vs if
                                      re.match("(int(eger)?|nat(ural)?|real|rational)", symbol_table[v].type)] for vs in
                               any_var_differences]
            if True in any_var_differences:
                var_differences += [True]
            else:
                var_differences += [False]

        if True in var_differences:
            index_of_last_loop_entry = len(var_differences) - 1 - var_differences[::-1].index(True)

            return True, previous_visits[index_of_last_loop_entry]
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
        indices_of_visits = [i for i, x in enumerate(counterstrategy_trans_con) if
                             any(i for i in last_trans if i in x)]
        corresponding_ce_state = [ce[i] for i in
                                  range((3 * min(*indices_of_visits)) + 1, (3 * max(*indices_of_visits)) + 1)]  #
        var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                           for i in range(0, len(corresponding_ce_state) - 1)]
        var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in var_differences]
        var_differences = [[v for v in vs if v in symbol_table.keys()] for vs in var_differences]
        if any([x for xs in var_differences for x in xs if
                re.match("(int(eger)?|nat(ural)?|real)", symbol_table[x].type)]):

            if len(indices_of_visits) == 0:
                raise Exception("Something weird here.")

            first_index = indices_of_visits[0]

            return True, first_index
        else:
            return False, None
    else:
        return False, None


def use_liveness_refinement(program,
                            agreed_on_transitions,
                            disagreed_on_transitions,
                            last_counterstrategy_state,
                            monitor_actually_took,
                            symbol_table, pred_label_to_formula):
    yes = False
    mon_transitions = [(y, st) for xs in agreed_on_transitions for y, st in xs]
    ce = [x for xs in agreed_on_transitions for _, x in xs] + [disagreed_on_transitions[1]]

    yes_state, first_index_state = use_liveness_refinement_state(ce, last_counterstrategy_state, symbol_table)
    if yes_state:
        yes = True
        first_index = first_index_state

    if yes:
        ce_prog_loop_tran_concretised = mon_transitions[first_index:]

        if [] == [t for t, _ in ce_prog_loop_tran_concretised if [] != [a for a in t.action if infinite_type(a.left, program.valuation)]]:
            return False, None, None, None

        entry_predicate = conjunct_formula_set([BiOp(Variable(key), "=", Value(value))
                                                    for tv in program.valuation
                                                    for key, value in ce_prog_loop_tran_concretised[0][1].items()
                                                    if key == tv.name])

        entry_preds = (
            [(pred_label_to_formula[Variable(key)], value) for key, value in ce_prog_loop_tran_concretised[0][1].items() if
             key.startswith("pred_")])
        entry_predicate_in_terms_of_preds = conjunct_formula_set([p for (p, v) in entry_preds if v == "TRUE"] + [neg(p) for (p, v) in entry_preds if v == "FALSE"])

        return True, ce_prog_loop_tran_concretised, entry_predicate, entry_predicate_in_terms_of_preds
    else:
        return False, None, None, None
