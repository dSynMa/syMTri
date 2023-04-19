import re

from pysmt.fnode import FNode
from pysmt.shortcuts import And, Not, serialize

from parsing.string_to_prop_logic import string_to_prop, string_to_math_expression
from programs.analysis.ranker import Ranker
from programs.typed_valuation import TypedValuation
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.util import ce_state_to_formula, fnode_to_formula, ground_formula_on_ce_state_with_index, \
    project_ce_state_onto_ev, get_differently_value_vars, ground_formula_on_ce_state, transition_associated_with_state
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct, conjunct_formula_set, neg, true, is_boolean, dnf, infinite_type, type_constraints, \
    propagate_negations, simplify_formula_with_math, cnf, disjunct_formula_set, is_tautology, implies
from prop_lang.value import Value
from prop_lang.variable import Variable

import logging
logger = logging.getLogger(__name__)

smt_checker = SMTChecker()

def safety_refinement(ce: [dict], agreed_on_transitions: [(Transition, dict)],
                      disagreed_on_state: (Formula, dict), abstract_transitions : [[[Transition]]],
                      symbol_table, program, use_dnf=False) -> [FNode]:
    # we collect interpolants in this set
    Cs = set()

    concurring_transitions = agreed_on_transitions

    # this is a hack to ensure correct behaviour when there is a mismatch with only transition (disagreed_on)
    # since interpolation requires len(concurring_transitions) to be at least one 1
    if concurring_transitions == []:
        concurring_transitions = [(Transition(program.initial_state, true(), [], [], program.initial_state), ce[0])]

    # abstract_path = [abstract_transitions[0][0]]
    # # identify one path in abstraction
    # for abs_ts in abstract_transitions:
    #     abstract_path += [t for t in abs_ts if t.src == abstract_path[-1].tgt]
    #
    # abstract_transitions = [[t] for t in abstract_path]

    for s in disagreed_on_state[0]:
        # ground and DNF disagreed_on_state formula
        grounded_condition = ground_formula_on_ce_state(propagate_negations(s),
                                                        project_ce_state_onto_ev(disagreed_on_state[1],
                                                                                            program.env_events
                                                                                            + program.con_events))
        if use_dnf:
            # some simplification before DNFing
            if isinstance(grounded_condition, BiOp) and grounded_condition.op[0] == "|":
                Bs = grounded_condition.sub_formulas_up_to_associativity()
                Bs = [b for b in Bs if not (isinstance(b, Value) and b.is_false())
                                        and not (isinstance(b, UniOp) and b.op == "!" and isinstance(b.right, Value) and b.right.is_true())]
            else:
                Bs = [grounded_condition]

            if use_dnf:
                new_Bs = []
                for b in Bs:
                    b_simplified = simplify_formula_with_math(b, symbol_table)
                    after_dnf = dnf((b_simplified), symbol_table)
                    if isinstance(after_dnf, BiOp) and after_dnf.op[0] == "|":
                        new_Bs += after_dnf.sub_formulas_up_to_associativity()
                    else:
                        new_Bs += [after_dnf]
                Bs = new_Bs
        else:
            # some simplification before DNFing
            if isinstance(grounded_condition, BiOp) and grounded_condition.op[0] == "&":
                Bs = grounded_condition.sub_formulas_up_to_associativity()
                Bs = [b for b in Bs if not (isinstance(b, Value) and b.is_true())
                                        and not (isinstance(b, UniOp) and b.op == "!" and isinstance(b.right, Value) and b.right.is_false())]
            else:
                Bs = [grounded_condition]

            new_Bs = []
            for b in Bs:
                b_simplified = simplify_formula_with_math(b, symbol_table)
                after_dnf = cnf((b_simplified), symbol_table)
                if isinstance(after_dnf, BiOp) and after_dnf.op[0] == "&":
                    new_Bs += after_dnf.sub_formulas_up_to_associativity()
                else:
                    new_Bs += [after_dnf]
            Bs = new_Bs

        Bs = [b for b in Bs if not (isinstance(b, Value))]

        if len(Bs) == 0:
            raise Exception("No interpolants found.")

        for j in reversed(range(0, len(concurring_transitions) + 1)):
            Css = interpolation(program, concurring_transitions, abstract_transitions, Bs, disagreed_on_state[1], j, symbol_table, use_dnf=use_dnf)
            if Css is None:
                logger.info("I think that interpolation is being checked against formulas that are not contradictory.")
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

            # if not use_dnf and len(Cs) > 0:
            #     break

    return {C.to_nuxmv() for C in Cs}


def interpolation(program: Program, concurring_transitions: [(Transition, dict)], abstract_transitions : [[[Transition]]],
                  Bs : [Formula], disagreed_on_state: dict, cut_point: int, symbol_table, use_dnf=False, use_abstract_knowledge=False):
    assert cut_point <= len(concurring_transitions)
    assert len(concurring_transitions) > 0

    logic = "QF_UFLRA"  # TODO what to put here?
    smt_checker = SMTChecker()

    # this will be used to add intermediate variables for each monitor state
    ith_vars = lambda i: [BiOp(Variable(v), ":=", Variable(v + "_" + str(i))) for v in symbol_table.keys() if not v.endswith("_prev")] + \
                         [BiOp(Variable(v), ":=", Variable(v.split("_prev")[0] + "_" + str(i-1))) for v in symbol_table.keys() if
                        v.endswith("_prev")]


    # symbol table is updated with intermediate variables (plus last one, len(prefix), for state after last transition
    new_symbol_table = {}
    for i in range(0, len(concurring_transitions) + 1):
        new_symbol_table.update({key + "_" + str(i): value for key, value in symbol_table.items()})

    # this will be used to generalise the interpolants references to intermediate variables to the original variable name
    reset_vars_i = lambda i, suffix : [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v) + "_" + suffix) for v in symbol_table.keys() if not v.endswith("_prev")]
    reset_vars = [BiOp(Variable(v + "_" + str(i)), ":=", Variable(v)) for v in symbol_table.keys() for i in
                  range(0, len(concurring_transitions) + 1) if not v.endswith("_prev")]

    # init_prop = ce_state_to_formula(concurring_transitions[0][1], symbol_table).replace(ith_vars(0))
    init_prop = conjunct_formula_set([BiOp(Variable(tv.name), " = ", Value(tv.value)) for tv in program.valuation])
    init_prop = init_prop.replace(ith_vars(0))

    abstract_states = []

    path_formula_set_A = []
    path_formula_set_A += [init_prop]
    for i in range(0, cut_point):
        path_formula_set_A += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]

        if use_abstract_knowledge:
            if i == 0:
                abstract_states += [disjunct_formula_set({conjunct_formula_set(
                    [p for p in t.tgt.predicates if not any(v for v in p.variablesin() if v.name.endswith("_prev"))])
                                                         .replace(ith_vars(i + 1)) for t in abstract_transitions[i]})]
            else:
                src_preds = {frozenset(t.src.predicates) for t in abstract_transitions[i]}
                src_preds_to_tgt_preds = {src: frozenset([frozenset(t.tgt.predicates)
                                                            for t in abstract_transitions[i]
                                                                if set(t.src.predicates) == src])
                                                                    for src in src_preds}

                abstract_states += [implies(conjunct_formula_set([p for p in src if not any(v for v in p.variablesin() if v.name.endswith("_prev"))]).replace(ith_vars(i)),
                                                disjunct_formula_set([conjunct_formula_set([p for p in tgt if not any(v for v in p.variablesin() if v.name.endswith("_prev"))]).replace(ith_vars(i+1))
                                                                      for tgt in src_preds_to_tgt_preds[src]]))
                                        for src in src_preds]

    path_formula_A = conjunct_formula_set(path_formula_set_A)

    path_formula_set_B = []
    upper_bound = len(concurring_transitions)
    i = cut_point
    while i < upper_bound:
        path_formula_set_B += [BiOp(Variable(act.left.name + "_" + str(i + 1)),
                                    "=",
                                    act.right.replace(ith_vars(i))) for act in
                               program.complete_action_set(concurring_transitions[i][0].action)]
        if use_abstract_knowledge:
            if i == 0:
                abstract_states += [disjunct_formula_set({conjunct_formula_set(
                    [p for p in t.tgt.predicates if not any(v for v in p.variablesin() if v.name.endswith("_prev"))])
                                                         .replace(ith_vars(i + 1)) for t in abstract_transitions[i]})]
            else:
                src_preds = {frozenset(t.src.predicates) for t in abstract_transitions[i]}
                src_preds_to_tgt_preds = {src: frozenset([frozenset(t.tgt.predicates)
                                                            for t in abstract_transitions[i]
                                                                if set(t.src.predicates) == src])
                                                                    for src in src_preds}

                abstract_states += [implies(conjunct_formula_set([p for p in src if not any(v for v in p.variablesin() if v.name.endswith("_prev"))]).replace(ith_vars(i)),
                                                disjunct_formula_set([conjunct_formula_set([p for p in tgt if not any(v for v in p.variablesin() if v.name.endswith("_prev"))]).replace(ith_vars(i+1))
                                                                      for tgt in src_preds_to_tgt_preds[src]]))
                                        for src in src_preds]

        i += 1

    Cs = set()

    for B in Bs:
        projected_condition = B.replace(ith_vars(len(concurring_transitions)))
        if any(v for v in projected_condition.variablesin() if "_prev" in str(v)):
            projected_condition = projected_condition.replace(
                [BiOp(Variable(str(v)), ":=", Variable(str(v).split("_prev")[0] + "_" + str(i - 1))) for v in
                 projected_condition.variablesin() if "_prev" in str(v)])

        B_formulas = path_formula_set_B + [projected_condition]
        if use_abstract_knowledge:
            B_formulas += abstract_states

        path_formula_B = conjunct_formula_set(B_formulas)

        A = And(*conjunct(init_prop, path_formula_A).to_smt(new_symbol_table))
        B = And(*path_formula_B.to_smt(new_symbol_table))
        # B_cnf = cnf(path_formula_B, new_symbol_table)
        # if(B_cnf.op[0] == "&"):
        #     Bs = B_cnf.sub_formulas_up_to_associativity()
        # else:
        #     Bs = [B_cnf]
        #
        # new_Bs = set()
        # for b in Bs:
        #     b_smt = b.to_smt(new_symbol_table)
        #     new_Bs |= {b_smt[0], b_smt[1]}
        # A_min, B_min = smt_checker.unsatcore(A, B)
        # print(serialize(A_min))
        # print(serialize(B_min))

        # for B in new_Bs:
        C = smt_checker.binary_interpolant(A, B, logic)

        if C is not None:
            Cfs = []
            C_formula = fnode_to_formula(C)
            # TODO do cnf here instead?
            if isinstance(C_formula, BiOp) and C_formula.op[0] == "&":
                Cfs = C_formula.sub_formulas_up_to_associativity()
            else:
                Cfs = [C_formula]
            for Cf in Cfs:
                Cf_normalized = Cf.replace(reset_vars)
                Cf_smt = Cf_normalized.to_smt(symbol_table)
                # if C is not a tautology and not a contradiction
                if smt_checker.check((And(Not(Cf_smt[0]), Cf_smt[1]))) and\
                    smt_checker.check((And((Cf_smt[0]), Cf_smt[1]))):
                    Cf = Cf_normalized
                    Cs |= {Cf}
                else: # if C is a tautology or a contradiction, resolve previous vars until it s not either
                    # previous_vars_related_to_current_vars = \
                    #     [v for v in Cf.variablesin()
                    #      if Variable(str(v).split("_")[0] + "_" + str(int(str(v).split("_")[1]) - 1)) in Cf.variablesin()]
                    # if len(previous_vars_related_to_current_vars) > 0:
                    # ground previous variables on their values;
                    # TODO instead of just looking one step back, have to go back to the first action,
                    #  or just use the variables value in the previous step
                    for j in reversed(range(1, i)):
                        Cf = Cf.replace([BiOp(Variable(act.left.name + "_" + str(j)), ":=", act.right.replace(ith_vars(j - 1))) for act in concurring_transitions[j][0].action])
                        Cf = Cf.replace(
                            [BiOp(Variable(v + "_" + str(j)), ":=", Variable(v + "_" + str(j - 1))) for v in symbol_table.keys()])
                        # if not is_tautology(Cf.replace(reset_vars), symbol_table, smt_checker):
                            #     break
                        if not is_tautology(Cf.replace(reset_vars), symbol_table, smt_checker)\
                                and not is_tautology(neg(Cf.replace(reset_vars)), symbol_table, smt_checker):
                            break
                    if not is_tautology(Cf.replace(reset_vars), symbol_table, smt_checker)\
                                and not is_tautology(neg(Cf.replace(reset_vars)), symbol_table, smt_checker):
                        Cf = Cf.replace(reset_vars)
                        Cs |= {Cf}
                    else:
                        Cf = Cf.replace([BiOp(Variable(tv.name + "_0"), " = ", Value(tv.value)) for tv in program.valuation])
                        if not is_tautology(Cf.replace(reset_vars), symbol_table, smt_checker) \
                                and not is_tautology(neg(Cf.replace(reset_vars)), symbol_table, smt_checker):
                            Cf = Cf.replace(reset_vars)
                            Cs |= {Cf}

    if len(Cs) == 0:
        return None
    else:
        return Cs


def liveness_refinement(symbol_table, program, entry_condition, unfolded_loop: [Transition], exit_predicate_grounded, add_natural_conditions=True):
    try:
        c_code = loop_to_c(symbol_table, program, entry_condition, unfolded_loop,
                           exit_predicate_grounded, add_natural_conditions)
        logger.info(c_code)
        ranker = Ranker()
        success, ranking_function, invars = ranker.check(c_code)

        # while not success or (success and any(v for v in ranking_function.variablesin() if symbol_table[str(v)].type.startswith("int"))):
        #     if success and any(v for v in ranking_function.variablesin() if symbol_table[str(v)].type.startswith("int")):
        #         print("Warning: The ranking function <<" + str(ranking_function) + ">> contains integer variables.\n"
        #               "We thus cannot guarantee the ranking abstraction will be a sound abstraction of the program.")
        #         print("Re-enter the same function if you want to continue with it, or suggest a new one.")
        #         text = raw_input("Enter 'force' to force the use of this unsound a ranking function, or 'stop' to quit ranking refinement:")
        #         if text.lower().startswith("force"):
        #             return ranking_function, invars
        #         elif text.lower().startswith("stop"):
        #             raise Exception("Exit: Terminated by user.")
        #
        #     if not success:
        #         print("Could not find a ranking function.")
        #
        #         text = raw_input("Enter 'stop' to quit, or suggest a ranking function:")
        #     if text == "stop":
        #         raise Exception("Exit: Terminated by user.")
        #     try:
        #         ranking_function, invars = string_to_math_expression(text), []
        #         success = True
        #     except Exception as e:
        #         print(str(e))
        #         success = False

        if not success:
            raise Exception("Could not prove termination.")

        return ranking_function, invars
    except Exception as e:
        raise e


def loop_to_c(symbol_table, program: Program, entry_condition: Formula, loop_before_exit: [Transition],
              exit_cond: Formula, add_natural_conditions=True):
    # params
    params = list(set(symbol_table[str(v)].type + " " + str(v)
                      for v in {v.name for v in program.valuation} | set(entry_condition.variablesin())
                      if
                      not is_boolean(v, program.valuation) and [str(vv) for t in loop_before_exit for vv in
                                                                (t.condition.variablesin()
                                                                 + entry_condition.variablesin()
                                                                 + exit_cond.variablesin()
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
    if add_natural_conditions:
        init = ["if(!(" + " && ".join(natural_conditions) + ")) return;" if len(natural_conditions) > 0 else ""]
    else:
        init = []
    choices = []

    for t in loop_before_exit:
        safety = str(type_constraints(t.condition, symbol_table)).replace(" = ", " == ").replace(" & ",
                                                                                                    " && ").replace(
            " | ", " || ")
        cond_simpl = str(t.condition.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ", " || ")
        acts = "\n\t\t".join([str(act.left) + " = " + str(act.right) + ";" for act in t.action if
                              not is_boolean(act.left, program.valuation) if act.left != act.right])

        if isinstance(string_to_prop(cond_simpl).simplify(), Value):
            if string_to_prop(cond_simpl).simplify().is_false():
                choices += ["break;"]
            elif string_to_prop(cond_simpl).simplify().is_true():
                choices += ["\t" + acts]
        else:
            # choices += ["\tif(" + cond_simpl + ") {" + acts + "}\n\t\t else break;"]
            choices += ["\t" + acts + ""]
        if safety != "true":
            if "..." in safety:
                raise Exception("Error: The loop contains a transition with a condition that is not a formula.")
            # choices += ["\tif(!(" + safety + ")) break;"]

    exit_cond_simplified = str(exit_cond.simplify()) \
        .replace(" = ", " == ") \
        .replace(" & ", " && ") \
        .replace(" | ", " || ")
    exit_cond_var_constraints = str(type_constraints(exit_cond, symbol_table)) \
        .replace(" = ", " == ") \
        .replace(" & ", " && ") \
        .replace(" | ", " || ")

    # TODO check for satisfiability instead of equality of with true
    # choices = [
    #               "\tif(!(" + exit_cond_var_constraints + ")) break;" if exit_cond_var_constraints.lower() != "true" else ""] \
    #           + choices
    choices = ["\tif(" + exit_cond_simplified + ") break;" if exit_cond_simplified.lower() != "true" else ""] \
              + choices

    loop_code = "\n\tdo{\n\t" \
                + "\n\t".join(choices) \
                + "\n\t} while(true);\n"

    loop_code = "\n\tif(" + str(entry_condition.simplify()).replace(" = ", " == ").replace(" & ", " && ").replace(" | ",
                                                                                                                  " || ") \
                + "){" + loop_code + "\n\t}"

    c_code = "#include<stdbool.h>\n\nvoid main(" + param_list + "){\n\t" + "\n\t".join(init).strip() + loop_code + "\n}"
    c_code = c_code.replace("TRUE", "true")
    c_code = c_code.replace("True", "true")
    c_code = c_code.replace("FALSE", "false")
    c_code = c_code.replace("False", "false")

    return c_code


def use_liveness_refinement_state(env_con_ce: [dict], last_cs_state, disagreed_on_state_dict, symbol_table):
    ce_with_stutter_states = []
    env_turn = True
    new_i_to_old_i = {}
    i = 0
    old_i = 0
    while i < len(env_con_ce):
        if env_turn:
            env_turn = False
            if env_con_ce[i]["turn"] == "env":
                ce_with_stutter_states.append((i, env_con_ce[i]))
                new_i_to_old_i[i] = old_i
            else:
                env_copy = env_con_ce[max(0, i - 1)]
                env_copy["turn"] = "env"
                ce_with_stutter_states.append((i + 1, env_con_ce[max(0, i - 1)]))
                new_i_to_old_i[old_i] = max(0, i - 1)
        else:
            env_turn = True
            if env_con_ce[i]["turn"] == "con":
                ce_with_stutter_states.append((i, env_con_ce[i]))
                new_i_to_old_i[i] = old_i
            else:
                con_copy = env_con_ce[max(0, i - 1)]
                con_copy["turn"] = "con"
                ce_with_stutter_states.append((i + 1, env_con_ce[max(0, i - 1)]))
                new_i_to_old_i[old_i] = max(0, i - 1)
        i += 1
        old_i += 1

    # ce_with_stutter_states.append(env_con_ce[-1])
    ce_with_stutter_states.append((len(env_con_ce), disagreed_on_state_dict))
    # if disagreed_on_state_dict["turn"] == "con":
    #     disagreed_on_state_dict_env = disagreed_on_state_dict
    #     disagreed_on_state_dict_env["turn"] = "env"
    #     ce_with_stutter_states.append(disagreed_on_state_dict_env)

    previous_visits = [i for i, dict in (ce_with_stutter_states) for key, value in dict.items()
                       if key == last_cs_state and value == "TRUE"]
    if len(previous_visits) - 1 > 0: # ignoring last visit
        var_differences = []

        for i, visit in enumerate(previous_visits[:-1]):
            corresponding_ce_state = [ce_with_stutter_states[i][1] for i in range(visit, previous_visits[i + 1] + 1)]

            any_var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                               for i in range(0, len(corresponding_ce_state) - 1)]
            any_var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in any_var_differences]
            any_var_differences = [[v for v in vs if v in symbol_table.keys() and not str(v).endswith("_prev")] for vs in any_var_differences]
            any_var_differences = [[] != [v for v in vs if
                                      not re.match("(bool(boolean)?)", symbol_table[v].type)] for vs in
                                      # the below only identifies loops when there are changes in infinite-domain variables in the loop
                                      # re.match("(int(eger)?|nat(ural)?|real|rational)", symbol_table[v].type)] for vs in
                               any_var_differences]
            if True in any_var_differences:
                var_differences += [True]
            else:
                var_differences += [False]

        if True in var_differences:
            # index_of_first_loop_entry = var_differences.index(True)
            # first_index = new_i_to_old_i[previous_visits[index_of_first_loop_entry]]
            index_of_last_loop_entry = len(var_differences) - 1 - var_differences[::-1].index(True)
            first_index = new_i_to_old_i[previous_visits[index_of_last_loop_entry]]
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
                            disagreed_on_state,
                            program_taken_transition,
                            last_counterstrategy_state,
                            symbol_table, pred_label_to_formula,
                            only_env_desired_loops=True):
    yes = False
    mon_transitions = [(y, st) for (y, st) in agreed_on_transitions]
    ce = [x for _, x in agreed_on_transitions]

    # TODO we can do more analysis here
    # check first if there are actions that change the value of a variable
    if not any(a for t, _ in mon_transitions for a in t.action if not isinstance(a.right, Value) and
                                                                  not symbol_table[str(a.left)] == "bool" and
                                                                  not a.left == a.right):
        return False, None, None, None, None, None

    # check if the counterstrategy tried to remain in a loop in its structure
    # checking if the last compatible state was already seen, and there was a change in an infinite valued variable in a non-boolean variable
    yes_state, first_index_state = use_liveness_refinement_state(ce, last_counterstrategy_state, disagreed_on_state[1], symbol_table)
    if yes_state:
        yes = True
        first_index = first_index_state
        loop_in_cs = True

    # check if the program is actually looping
    if not only_env_desired_loops and not yes_state:
        prev_appearance = [t == program_taken_transition[0] for t, _ in mon_transitions]
        if True in prev_appearance:
            yes = True
            first_index = len(prev_appearance) - 1 - prev_appearance[::-1].index(True)
            loop_in_cs = False

    if yes:
        ce_prog_loop_tran_concretised = mon_transitions[first_index:]
        # prune up to predicate mismatch
        # TODO THIS IS NOT CORRECT
        # ce_prog_loop_tran_concretised = []
        pred_mismatch = False
        pred_symbol_table = symbol_table | {str(p):TypedValuation(str(p), "bool", None) for p in pred_label_to_formula.keys() if isinstance(p, Variable)}
        exit = False

        # TODO simplify loop by finding repeated sequences


        if [] == [t for t, _ in ce_prog_loop_tran_concretised if [] != [a for a in t.action if a.left != a.right and infinite_type(a.left, program.valuation)]]:
            return False, None, None, None, None, None

        entry_valuation = conjunct_formula_set([BiOp(Variable(key), "=", Value(value))
                                                    for tv in program.valuation
                                                    for key, value in ce_prog_loop_tran_concretised[0][1].items()
                                                    if key == tv.name])

        true_preds = [p for p in pred_label_to_formula.values() if smt_checker.check(And(*conjunct(p, entry_valuation).to_smt(symbol_table)))]
        false_preds = [neg(p) for p in pred_label_to_formula.values() if p not in true_preds]
        entry_predicate = conjunct_formula_set(true_preds + false_preds)

        return True, ce_prog_loop_tran_concretised, entry_valuation, entry_predicate, pred_mismatch, loop_in_cs
    else:
        return False, None, None, None, None, None
