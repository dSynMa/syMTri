import os
import re
import shutil

from pysmt.factory import SolverRedefinitionError
from pysmt.fnode import FNode
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import get_env, And, Not

from programs.analysis.model_checker import ModelChecker
from programs.analysis.nuxmv_model import NuXmvModel
from programs.analysis.smt_checker import SMTChecker
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, conjunct, neg, append_to_variable_name, dnf
from prop_lang.value import Value
from prop_lang.variable import Variable

smt_checker = SMTChecker()

def create_nuxmv_model_for_compatibility_checking(program_model: NuXmvModel, strategy_model: NuXmvModel, mon_events,
                                                  pred_list):
    text = "MODULE main\n"
    vars = sorted(program_model.vars) \
           + sorted([v for v in strategy_model.vars
                     if v not in program_model.vars]) \
           + ["mismatch : boolean"]
    text += "VAR\n" + "\t" + ";\n\t".join(vars) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(program_model.define + strategy_model.define) + ";\n"
    env_turn = BiOp(Variable("turn"), "=", Value("env"))

    prog_and_mon_events_equality = [BiOp(m, '=', Variable("mon_" + m.name)) for m in mon_events]
    text += "\tcompatible := !(turn = mon) | (" + str(
        conjunct_formula_set(prog_and_mon_events_equality)) + ");\n"
    # TODO consider adding checks that state predicates expected by env are true, for debugging predicate abstraction

    text += "INIT\n" + "\t(" + ")\n\t& (".join(
        program_model.init + strategy_model.init + ["turn = env", "mismatch = FALSE"]) + ")\n"
    text += "INVAR\n" + "\t((" + ")\n\t& (".join(program_model.invar + strategy_model.invar) + "))\n"

    turn_logic = ["(turn = con -> next(turn) = env)"]
    turn_logic += ["(turn = env -> next(turn) = mon)"]
    turn_logic += ["(turn = mon -> next(turn) = con)"]

    maintain_mon_vars = str(conjunct_formula_set(
        [BiOp(UniOp("next", Variable("mon_" + m.name)), ' = ', Variable("mon_" + m.name)) for m in (mon_events)]
        + [BiOp(UniOp("next", Variable(m.name)), ' = ', Variable(m.name)) for m in
           [label_pred(p, pred_list) for p in pred_list]]))
    new_trans = ["compatible", "!next(mismatch)"] + program_model.trans + strategy_model.trans + turn_logic
    normal_trans = "\t((" + ")\n\t& (".join(new_trans) + "))\n"

    normal_trans += "\t | (!compatible & " + \
                    " next(mismatch) & identity_" + program_model.name + \
                    " & identity_" + strategy_model.name + " & next(turn) = turn & " + maintain_mon_vars + ")"
    normal_trans = "(!mismatch -> (" + normal_trans + "))"

    deadlock = "(mismatch -> (next(mismatch) & identity_" + program_model.name + " & identity_" + strategy_model.name + " & next(turn) = turn & " + maintain_mon_vars + "))"

    text += "TRANS\n" + normal_trans + "\n\t& " + deadlock + "\n"
    text = text.replace("%", "mod")
    text = text.replace("&&", "&")
    text = text.replace("||", "|")
    text = text.replace("==", "=")
    return text


def create_nuxmv_model(nuxmvModel):
    text = "MODULE main\n"
    text += "VAR\n" + "\t" + ";\n\t".join(nuxmvModel.vars) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(nuxmvModel.define) + ";\n"
    text += "INIT\n" + "\t(" + ")\n\t& (".join(nuxmvModel.init + ["turn = env"]) + ")\n"
    text += "INVAR\n" + "\t(" + ")\n\t& (".join(nuxmvModel.invar) + ")\n"

    turn_logic = ["(turn = con -> next(turn) = env)"]
    turn_logic += ["(turn = env -> next(turn) = mon)"]
    turn_logic += ["(turn = mon -> next(turn) = con)"]

    text += "TRANS\n" + "\t(" + ")\n\t& (".join(nuxmvModel.trans + turn_logic) + ")\n"
    text = text.replace("%", "mod")
    text = text.replace("&&", "&")
    text = text.replace("||", "|")
    text = text.replace("==", "=")
    return text


def symbol_table_from_program(program):
    symbol_table = dict()
    for state in program.states:
        symbol_table[state] = TypedValuation(state, "bool", None)
    for ev in program.out_events + program.env_events + program.con_events:
        symbol_table[ev.name] = TypedValuation(ev, "bool", None)
    for t_val in program.valuation:
        symbol_table[t_val.name] = t_val
    return symbol_table


def ce_state_to_predicate_abstraction_trans(ltl_to_program_transitions, symbol_table, mon_state, con_state, env_state):
    # ltl_to_program_transitions is a dict of the form {now: {(con_ev, env_ev) : [(con_trans, env_trans)]}}

    con_start = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in mon_state.items() if
                                      (key.startswith("mon_") or key.startswith("pred_")) and value == "TRUE"]
                                     + [neg(Variable(key.removeprefix("mon_"))) for key, value in mon_state.items() if
                                        (key.startswith("mon_") or key.startswith("pred_")) and value == "FALSE"])
    env_start = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in con_state.items() if
                                      (key.startswith("mon_") or key.startswith("pred_")) and value == "TRUE"]
                                     + [neg(Variable(key.removeprefix("mon_"))) for key, value in con_state.items() if
                                        (key.startswith("mon_") or key.startswith("pred_")) and value == "FALSE"])
    env_end = conjunct_formula_set([Variable(key.removeprefix("mon_")) for key, value in env_state.items() if
                                    (key.startswith("mon_") or key.startswith("pred_")) and value == "TRUE"]
                                   + [neg(Variable(key.removeprefix("mon_"))) for key, value in env_state.items() if
                                      (key.startswith("mon_") or key.startswith("pred_")) and value == "FALSE"])

    for abs_con_start in ltl_to_program_transitions.keys():
        if abs_con_start == "init":
            continue
        if smt_checker.check(And(*(conjunct(abs_con_start, con_start).to_smt(symbol_table)))):
            for (abs_env_start, abs_env_end) in ltl_to_program_transitions[abs_con_start].keys():
                if smt_checker.check(And(*(conjunct(abs_env_start, env_start).to_smt(symbol_table)))):
                    if smt_checker.check(And(*(conjunct(abs_env_end, env_end).to_smt(symbol_table)))):
                        return ltl_to_program_transitions[abs_con_start][(abs_env_start, abs_env_end)]

    return []


def check_for_nondeterminism_last_step(state_before_mismatch, program, raise_exception : bool, exception):
    transitions = program.env_transitions + program.con_transitions

    guards = []
    for (key, value) in state_before_mismatch.items():
        if key.startswith("guard_") and value == "TRUE":
            guards.append(transitions[int(key.replace("guard_", ""))])

    if len(guards) > 1:
        message = ("Nondeterminism in last step of counterexample; monitor has choice between: \n"
                        + "\n".join([str(t) for t in guards])
                        + "\nWe do not handle this yet."
                        + "\nIf you suspect the problem to be realisabile, "
                        + "give control to the environment of the transitions (e.g., with a new variable).\n"
                        + "Otherwise, if you suspect unrealisability, give control of the transitions to the controller.")
        if raise_exception:
            raise Exception(message) from exception
        else:
            print("WARNING: " + message)

def parse_nuxmv_ce_output_finite(out: str):
    prefix, _ = get_ce_from_nuxmv_output(out)

    return prefix, prog_transition_indices_and_state_from_ce(prefix)


def prog_transition_indices_and_state_from_ce(prefix):
    monitor_transitions_and_state = []

    for dic in prefix:
        if dic["turn"] != "mon":
            transition = "-1"
            for (key, value) in dic.items():
                if key.startswith("guard_") and value == "TRUE":
                    if dic[key.replace("guard_", "act_")] == "TRUE":
                        transition = key.replace("guard_", "")
                        break
            dic_without_prev_vars = {key: value for key, value in dic.items() if not key.endswith("_prev")}
            monitor_transitions_and_state.append((transition, dic_without_prev_vars))

    return monitor_transitions_and_state


def get_ce_from_nuxmv_output(out: str):
    ce = out.split("Counterexample")[1].strip()
    # ce = re.sub("[^\n]*(act|guard)\_[0-9]+ = [^\n]+", "", ce)
    ce = re.sub("[^\n]*(identity)_[^\n]+", "", ce)
    prefix_and_loop = re.split("-- Loop starts here", ce)
    prefix = prefix_and_loop[0].strip()
    loop = prefix_and_loop[1].strip()

    prefix = re.split("[^\n]*\->[^<]*<\-", prefix)
    prefix = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in prefix]
    prefix.remove([])
    prefix = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t]) for t in prefix]

    loop = re.split("[^\n]*\->[^<]*<\-", loop.strip())
    loop = [[p.strip() for p in re.split("\n", t) if "=" in p] for t in loop]
    loop.remove([])
    loop = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t if len(s.strip()) > 0]) for t in loop]

    complete_prefix, complete_loop = complete_ce(prefix, loop)

    prune_up_to_mismatch = [i for i in range(0, len(complete_prefix)) if complete_prefix[i]["compatible"] == "FALSE"]

    return complete_prefix[0:prune_up_to_mismatch[0] + 1], complete_prefix[prune_up_to_mismatch[0] + 1:] + complete_loop


def complete_ce(prefix, loop):
    for i in range(1, len(prefix)):
        complete_ce_state(prefix[i - 1], prefix[i])

    complete_ce_state(prefix[len(prefix) - 1], loop[0])
    for i in range(1, len(loop)):
        complete_ce_state(loop[i - 1], loop[i])
    return prefix, loop


def complete_ce_state(state, next_state):
    missing = dict([(k, state[k]) for k in state.keys() if k not in next_state.keys()])
    next_state.update(missing)


def only_this_state(states, state):
    only_this_state = str(state)
    for other in states:
        if other != state:
            only_this_state += " & !(" + str(other) + ")"
    return only_this_state


def only_this_state_next(states, state):
    only_this_state = "next(" + str(state) + ")"
    for other in states:
        if other != state:
            only_this_state += " & !next(" + str(other) + ")"
    return only_this_state


def get_differently_value_vars(state1: dict, state2: dict):
    return [key for key in state1.keys() if key in state2.keys() and state1[key] != state2[key]]


def fnode_to_formula(fnode: FNode) -> Formula:
    if fnode.is_constant():
        return Value(fnode.constant_value())
    elif fnode.is_symbol():
        return Variable(fnode.symbol_name())
    else:
        args = [fnode_to_formula(x) for x in fnode.args()]
        if fnode.is_le():
            return MathExpr(BiOp(args[0], "<=", args[1]))
        elif fnode.is_lt():
            return MathExpr(BiOp(args[0], "<", args[1]))
        elif fnode.is_plus():
            return MathExpr(BiOp(args[0], "+", args[1]))
        elif fnode.is_minus():
            return MathExpr(BiOp(args[0], "-", args[1]))
        elif fnode.is_div():
            return MathExpr(BiOp(args[0], "/", args[1]))
        elif fnode.is_times():
            return MathExpr(BiOp(args[0], "*", args[1]))
        elif fnode.is_not():
            return UniOp("!", args[0])
        else:
            if fnode.is_equals():
                op = "="
            elif fnode.is_and():
                op = "&"
            elif fnode.is_or():
                op = "|"
            elif fnode.is_implies():
                op = "<->"
            elif fnode.is_iff():
                op = "<->"
            else:
                raise NotImplementedError(str(fnode) + " cannot be represented as a Formula.")

            if len(args) < 2:
                raise Exception("Expected equality to have more that 1 sub-formula.")

            formula = BiOp(args[0], op, args[1])
            for i in range(2, len(args)):
                formula = conjunct(formula, BiOp(args[i - 1], op, args[i]))
            return formula


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


def ce_state_to_formula(state: dict, symbol_table: dict) -> Formula:
    formula = None
    for key, value in state.items():
        if key not in symbol_table.keys():
            continue
        conjunctt = BiOp(Variable(key), "=", Value(value))
        if formula is None:
            formula = conjunctt
        else:
            formula = conjunct(formula, conjunctt)
    return formula


def ground_formula_on_ce_state_with_index(formula: Formula, state: dict, i) -> Formula:
    to_replace_with = []
    for key, value in state.items():
        to_replace_with.append(BiOp(Variable(key + "_" + str(i)), ":=", Value(value)))
    return formula.replace(to_replace_with)


def label_pred(p, preds):
    if p not in preds:
        if (isinstance(p, UniOp) and p.op == "!"):
            return neg(stringify_pred(p.right))
        else:
            return neg(stringify_pred(neg(p)))
    else:
        return stringify_pred(p)


def stringify_pred(p):
    return Variable("pred_" +
                    str(p)
                    .replace(" ", "")
                    .replace("_", "")
                    .replace("(", "_")
                    .replace(")", "_")
                    .replace("=", "_EQ_")
                    .replace(">", "_GT_")
                    .replace("<=", "_LTEQ_")
                    .replace("<", "_LT_")
                    .replace(">=", "_GTEQ_")
                    .replace("-", "_MINUS_")
                    .replace("+", "_PLUS_")
                    .replace("/", "_DIV_")
                    .replace("*", "_MULT_")
                    .replace("%", "_MOD_")
                    .replace("!", "_NEG_")
                    .replace("&&", "_AND_")
                    .replace("&", "_AND_")
                    .replace("||", "_OR_")
                    .replace("|", "_OR_")
                    .replace("->", "_IMPLIES_")
                    .replace("=>", "_IMPLIES_")
                    .replace("<->", "_IFF_")
                    .replace("<=>", "_IFF_")
                    )


def label_preds(ps, preds):
    return {label_pred(p, preds) for p in ps}


def there_is_mismatch_between_monitor_and_strategy(system, controller : bool, livenesstosafety: bool, ltl_assumptions: Formula,
                                                   ltl_guarantees: Formula):
    print(system)
    model_checker = ModelChecker()
    # Sanity check
    result, out = model_checker.check(system, "F FALSE", None, livenesstosafety)
    if result:
        print("Are you sure the counterstrategy given is complete?")
        return True, None, out

    if not controller:
        there_is_no_mismatch, out = model_checker.check(system, "G !mismatch", None, livenesstosafety)

        return False, not there_is_no_mismatch, out
    else:
        return False, False, None


def reduce_up_to_iff(old_preds, new_preds, symbol_table):
    if len(new_preds) == 0:
        return old_preds
    if len(old_preds) == 0:
        return new_preds

    keep_these = set()
    remove_these = set()

    for p in new_preds:
        if p and neg(p) not in keep_these and p and neg(p) not in remove_these and \
                not has_equiv_pred(p, set(old_preds) | keep_these, symbol_table) and \
                not has_equiv_pred(neg(p), set(old_preds) | keep_these, symbol_table):
            keep_these.add(p)
        else:
            remove_these.add(p)
            remove_these.add(neg(p))

    return keep_these | set(old_preds)


def has_equiv_pred(p, preds, symbol_table):
    for pp in preds:
        if p is pp:
            return True
        else:
            p_smt = p.to_smt(symbol_table)
            pp_smt = pp.to_smt(symbol_table)
            if not smt_checker.check(And(*p_smt)) or not smt_checker.check(Not(And(*p_smt))):
                # if p or !p is unsat (i.e., p or !p is False), then no need to add it
                return True
            elif not (smt_checker.check(And(Not(And(*p_smt)), And(*pp_smt))) or
                      smt_checker.check(And(Not(And(*pp_smt)), And(*p_smt)))):
                return True
    return False


def project_ce_state_onto_ev(state: dict, events):
    return {k: v for k, v in state.items() if Variable(k) in events}


def synthesis_problem_to_TLSF_script(inputs, outputs, assumptions, guarantees):
    info = "INFO {\n" + \
           '\tTITLE:       ""\n' + \
           '\tDESCRIPTION: ""\n' + \
           "\tSEMANTICS:   Mealy\n" + \
           "\tTARGET:      Mealy\n" + \
           "}\n"

    main = "MAIN {\n"
    main += "\tINPUTS { \n\t\t"
    main += ";\n\t\t".join(map(str, inputs))
    main += "\n\t}\n"
    main += "\tOUTPUTS { \n\t\t"
    main += ";\n\t\t".join(map(str, outputs))
    main += "\n\t}\n"
    main += "\tASSUMPTIONS {\n\t\t"
    main += ";\n\n\t\t".join(map(str, assumptions))
    main += "\n\t}\n"
    main += "\tGUARANTEES { \n\t\t"
    main += ";\n\n\t\t".join(map(str, guarantees))
    main += "\n\t}\n"
    main += "}"

    return info + main


def stutter_transitions(program, env: bool):
    stutter_transitions = []
    for state in program.states:
        st = stutter_transition(program, state, env)
        if st != None:
            stutter_transitions.append(st)
    return stutter_transitions


def stutter_transition(program, state, env: bool):
    transitions = program.env_transitions if env else program.con_transitions
    condition = conjunct_formula_set([neg(t.condition)
                                            for t in transitions if t.src == state])

    if smt_checker.check(And(*condition.to_smt(symbol_table_from_program(program)))):
        return Transition(state,
                          condition,
                          [],
                          [],
                          state)
    else:
        return None


def concretize_transitions(program, indices_and_state_list):
    transitions = program.env_transitions + program.con_transitions

    concretized = []

    first_transition_index = int(indices_and_state_list[0][0])
    if first_transition_index != -1:
        concretized += [[(transitions[first_transition_index], indices_and_state_list[0][1])]]
    if first_transition_index == -1 and len(indices_and_state_list) == 1:
        trans = stutter_transition(program, program.initial_state, True)
        concretized += [(trans, indices_and_state_list[0][1])]

    for i in range(1, len(indices_and_state_list) - 2):
        if i % 2 == 0:
            continue
        trans_here = []
        trans_index_con = int(indices_and_state_list[i][0])
        if trans_index_con != -1:
            trans_here += [(transitions[trans_index_con], indices_and_state_list[i][1])]
        if i + 1 < len(indices_and_state_list) - 2:
            trans_index_env = int(indices_and_state_list[i + 1][0])
            if trans_index_env != -1:
                trans_here += [(transitions[int(trans_index_env)], indices_and_state_list[i + 1][1])]
        if len(trans_here) > 0:
            concretized += [trans_here]

    trans_here = []

    if len(indices_and_state_list) > 1:
        # for last two transitions
        con_from_state = concretized[-1][-1][0].tgt
        con_trans = stutter_transition(program, con_from_state, False) \
            if indices_and_state_list[-2][0] == '-1' \
            else transitions[int(indices_and_state_list[-2][0])]

        if con_trans == None:
            raise Exception("No controller stutter transition found for state " + str(con_from_state))
        else:
            trans_here += [(con_trans, indices_and_state_list[-2][1])]

        env_from_state = con_trans.tgt
        env_trans = stutter_transition(program, env_from_state, True) \
            if indices_and_state_list[-1][0] == '-1' \
            else transitions[int(indices_and_state_list[-1][0])]

        if env_trans == None:
            raise Exception("No controller stutter transition found for state " + str(con_from_state))
        else:
            trans_here += [(env_trans, indices_and_state_list[-1][1])]

        concretized += [trans_here]

    return concretized


def ground_transitions_and_flatten(program, transitions_and_state_list):
    return ground_transitions(program, [(t,s) for ts in transitions_and_state_list for t, s in ts])


def ground_transitions(program, transition_and_state_list):
    grounded = []
    for (t,st) in transition_and_state_list:
        projected_condition = ground_predicate_on_bool_vars(program, t.condition, st)
        grounded += [Transition(t.src,
                                projected_condition,
                                t.action,
                                t.output,
                                t.tgt)]
    return grounded


def ground_predicate_on_bool_vars(program, predicate, ce_state):
    grounded_state = project_ce_state_onto_ev(ce_state,
                                              program.env_events + program.con_events + [Variable(v.name) for v in
                                                                                         program.valuation if
                                                                                         re.match("bool(ean)?",
                                                                                                  v.type.lower())])
    projected_condition = predicate.ground(
        [TypedValuation(key, "bool", Value(grounded_state[key].lower())) for key in grounded_state.keys()])
    return projected_condition


def add_prev_suffix(program, formula):
    return append_to_variable_name(formula, [tv.name for tv in program.valuation], "_prev")


def transition_up_to_dnf(transition: Transition):
    dnf_condition = dnf(transition.condition)
    if not (isinstance(dnf_condition, BiOp) and dnf_condition.op.startswith("|")):
        return [transition]
    else:
        conds = dnf_condition.sub_formulas_up_to_associativity()
        return [Transition(transition.src, cond, transition.action, transition.output, transition.tgt) for cond in conds]


def check_determinism(program):
    env_state_dict = {s:[t.condition for t in program.env_transitions if t.src == s] for s in program.states}

    symbol_table = symbol_table_from_program(program)

    for (s, conds) in env_state_dict.items():
        sat_conds = [cond for cond in conds if smt_checker.check(And(*cond.to_smt(symbol_table)))]
        for cond in conds:
            if cond not in sat_conds:
                print("WARNING: " + str(cond) + " is not satisfiable, see transitions from state " + str(s))

        for i, cond in enumerate(sat_conds):
            for cond2 in sat_conds[i+1:]:
                if smt_checker.check(And(*(cond.to_smt(symbol_table) + cond2.to_smt(symbol_table)))):
                    print("WARNING: " + str(cond) + " and " + str(cond2) + " are satisfiable together, see environment transitions from state " + str(s))

    con_state_dict = {s:[t.condition for t in program.con_transitions if t.src == s] for s in program.states}

    for (s, conds) in con_state_dict.items():
        sat_conds = [cond for cond in conds if smt_checker.check(And(*cond.to_smt(symbol_table)))]
        for cond in conds:
            if cond not in sat_conds:
                print("WARNING: " + str(cond) + " is not satisfiable, see transitions from state " + str(s))
        for i, cond in enumerate(sat_conds):
            for cond2 in sat_conds[i+1:]:
                if smt_checker.check(And(*(cond.to_smt(symbol_table) + cond2.to_smt(symbol_table)))):
                    print("WARNING: " + str(cond) + " and " + str(cond2) + " are satisfiable together, see controller transitions from state " + str(s))


def safe_update(d, k, v_arr):
    if k in d.keys():
        d[k] = d[k] + v_arr
    else:
        d[k] = v_arr
