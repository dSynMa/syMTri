import re
import os
import shutil
from pysmt.factory import SolverRedefinitionError
from pysmt.fnode import FNode
from pysmt.logics import QF_UFLRA
from pysmt.shortcuts import get_env

from programs.analysis.model_checker import ModelChecker
from programs.analysis.nuxmv_model import NuXmvModel
from programs.program import Program
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set, conjunct, neg
from prop_lang.value import Value
from prop_lang.variable import Variable


def create_nuxmv_model_for_compatibility_checking(model1: NuXmvModel, model2: NuXmvModel, mon_events, pred_list):
    text = "MODULE main\n"
    text += "VAR\n" + "\t" + ";\n\t".join(set(model1.vars + model2.vars + ["mismatch : boolean"])) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(model1.define + model2.define) + ";\n"
    text += "\tcompatible := !(turn = mon) | (" + str(conjunct_formula_set([BiOp(m, ' = ', Variable("mon_" + m.name)) for m in mon_events])) + ");\n"

    text += "INIT\n" + "\t(" + ")\n\t& (".join(model1.init + model2.init + ["turn = env", "mismatch = FALSE"]) + ")\n"
    text += "INVAR\n" + "\t((" + ")\n\t& (".join(model1.invar + model2.invar
                                                 + ["turn = mon -> (pred_" + str(i) + " <-> " + str(pred_list[i]) + ")" for i in range(0, len(pred_list))]) + "))\n"

    turn_logic = ["(turn = con -> next(turn) = env)"]
    turn_logic += ["(turn = env -> next(turn) = mon)"]
    turn_logic += ["(turn = mon -> next(turn) = con)"]

    maintain_mon_vars = str(conjunct_formula_set([BiOp(UniOp("next", Variable("mon_" + m.name)), ' = ', Variable("mon_" + m.name)) for m in mon_events]))
    new_trans = ["compatible", "!next(mismatch)"] + model1.trans + model2.trans + turn_logic
    normal_trans = "\t((" + ")\n\t& (".join(new_trans) + "))\n"

    normal_trans += "\t | (!compatible & " + \
                    " next(mismatch) & identity_" + model1.name + \
                    " & identity_" + model2.name + " & next(turn) = turn & " + maintain_mon_vars + ")"
    normal_trans = "(!mismatch -> (" + normal_trans + "))"

    deadlock = "(mismatch -> (next(mismatch) & identity_" + model1.name + " & identity_" + model2.name + " & next(turn) = turn & " + maintain_mon_vars + "))"

    text += "TRANS\n" + normal_trans + "\n\t& " + deadlock + "\n"
    text = text.replace("%", "mod")
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
    return text


def symbol_table_from_program(program: Program):
    symbol_table = dict()
    for state in program.states:
        symbol_table[state] = TypedValuation(state, "bool", None)
    for ev in program.out_events + program.env_events + program.con_events:
        symbol_table[ev.name] = TypedValuation(ev, "bool", None)
    for t_val in program.valuation:
        symbol_table[t_val.name] = t_val
    return symbol_table


def parse_nuxmv_ce_output_finite(out: str):
    prefix, _ = get_ce_from_nuxmv_output(out)

    prefix = prefix[:-1]

    monitor_transitions = []
    for dic in prefix:
        if dic["turn"] != "mon":
            transition = "-1"
            for (key,value) in dic.items():
                if key.startswith("guard_") and value == "TRUE":
                    if dic[key.replace("guard_", "act_")] == "TRUE":
                        transition = key.replace("guard_", "")
                        break
            monitor_transitions.append(transition)

    return prefix, monitor_transitions


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
    loop = [[p.strip() for p in re.split("\n", t)  if "=" in p] for t in loop]
    loop.remove([])
    loop = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t if len(s.strip()) > 0]) for t in loop]

    return complete_ce(prefix, loop)


def complete_ce(prefix, loop):
    for i in range(1, len(prefix)):
        complete_ce_state(prefix[i - 1], prefix[i])

    complete_ce_state(prefix[len(prefix) - 1], loop[0])
    for i in range(1, len(loop)):
        complete_ce_state(loop[i - 1], loop[i])
    return prefix, loop


def complete_ce_state(state, next_state):
    missing = dict([(k,state[k]) for k in state.keys() if k not in next_state.keys()])
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


def use_liveness_abstraction(ce: [dict], symbol_table):
    assert len(ce) > 0

    counterstrategy_states_con = [key for dict in ce for key, value in dict.items()
                                if dict["turn"] == "env" and key.startswith("st_") and value == "TRUE"]
    # counterstrategy_states = ["st_0"] \
    #                          + ["st_" + re.split("_", key)[3] for dict in ce for key, value in dict.items()
    #                             if dict["turn"] == "env" and key.startswith("st_") and value == "TRUE"]

    # TODO would it be useful to check if the repeated states in the counterexample involve different values of
    #  an infinite-state variable? if they don't probably safety would suffice, but a liveness abstraction
    #  could give us a more succinct condition to eliminate the environment beliefs about the monitor

    # TODO, do we need to show that at the same time there is a loop in the monitor?
    last_state = counterstrategy_states_con[len(counterstrategy_states_con)-1]
    if last_state in counterstrategy_states_con[:-1]:
        indices_of_prev_visits = [i for i, x in enumerate(counterstrategy_states_con[:-1]) if x == last_state]
        corresponding_ce_state = [ce[(3*i) + 1] for i in indices_of_prev_visits]
        var_differences = [get_differently_value_vars(corresponding_ce_state[i], corresponding_ce_state[i + 1])
                           for i in range(0, len(corresponding_ce_state) - 1)]
        var_differences = [[re.sub("_[0-9]+$", "", v) for v in vs] for vs in var_differences]
        var_differences = [[v for v in vs if v in symbol_table.keys()] for vs in var_differences]
        if any([x for xs in var_differences for x in xs if re.match("(int(eger)?|nat(ural)?|real)", symbol_table[x].type)]):
            return True
        else:
            return False
    else:
        return False


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


def label_pred_according_to_index(p, _list_for_indexing):
    if p in _list_for_indexing:
        return Variable("pred_" + str(_list_for_indexing.index(p)))
    elif isinstance(p, UniOp) and p.op == "!":
        return neg(Variable("pred_" + str(_list_for_indexing.index(p.right))))
    elif not(isinstance(p, UniOp) and p.op == "!"):
        return neg(Variable("pred_" + str(_list_for_indexing.index(neg(p)))))
    else:
        raise NotImplementedError("Cannot find " + str(p) + " in " + ", ".join([str(q) for q in _list_for_indexing]) + ".")


def label_preds_according_to_index(ps, _list_for_indexing):
    return {label_pred_according_to_index(p, _list_for_indexing) for p in ps}


def mismatch_between_monitor_strategy(system):
    print(system)
    model_checker = ModelChecker()
    # Sanity check
    result, ce = model_checker.check(system, "F FALSE", 50)
    assert not result

    return model_checker.check(system, "G !mismatch", None)