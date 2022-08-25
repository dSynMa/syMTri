import re

from programs.analysis.nuxmv_model import NuXmvModel
from programs.program import Program
from programs.typed_valuation import TypedValuation
from prop_lang.biop import BiOp
from prop_lang.uniop import UniOp
from prop_lang.util import conjunct_formula_set
from prop_lang.variable import Variable


def create_nuxmv_model_for_compatibility_checking(model1: NuXmvModel, model2: NuXmvModel, mon_events):
    text = "MODULE main\n"
    text += "VAR\n" + "\t" + ";\n\t".join(set(model1.vars + model2.vars + ["mismatch: boolean"])) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(model1.define + model2.define) + ";\n"
    text += "\tcompatible := !(turn = mon) | (" + str(conjunct_formula_set([BiOp(m, ' = ', Variable("mon_" + m.name)) for m in mon_events])) + ");\n"

    text += "INIT\n" + "\t(" + ")\n\t& (".join(model1.init + model2.init + ["turn = env", "mismatch = FALSE"]) + ")\n"
    text += "INVAR\n" + "\t((" + ")\n\t& (".join(model1.invar + model2.invar) + "))\n"

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
    prefix, _ = parse_nuxmv_ce_output(out)
    return prefix.pop(len(prefix) - 1)


def parse_nuxmv_ce_output(out: str):
    ce = out.split("Counterexample")[1].strip()
    ce = re.sub("[^\n]*(act|guard)\_[0-9]+ = [^\n]+", "", ce)
    ce = re.sub("[^\n]*(identity)_[^\n]+", "", ce)
    prefix_and_loop = re.split("-- Loop starts here", ce)
    prefix = prefix_and_loop[0].strip()
    loop = prefix_and_loop[1].strip()

    prefix = re.split("[^\n]*\->[^<]*<\-", prefix)
    prefix.remove('')
    prefix = [re.split("\n", t.strip()) for t in prefix]
    prefix = [dict([(s.split("=")[0].strip(), s.split("=")[1].strip()) for s in t]) for t in prefix]

    loop = re.split("[^\n]*\->[^<]*<\-", loop.strip())
    loop.remove('')
    loop = [re.split("\n", t.strip()) for t in loop]
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