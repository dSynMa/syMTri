import re

from programs.program import Program
from programs.typed_valuation import TypedValuation
from prop_lang.parsing.string_to_assignments import string_to_assignments


def create_nuxmv_model(name, vars, define, init, trans):
    text = "MODULE main\n"
    text += "VAR\n" + "\t" + ";\n\t".join(vars) + ";\n"
    text += "DEFINE\n" + "\t" + ";\n\t".join(define) + ";\n"
    text += "INIT\n" + "\t(" + ")\n\t& (".join(init) + ")\n"
    text += "TRANS\n" + "\t(" + ")\n\t& (".join(trans) + ")\n"
    text = text.replace("%", "mod")
    return text


def symbol_table_from_program(program: Program):
    symbol_table = dict()
    for state in program.states:
        symbol_table[state] = TypedValuation(state, "bool", None)
    for ev in program.mon_events + program.env_events + program.con_events:
        symbol_table[ev.name] = TypedValuation(ev, "bool", None)
    for t_val in program.valuation:
        symbol_table[t_val.name] = t_val
    return symbol_table


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
    prefix = [[string_to_assignments(s.strip().replace("=", ":="))[0] for s in t] for t in prefix]

    loop = re.split("[^\n]*\->[^<]*<\-", loop.strip())
    loop.remove('')
    loop = [re.split("\n", t.strip()) for t in loop]
    loop = [[string_to_assignments(s.strip().replace("=", ":="))[0] for s in t] for t in loop]

    return complete_ce(prefix, loop)


def complete_ce(prefix, loop):
    for i in range(1, len(prefix)):
        prefix[i] = complete_ce_state(prefix[i-1], prefix[i])

    loop[0] = complete_ce_state(prefix[len(prefix) - 1], loop[0])
    for i in range(1, len(loop)):
        loop[i] = complete_ce_state(loop[i-1], loop[i])
    return prefix, loop


def complete_ce_state(state, next_state):
    missing = [b for b in state if b.left not in [biop.left for biop in next_state]]
    return missing + next_state