from programs.program import Program
from programs.typed_valuation import TypedValuation


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