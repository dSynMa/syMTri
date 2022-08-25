import re
from typing import Tuple

from programs.analysis.model_checker import ModelChecker
from programs.analysis.util import create_nuxmv_model
from programs.program import Program
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import tighten_ltl, conjunct, implies
from prop_lang.variable import Variable
from strix import strix_adapter
from strix.strix_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool) -> Tuple[bool, Program]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        ltl_text = ltl_text.replace('"', "")
        # TODO use below for sanity checking of monitor variables
        in_acts = syfco_ltl_in(tlsf_path)
        out_acts = syfco_ltl_out(tlsf_path)

    ltl = string_to_ltl(ltl_text)
    in_acts = [e for e in aut.env_events + aut.mon_events] + [e for e in aut.states]
    out_acts = [e for e in aut.con_events]
    # TODO validate in_acts, out_acts against those from TLSF
    return abstract_synthesis_loop(aut, ltl, in_acts, out_acts, docker)


def abstract_synthesis_loop(program: Program, ltl: Formula, in_acts: [Variable], out_acts: [Variable], docker: str) -> \
        Tuple[bool, MealyMachine]:
    abstract_monitor = predicate_abstraction(program, [], symbol_table_from_program(program))
    abstraction = abstraction_to_ltl(abstract_monitor)
    print(abstraction)
    abstract_problem = implies(abstraction, ltl)

    (real, mm) = strix_adapter.strix(abstract_problem, in_acts, out_acts, docker)

    if real:
        return mm
    else:
        name, vars, define, init, trans = program.to_nuXmv_with_turns()
        name_mm, vars_mm, define_mm, init_mm, trans_mm = mm.to_nuXmv_with_turns()

        system = create_nuxmv_model(name + "&&" + name_mm,
                                    list(set(vars + vars_mm)),
                                    define + define_mm,
                                    init + init_mm,
                                    trans + trans_mm)

        model_checker = ModelChecker()
        NotImplemented
