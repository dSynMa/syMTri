import re
from typing import Tuple

from programs.program import Program
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import tighten_ltl, conjunct, implies
from prop_lang.variable import Variable
from strix import strix_adapter
from strix.strix_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, server: str, docker: str) -> Tuple[bool, Program]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        ltl_text = ltl_text.replace('"', "")
        in_acts = syfco_ltl_in(tlsf_path)
        out_acts = syfco_ltl_out(tlsf_path)

    ltl = string_to_ltl(ltl_text)
    in_acts = [e for e in aut.env_events + aut.mon_events] + [e for e in aut.states]
    out_acts = [e for e in aut.con_events]
    # TODO validate in_acts, out_acts against those from TLSF
    return abstract_synthesis_loop(aut, ltl, in_acts, out_acts, server, docker)


def abstract_synthesis_loop(aut: Program, ltl: Formula, in_acts: [Variable], out_acts: [Variable], server: str,
                            docker: str) -> \
        Tuple[bool, Program]:
    abstract_monitor = aut.abstract_into_ltl();
    abstract_problem = implies(abstract_monitor, ltl)

    (real, mm) = strix_adapter.strix(abstract_problem, in_acts, out_acts, None, docker)

    if real:
        return mm
    else:
        NotImplemented
