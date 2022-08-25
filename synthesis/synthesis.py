from typing import Tuple

from programs.analysis.model_checker import ModelChecker
from programs.analysis.predicate_abstraction import predicate_abstraction, abstraction_to_ltl
from programs.util import symbol_table_from_program, create_nuxmv_model_for_compatibility_checking
from programs.program import Program
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import implies
from prop_lang.variable import Variable
from strix import strix_adapter
from strix.strix_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out
from synthesis.mealy_machine import MealyMachine


def synthesize(aut: Program, ltl_text: str, tlsf_path: str, docker: bool) -> Tuple[bool, Program]:
    if tlsf_path is not None:
        ltl_text = syfco_ltl(tlsf_path)
        ltl_text = ltl_text.replace('"', "")
        # TODO use below for sanity checking of monitor variables
        in_acts = syfco_ltl_in(tlsf_path)
        out_acts = syfco_ltl_out(tlsf_path)

    ltl = string_to_ltl(ltl_text)
    in_acts = [e for e in aut.env_events + aut.out_events] + [e for e in aut.states]
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
        return (real, mm)
    else:
        program_nuxmv_model = program.to_nuXmv_with_turns()
        mon_events = program.out_events \
                     + [Variable(s) for s in program.states] \
                     + [p for s in abstract_monitor.states if s != abstract_monitor.initial_state for p in s[1]]
        mealy = mm.to_nuXmv_with_turns(mon_events)
        print(mm.to_dot())

        system = create_nuxmv_model_for_compatibility_checking(program_nuxmv_model, mealy, mon_events)

        print(system)

        model_checker = ModelChecker()
        # Sanity check
        result, ce = model_checker.check(system, "F FALSE", 50)
        assert not result

        result, ce = model_checker.check(system, "G !mismatch", None)
        if result:
            # then the problem is unrealisable (i.e., the counterstrategy is a real counterstrategy)
            return False, mm
        else:
            print(ce)
            # TODO refinement of abstraction
            raise NotImplementedError()
