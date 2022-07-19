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


def synthesize_seq(aut: FlaggingMonitor, tlsf_file: str, server: str, docker: str) -> Tuple[bool, FlaggingMonitor]:
    ltl = syfco_ltl(tlsf_file)
    in_acts = syfco_ltl_in(tlsf_file)
    out_acts = syfco_ltl_out(tlsf_file)
    return synthesize_ltl_seq(aut, ltl, in_acts, out_acts, server, docker)


def synthesize_ltl_seq(aut: FlaggingMonitor, ltl: Formula, in_acts: [Variable], out_acts: [Variable], server: str,
                       docker: str) -> \
        Tuple[bool, FlaggingMonitor]:
    if server:
        (real, mm) = server_adapter.strix(ltl, in_acts, out_acts, server)
    else:
        (real, mm) = strix_adapter.strix(ltl, in_acts, out_acts, None, docker)

    if not real:
        return (False, None)
    else:
        return (True, seq(aut, mm))


def seq(mon: FlaggingMonitor, contr: FlaggingMonitor) -> FlaggingMonitor:
    monitor_transitions_to_not_flag = [Transition("m" + str(t.src),
                                                  t.condition,
                                                  t.action,
                                                  t.output,
                                                  "m" + str(t.tgt)) for t in mon.transitions if
                                       t.tgt not in mon.flag_states]

    contr_transitions_to_non_flag_and_non_init = [Transition("c" + str(t.src),
                                                             t.condition,
                                                             t.action,
                                                             t.output,
                                                             "c" + str(t.tgt)) for t in contr.transitions if
                                                  t.tgt not in contr.flag_states
                                                  and t.src != contr.initial_state]

    mon_to_contr = [Transition("m" + str(lt.src),
                               conjunct(lt.condition, rt.condition),
                               lt.action + rt.action,
                               conjunct(lt.output, rt.output),
                               "c" + str(rt.tgt))
                    for lt in mon.transitions if lt.tgt in mon.flag_states
                    for rt in contr.transitions if rt.src == contr.initial_state]

    seq_contr = FlaggingMonitor("monitor-then-controller",
                                ["m" + str(s) for s in mon.states if s not in mon.flag_states] +
                                ["c" + str(s) for s in contr.states],
                                "m" + str(mon.initial_state),
                                mon.valuation + contr.valuation,
                                [],
                                monitor_transitions_to_not_flag + contr_transitions_to_non_flag_and_non_init + mon_to_contr,
                                mon.input_events + contr.input_events,
                                mon.output_events + contr.output_events
                                )

    seq_contr.reduce()
    return seq_contr


def seq_rep(mon: FlaggingMonitor, contr: FlaggingMonitor) -> FlaggingMonitor:
    monitor_transitions_to_not_flag = [Transition("m" + str(t.src),
                                                  t.condition,
                                                  t.action,
                                                  t.output,
                                                  "m" + str(t.tgt)) for t in mon.transitions if
                                       t.tgt not in mon.flag_states]

    contr_transitions_to_non_flag_and_non_init = [Transition("c" + str(t.src),
                                                             t.condition,
                                                             t.action,
                                                             t.output,
                                                             "c" + str(t.tgt)) for t in contr.transitions if
                                                  t.tgt not in contr.flag_states
                                                  and t.src != contr.initial_state]

    mon_to_contr = [Transition("m" + str(lt.src),
                               conjunct(lt.condition, rt.condition),
                               lt.action + rt.action,
                               lt.output + rt.output,
                               "c" + str(rt.tgt))
                    for lt in mon.transitions if lt.tgt in mon.flag_states
                    for rt in contr.transitions if rt.src == contr.initial_state]

    contr_to_mon = [Transition("c" + str(rt.src),
                               conjunct(lt.condition, rt.condition),
                               lt.action + rt.action,
                               lt.output + rt.output,
                               "m" + str(lt.tgt))
                    for rt in contr.transitions if rt.tgt in contr.flag_states
                    for lt in mon.transitions if lt.src == mon.initial_state]

    seq_rep_contr = FlaggingMonitor("repeat-monitor-then-controller",
                                    ["m" + str(s) for s in mon.states if s not in mon.flag_states] +
                                    ["c" + str(s) for s in contr.states],
                                    "m" + str(mon.initial_state),
                                    mon.valuation + contr.valuation,
                                    [],
                                    monitor_transitions_to_not_flag + contr_transitions_to_non_flag_and_non_init + mon_to_contr + contr_to_mon,
                                    mon.input_events + contr.input_events,
                                    mon.output_events + contr.output_events
                                    )

    seq_rep_contr.reduce()
    return seq_rep_contr
