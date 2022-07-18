import re
from typing import Tuple

from monitors.flaggingmonitor import FlaggingMonitor
from monitors.monitor import Monitor
from monitors.transition import Transition
from prop_lang.formula import Formula
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import tighten_ltl, conjunct, implies
from prop_lang.variable import Variable
from strix import server_adapter, strix_adapter
from strix.strix_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out


def synthesize_seq_rep(aut: FlaggingMonitor, tlsf_file: str, server: bool, docker: bool) -> Tuple[
    bool, FlaggingMonitor]:
    (tightened_tlsf_file, end_act) = tighten_guarantees(tlsf_file)
    ltl = syfco_ltl(tightened_tlsf_file)
    in_acts = syfco_ltl_in(tightened_tlsf_file)
    out_acts = syfco_ltl_out(tightened_tlsf_file)
    return synthesize_ltl_seq_rep(aut, ltl, in_acts, out_acts, end_act, server, docker)


def tighten_guarantees(tlsf_file: str) -> Tuple[str, Variable]:
    tlsf = open(tlsf_file).read()
    matches = re.findall(r"(GUARANTEES( |\n)*?\{(.|\n)*?\})", tlsf, re.M)
    if len(matches) > 1:
        "Multiple guarantees clauses. Not doing anything in this case."
    if len(matches) == 0:
        "No guarantees clauses. Not doing anything in this case."

    # TODO
    print("Assuming tlsf file does not use definitions in guarantees.")

    match: str = matches[0][0]
    without_header = match.replace("GUARANTEES", "").replace("{", "").replace("}", "").strip().strip(";")
    guarantee = "(" + without_header.replace(";", ") & (") + ")";
    to_LTL = string_to_ltl(guarantee)
    (tightened, new_out, end_act) = tighten_ltl(to_LTL)
    tightened_str = str(tightened)

    tightened_tlsf = tlsf.replace(without_header, tightened_str);
    tightened_tlsf = re.sub(r"OUTPUTS( |\n*?)\{",
                            "OUTPUTS {\n\t" + ";\n\n\t".join(map(lambda o: str(o), new_out)) + ";\n", tightened_tlsf,
                            re.M)

    path = tlsf_file.replace(".tlsf", "") + "-tightened" + ".tlsf"
    tightened_tlsf_file = open(path, "w+")
    tightened_tlsf_file.seek(0)
    tightened_tlsf_file.write(tightened_tlsf)
    tightened_tlsf_file.truncate()
    ## TODO Need to add end events to outputs
    return (path, end_act)


def synthesize_ltl_seq_rep(aut: FlaggingMonitor, ltl: Formula, in_acts: [Variable], out_acts: [Variable],
                           end_act: Variable, server: str,
                           docker: str) -> Tuple[bool, FlaggingMonitor]:
    if server:
        (real, mm) = server_adapter.strix(ltl, in_acts, out_acts, end_act, server)
    else:
        (real, mm) = strix_adapter.strix(ltl, in_acts, out_acts, end_act, docker)

    if len(mm.flag_states) < 1:
        raise Exception("Are you sure the LTL spec is co-safety?\n"
                        "Try adding a guarantee that eventually the controller must be inactive.")

    if not real:
        return (False, None)
    else:
        return (True, seq_rep(aut, mm))


def synthesize(aut: Monitor, ltl_text: str, tlsf_path: str, server: str, docker: str) -> Tuple[bool, Monitor]:
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


def abstract_synthesis_loop(aut: Monitor, ltl: Formula, in_acts: [Variable], out_acts: [Variable], server: str,
                             docker: str) -> \
        Tuple[bool, Monitor]:

    abstract_monitor = aut.abstract_into_ltl();
    abstract_problem = implies(abstract_monitor, ltl)
    if server:
        (real, mm) = server_adapter.strix(abstract_problem, in_acts, out_acts, server)
    else:
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
