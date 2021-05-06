import re
from typing import Tuple

from monitors.monitor import Monitor
from monitors.transition import Transition
from prop_lang.formula import Formula
from prop_lang.atom import Atom
from prop_lang.parsing.string_to_ltl import string_to_ltl
from prop_lang.util import tighten_ltl, andd
from strix import server_adapter, strix_adapter
from strix.strix_adapter import syfco_ltl, syfco_ltl_in, syfco_ltl_out


def synthesize_seq_rep(aut: Monitor, tlsf_file: str, server: bool, docker: bool) -> Tuple[bool, Monitor]:
    (tightened_tlsf_file, end_act) = tighten_guarantees(tlsf_file)
    ltl = syfco_ltl(tightened_tlsf_file)
    in_acts = syfco_ltl_in(tightened_tlsf_file)
    out_acts = syfco_ltl_out(tightened_tlsf_file)
    return synthesize_ltl_seq_rep(aut, ltl, in_acts, out_acts, end_act, server, docker)


def tighten_guarantees(tlsf_file: str) -> Tuple[str, Atom]:
    tlsf = open(tlsf_file).read()
    matches = re.findall(r"(GUARANTEES( |\n)*?\{(.|\n)*?\})", tlsf, re.M)
    if len(matches) > 1:
        "Multiple guarantees clauses. Not doing anything in this case."
    if len(matches) == 0:
        "No guarantees clauses. Not doing anything in this case."

    #TODO
    print("Assuming tlsf file does not use definitions in guarantees.")

    match: str = matches[0][0]
    without_header = match.replace("GUARANTEES", "").replace("{", "").replace("}", "").strip().strip(";")
    guarantee = "(" + without_header.replace(";", ") & (") + ")";
    to_LTL = string_to_ltl(guarantee)
    (tightened, new_out, end_act) = tighten_ltl(to_LTL)
    tightened_str = str(tightened)

    tightened_tlsf = tlsf.replace(without_header, tightened_str);
    tightened_tlsf = re.sub(r"OUTPUTS( |\n*?)\{", "OUTPUTS {\n\t" + ";\n\n\t".join(map(lambda o: str(o), new_out)) + ";\n", tightened_tlsf, re.M)

    path = tlsf_file.replace(".tlsf", "") + "-tightened" + ".tlsf"
    tightened_tlsf_file = open(path, "w+")
    tightened_tlsf_file.seek(0)
    tightened_tlsf_file.write(tightened_tlsf)
    tightened_tlsf_file.truncate()
    ## TODO Need to add end events to outputs
    return (path, end_act)


def synthesize_ltl_seq_rep(aut: Monitor, ltl: Formula, in_acts: [Atom], out_acts: [Atom], end_act: Atom, server: str, docker: str) -> Tuple[bool, Monitor]:
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


def synthesize_seq(aut: Monitor, tlsf_file: str, server: str, docker: str) -> Tuple[bool, Monitor]:
    ltl = syfco_ltl(tlsf_file)
    in_acts = syfco_ltl_in(tlsf_file)
    out_acts = syfco_ltl_out(tlsf_file)
    return synthesize_ltl_seq(aut, ltl, in_acts, out_acts, server, docker)


def synthesize_ltl_seq(aut: Monitor, ltl: Formula, in_acts: [Atom], out_acts: [Atom], server: str, docker: str) -> Tuple[bool, Monitor]:
    if server:
        (real, mm) = server_adapter.strix(ltl, in_acts, out_acts, server)
    else:
        (real, mm) = strix_adapter.strix(ltl, in_acts, out_acts, None, docker)

    if not real:
        return (False, None)
    else:
        return (True, seq(aut, mm))


def seq(mon: Monitor, contr: Monitor) -> Monitor:
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
                               andd(lt.condition, rt.condition),
                               lt.action + rt.action,
                               andd(lt.output,rt.output),
                               "c" + str(rt.tgt))
                    for lt in mon.transitions if lt.tgt in mon.flag_states
                    for rt in contr.transitions if rt.src == contr.initial_state]

    seq_contr = Monitor("monitor-then-controller",
                        ["m" + str(s) for s in mon.states if s not in mon.flag_states] +
                        ["c" + str(s) for s in contr.states],
                     "m" + str(mon.initial_state),
                        mon.valuation + contr.valuation,
                        [],
                        monitor_transitions_to_not_flag + contr_transitions_to_non_flag_and_non_init + mon_to_contr
                        )

    seq_contr.reduce()
    return seq_contr


def seq_rep(mon: Monitor, contr: Monitor) -> Monitor:
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
                               andd(lt.condition, rt.condition),
                               lt.action + rt.action,
                               andd(lt.output, rt.output),
                               "c" + str(rt.tgt))
                    for lt in mon.transitions if lt.tgt in mon.flag_states
                    for rt in contr.transitions if rt.src == contr.initial_state]

    contr_to_mon = [Transition("c" + str(rt.src),
                               andd(lt.condition, rt.condition),
                               lt.action + rt.action,
                               andd(lt.output, rt.output),
                               "m" + str(lt.tgt))
                    for rt in contr.transitions if rt.tgt in contr.flag_states
                    for lt in mon.transitions if lt.src == mon.initial_state]

    seq_rep_contr = Monitor("repeat-monitor-then-controller",
                            ["m" + str(s) for s in mon.states if s not in mon.flag_states] +
                            ["c" + str(s) for s in contr.states],
                         "m" + str(mon.initial_state),
                            mon.valuation + contr.valuation,
                            [],
                            monitor_transitions_to_not_flag + contr_transitions_to_non_flag_and_non_init + mon_to_contr + contr_to_mon
                            )

    seq_rep_contr.reduce()
    return seq_rep_contr
