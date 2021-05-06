from typing import Tuple
from monitors.monitor import Monitor
from monitors.parsing.kiss_to_monitor import kiss_to_monitor
import subprocess

from prop_lang.atom import Atom


def strix(ltl: str, in_act: [Atom], out_act: [Atom], end_act: Atom, docker: str) -> Tuple[bool, Monitor]:
    in_act_string = ",".join([str(a).lower() for a in in_act])
    out_act_string = ",".join([str(a).lower() for a in out_act])
    ltl_string = ltl
    for inp in in_act:
        ltl_string = ltl_string.replace("\"" + str(inp) + "\"", str(inp).lower())
    for out in out_act:
        ltl_string = ltl_string.replace("\"" + str(out) + "\"", str(out).lower())

    try:
        cmd = "strix -k -f \"" + ltl_string + "\" --ins=\"" + in_act_string + "\" --outs=\"" + out_act_string + "\""
        if docker is not None:
            cmd = "docker run " + docker + " " + cmd
        so = subprocess.getstatusoutput(cmd)
        output: str = so[1]

        if output.startswith("UNREALIZABLE"):
            return (False, {})
        elif output.startswith("REALIZABLE"):
            return (True, kiss_to_monitor(output.replace("REALIZABLE", "").strip(' '), in_act, out_act, end_act))
        else:
            raise Exception("Strix not returning appropriate value.")
    except Exception as err:
        raise err
    pass


# this does what ./scripts/strix_tlsf.sh does
def syfco_ltl(tlsf_file: str) -> str:
    try:
        LTL_cmd = 'syfco -f ltl -q double -m fully ' + tlsf_file
        so = subprocess.getstatusoutput(LTL_cmd)
        LTL_str: str = so[1]
        # LTL = string_to_ltl(LTL_str.replace("\"", ""))

        return LTL_str
    except Exception as err:
        raise err
    pass


def syfco_ltl_in(tlsf_file: str):
    try:
        INS_cmd = 'syfco -f ltl --print-input-signals ' + tlsf_file
        so = subprocess.getstatusoutput(INS_cmd)
        INS_str: str = so[1]
        INS = [Atom(a.strip(" ")) for a in INS_str.split(",")]

        return INS
    except Exception as err:
        raise err
    pass


def syfco_ltl_out(tlsf_file: str) :#-> Array[Atom]:
    try:
        OUTS_cmd = 'syfco -f ltl --print-output-signals ' + tlsf_file
        so = subprocess.getstatusoutput(OUTS_cmd)
        OUTS_str: str = so[1]
        OUTS = [Atom(a.strip(" ")) for a in OUTS_str.split(",")]

        return OUTS
    except Exception as err:
        raise err
    pass
