import subprocess
from typing import Tuple

from monitors.flaggingmonitor import FlaggingMonitor
from monitors.parsing.kiss_to_monitor import kiss_to_monitor
from prop_lang.variable import Variable


def strix(ltl: str, in_act: [Variable], out_act: [Variable], end_act: Variable, docker: str) -> Tuple[bool, FlaggingMonitor]:
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
        INS = [Variable(a.strip(" ")) for a in INS_str.split(",")]

        return INS
    except Exception as err:
        raise err
    pass


def syfco_ltl_out(tlsf_file: str):
    try:
        OUTS_cmd = 'syfco -f ltl --print-output-signals ' + tlsf_file
        so = subprocess.getstatusoutput(OUTS_cmd)
        OUTS_str: str = so[1]
        OUTS = [Variable(a.strip(" ")) for a in OUTS_str.split(",")]

        return OUTS
    except Exception as err:
        raise err
    pass
