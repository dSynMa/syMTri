import subprocess
from typing import Tuple

from hoa.ast.boolean_expression import TrueFormula

from programs.program import Program
from prop_lang.biop import BiOp
from prop_lang.parsing.hoaparser_label_expression_to_prop_logic import hoaparser_label_expression_to_pl
from prop_lang.util import true
from prop_lang.variable import Variable

from hoa.parsers import HOAParser, HOA

from programs.synthesis.mealy_machine import MealyMachine


def strix(ltl: str, in_act: [Variable], out_act: [Variable], docker: str) -> Tuple[bool, Program]:
    in_act_string = ",".join([str(a).lower() for a in in_act])
    out_act_string = ",".join([str(a).lower() for a in out_act])
    ltl_string = str(ltl)
    ltl_string = ltl_string.replace("TRUE", "true")
    ltl_string = ltl_string.replace("True", "true")
    ltl_string = ltl_string.replace("FALSE", "false")
    ltl_string = ltl_string.replace("False", "false")

    for inp in in_act:
        ltl_string = ltl_string.replace("\"" + str(inp) + "\"", str(inp).lower())
    for out in out_act:
        ltl_string = ltl_string.replace("\"" + str(out) + "\"", str(out).lower())

    try:
        cmd = "-f \"" + ltl_string + "\" --ins=\"" + in_act_string + "\" --outs=\"" + out_act_string + "\""
        if docker is not None:
            cmd = "docker run " + docker + " -m both " + cmd
        else:
            cmd = "strix -m both " + cmd
        so = subprocess.getstatusoutput(cmd)
        output: str = so[1]

        if output.startswith("UNREALIZABLE"):
            mon = parse_hoa(output)
            return False, mon
        elif output.startswith("REALIZABLE"):
            mon = parse_hoa(output)
            return True, mon
        else:
            raise Exception("Strix not returning appropriate value.\n" + output)
    except Exception as err:
        raise err
    pass


def parse_hoa(output) -> Program:
    hoa_parser = HOAParser()
    good_output = "\n".join(
        ln for ln in output.split("\n")
        if not ln.startswith("controllable-AP")
        and not ln.startswith("REALIZABLE")
        and not ln.startswith("UNREALIZABLE")
    )
    hoa: HOA = hoa_parser(good_output)
    ctrl_aps = ([ln for ln in output.split("\n")
                 if ln.startswith("controllable-AP")
                 ][0].strip().split()[1:])
    ctrl_aps = set(int(i) for i in ctrl_aps)

    env_events = [
        ap for i, ap in enumerate(hoa.header.propositions)
        if i in ctrl_aps]
    con_events = [
        ap for i, ap in enumerate(hoa.header.propositions)
        if i not in ctrl_aps]

    init_st = next(iter(hoa.header.start_states))
    if len(init_st) != 1:
        raise Exception("More than one initial state:\n" + good_output)
    else:
        init_st = list(init_st)[0]

    mon = MealyMachine("counterstrategy", init_st, env_events, con_events)

    for st, edges in hoa.body.state2edges.items():
        for e in edges:
            if e.label == TrueFormula():
                mon.add_transition(
                    src=st.index,
                    env_behaviour=true(),
                    con_behaviour=true(),
                    tgt=e.state_conj[0]
                )
            else:
                assert e.label.SYMBOL == '&'
                var_labels = [BiOp(Variable(i), ":=", Variable(ap)) for i, ap in
                              enumerate(hoa.header.propositions)]

                env = hoaparser_label_expression_to_pl(str(e.label.operands[0]))
                env = env.replace(var_labels)

                con = hoaparser_label_expression_to_pl(str(e.label.operands[1]))
                con = con.replace(var_labels)

                mon.add_transition(
                    src=st.index,
                    env_behaviour=env,
                    con_behaviour=con,
                    tgt=e.state_conj[0]
                )
    return mon


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
