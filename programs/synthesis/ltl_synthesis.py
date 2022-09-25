import subprocess
from tempfile import NamedTemporaryFile
from typing import Tuple

from hoa.ast.boolean_expression import TrueFormula
from hoa.parsers import HOAParser, HOA

from programs.program import Program
from programs.synthesis.mealy_machine import MealyMachine
from programs.util import synthesis_problem_to_TLSF_script
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.parsing.hoaparser_label_expression_to_prop_logic import hoaparser_label_expression_to_pl
from prop_lang.util import true
from prop_lang.variable import Variable


def ltl_synthesis(assumptions: [Formula], guarantees: [Formula], in_act: [Variable], out_act: [Variable],
                  strix_tlsf_command: str) -> Tuple[
    bool, MealyMachine]:
    # prepare for tlsf
    in_acts_lowered = [str(a) for a in in_act]
    out_acts_lowered = [str(a) for a in out_act]

    assumptions_tlsf = [str(a).replace("TRUE", "true") \
                            .replace("True", "true") \
                            .replace("FALSE", "false") \
                            .replace("False", "false") \
                            .replace(" & ", " && ") \
                            .replace(" | ", " || ") \
                            .replace("\"", "") for a in assumptions]

    guarantees_tlsf = [str(g).replace("TRUE", "true") \
                           .replace("True", "true") \
                           .replace("FALSE", "false") \
                           .replace("False", "false") \
                           .replace(" & ", " && ") \
                           .replace(" | ", " || ") \
                           .replace("\"", "") for g in guarantees]

    tlsf_script = synthesis_problem_to_TLSF_script(in_acts_lowered,
                                                   out_acts_lowered,
                                                   assumptions_tlsf,
                                                   guarantees_tlsf)
    print(tlsf_script)
    try:
        with NamedTemporaryFile('w', suffix='.tlsf', delete=False) as tmp:
            tmp.write(tlsf_script)
            tmp.close()

            # cmd = strix_tlsf_command + " -v '" + tmp.name + "':./spec.tlsf -m both "
            cmd = "docker run " + " -v " + tmp.name + ":/spec.tlsf" + " --entrypoint ./strix/scripts/strix_tlsf.sh shaunazzopardi/strix_tlsf /spec.tlsf" + " -m both"

            so = subprocess.getstatusoutput(cmd)
            output: str = so[1]

            if "UNREALIZABLE" in output:
                mon = parse_hoa(output)
                return False, mon
            elif "REALIZABLE" in output:
                mon = parse_hoa(output)
                return True, mon
            else:
                raise Exception("Strix not returning appropriate value.\n\n" + cmd + "\n\n" + output + "\n\n" + tlsf_script)
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

    trans = {}

    for st, edges in hoa.body.state2edges.items():
        for e in edges:
            if e.label == TrueFormula():
                key = (st.index, true())
                if key not in trans.keys():
                    trans[(st.index, true())] = []
                trans[(st.index, true())] += [(true(), e.state_conj[0])]
            else:
                assert e.label.SYMBOL == '&'
                var_labels = [BiOp(Variable(i), ":=", Variable(ap)) for i, ap in
                              enumerate(hoa.header.propositions)]

                env = hoaparser_label_expression_to_pl(str(e.label.operands[0]))
                env = env.replace(var_labels)

                con = hoaparser_label_expression_to_pl(str(e.label.operands[1]))
                con = con.replace(var_labels)

                key = (st.index, env)
                if key not in trans.keys():
                    trans[(st.index, env)] = []
                trans[(st.index, env)] += [(con, e.state_conj[0])]
    mon.add_transitions(trans)
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
