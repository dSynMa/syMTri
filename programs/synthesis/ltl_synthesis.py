import subprocess
from tempfile import NamedTemporaryFile
from typing import Tuple

from parsing.hoa_parser import hoa_to_transitions
from programs.program import Program
from programs.synthesis.mealy_machine import MealyMachine
from programs.util import synthesis_problem_to_TLSF_script
from prop_lang.formula import Formula
from prop_lang.util import conjunct, conjunct_formula_set, implies
from prop_lang.variable import Variable


def ltl_synthesis(outside_guarantees : [Formula], assumptions: [Formula], guarantees: [Formula], in_act: [Variable], program_out : [Variable], program_preds : [Variable], out_act: [Variable],
                  strix_tlsf_command: str) -> Tuple[
    bool, MealyMachine]:
    # prepare for tlsf
    in_acts_lowered = [str(a) for a in in_act]
    program_acts_lowered = [str(a) for a in program_preds + program_out]
    out_acts_lowered = [str(a) for a in out_act]

    # new_guarantees = conjunct(conjunct_formula_set(outside_guarantees), implies(conjunct_formula_set(assumptions), conjunct_formula_set(guarantees)))

    ass_tlsf = [str(a.to_strix())
                               .replace("\"", "") for a in assumptions]
    guarantees_tlsf = [str(g.to_strix())
                               .replace("\"", "") for g in guarantees]
    # new_guarantees_tlsf = [str(g.to_strix())
    #                        .replace("\"", "") for g in outside_guarantees]

    # new_guarantees_tlsf = [str(new_guarantees.to_strix())
    #                        .replace("\"", "")]

    tlsf_script = synthesis_problem_to_TLSF_script(in_acts_lowered + program_acts_lowered,
                                                   out_acts_lowered,
                                                   ass_tlsf,
                                                   guarantees_tlsf)
    print(tlsf_script)
    try:
        with NamedTemporaryFile('w', suffix='.tlsf', delete=False) as tmp:
            tmp.write(tlsf_script)
            tmp.close()

            # cmd = strix_tlsf_command + " -v '" + tmp.name + "':./spec.tlsf -m both "
            cmd = "docker run" + " -v " + tmp.name + ":/spec.tlsf" + " --entrypoint ./strix/scripts/strix_tlsf_file.sh strix_tlsf_file /spec.tlsf" + " -m both"

            so = subprocess.getstatusoutput(cmd)
            output: str = so[1]

            if "UNREALIZABLE" in output:
                logger.info("\nINFO: Strix thinks the current abstract problem is unrealisable! I will check..\n")
                mon = parse_hoa(env_events=in_act, program_out=program_out, program_preds=program_preds, con_events=out_act, output=output)
                return False, mon
            elif "REALIZABLE" in output:
                logger.info("\nINFO: Strix thinks the current abstract problem is realisable! I will check..\n")
                try:
                    mon = parse_hoa(env_events=in_act, program_out=program_out, program_preds=program_preds, con_events=out_act, output=output)
                    return True, mon
                except Exception as err:
                    raise err
            else:
                raise Exception(
                    "Strix not returning appropriate value.\n\n" + cmd + "\n\n" + output + "\n\n" + tlsf_script)
    except Exception as err:
        raise err
    pass


def parse_hoa(env_events, program_out, program_preds, con_events, output) -> Program:
    if "UNREALIZABLE" in output:
        counterstrategy = True
    else:
        counterstrategy = False

    logger.info(output)

    logger.info("Parsing Strix output..")
    init_st, trans = hoa_to_transitions(output, not counterstrategy)
    logger.info("Finished parsing Strix output.. Constructing expanded Mealy Machine now..")

    mon = MealyMachine("counterstrategy" if counterstrategy else "controller", "st_" + init_st, env_events + program_out + program_preds, con_events, {}, {})

    mon.add_transitions(not counterstrategy, trans, resolve_env_turns=True, env_events=env_events, prog_out=program_out, prog_preds=program_preds, con_events=con_events)
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
