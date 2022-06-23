from typing import Tuple
from urllib.parse import quote

import requests as req

from monitors.flaggingmonitor import FlaggingMonitor
from monitors.parsing.kiss_to_monitor import kiss_to_monitor


# endpoint = "http://192.168.88.134:5000/kiss"
from prop_lang.variable import Variable


def strix(ltl: str, in_act: [Variable], out_act: [Variable], end_act: Variable, endpoint: str) -> Tuple[bool, FlaggingMonitor]:
    in_act_string = ",".join([str(a) for a in in_act])
    out_act_string = ",".join([str(a) for a in out_act])
    ltl_string = quote(ltl)
    try:
        url_req = endpoint + "?in=" + in_act_string + "&out=" + out_act_string + "&parsing=" + ltl_string + ""
        resp = req.get(url_req)
        output: str = resp.text

        if output.startswith("UNREALIZABLE"):
            return (False, {})
        elif output.startswith("REALIZABLE"):
            return True, kiss_to_monitor(output.replace("REALIZABLE", "").strip(' '), in_act, out_act, end_act)
        else:
            raise Exception("Strix not returning appropriate value.\n" + output)
    except Exception as err:
        raise err
    pass
