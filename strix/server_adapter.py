from typing import Tuple
from urllib.parse import quote

import requests as req

from monitors.monitor import Monitor
from monitors.parsing.kiss_to_monitor import kiss_to_monitor
from prop_lang.atom import Atom


# endpoint = "http://192.168.88.134:5000/kiss"


def strix(ltl: str, in_act: [Atom], out_act: [Atom], end_act: Atom, endpoint: str) -> Tuple[bool, Monitor]:
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
            return (True, kiss_to_monitor(output.replace("REALIZABLE", "").strip(' '), in_act, out_act, end_act))
        else:
            raise Exception("Strix not returning appropriate value.\n" + output)
    except Exception as err:
        raise err
    pass
