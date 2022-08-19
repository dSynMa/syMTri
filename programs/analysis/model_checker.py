import os
import re
import subprocess
from tempfile import NamedTemporaryFile

from programs.analysis.util import parse_nuxmv_ce_output


class ModelChecker:
    def check(self, nuxmv_script: str, ltl_spec):
        with NamedTemporaryFile('w', suffix='.smv', delete=False) as model, \
                NamedTemporaryFile('w', suffix='.txt', delete=False) as commands:
            model.write(nuxmv_script)
            model.close()

            commands.write("go_msat\n")
            commands.write('check_ltlspec_ic3 -i -p "' + str(ltl_spec) + '"\n')
            commands.write('quit')
            commands.close()
            try:
                out = subprocess.check_output([
                    "nuxmv", "-source", commands.name, model.name], encoding="utf-8")

                if "is true" in out:
                    return True, None
                elif "is false" in out:
                    return False, parse_nuxmv_ce_output(out)
                else:
                    # TODO
                    return NotImplemented
            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(model.name)
                os.remove(commands.name)
