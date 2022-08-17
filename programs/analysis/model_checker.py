import os
import re
import subprocess
from tempfile import NamedTemporaryFile


class ModelChecker:
    def check(self, nuxmv_script: str, ltl_spec):
        with NamedTemporaryFile('w', suffix='.smv', delete=False) as model, \
                NamedTemporaryFile('w', suffix='.txt', delete=False) as commands:
            model.write(nuxmv_script)
            model.close()

            commands.write("go_msat\n")
            # commands.write("build_boolean_model\n")
            commands.write('check_ltlspec_ic3 -i -p "' + str(ltl_spec) + '"\n')
            commands.write('quit')
            commands.close()
            try:
                out = subprocess.check_output([
                    "nuxmv", "-source", commands.name, model.name], encoding="utf-8")

                if "is true" in out:
                    return True, None
                elif "is false" in out:
                    ce = out.split("Counterexample")[1].strip()
                    ce = re.sub("[^\n] *(act|guard)\_[0-9]+ = [^\n]+\n", "", ce)
                    ce = re.sub("[^\n] *(identity)_[^\n]+\n", "", ce)
                    return False, ce
                else:
                    return NotImplemented
            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(model.name)
                os.remove(commands.name)
