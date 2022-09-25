import os
import subprocess
from tempfile import NamedTemporaryFile


class ModelChecker:
    def check(self, nuxmv_script: str, ltl_spec, bound):
        with NamedTemporaryFile('w', suffix='.smv', delete=False) as model, \
                NamedTemporaryFile('w', suffix='.txt', delete=False) as commands:
            model.write(nuxmv_script)
            model.close()

            commands.write("go_msat\n")
            if bound is None:
                commands.write('check_ltlspec_ic3 -i -K 0 -p "' + str(ltl_spec) + '"\n')
            else:
                commands.write('check_ltlspec_ic3 -i -K 0 -k ' + str(bound) + ' -p "' + str(ltl_spec) + '"\n')
            commands.write('quit')
            commands.close()
            try:
                out = subprocess.check_output([
                    "nuxmv", "-source", commands.name, model.name], encoding="utf-8")

                if "is true" in out:
                    return True, None
                elif "is false" in out:
                    return False, out
                elif "Maximum bound reached" in out:
                    return False, None
                else:
                    # TODO
                    return NotImplemented
            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(model.name)
                os.remove(commands.name)

    def to_vmt(self, nuxmv_script: str, ltl_spec):
        with NamedTemporaryFile('w', suffix='.smv', delete=False) as model, \
                NamedTemporaryFile('w', suffix='.txt', delete=False) as commands:
            model.write(nuxmv_script)
            if ltl_spec != None:
                model.write("LTLSPEC " + str(ltl_spec))
            model.close()

            commands.write("go_msat\n")
            commands.write("write_vmt_model -n 0 -o model.vmt\n")
            commands.write('quit\n')
            commands.close()

            try:
                out = subprocess.check_output([
                    "nuxmv", "-source", commands.name, model.name], encoding="utf-8")
                print(out)
            except subprocess.CalledProcessError as err:
                self.fail(err.output)
            finally:
                os.remove(model.name)
                os.remove(commands.name)
