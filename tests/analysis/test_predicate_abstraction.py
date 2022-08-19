from unittest import TestCase

from programs.analysis.model_checker import ModelChecker
from programs.analysis.predicate_abstraction import abstraction_to_ltl_with_turns, predicate_abstraction
from programs.analysis.util import create_nuxmv_model, symbol_table_from_program
from programs.parsing.string_to_program import string_to_program


class Test(TestCase):
    def test_abstraction_to_ltl_with_turns(self):
        with open('../monitors/example.prog', 'r') as file:
            data = file.read()
            program = string_to_program(data)
            model_checker = ModelChecker()
            nuxmv_model = create_nuxmv_model(*program.to_nuXmv_with_turns())
            abstraction = predicate_abstraction(program, [], symbol_table_from_program(program))
            ltl_abstraction = abstraction_to_ltl_with_turns(abstraction)
            print(ltl_abstraction)
            out = model_checker.check(nuxmv_model, str(ltl_abstraction))
            if not out[0]:
                print(out[1])
            assert(out[0] is True)
