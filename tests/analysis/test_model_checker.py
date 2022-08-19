from unittest import TestCase

from programs.analysis.model_checker import ModelChecker
from programs.analysis.util import create_nuxmv_model
from programs.parsing.string_to_program import string_to_program


class TestModelChecker(TestCase):
    def test_check(self):
        with open('../monitors/example.prog', 'r') as file:
            data = file.read()
            program = string_to_program(data)
            model_checker = ModelChecker()
            nuxmv_model = create_nuxmv_model(*program.to_nuXmv_with_turns())
            out = model_checker.check(nuxmv_model, "G FALSE")
            print(out[1])
            assert(out[0] is False)
