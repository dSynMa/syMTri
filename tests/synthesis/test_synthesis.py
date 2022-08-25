from unittest import TestCase

from programs.parsing.string_to_program import string_to_program
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable
from synthesis.synthesis import abstract_synthesis_loop


class Test(TestCase):
    def test_abstract_synthesis_loop_realisable(self):
        with open('../../examples/parallel/arbiter/program.prog') as file:
            data = file.read()
            program = string_to_program(data)
            prop = UniOp("G", Value("true"))
            real, _ = abstract_synthesis_loop(program, prop, program.env_events + list(program.states) + program.out_events, program.con_events, "shaunazzopardi/strix")
            self.assertTrue(real)


    def test_abstract_synthesis_loop_unrealisable(self):
        with open('../../examples/parallel/arbiter/program.prog') as file:
            data = file.read()
            program = string_to_program(data)
            prop = UniOp("G", Value("false"))
            real, _ = abstract_synthesis_loop(program, prop, program.env_events + list(program.states) + program.out_events, program.con_events, "shaunazzopardi/strix")
            self.assertFalse(real)
