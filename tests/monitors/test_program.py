import unittest
import os

from programs.parsing.string_to_program import string_to_program


class MyTestCase(unittest.TestCase):
    def test_example(self):
        with open('example.prog') as f:
            lines = f.readlines()
            monitor = string_to_program("\n".join(lines))
            print(monitor)
            if monitor is None:
                self.fail()
        self.assertEqual(True, True)


if __name__ == '__main__':
    unittest.main()