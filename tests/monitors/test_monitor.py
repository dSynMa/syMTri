import unittest
import os

from monitors.parsing.string_to_monitor import string_to_monitor


class MyTestCase(unittest.TestCase):
    def test_example(self):
        with open('./example.mon') as f:
            lines = f.readlines()
            monitor = string_to_monitor("\n".join(lines))
            print(monitor)
            if monitor is None:
                self.fail()
        self.assertEqual(True, True)

    def test_abstract_into_ltl(self):
        with open('./example.mon') as f:
            lines = f.readlines()
            monitor = string_to_monitor("\n".join(lines))
            print(monitor.abstract_into_ltl())
            if monitor is None:
                self.fail()
        self.assertEqual(True, True)

    def test_verify_abstract_into_ltl(self):
        with open('./example.mon') as f:
            lines = f.readlines()
            monitor = string_to_monitor("\n".join(lines))
            ltl = monitor.abstract_into_ltl()
            nuxmv = monitor.to_nuXmv()
            nuxmv += "\nLTLSPEC " + str(ltl)

            f = open("example-ltl-test.smv", "a")
            f.truncate(0)
            f.write(nuxmv)
            f.close()
            stream = os.popen('nuxmv "./example-ltl-test.smv')
            output = stream.read()
            print(output)

            if monitor is None:
                self.fail()
        self.assertEqual(True, True)


if __name__ == '__main__':
    unittest.main()
