import argparse

from programs.parsing.string_to_program import string_to_program
from synthesis.synthesis import synthesize


# inputs: date_file ltl_file
def main():
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument('--p', dest='program', help="Path to a .prog file.", type=str)

    parser.add_argument('--translate', dest='translate', help="Translation workflow.", type=bool)

    parser.add_argument('--format', dest='format', type=str, nargs='?', const=True, default="dot")

    # Synthesis workflow
    parser.add_argument('--synthesise', dest='synthesise', help="Synthesis workflow.", type=bool, nargs='?', const=True)

    parser.add_argument('--l', dest='ltl', help="Inline LTL formula.", type=str)
    parser.add_argument('--tlsf', dest='tlsf', help="Path to a .tlfs file.", type=str)

    # how to connect to strix (default just assume `strix' is in path)
    parser.add_argument('--strix_docker', dest='docker', type=str, nargs='?', const=False)

    args = parser.parse_args()

    if args.program is None:
        raise Exception("Program path not specified.")

    date_file = open(args.program, "r").read()

    date = string_to_program(date_file)

    if args.translate:
        if args.to_nuxmv:
            print(date.to_nuXmv())
        else:
            print(date.to_nuXmv_case_style())
    elif args.synthesise:
        if args.ltl is None and args.tlsf is None:
            raise Exception("No property specified.")

        (realiz, mm) = synthesize(date, args.ltl, args.tlsf, args.docker)

        if realiz:
            print('Realizable.')
            print(str(mm.to_dot()))
        else:
            print('Unrealizable.')
            print(str(mm.to_dot()))
    else:
        raise Exception("Specify either --translate or --synthesise.")


if __name__ == "__main__":
    main()
