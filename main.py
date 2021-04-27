import sys
import argparse
from monitors.string_to_date import string_to_date
from synthesis.synthesis import synthesize_seq_rep, synthesize_seq


# inputs: date_file ltl_file
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--m', dest='monitor', type=str)
    parser.add_argument('--l', dest='ltl', type=str)
    parser.add_argument('--rep', dest='rep', type=bool, nargs='?', const=True, default=False)
    parser.add_argument('--server', dest='server', type=str)
    parser.add_argument('--docker', dest='docker', type=str)
    parser.add_argument('--dot', dest='dot', type=bool, nargs='?', const=True, default=False)
    args = parser.parse_args()

    if args.monitor is None:
        raise Exception("Monitor path not specified.")
    if args.ltl is None:
        raise Exception("TLSF path not specified.")

    date_file = open(args.monitor, "r").read()

    date = string_to_date(date_file)
    if args.rep:
        (realiz, date) = synthesize_seq_rep(date, args.ltl, args.server, args.docker)
    else:
        (realiz, date) = synthesize_seq(date, args.ltl, args.server, args.docker)

    if realiz:
        print(str(date))
        if args.dot:
            print("\n\nDOT:\n")
            print(date.to_dot().source)
    else:
        print('Unrealizable.')


if __name__ == "__main__":
    main()
import sys
import argparse
from monitors.string_to_date import string_to_date
from synthesis.synthesis import synthesize_seq_rep, synthesize_seq


# inputs: date_file ltl_file
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--m', dest='monitor', type=str)
    parser.add_argument('--l', dest='ltl', type=str)
    parser.add_argument('--rep', dest='rep', type=bool, nargs='?', const=True, default=False)
    parser.add_argument('--server', dest='server', type=str)
    parser.add_argument('--docker', dest='docker', type=str)
    parser.add_argument('--dot', dest='dot', type=bool, nargs='?', const=True, default=False)
    args = parser.parse_args()

    if args.monitor is None:
        raise Exception("Monitor path not specified.")
    if args.ltl is None:
        raise Exception("TLSF path not specified.")

    date_file = open(args.monitor, "r").read()

    date = string_to_date(date_file)
    if args.rep:
        (realiz, date) = synthesize_seq_rep(date, args.ltl, args.server, args.docker)
    else:
        (realiz, date) = synthesize_seq(date, args.ltl, args.server, args.docker)

    if realiz:
        print(str(date))
        if args.dot:
            print("\n\nDOT:\n")
            print(date.to_dot().source)
    else:
        print('Unrealizable.')


if __name__ == "__main__":
    main()
