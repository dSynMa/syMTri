import argparse

from monitors.parsing.string_to_flagging_monitor import string_to_flagging_monitor
from monitors.parsing.string_to_monitor import string_to_monitor
from synthesis.synthesis import synthesize_seq_rep, synthesize_seq, synthesize


# inputs: date_file ltl_file
def main():
    parser = argparse.ArgumentParser()
    # input monitor
    parser.add_argument('--m', dest='monitor', help="Path to a .mon file.", type=str)

    parser.add_argument('--translate', dest='translate', help="Translation workflow.", type=bool)

    parser.add_argument('--format', dest='format', type=str, nargs='?', const=True, default="dot")

    # Synthesis workflow
    parser.add_argument('--synthesise', dest='synthesise', help="Synthesis workflow.", type=bool)

    parser.add_argument('--l', dest='ltl', help="Path to a .tlfs file.", type=str)

    # type of combination
    parser.add_argument('--parallel', dest='parallel', type=bool, nargs='?', const=True, default=False)
    parser.add_argument('--trig_rep', dest='trig_rep', type=bool, nargs='?', const=True, default=False)
    parser.add_argument('--trig_seq', dest='trig_seq', type=bool, nargs='?', const=True, default=False)

    # how to connect to strix (default just assume `strix' is in path)
    parser.add_argument('--strix_server', dest='server', type=str)
    parser.add_argument('--strix_docker', dest='docker', type=str)

    args = parser.parse_args()

    if args.monitor is None:
        raise Exception("Monitor path not specified.")

    date_file = open(args.monitor, "r").read()

    if args.translate:
        try:
            date = string_to_flagging_monitor(date_file)
        except:
            date = string_to_monitor(date_file)

        if args.to_nuxmv:
            print(date.to_nuXmv())
        else:
            print(date.to_nuXmv_case_style())
    elif args.synthesis:
        if args.ltl is None:
            raise Exception("TLSF path not specified.")

        if args.trig_rep:
            date = string_to_flagging_monitor(date_file)
            (realiz, date) = synthesize_seq_rep(date, args.ltl, args.server, args.docker)
        elif args.trig_seq:
            date = string_to_flagging_monitor(date_file)

            (realiz, date) = synthesize_seq(date, args.ltl, args.server, args.docker)
        elif args.parallel:
            date = string_to_monitor(date_file)

            (realiz, date) = synthesize(date, args.ltl, args.server, args.docker)
        else:
            raise NotImplementedError("Synthesis method not specified.")

        if realiz:
            print(str(date))
        else:
            print('Unrealizable.')
    else:
        raise Exception("Specify either --translate or --synthesis.")


if __name__ == "__main__":
    main()
