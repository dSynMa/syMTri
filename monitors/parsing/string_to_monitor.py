from monitors.monitor import Monitor
from monitors.transition import Transition
from monitors.typed_valuation import TypedValuation
from prop_lang.parsing.string_to_assignments import *
from prop_lang.parsing.string_to_fol import fol_expression

nameRegex = r'[_a-zA-Z][_a-zA-Z0-9$@\_\-]*'
name = regex(nameRegex)
state = regex(r'[a-zA-Z0-9@$_-]+')

@generate
def monitor_parser():
    yield string("monitor") >> spaces()
    monitor_name = yield name << spaces()
    yield string("{") >> spaces()
    states = yield state_parser
    yield spaces()
    initial_state = yield initial_state_parser
    yield spaces()
    flagging_states = yield flagging_states_parser
    yield spaces()
    initial_vals = yield initial_val_parser
    yield spaces()
    transitions = yield transitions_parser
    yield spaces() >> string("}") >> spaces()

    monitor = Monitor(monitor_name, states, initial_state, initial_vals, flagging_states, transitions)

    return monitor

@generate
def state_parser():
    yield string("STATES") >> spaces() >> string("{") >> spaces()
    states = yield sepBy(state, regex("(,|;)") << spaces())
    yield optional(regex("(,|;)"))
    yield spaces()
    yield string("}")
    yield spaces()
    return states

@generate
def initial_state_parser():
    yield string("INITIAL") >> spaces() >> string("{") >> spaces()
    state_id = yield state << spaces()
    yield spaces() >> string("}")
    return state_id


@generate
def flagging_states_parser():
    yield string("FLAGGING") >> spaces() >> string("{") >> spaces()
    state_id = yield sepBy(state, regex("(,|;)")) << spaces()
    yield spaces() >> string("}")
    return state_id


@generate
def bool_val_parser():
    var = yield name << spaces() << string(":") << spaces()
    type = yield regex("boolean") << spaces()
    yield spaces()
    yield string(":=") << spaces()
    value = yield fol_expression << spaces()
    return TypedValuation(var, type, value)


@generate
def num_val_parser():
    var = yield name << spaces() << string(":") << spaces()
    type = yield regex("(integer|real|([0-9]+|" + nameRegex + ")+\.\.+([0-9]+|" + nameRegex + "))") << spaces()
    yield spaces()
    yield string(":=") << spaces()
    value = yield math_expression << spaces()
    return TypedValuation(var, type, value)


@generate
def initial_val_parser():
    yield string("INITIAL_VALUATION") >> spaces() >> string("{") >> spaces()
    vals = yield sepBy(try_choice(bool_val_parser, num_val_parser), regex("(,|;)") >> spaces())
    yield spaces()
    yield optional(regex("(,|;)"))
    yield spaces() >> string("}")
    return vals

# 0 -> 0 {personInroom & inUse < n >> inUse := inUse + 1},

@generate
def transition_parser():
    yield spaces()
    source = yield state << spaces()
    yield regex("-+>") >> spaces()
    dest = yield state << spaces()
    yield string("[") >> spaces()
    cond = yield optional(fol_expression, [])
    yield spaces()
    if cond == []:
        yield optional(regex(">>+") >> spaces())
        act = yield optional(assignments, [Atom("skip")])
    else:
        actNext = yield optional(regex(">>+") >> spaces(), [])
        if actNext != []:
            act = yield assignments
        else:
            act = []
    yield spaces()
    yield string("]") >> spaces()
    if cond == []:
        cond = Atom("true")
    return Transition(source, cond, act, Atom("TRUE"), dest)


@generate
def transitions_parser():
    yield string("TRANSITIONS") >> spaces() >> string("{") >> spaces()
    transitions = yield sepBy(transition_parser, spaces() >> regex("(,|;)") >> spaces())
    yield spaces() >> string("}")
    return transitions


parser = monitor_parser


def string_to_monitor(input : str) -> Monitor:
    monitor = (parser << parsec.eof()).parse(input)
    monitor.reduce()
    return monitor