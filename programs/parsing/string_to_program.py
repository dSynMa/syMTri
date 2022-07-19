from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from prop_lang.parsing.string_to_assignments import *
from prop_lang.parsing.string_to_prop_logic import prop_logic_expression, number_val
from prop_lang.util import true
from prop_lang.variable import Variable

name_regex = r'[_a-zA-Z][_a-zA-Z0-9$@\_\-]*'
name = regex(name_regex)
state = regex(r'[a-zA-Z0-9@$_-]+')


@generate
def program_parser():
    yield string("program") >> spaces()
    program_name = yield name << spaces()
    yield string("{") >> spaces()
    (states, initial_state) = yield state_parser
    yield spaces()
    env = yield string("ENVIRONMENT EVENTS") >> event_parser
    yield spaces()
    con = yield string("CONTROLLER EVENTS") >> event_parser
    yield spaces()
    mon = yield string("PROGRAM EVENTS") >> event_parser
    yield spaces()
    initial_vals = yield initial_val_parser
    yield spaces()
    env_transitions = yield env_transitions_parser
    yield spaces()
    con_transitions = yield con_transitions_parser
    yield spaces() >> string("}") >> spaces()

    program = Program(program_name, states, initial_state, initial_vals, env_transitions, con_transitions, env, con, mon)

    return program


@generate
def event_parser():
    yield spaces() >> string("{") >> spaces()
    events = yield sepBy(name << spaces(), regex("(,|;)") << spaces())
    yield optional(regex("(,|;)"))
    yield spaces()
    yield string("}")
    yield spaces()
    return [Variable(s) for s in events]


@generate
def state_parser():
    yield string("STATES") >> spaces() >> string("{") >> spaces()
    tagged_states = yield sepBy(tagged_state_parser << spaces(), regex("(,|;)") << spaces())
    yield optional(regex("(,|;)"))
    yield spaces()
    yield string("}")
    yield spaces()
    initial_state = [s for (s, tag) in tagged_states if tag == "init"]
    if len(initial_state) != 1:
        yield parsec.none_of(parsec.spaces())
    states = [s for (s, _) in tagged_states]
    return states, initial_state[0]


@generate
def tagged_state_parser():
    state_name = yield state << spaces()
    state_label = yield optional(string(":") >> spaces() >> regex("(init|flag)"), "")
    return state_name, state_label


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
def bool_decl_parser():
    var = yield name << spaces() << string(":") << spaces()
    type = yield regex("bool(ean)?") << spaces()
    yield spaces()
    yield string(":=") << spaces()
    value = yield prop_logic_expression << spaces()
    return TypedValuation(var, type, value)


@generate
def num_decl_parser():
    var = yield name << spaces() << string(":") << spaces()
    type = yield regex("(int(eger)?|real|([0-9]+|" + name_regex + ")+\.\.([0-9]+|" + name_regex + "))") << spaces()
    yield spaces()
    yield string(":=") << spaces()
    value = yield math_expression << spaces()
    return TypedValuation(var, type, value)


@generate
def initial_val_parser():
    yield string("VALUATION") >> spaces() >> string("{") >> spaces()
    vals = yield sepBy(try_choice(bool_decl_parser, num_decl_parser), regex("(,|;)") << spaces())
    yield spaces()
    yield optional(regex("(,|;)"))
    yield spaces() >> string("}")
    return vals


@generate
def transition_parser():
    yield spaces()
    source = yield state << spaces()
    yield regex("-+>") >> spaces()
    dest = yield state << spaces()
    yield string("[") >> spaces()
    cond = yield optional(prop_logic_expression, [])
    yield spaces()
    act = yield optional(string("$") >> spaces() >> assignments, [])
    yield spaces()
    events = yield optional(string(">>") >> spaces() >> assignments, [])
    yield spaces()
    yield string("]") >> spaces()
    if not cond:
        cond = true()
    return Transition(source, cond, act, events, dest)


@generate
def env_transitions_parser():
    yield string("ENVIRONMENT") >> spaces() >> string("TRANSITIONS") >> spaces() >> string("{") >> spaces()
    transitions = yield sepBy(transition_parser, spaces() << regex("(,|;)") << spaces())
    yield spaces() >> string("}")
    return transitions



@generate
def con_transitions_parser():
    yield string("CONTROLLER") >> spaces() >> string("TRANSITIONS") >> spaces() >> string("{") >> spaces()
    transitions = yield sepBy(transition_parser, spaces() >> regex("(,|;)") >> spaces())
    yield spaces() >> string("}")
    return transitions


parser = program_parser


def string_to_program(input: str) -> Program:
    program = (parser << parsec.eof()).parse(input)
    return program
