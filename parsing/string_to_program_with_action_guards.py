import parsec
from parsec import generate, string, sepBy, spaces, regex

from parsing.string_to_prop_logic import string_to_math_expression, string_to_prop
from programs.analysis.smt_checker import SMTChecker
from programs.program import Program
from programs.transition import Transition
from programs.typed_valuation import TypedValuation
from programs.util import guarded_action_transitions_to_normal_transitions, resolve_next_references
from prop_lang.biop import BiOp
from prop_lang.mathexpr import MathExpr
from prop_lang.util import true, sat, conjunct
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

    new_env_transitions = [resolve_next_references(tt, initial_vals) for t in env_transitions for tt in guarded_action_transitions_to_normal_transitions(t, initial_vals, env, con, mon)]
    new_con_transitions = [resolve_next_references(tt, initial_vals) for t in con_transitions for tt in guarded_action_transitions_to_normal_transitions(t, initial_vals, env, con, mon)]

    program = Program(program_name, states, initial_state, initial_vals, new_env_transitions, new_con_transitions, env, con,
                      mon)

    return program

@generate
def event_parser():
    yield spaces() >> string("{") >> spaces()
    events = yield sepBy(name << spaces(), regex("(,|;)") << spaces())
    yield parsec.optional(regex("(,|;)"))
    yield spaces()
    yield string("}")
    yield spaces()
    return [Variable(s) for s in events]


@generate
def state_parser():
    yield string("STATES") >> spaces() >> string("{") >> spaces()
    tagged_states = yield sepBy(tagged_state_parser << spaces(), regex("(,|;)") << spaces())
    yield parsec.optional(regex("(,|;)"))
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
    state_label = yield parsec.optional(string(":") >> spaces() >> regex("(init|flag)"), "")
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
    yield string(":=") << spaces()
    raw_value = yield regex("[^,;\}]+") << spaces()
    try:
        value = string_to_prop(raw_value)
    except Exception as e:
        yield parsec.fail_with(str(e))
    return TypedValuation(var, type, value)


@generate
def num_decl_parser():
    var = yield name << spaces() << string(":") << spaces()
    type = yield regex(
        "(int(eger)?|nat(ural)?|bool(ean)?|real|([0-9]+|" + name_regex + ")+\.\.([0-9]+|" + name_regex + "))") << spaces()
    yield spaces()
    yield string(":=") << spaces()
    raw_value = yield regex("[^,;\}]+") << spaces()
    try:
        value = string_to_math_expression(raw_value)
    except Exception as e:
        yield parsec.fail_with(str(e))
    return TypedValuation(var, type, value)


@generate
def bool_decl_parser_untyped():
    var = yield name << spaces() << spaces()
    yield string(":=") << spaces()
    raw_value = yield regex("[^,;\]\#]+") << spaces()
    action_and_guard = raw_value.split(" if ")
    try:
        if len(action_and_guard) == 1:
            value = string_to_prop(action_and_guard[0])
            guard = true()
        else:
            value = string_to_prop(action_and_guard[0])
            guard = string_to_prop(action_and_guard[1])
    except Exception as e:
        yield parsec.fail_with(str(e))
    return (BiOp(Variable(var), ":=", value), guard)


@generate
def num_decl_parser_untyped():
    var = yield name << spaces() << spaces()
    yield string(":=") << spaces()
    raw_value = yield regex("[^,;\]\#]+") << spaces()
    action_and_guard = raw_value.split(" if ")
    try:
        if len(action_and_guard) == 1:
            value = string_to_math_expression(action_and_guard[0])
            guard = true()
        else:
            value = string_to_math_expression(action_and_guard[0])
            guard = string_to_prop(action_and_guard[1])
    except Exception as e:
        yield parsec.fail_with(str(e))
    return (BiOp(Variable(var), ":=", MathExpr(value)), guard)


@generate
def assignment_parser_with_action_guard():
    assignment = yield parsec.try_choice(bool_decl_parser_untyped, num_decl_parser_untyped) << spaces()
    guard = yield action_guard << spaces()
    return (assignment, guard)


@generate
def action_guard():
    yield string("if") << spaces() << spaces()
    raw_value = yield regex("[^,;\]\#]+") << spaces()
    try:
        value = string_to_prop(raw_value)
    except Exception as e:
        yield parsec.fail_with(str(e))
    return value


@generate
def initial_val_parser():
    yield string("VALUATION") >> spaces() >> string("{") >> spaces()
    vals = yield sepBy(parsec.try_choice(bool_decl_parser, num_decl_parser), regex("(,|;)") << spaces())
    yield spaces()
    yield parsec.optional(regex("(,|;)"))
    yield spaces() >> string("}")
    if len(set([v.name for v in vals])) < len(vals):
        raise Exception("Variables with same name in VALUATION.")
    return vals


@generate
def transition_parser():
    yield spaces()
    source = yield state << spaces()
    yield regex("-+>") >> spaces()
    dest = yield state << spaces()
    yield string("[") >> spaces()
    raw_cond = yield parsec.optional(spaces() >> regex("[^$#\]]+"), "true")
    cond = string_to_prop(raw_cond)
    yield spaces()
    act = yield parsec.optional(string("$")
                                >> spaces()
                                >> assignments
                                << spaces()
                                << parsec.optional(regex("(,|;)") >> spaces())
                                << parsec.lookahead(regex("(#|\])")),
                                [])
    yield spaces()
    raw_events = yield parsec.optional(outputs, [])
    events = [Variable(e) for e in raw_events]
    yield spaces()
    yield string("]") >> spaces()
    if not cond:
        cond = true()
    return Transition(source, cond, act, events, dest)


@generate
def outputs():
    outputs = yield string("#") \
                       >> spaces() \
                       >> sepBy(parsec.try_choice(bool_decl_parser_untyped, regex("[^\],;]+"))
                                << spaces(), regex("(,|;)")
                                >> spaces())

    if len({str(v.left) for v in outputs if isinstance(v, BiOp)} | {str(v) for v in outputs if not isinstance(v, BiOp)}) < len(outputs):
        raise Exception("Output variables can only be assigned once by a transition.")
    return outputs


@generate
def assignments():
    asss = yield sepBy(parsec.try_choice(bool_decl_parser_untyped, num_decl_parser_untyped),
                       regex("(,|;)") >> spaces()) << parsec.optional(regex("(,|;)") >> spaces())
    # if len(set([v[0].left for v in asss])) < len(asss):
    #     raise Exception("Variables can only be assigned once by a transition.")
    return asss


# @generate
# def assignment():
#     assign = yield parsec.try_choice(bool_decl_parser_untyped, num_decl_parser_untyped) >> spaces()
#     guard = yield parsec.optional(action_guard, true())
#     return (assign, guard)


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
