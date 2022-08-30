import re

from pysmt.shortcuts import Solver

from programs.typed_valuation import TypedValuation
from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp
from prop_lang.value import Value
from prop_lang.variable import Variable


def true():
    return Value("TRUE")


def false():
    return Value("FALSE")


def conjunct(left: Formula, right: Formula):
    if isinstance(left, Value):
        if left.is_true():
            return right
    if isinstance(right, Value):
        if right.is_true():
            return left

    if isinstance(left, Value):
        if left.is_false():
            return left
    if isinstance(right, Value):
        if right.is_false():
            return right

    return BiOp(left, "&", right)


def conjunct_formula_set(s) -> Formula:
    ret = true()
    for f in s:
        ret = conjunct(ret, f)
    return ret


def conjunct_typed_valuation_set(s: set[TypedValuation]) -> Formula:
    ret = true()
    for f in s:
        ret = conjunct(ret, BiOp(Variable(f.name), "=", Value(f.value)))
    return ret


def disjunct(left: Formula, right: Formula):
    if isinstance(left, Value):
        if left.is_false():
            return right
    if isinstance(right, Value):
        if right.is_false():
            return left

    if isinstance(left, Value):
        if left.is_true():
            return left
    if isinstance(right, Value):
        if right.is_true():
            return right

    return BiOp(left, "|", right);


def disjunct_formula_set(s) -> Formula:
    ret = false()
    for f in s:
        ret = disjunct(ret, f)
    return ret


def implies(left: Formula, right: Formula):
    return BiOp(left, "->", right);


def iff(left: Formula, right: Formula):
    return BiOp(left, "<->", right);


def U(left: Formula, right: Formula):
    return BiOp(left, "U", right);


def neg(ltl: Formula):
    if isinstance(ltl, UniOp):
        if ltl.op == "!":
            return ltl.right

    return UniOp("!", ltl);


def G(ltl: Formula):
    return UniOp("G", ltl);


def F(ltl: Formula):
    return UniOp("F", ltl);


def X(ltl: Formula):
    return UniOp("X", ltl);


def nnf(prop: Formula) -> Formula:
    if isinstance(prop, Atom):
        return prop
    elif isinstance(prop, UniOp):
        if prop.op == "!":
            if isinstance(prop.right, Atom):
                return prop
            elif isinstance(prop.right, UniOp) and prop.right.op == "!":
                return nnf(prop.right)
    elif isinstance(prop, BiOp):
        if re.match("<(-|=)>", prop.op):
            return nnf(conjunct(
                implies(prop.left, prop.right),
                implies(prop.right, prop.left)))
        elif re.match("(-|=)>", prop.op):
            return nnf(disjunct(neg(prop.left), prop.right))
        elif re.match("&&*", prop.op):
            return conjunct(nnf(prop.left), nnf(prop.right))
        elif re.match("\|\|?", prop.op):
            return disjunct(nnf(prop.left), nnf(prop.right))
        else:  # math expression
            return prop
    else:
        return NotImplemented


def sat(formula: Formula, symbol_table: dict, solver: Solver) -> bool:
    return solver.is_sat(formula.to_smt(symbol_table))


def negation_closed(predicates: [Formula]):
    for p in predicates:
        if neg(p) not in predicates:
            return False
    return True


def prime_action(acts: [BiOp]) -> Formula:
    if len(acts) == 0:
        return acts
    else:
        primed_acts = []
        for act in acts:
            primed_acts.append(BiOp(Atom(act.left.name + "_next"), "=", act.right))
    return conjunct_formula_set(primed_acts)


def push_negation(f: Formula):
    if isinstance(f, Atom):
        return f
    elif isinstance(f, BiOp):
        return BiOp(push_negation(f.left), f.op, push_negation(f.right))
    elif isinstance(f, UniOp):
        if isinstance(f.right, Value) or isinstance(f.right, Variable):
            return f
        elif f.op != "!":
            return UniOp("!", push_negation(f.right))
        else:
            if isinstance(f.right, UniOp) and f.right.op == "!":
                return push_negation(f.right.right)
            elif isinstance(f.right, UniOp) and f.right.op != "!":
                return UniOp("!", push_negation(f.right))
            elif isinstance(f.right, BiOp):
                if f.right.op in ["&", "&&"]:
                    return BiOp(push_negation(UniOp("!", f.right.left)), "|",
                                push_negation(UniOp("!", f.right.right)))
                elif f.right.op in ["|", "||"]:
                    return BiOp(push_negation(UniOp("!", f.right.left)), "&",
                                push_negation(UniOp("!", f.right.right)))
                elif f.right.op in ["->", "=>"]:
                    return BiOp(push_negation(f.right.left), "&", push_negation(UniOp("!", f.right.right)))
                elif f.right.op in ["<->", "<=>"]:
                    return BiOp(
                        BiOp(push_negation(f.right.left), "&", push_negation(UniOp("!", f.right.right)),
                             "|",
                             BiOp(push_negation(UniOp("!", f.right.left)), "&", push_negation(f.right.right))))
                else:
                    return UniOp(f.op, push_negation(f.right))
    else:
        return f
