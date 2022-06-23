import re

from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.mathexpr import MathExpr
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

    return BiOp(left, "&", right);


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

def tighten_ltl(ltl: Formula):
    end_act = Variable("END")
    (success, ltl_next, new_end_conditions, ends) = tighten_ltl_basic(ltl, end_act)
    if success:
        result = ltl_next
        if new_end_conditions is not None:
            result = (conjunct(ltl_next, new_end_conditions), ends, end_act)
        return result
    else:
        return None


# -> Tuple[bool, Formula, Formula, Variable[]]
def tighten_ltl_basic(ltl: Formula, end: Variable):
    result = (False, None, None, None)
    if isinstance(ltl, Atom):
        result = (True, conjunct(ltl, G(end)), None, [end])
    if isinstance(ltl, UniOp):
        if ltl.op == "!":
            if isinstance(ltl.right, Atom):
                result = (True, conjunct(ltl, G(end)), None, [end])
            else:
                # Not co-safety
                result = (False, None, None, None)
        if ltl.op == "X":
            (success, ltl_next, new_end_conditions, ends) = tighten_ltl_basic(ltl.right, end)
            if success:
                result = (True, conjunct(neg(end), X(ltl_next)), new_end_conditions, list(dict.fromkeys([end] + ends)))
        if ltl.op == "F":
            result = tighten_ltl_basic(U(true(), ltl.right), end)
        if ltl.op == "G":
            # Not co-safety
            result = (False, None, None, None)
    if isinstance(ltl, BiOp):
        if re.match("<(-|=)>", ltl.op):
            result = tighten_ltl_basic(conjunct(
                implies(ltl.left, ltl.right),
                implies(ltl.right, ltl.left)),
                end)
        if re.match("(-|=)>", ltl.op):
            result = tighten_ltl_basic(disjunct(neg(ltl.left), ltl.right), end)
        if ltl.op == "U":
            (success, ltl_next, new_end_conditions, ends) = tighten_ltl_basic(ltl.right, end)
            if success:
                left = conjunct(neg(ltl.right), neg(end))
                if not ltl.left.is_true():
                    left = conjunct(ltl.left, left)
                result = (True, U(left,
                                  ltl_next), new_end_conditions, list(dict.fromkeys([end] + ends)))
        if re.match("&&?", ltl.op):
            end1 = Variable(end.name + "1")
            (v1, ltl1, assm1, ends1) = tighten_ltl_basic(ltl.left, end1)
            end2 = Variable(end.name + str(len(ends1) + 1))
            (v2, ltl2, assm2, ends2) = tighten_ltl_basic(ltl.right, end2)
            if v1 & v2:
                end_conds = G(iff(end, conjunct(end1, end2)))
                if assm1 != None:
                    end_conds = conjunct(end_conds, assm1)
                if assm2 is not None:
                    end_conds = conjunct(end_conds, assm2)
                result = (True,
                          conjunct(ltl1, ltl2),
                          end_conds,
                          list(dict.fromkeys([end] + ends1 + ends2)))
        if re.match("\|\|?", ltl.op):
            end1 = Variable(end.name + "1")
            (v1, ltl1, assm1, ends1) = tighten_ltl_basic(ltl.left, end1)
            end2 = Variable(end.name + str(len(ends1) + 1))
            (v2, ltll2, assm2, ends2) = tighten_ltl_basic(ltl.right, end2)
            if v1 & v2:
                end_conds = G(implies(disjunct(end1, end2), end))
                if assm1 is not None:
                    end_conds = conjunct(end_conds, assm1)
                if assm2 is not None:
                    end_conds = conjunct(end_conds, assm2)
                result = (True,
                          disjunct(
                              conjunct(ltl1, neg(ltl.right)),
                              disjunct(
                                  conjunct(neg(ltl.left), ltll2),
                                  conjunct(ltl1, ltll2)
                              )
                          ),
                          end_conds,
                          list(dict.fromkeys([end] + ends1 + ends2)))
    return result


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
        else: #math expression
            return prop
    else:
        return NotImplemented


def project(prop: Formula, events: [Atom]) -> Formula:
    nnf_prop = prop
    if isinstance(nnf_prop, Variable):
        if nnf_prop in events:
            return nnf_prop
        else:
            return true()
    if isinstance(nnf_prop, Value):
        return prop
    elif isinstance(nnf_prop, UniOp):
        if nnf_prop.op == "!":
            if isinstance(nnf_prop.right, Value):
                return nnf_prop
            elif isinstance(nnf_prop.right, Variable):
                if nnf_prop.right in events:
                    return nnf_prop
                else:
                    return true()
            else:
                return Exception("(util.project) Not in NNF form.")
        else:
            return NotImplemented
    elif isinstance(nnf_prop, BiOp):
        # TODO need to actually handle math expressions
        nnf_left = project(nnf(nnf_prop.left), events)
        nnf_right = project(nnf(nnf_prop.right), events)
        if re.match("&&?", nnf_prop.op):
            #this handles the case that the left hand side is a math expression
            if nnf_left is nnf_prop.left and isinstance(nnf_left, MathExpr):
                return nnf_right
            #this handles the case that the right hand side is a math expression
            elif nnf_right is nnf_prop.right and not isinstance(nnf_right, Atom):
                return nnf_left
            else:
                return conjunct(nnf(nnf_prop.left), nnf(nnf_prop.right))
        elif re.match("\|\|?", nnf_prop.op):
            if nnf_left is nnf_prop.left and not isinstance(nnf_left, Atom):
                return nnf_right
            elif nnf_right is nnf_prop.right and not isinstance(nnf_right, Atom):
                return nnf_left
            else:
                return disjunct(nnf(nnf_prop.left), nnf(nnf_prop.right))
        elif re.match("->", nnf_prop.op):
            return project(disjunct(neg(nnf_prop.left), (nnf_prop.right)), events)
        elif re.match("<-", nnf_prop.op):
            return project(disjunct(nnf_prop.left, neg(nnf_prop.right)), events)
        elif re.match("<->", nnf_prop.op):
            return project(conjunct(disjunct(nnf_prop.left, neg(nnf_prop.right)),
                                    disjunct(nnf_prop.left, neg(nnf_prop.right))), events)
        else:
            return nnf_prop
    elif isinstance(nnf_prop, MathExpr):
        return project(conjunct(true(), nnf_prop.formula), events)
    else:
        return nnf_prop
