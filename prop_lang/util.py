import re

from prop_lang.atom import Atom
from prop_lang.biop import BiOp
from prop_lang.formula import Formula
from prop_lang.uniop import UniOp


def andd(left: Formula, right: Formula):
    if isinstance(left, Atom):
        if left.name.lower() == "true" or left.name.lower == "tt":
            return right
    if isinstance(right, Atom):
        if right.name.lower() == "true" or right.name.lower == "tt":
            return left

    if isinstance(left, Atom):
        if left.name.lower() == "false" or left.name.lower == "ff":
            return left
    if isinstance(right, Atom):
        if right.name.lower() == "false" or right.name.lower == "ff":
            return right

    return BiOp(left, "&&", right);


def orr(left: Formula, right: Formula):
    if isinstance(left, Atom):
        if left.name.lower() == "false" or left.name.lower == "ff":
            return right
    if isinstance(right, Atom):
        if right.name.lower() == "false" or right.name.lower == "ff":
            return left

    if isinstance(left, Atom):
        if left.name.lower() == "true" or left.name.lower == "tt":
            return left
    if isinstance(right, Atom):
        if right.name.lower() == "true" or right.name.lower == "tt":
            return right

    return BiOp(left, "||", right);


def implies(left: Formula, right: Formula):
    return BiOp(left, "->", right);


def iff(left: Formula, right: Formula):
    return BiOp(left, "<->", right);


def until(left: Formula, right: Formula):
    return BiOp(left, "U", right);


def nott(ltl: Formula):
    if isinstance(ltl, UniOp):
        if ltl.op == "!":
            return ltl.right

    return UniOp("!", ltl);


def globally(ltl: Formula):
    return UniOp("G", ltl);


def eventually(ltl: Formula):
    return UniOp("F", ltl);


def next(ltl: Formula):
    return UniOp("X", ltl);


def tighten_ltl(ltl: Formula):
    end_act = Atom("END")
    (success, ltl_next, new_end_conditions, ends) = tighten_ltl_basic(ltl, end_act)
    if success:
        result = ltl_next
        if new_end_conditions is not None:
            result = (andd(ltl_next, new_end_conditions), ends, end_act)
        return result
    else:
        return None


# -> Tuple[bool, Formula, Formula, Atom[]]
def tighten_ltl_basic(ltl: Formula, end: Atom):
    result = (False, None, None, None)
    if isinstance(ltl, Atom):
        result = (True, andd(ltl, globally(end)), None, [end])
    if isinstance(ltl, UniOp):
        if ltl.op == "!":
            if isinstance(ltl.right, Atom):
                result = (True, andd(ltl, globally(end)), None, [end])
            else:
                # Not co-safety
                result = (False, None, None, None)
        if ltl.op == "X":
            (success, ltl_next, new_end_conditions, ends) = tighten_ltl_basic(ltl.right, end)
            if success:
                result = (True, andd(nott(end), next(ltl_next)), new_end_conditions, list(dict.fromkeys([end] + ends)))
        if ltl.op == "F":
            result = tighten_ltl_basic(until(Atom("TRUE"), ltl.right), end)
        if (ltl.op == "G"):
            # Not co-safety
            result = (False, None, None, None)
    if isinstance(ltl, BiOp):
        if re.match("<(-|=)>", ltl.op):
            result = tighten_ltl_basic(andd(
                implies(ltl.left, ltl.right),
                implies(ltl.right, ltl.left)),
                end)
        if re.match("(-|=)>", ltl.op):
            result = tighten_ltl_basic(orr(nott(ltl.left), ltl.right), end)
        if ltl.op == "U":
            (success, ltl_next, new_end_conditions, ends) = tighten_ltl_basic(ltl.right, end)
            if success:
                left = andd(nott(ltl.right), nott(end))
                if ltl.left.name != "TRUE":
                    left = andd(ltl.left, left)
                result = (True, until(left,
                                      ltl_next), new_end_conditions, list(dict.fromkeys([end] + ends)))
        if re.match("&&?", ltl.op):
            end1 = Atom(end.name + "1")
            (v1, ltl1, assm1, ends1) = tighten_ltl_basic(ltl.left, end1)
            end2 = Atom(end.name + str(len(ends1) + 1))
            (v2, ltl2, assm2, ends2) = tighten_ltl_basic(ltl.right, end2)
            if v1 & v2:
                end_conds = globally(iff(end, andd(end1, end2)))
                if assm1 != None:
                    end_conds = andd(end_conds, assm1)
                if assm2 is not None:
                    end_conds = andd(end_conds, assm2)
                result = (True,
                          andd(ltl1, ltl2),
                          end_conds,
                          list(dict.fromkeys([end] + ends1 + ends2)))
        if re.match("\|\|?", ltl.op):
            end1 = Atom(end.name + "1")
            (v1, ltl1, assm1, ends1) = tighten_ltl_basic(ltl.left, end1)
            end2 = Atom(end.name + str(len(ends1) + 1))
            (v2, ltll2, assm2, ends2) = tighten_ltl_basic(ltl.right, end2)
            if v1 & v2:
                end_conds = globally(implies(orr(end1, end2), end))
                if assm1 is not None:
                    end_conds = andd(end_conds, assm1)
                if assm2 is not None:
                    end_conds = andd(end_conds, assm2)
                result = (True,
                          orr(
                              andd(ltl1, nott(ltl.right)),
                              orr(
                                  andd(nott(ltl.left), ltll2),
                                  andd(ltl1, ltll2)
                              )
                          ),
                          end_conds,
                          list(dict.fromkeys([end] + ends1 + ends2)))
    return result
