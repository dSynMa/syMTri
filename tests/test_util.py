from unittest import TestCase

from programs.typed_valuation import TypedValuation
from programs.util import reduce_up_to_iff
from prop_lang.biop import BiOp
from prop_lang.util import neg
from prop_lang.value import Value
from prop_lang.variable import Variable


class Test(TestCase):
    def test_reduce_up_to_iff(self):
        old_preds = [Variable("a")]
        new_preds = [Variable("a")]
        reduced = reduce_up_to_iff(old_preds, new_preds, {"a" : TypedValuation("a", "bool", None)})
        self.assertTrue(set(reduced) == set(old_preds))
    def test_reduce_up_to_iff1(self):
        old_preds = [Variable("a")]
        new_preds = [BiOp(Variable("a"), "=", Value("TRUE"))]
        reduced = reduce_up_to_iff(old_preds, new_preds, {"a" : TypedValuation("a", "bool", None)})
        self.assertTrue(set(reduced) == set(old_preds))

    def test_reduce_up_to_iff2(self):
        old_preds = [Variable("a")]
        new_preds = [BiOp(neg(Variable("a")), "=", Value("TRUE"))]
        reduced = reduce_up_to_iff(old_preds, new_preds, {"a" : TypedValuation("a", "bool", None)})
        self.assertTrue(set(reduced) == set(old_preds))
