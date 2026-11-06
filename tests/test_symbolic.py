import unittest

from sympy import And, Symbol

from minimermaid import miniscript_to_sympy, simplify_miniscript


class SymbolicThresholdTests(unittest.TestCase):
    def test_thresholds_are_boolean_operands(self):
        threshold = "thresh(2,pk(Dave),pk(Eve),pk(Frank))"
        for operator in ("and", "or"):
            with self.subTest(operator=operator):
                source = f"{operator}(pk(Alice),{threshold})"
                expression = miniscript_to_sympy(source)
                self.assertEqual(
                    expression.free_symbols, {Symbol("pk.Alice"), Symbol(threshold)}
                )
                self.assertIn(Symbol(threshold), And(Symbol("control"), expression).free_symbols)

    def test_surrounding_boolean_optimization_can_absorb_a_threshold(self):
        threshold = "thresh(2,pk(B),pk(C),pk(D))"
        source = f"or(pk(A),and(pk(A),{threshold}))"
        self.assertEqual(simplify_miniscript(source), "pk(A)")

    def test_keeps_each_slot_in_a_proper_threshold(self):
        source = "thresh(2,thresh(2,pk(A),pk(A),pk(B)),pk(C),pk(D))"
        self.assertEqual(simplify_miniscript(source), source)

    def test_a_large_threshold_is_not_duplicated_by_a_boolean_rewrite(self):
        threshold = "thresh(2,thresh(2,pk(A),pk(B),pk(C)),pk(D),pk(E))"
        source = f"or(and(pk(F),pk(G)),{threshold})"
        self.assertEqual(simplify_miniscript(source).count("thresh("), 2)

    def test_nested_rewrites_cannot_multiply_an_inner_threshold(self):
        source = "thresh(2,pk(Seed),pk(X),pk(Y))"
        for index in range(12):
            source = (
                f"thresh(2,or(pk(A{index}),and({source},or(pk(B{index}),pk(C{index})))),"
                f"pk(U{index}),pk(V{index}))"
            )
        simplified = simplify_miniscript(source)
        self.assertEqual(simplified.count("pk(Seed)"), 1)
        self.assertEqual(simplified.count("thresh("), 13)

    def test_more_levels_than_the_python_call_stack(self):
        depth = 2000
        source = (
            "thresh(2," * depth
            + "pk(Seed)"
            + "".join(f",pk(A{i}),pk(B{i}))" for i in range(depth))
        )
        self.assertEqual(simplify_miniscript(source), source)
        self.assertEqual(len(miniscript_to_sympy(source).free_symbols), 1)

    def test_long_chain_of_boolean_gates_preserves_each_operand(self):
        depth = 2000
        source = "and(" * depth + "pk(Seed)" + "".join(f",pk(A{i}))" for i in range(depth))
        simplified = simplify_miniscript(source)
        self.assertEqual(simplified.count("pk("), depth + 1)
        self.assertIn("pk(Seed)", simplified)

    def test_validates_a_threshold_even_if_the_branch_could_be_absorbed(self):
        source = "or(pk(A),and(pk(A),thresh(4,pk(B),pk(C),pk(D))))"
        with self.assertRaisesRegex(ValueError, "thresh requires a threshold"):
            simplify_miniscript(source)

    def test_threshold_limits_are_and_or_at_any_level(self):
        source = "thresh(2,thresh(1,pk(A),pk(B)),pk(C))"
        expression = miniscript_to_sympy(source)
        self.assertEqual(expression, And(Symbol("pk.C"), Symbol("pk.A") | Symbol("pk.B")))

    def test_a_bare_symbol_cannot_alias_a_typed_predicate(self):
        expression = miniscript_to_sympy("and(pk(Alice),pk.Alice)")
        self.assertEqual(expression, And(Symbol("pk(Alice)"), Symbol("pk.Alice")))


if __name__ == "__main__":
    unittest.main()
