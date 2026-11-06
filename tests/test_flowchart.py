import re
import unittest

from minimermaid import json_to_mermaid, miniscript_to_json, miniscript_to_mermaid


class FlowchartTests(unittest.TestCase):
    def test_reported_policy_with_threshold_inside_or(self):
        source = (
            "and(or(pk(alice),and(pk(bob),older(10080))),"
            "or(and(pk(charlie),sha256(h)),thresh(2,pk(dave),pk(eve),pk(frank))))"
        )
        for simplify in (False, True):
            with self.subTest(simplify=simplify):
                graph = miniscript_to_mermaid(source, simplify)
                self.assertEqual(graph.count("{Check 2/3}"), 1)
                for name in ("alice", "bob", "charlie", "dave", "eve", "frank"):
                    self.assertIn(f'["{name}"]', graph)

    def test_deep_thresholds_render_with_and_without_simplification(self):
        depth = 2000
        source = (
            "thresh(2," * depth
            + "pk(Seed)"
            + "".join(f",pk(A{i}),pk(B{i}))" for i in range(depth))
        )
        for simplify in (False, True):
            with self.subTest(simplify=simplify):
                graph = miniscript_to_mermaid(source, simplify)
                self.assertEqual(graph.count("{Check 2/3}"), depth)
                leaf_ids = re.findall(r"^(leaf_\d+)\[", graph, re.MULTILINE)
                self.assertEqual(len(set(leaf_ids)), 2 * depth + 1)
                self.assertIn('["Seed"]', graph)

    def test_duplicate_slots_are_distinct_and_cannot_alias_spend(self):
        source = "thresh(2,pk(s),pk(s),pk(n))"
        for simplify in (False, True):
            with self.subTest(simplify=simplify):
                graph = miniscript_to_mermaid(source, simplify)
                self.assertEqual(graph, miniscript_to_mermaid(source, simplify))
                self.assertEqual(graph.count('["s"]'), 2)
                self.assertEqual(graph.count("-->|pk| thresh_0"), 3)
                self.assertIn("thresh_0 -->|yes|s((spend))", graph)
                self.assertIn("thresh_0 -->|no|n((nothing))", graph)

    def test_preserves_literal_case_and_escapes_graph_labels(self):
        graph = miniscript_to_mermaid("and(pk(Alice),pk(alice))")
        self.assertIn('["Alice"]', graph)
        self.assertIn('["alice"]', graph)
        literal = json_to_mermaid({"pk": ['a"b#c']})
        self.assertIn('["a#34;b#35;c"]', literal)

    def test_rejects_malformed_input_in_both_modes(self):
        for source in ("pk(A))", "pk(A)junk", "pk(A", "thresh(1)", "thresh(3,pk(A),pk(B))"):
            for simplify in (False, True):
                with self.subTest(source=source, simplify=simplify):
                    with self.assertRaises(ValueError):
                        miniscript_to_mermaid(source, simplify)

    def test_parser_accepts_weights_and_preserves_numeric_and_text_leaves(self):
        self.assertEqual(
            miniscript_to_json("or(10@pk(Alice), older(42))"),
            {"or": [{"pk": ["Alice"]}, {"older": [42]}]},
        )


if __name__ == "__main__":
    unittest.main()
