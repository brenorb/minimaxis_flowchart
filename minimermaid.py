from __future__ import annotations

import re
from dataclasses import dataclass

from sympy import And, Or, Symbol
from sympy.logic.boolalg import simplify_logic


LEAVES = {"pk", "after", "older", "sha256", "hash256", "ripemd160", "hash160"}
HASH_LENGTHS = {"sha256": 64, "hash256": 64, "ripemd160": 40, "hash160": 40}
TOKEN = re.compile(r"[^(),\s]+|[(),]")
WEIGHT = re.compile(r"\b\d+@\s*(?=[A-Za-z]\w*\s*\()")
# Keep the SymPy expression shallow even when the policy itself is very deep.
# Larger Boolean regions can still use their children as opaque predicates.
FORMULA_NODE_BUDGET = 32


@dataclass(frozen=True, eq=False)
class Policy:
    kind: str
    children: tuple[Policy, ...] = ()
    value: str | int | None = None


def _policy(value):
    return Policy("symbol", value=value) if isinstance(value, str) else value


def _integer(value, function):
    if not isinstance(value, str) or not re.fullmatch(r"[0-9]+", value):
        raise ValueError(f"{function} requires a non-negative integer argument")
    return int(value)


def _make_policy(name, args):
    name = name.lower()
    if name in {"and", "or"}:
        if len(args) < 2:
            raise ValueError(f"{name} requires at least two policies")
        return Policy(name, tuple(map(_policy, args)))
    if name == "thresh":
        count = _integer(args[0], name)
        children = tuple(map(_policy, args[1:]))
        if not 1 <= count <= len(children):
            raise ValueError("thresh requires a threshold between 1 and its number of policies")
        return Policy(name, children, count)
    if name not in LEAVES:
        raise ValueError(f"Invalid function: {name}")
    if len(args) != 1 or not isinstance(args[0], str):
        raise ValueError(f"{name} requires one literal argument")
    value = args[0]
    if name in {"after", "older"}:
        value = _integer(value, name)
        if not value:
            raise ValueError(f"{name} requires a positive integer argument")
    elif name in HASH_LENGTHS and value.lower() != "h" and len(value) != HASH_LENGTHS[name]:
        raise ValueError(f"{name} requires a {HASH_LENGTHS[name]}-character hash")
    return Policy(name, value=value)


def _parse_policy(source):
    """Read one policy using a stack of unfinished calls."""
    tokens = TOKEN.findall(WEIGHT.sub("", source))
    frames = []
    root = None
    expecting_value = True
    index = 0
    while index < len(tokens):
        token = tokens[index]
        index += 1
        if expecting_value:
            if token in {"(", ")", ","}:
                raise ValueError(f"Expected a policy or argument, got {token!r}")
            if index < len(tokens) and tokens[index] == "(":
                frames.append((token, []))
                index += 1
                continue
            value = token
        elif token == "," and frames:
            expecting_value = True
            continue
        elif token == ")" and frames:
            name, args = frames.pop()
            value = _make_policy(name, args)
        else:
            raise ValueError(f"Unexpected token: {token!r}")

        if frames:
            frames[-1][1].append(value)
        else:
            root = _policy(value)
        expecting_value = False

    if frames:
        raise ValueError("Missing closing parenthesis")
    if root is None or expecting_value:
        raise ValueError("Expected a policy")
    return root


def _postorder(root, children):
    pending = [(root, False)]
    while pending:
        node, visited = pending.pop()
        if visited:
            yield node
        else:
            pending.append((node, True))
            pending.extend((child, False) for child in reversed(children(node)))


def _policy_text(root):
    parts = []
    pending = [root]
    while pending:
        node = pending.pop()
        if isinstance(node, str):
            parts.append(node)
        elif node.kind == "symbol":
            parts.append(node.value)
        elif not node.children:
            parts.append(f"{node.kind}({node.value})")
        else:
            parts.append(f"{node.kind}(")
            if node.kind == "thresh":
                parts.append(f"{node.value},")
            pending.append(")")
            for index in range(len(node.children) - 1, -1, -1):
                pending.append(node.children[index])
                if index:
                    pending.append(",")
    return "".join(parts)


class _Optimizer:
    def __init__(self):
        self.policies = {}
        self.policy_sizes = {}
        self.atoms = {}
        self.symbols = {}

    def intern(self, policy):
        key = (policy.kind, policy.value, policy.children)
        if key not in self.policies:
            self.policies[key] = policy
            self.policy_sizes[policy] = 1 + sum(self.policy_sizes[child] for child in policy.children)
        return self.policies[key]

    def atom(self, policy):
        if policy not in self.atoms:
            symbol = Symbol(f"_policy_{len(self.atoms)}")
            self.atoms[policy] = symbol
            self.symbols[symbol] = policy
        return self.atoms[policy]

    def expanded_size(self, formula):
        size = 0
        pending = [formula]
        while pending:
            expression = pending.pop()
            if expression in self.symbols:
                size += self.policy_sizes[self.symbols[expression]]
            else:
                size += 1
                pending.extend(expression.args)
        return size

    def from_formula(self, formula):
        nodes = {}
        for expression in _postorder(formula, lambda expr: expr.args):
            if expression in self.symbols:
                nodes[expression] = self.symbols[expression], 1
            else:
                kind = "and" if expression.func == And else "or"
                children = tuple(nodes[child] for child in expression.args)
                nodes[expression] = (
                    self.intern(Policy(kind, tuple(child[0] for child in children))),
                    1 + sum(child[1] for child in children),
                )
        return nodes[formula]

    def optimize(self, root):
        resolved = {}
        for node in _postorder(root, lambda policy: policy.children):
            children = [resolved[child] for child in node.children]
            if node.kind in {"and", "or"} or (
                node.kind == "thresh" and node.value in {1, len(children)}
            ):
                use_or = node.kind == "or" or (node.kind == "thresh" and node.value == 1)
                combine = Or if use_or else And
                if sum(child[2] for child in children) <= FORMULA_NODE_BUDGET:
                    formula = combine(*(child[1] for child in children))
                    # And and Or already flatten and deduplicate a single gate.
                    if any(not argument.is_Symbol for argument in formula.args):
                        candidate = simplify_logic(formula)
                        # A rewrite that is small in SymPy can duplicate large
                        # thresholds when the opaque symbols are expanded.
                        if self.expanded_size(candidate) <= self.expanded_size(formula):
                            formula = candidate
                else:
                    formula = combine(*(self.atom(child[0]) for child in children))
                policy, size = self.from_formula(formula)
            else:
                # A proper threshold remains one Boolean predicate to its parent.
                # Preserve duplicate child slots because each slot counts.
                policy = self.intern(Policy(node.kind, tuple(child[0] for child in children), node.value))
                formula, size = self.atom(policy), 1
            resolved[node] = policy, formula, size
        return resolved[root]


def miniscript_to_sympy(miniscript):
    """Represent a policy with proper thresholds as opaque Boolean symbols."""
    optimizer = _Optimizer()
    _, formula, _ = optimizer.optimize(_parse_policy(miniscript))
    policies = {symbol: optimizer.symbols[symbol] for symbol in formula.free_symbols}
    bare_names = {policy.value for policy in policies.values() if policy.kind == "symbol"}
    names = {}
    for symbol, policy in policies.items():
        if policy.kind in LEAVES:
            name = f"{policy.kind}.{policy.value}"
            if name in bare_names:
                name = _policy_text(policy)
        else:
            name = _policy_text(policy)
        names[symbol] = Symbol(name)
    return formula.xreplace(names)


def simplify_miniscript(miniscript):
    policy, _, _ = _Optimizer().optimize(_parse_policy(miniscript))
    return _policy_text(policy)


def _policy_json(root):
    values = {}
    for node in _postorder(root, lambda policy: policy.children):
        if node.kind == "symbol":
            values[node] = node.value
        elif node.kind == "thresh":
            values[node] = {
                "thresh": {"num": node.value, "subpolicies": [values[child] for child in node.children]}
            }
        elif node.kind in {"and", "or"}:
            values[node] = {node.kind: [values[child] for child in node.children]}
        else:
            values[node] = {node.kind: [node.value]}
    return values[root]


def miniscript_to_json(miniscript):
    """Parse a policy into the JSON-compatible tree used by the renderer."""
    return _policy_json(_parse_policy(miniscript))


def split_at_commas_outside_parentheses(s):
    components = []
    bracket_level = 0
    current_component = ""
    for char in s:
        if char == ',' and bracket_level == 0:
            components.append(current_component)
            current_component = ""
        else:
            if char == '(':
                bracket_level += 1
            elif char == ')':
                bracket_level -= 1
            current_component += char
    components.append(current_component)  # add the last component
    return components


def merge_or_nodes(node):
    # Base case: if the node is a leaf node (i.e., it has no children), return the node as is
    if not isinstance(node, dict):
        return node

    # Recursive case: first handle the child nodes
    for key in node:
        node[key] = [merge_or_nodes(child) for child in node[key]]

    # If the node is an 'or' node and one of its children is also an 'or' node,
    # merge the node with its child and convert it to a 'thresh' node
    if isinstance(node, type({})):
        if 'or' in node and (any('or' in child for child in node['or']) or
                             any('thresh' in child and child['thresh']['num'] == 1 
                                  for child in node['or'])):
            # Merge the children into a single 'thresh' node
            subpolicies = []
            for child in node['or']:
                if 'or' in child:
                    subpolicies.extend(child['or'])
                elif 'thresh' in child:
                    subpolicies.extend(child['thresh']['subpolicies'])
                else:
                    subpolicies.append(child)
            
            merged_node = {
                'thresh': {
                    'num': 1,
                    'subpolicies': subpolicies
                }
            }
            return merged_node
        
        if 'and' in node and (any('and' in child for child in node['and']) or 
                              any('thresh' in child and child['thresh']['num'] == len(child['thresh']['subpolicies']) 
                                  for child in node['and'])):
            # Merge the children into a single 'thresh' node
            subpolicies = []
            for child in node['and']:
                if 'and' in child:
                    subpolicies.extend(child['and'])
                elif 'thresh' in child:
                    subpolicies.extend(child['thresh']['subpolicies'])
                else:
                    subpolicies.append(child)
            
            merged_node = {
                'thresh': {
                    'num': len(subpolicies),
                    'subpolicies': subpolicies
                }
            }
            return merged_node
  
    elif isinstance(node, list):
        for i, item in enumerate(node):
            node[i] = merge_or_nodes(item)
    return node


def _mermaid_label(value):
    """Encode delimiter and markup characters using Mermaid entities."""
    special = '#"&<>`|\\[]{}()'
    return ''.join(
        f'#{ord(character)};' if character in special or ord(character) < 32 else character
        for character in str(value)
    )


def json_to_mermaid(json_data, parent=None, depth=0, key_counter=None, min_check=1, tot_check=1):
    """Render one policy tree as Mermaid, visiting child slots in input order."""
    counters = {} if key_counter is None else key_counter

    def next_id(prefix):
        counters[prefix] = counters.get(prefix, -1) + 1
        node_id = f'{prefix}_{counters[prefix]}'
        if node_id == parent:
            counters[prefix] += 1
            node_id = f'{prefix}_{counters[prefix]}'
        return node_id

    lines = ['graph TD'] if not depth else []
    policies = json_data if isinstance(json_data, list) and parent is not None else [json_data]
    pending = [(policy, parent) for policy in reversed(policies)]
    root = None
    while pending:
        policy, target = pending.pop()
        if isinstance(policy, str):
            operator, value = None, [policy]
        elif isinstance(policy, dict) and len(policy) == 1:
            operator, value = next(iter(policy.items()))
        else:
            raise ValueError('Expected a policy string or a single-operation object')

        if operator in ('and', 'or', 'thresh'):
            if operator == 'thresh' and (not isinstance(value, dict) or {'num', 'subpolicies'} - value.keys()):
                raise ValueError('Expected a threshold with num and subpolicies')
            children = value['subpolicies'] if operator == 'thresh' else value
            if not isinstance(children, list):
                raise ValueError('Expected gate children as a list')
            required = len(children) if operator == 'and' else 1
            if operator == 'thresh':
                required = value['num']
            if type(required) is not int or not 1 <= required <= len(children):
                raise ValueError('Expected a threshold between 1 and the number of policies')
            gate = next_id(operator)
            lines.append(f'{gate}{{Check {required}/{len(children)}}}')
            if target is None:
                root = gate
            else:
                lines.append(f'{gate} --> {target}')
            pending.extend((child, gate) for child in reversed(children))
            continue

        if operator is not None and operator not in LEAVES:
            raise ValueError(f'Invalid leaf function: {operator}')
        if not isinstance(value, list) or len(value) != 1 or not isinstance(value[0], (str, int)):
            raise ValueError('Expected a single text or integer leaf value')
        if target is None:
            if type(min_check) is not int or type(tot_check) is not int:
                raise ValueError('Expected integer check counts')
            target = root = next_id('check')
            lines.append(f'{target}{{Check {min_check}/{tot_check}}}')
        leaf = next_id('leaf')
        lines.append(f'{leaf}["{_mermaid_label(value[0])}"]')
        edge_label = f'|{_mermaid_label(operator)}|' if operator is not None else ''
        lines.append(f'{leaf} -->{edge_label} {target}')

    if not depth and root is not None:
        lines.extend((f'{root} -->|yes|s((spend))', f'{root} -->|no|n((nothing))'))
    graph = '\n'.join(lines)
    return graph + '\n' if lines and (depth or parent is not None) else graph


def unbalanced_parentheses(source):
    depth = 0
    for character in source:
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth < 0:
                return True
    return depth != 0


def miniscript_to_mermaid(miniscript, simp=True):
    """Render a policy, optionally simplifying its Boolean expressions."""
    policy = _parse_policy(miniscript)
    if simp:
        policy, _, _ = _Optimizer().optimize(policy)
    return json_to_mermaid(_policy_json(policy))


if __name__ == '__main__':
    # Tests
    # miniscript = 'or(pk(key_revocation),or(pk(key_remote),or(pk(key_local),older(1008))))'
    # miniscript = 'or(pk(key_0),or(pk(key_1),or(pk(key_2),or(pk(key_3),pk(key_4)))))' 
    # miniscript = 'thresh(3,pk(key_1),pk(key_2),pk(key_3),older(12960))'
    # miniscript = 'thresh(2,pk(key_1),pk(key_2),and(pk(key_3),older(12960)))'
    miniscript = 'thresh(3,pk(key_revocation),and(pk(key_remote),or(and(pk(key_local),hash160(H)),older(1008))),pk(key_3))'
    # miniscript = 'thresh(3, pk(key_1), pk(key_2), pk(key_3))'
    # miniscript = 'pk(key_revocation)'
    # miniscript = 'or(pk(key_revocation),and(pk(key_local),older(1008)))'
    # miniscript = 'or(or(pk(key_revocation),pk(key_other)),and(pk(key_local),older(1008)))'
    # miniscript = 'or(pk(key_1),or(pk(key_2),or(pk(key_3),or(pk(key_4),or(pk(key_5),or(pk(key_6),or(pk(key_7),pk(key_8))))))))'
    # miniscript = 'or(pk(key_1),or(pk(key_2),or(pk(key_3),or(pk(key_4),or(pk(key_5),or(pk(key_6),or(pk(key_7),or(pk(key_8),or(pk(key_9),pk(key_10))))))))))'
    # miniscript = 'or(pk(key_1),or(pk(key_2),or(pk(key_3),or(pk(key_4),or(pk(key_5),pk(key_6))))))'
    # miniscript = 'thresh(2,pk(key1),pk(key2))'
    # miniscript = 'pk(NAME)'
    # miniscript = 'or(9@pk(key_preferred),pk(key_alternate))'
    # miniscript = 'or(99@pk(regular_key),pk(backup_key))'
    # miniscript = 'or(pk(wife_key),pk(husband_key))'
    # miniscript = 'and(pk(party_1), pk(party_2))'
    # miniscript = 'or(pk(key_revocation),and(pk(key_local),older(1008))'
    # miniscript = 'thresh(1, and(pk(key1),pk(key2)), and(pk(key1),pk(key3)))'
    # miniscript = 'thresh(2, pk(keyA), pk(keyB), or(pk(keyC),after(1081201)))'
    # miniscript = 'multi(2, pk(keyA),pk(keyB),pk(keyC))'
    # miniscript = 'or(and(pk(A),pk(B)),and(pk(A),pk(C)))'
    # miniscript = 'thresh(1,pk(key1),pk(key2))'
    # miniscript = 'thresh(1,pk(key1),pk(key2),pk(key3))'
    # miniscript = 'thresh(4,pk(key1),pk(key2),pk(key3),pk(key4))'
    # miniscript = 'thresh(2,pk(key1),pk(key2),pk(key3))'

    print(miniscript_to_mermaid(miniscript, True))
