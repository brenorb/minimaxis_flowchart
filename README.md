# minimaxis_flowchart

🤏🧜‍♀️ Visualize Miniscript policies using Mermaid.

![License](https://img.shields.io/badge/License-MIT-green)

## Setup

From the repository directory, install the dependency into a virtual environment.

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
```

## Usage

```python
from minimermaid import miniscript_to_mermaid

policy = "or(pk(Recovery),thresh(2,pk(Alice),pk(Bob),thresh(2,pk(Carol),pk(Dave),older(1008))))"
print(miniscript_to_mermaid(policy))
```

Pass `simp=False` to keep the input's gate structure and operand order for auditing.
By default, the converter simplifies Boolean expressions, including those inside
nested thresholds. A threshold retains a separate vote for each operand slot,
even when two slots have the same predicate.

The converter accepts the policy functions `and`, `or`, `thresh`, `pk`, `after`,
`older`, `sha256`, `hash256`, `ripemd160`, and `hash160`. Probability weights such
as `9@pk(Alice)` are ignored when drawing the policy. The output is Mermaid graph
source that can be pasted into a Mermaid editor.

## Tests

```sh
python -m unittest discover -s tests -v
```

## Contributing

Pull requests are welcome. For major changes, open an issue first to discuss the proposal.
