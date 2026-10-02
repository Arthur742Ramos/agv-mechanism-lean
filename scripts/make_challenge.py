"""Generate Challenge.lean by verbatim copy from the AGV library.

Copies the module body (variable line, all definitions, helper theorems)
byte-for-byte from AGV/Defs.lean, so that Lean's variable auto-binding
produces syntactically identical declaration types. Only the four
comparator-selected theorem proofs are replaced with `sorry` placeholders.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THEOREMS = ["agv_efficient", "agv_bic", "agv_budget_balanced", "agv_theorem"]


def statement_sorry(source: str, name: str) -> str:
    match = re.search(r"(?m)^theorem " + re.escape(name) + r"\b[\s\S]*?:=", source)
    assert match, f"Missing theorem statement: {name}"
    return match.group(0) + " by\n  sorry\n"


def render() -> str:
    src = (ROOT / "AGV" / "Defs.lean").read_text()
    namespace = "namespace AGV\n"
    start = src.index(namespace) + len(namespace)
    # Definitions block: everything up to the first comparator theorem.
    stop = src.index("theorem agv_efficient", start)
    definitions = src[start:stop]
    # Ensure the block ends cleanly (after pmf_sum_one's proof) before we
    # append the sorry-theorems.
    definitions = definitions.rstrip() + "\n\n"
    header = """module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
Compact comparison surface for the AGV expected-externality mechanism.
All definitions below are genuine, with their exact library bodies, copied
verbatim (including the variable binders) so that declaration types match
the library syntactically.
Only the four comparator-selected theorem proofs are deliberate statement holes.
The complete, mechanically checked proofs are in the AGV library imported by
Solution. The proofs were developed with AI assistance and then independently
compiled, audited for placeholders and axioms, and comparator-checked; no
separate independent human review of the proofs was performed.
The official comparator checks their exact contracts.
-/

@[expose] public section

open scoped BigOperators NNReal

namespace AGV
"""
    body = header + definitions
    for name in THEOREMS:
        body += statement_sorry(src, name) + "\n"
    body += "end\n\nend AGV\n"
    return body


if __name__ == "__main__":
    (ROOT / "Challenge.lean").write_text(render())
    print("wrote Challenge.lean")
