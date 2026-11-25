module

public import WordRAM.Model
public import MinCostFlow.Statement.Main
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.Stage0Entry

/-!
# Local narrow-word statement of Theorem 1.1

Defines `NarrowMinCostFlowStatement`: the narrow-word version of `MinCostFlowStatement`
(`MinCostFlow/Statement/Main.lean`) from branch `track/narrow-statement`, using the base-`2 ^ k`
encoding `narrowEncode` and answer predicate `narrowIsCorrectAnswer` from
`MinCostFlow/NarrowProg/Stage0Defs.lean`.

Every definition in `Stage0Defs.lean` (`narrowIntBits`, `narrowEdgeBits`, `narrowBitLength`,
`narrowLimbWidth`, `narrowEdgeWords`, `narrowEncode`, `narrowIsCorrectAnswer`, via `intWords` in
`ReadInt.lean`) agrees word-for-word by unfolding with `intBits`, `Edge.bits`, `Instance.bitLength`,
`Instance.limbWidth`, `Edge.encode`, `Instance.encode`, and `Instance.IsCorrectAnswer` on branch
`track/narrow-statement`.
-/

@[expose] public section

open WordRAM Filter Topology
open MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowTop

/-- **Theorem 1.1 (Min-cost flow, page 2)** in the narrow-word encoding (`track/narrow-statement`):
there are a deterministic program `P`, a word-size constant `c`, a constant `K`, and a function
`ε` tending to `0`, such that on every well-formed instance `I`, `P` halts on `narrowEncode I`
at word size `wordSize c (narrowEncode I)` with a correct answer (`narrowIsCorrectAnswer I out`)
within `timeBound K ε I` steps. -/
def NarrowMinCostFlowStatement : Prop :=
  ∃ (P : Program) (c : ℕ) (K : ℝ) (ε : ℕ → ℝ),
    P.IsDeterministic ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ I : Instance, I.IsValid → ∀ ω, ∃ out cost,
      RunsTo (wordSize c (narrowEncode I)) P (narrowEncode I) ω out cost ∧
        narrowIsCorrectAnswer I out ∧ (cost : ℝ) ≤ timeBound K ε I

end MinCostFlow.NarrowTop
