module

public import MinCostFlow.Chain.Ordered.ShiftLoopLevels

/-!
# The level facts of a chain of the shift loop (`ShiftLoopLevelFacts`)

The machine calls the sparse-core module at the level graphs of a chain. The module meets its
contract at a graph `G` with `G.n ≤ G.m + 1`, at the level sizes `levelM` and at the vertex bound
`N₀` of the configuration. `ShiftLoopLevelFacts` says that a chain has these three facts, and
`shiftLoopLevelFacts_of_inv` gets them from `Chain.Ordered.ShiftLoopChainInv`.

This file imports only `Chain/Ordered/ShiftLoopLevels.lean`. So the loop of `Update` and the select
files can import it. They cannot import `OrdShiftLoopLevels.lean`, since that file imports
`OrdSolverReached.lean`, which imports the loop.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- The facts about a chain of the shift loop that the machine needs to call the sparse-core
module: every level graph has `n ≤ m + 1` (for the init of a level), and the level sizes and the
vertex bound are those of the configuration (the sizes at which the module meets its
contract). -/
@[expose] def ShiftLoopLevelFacts (cfg : Alg2Config) (ch : ChainState cfg.T cfg.P) : Prop :=
  (∀ j ≤ cfg.P.d, (ch.G j).n ≤ (ch.G j).m + 1) ∧ ch.lvlM = levelM cfg.TP cfg.P ∧
    ch.N₀ = cfg.N₀ ∧ (∀ j ≤ cfg.P.d, (ch.G j).m ≤ (ch.G 0).m)

/-- `ShiftLoopChainInv` gives the facts `ShiftLoopLevelFacts`. -/
theorem shiftLoopLevelFacts_of_inv {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {ch : ChainState cfg.T cfg.P} (h : Ordered.ShiftLoopChainInv cfg ch) :
    ShiftLoopLevelFacts cfg ch :=
  ⟨h.levels_n_le hV, h.lvlM_eq, h.N₀_eq, h.levels_m_le hV⟩

end MinCostFlow.MinRatio

end
