module

public import MinCostFlow.Chain.Ordered.Traces
public import MinCostFlow.Chain.Ordered.BudgetHelpers
public import MinCostFlow.Chain.Ordered.ShiftPreserves
public import MinCostFlow.Chain.Ordered.UpdateProofs
public import MinCostFlow.Chain.Ordered.CollapseBounds
public import MinCostFlow.Chain.Ordered.LevelConnected
public import MinCostFlow.Chain.Ordered.Lemma5_11
public import MinCostFlow.Chain.Ordered.Algorithm2Uncond
public import MinCostFlow.Chain.Ordered.HiddenTrace
public import MinCostFlow.Chain.Ordered.HiddenTraceHelpers
public import MinCostFlow.Chain.Ordered.HiddenTraceSteps
public import MinCostFlow.Chain.Ordered.HiddenTraceShift
public import MinCostFlow.Chain.CyclePathRep

/-!
# Shared Imports and Trace Congruence Helper for Ordered Theorem 5.1

Re-exports the ordered chain preservation, collapse, connectedness, Lemma 5.11, Algorithm 2
unconditional, and hidden-trace modules used by `Theorem5_1Helpers` and `Theorem5_1SmallKappa`,
and provides `alg2HiddenTrace_congr` for transferring `Ordered.Alg2HiddenTraceAt` across
updates to non-structural fields.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered.Theorem5_1Deps

open MinCostFlow.Bundle

/-- Transfer ordered `Alg2HiddenTraceAt` across state updates that only touch non-structural fields. -/
def alg2HiddenTrace_congr {σ_cap : ℝ} {cfg : Alg2Config} {D : DynamicInstance}
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st₁ st₂ : Alg2State cfg}
    (tr : Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st₁)
    (hc : st₂.chain = st₁.chain) (hb : st₂.branD = st₁.branD) (hp : st₂.passes = st₁.passes)
    (he2i : st₂.extToInt = st₁.extToInt) (hi2e : st₂.intToExt = st₁.intToExt)
    (hnf : st₂.nextFresh = st₁.nextFresh) :
    Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st₂ := by
  cases st₁
  cases st₂
  dsimp only at hc hb hp he2i hi2e hnf
  subst hc hb hp he2i hi2e hnf
  exact ⟨tr.moves, tr.hmne, tr.initStr, tr.W_game, tr.hv, tr.hf, tr.hPhase, tr.timeOfRound,
    tr.hTimeMono, tr.hTimeEnd, tr.hW_eq, tr.hShiftMatch, tr.hRebMatch, tr.hPassMatch,
    tr.hBranMatch, tr.snapC, tr.snapE2I, tr.snapI2E, tr.snapNF, tr.hSnapEndC, tr.hSnapEndE2I,
    tr.hSnapEndI2E, tr.hSnapEndNF, tr.hSnapFresh, tr.hSnapHolds, tr.reinit, tr.hRebRep,
    tr.hRepRe, tr.hSnapBran, tr.hStrMatch, tr.H, tr.lvlIdx, tr.hLvlReinit, tr.hLvlEnd,
    tr.hLvlMono, tr.hLvlSucc, tr.hLvlSnap, tr.hLvlCore, tr.updRound, tr.hUpdBound, tr.hUpdMono,
    tr.hUpdBand, tr.hLvl0Match, tr.hLvl0NoIns⟩

end MinCostFlow.Chain.Ordered.Theorem5_1Deps
