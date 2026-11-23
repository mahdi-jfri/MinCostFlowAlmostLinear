module

public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import Mathlib.Tactic

/-!
# The deep-shift spec for a larger tree multiplier (`WireShiftDeepSpecMonoKFBL`)

The deep shift proves `ShiftDeepChainSyncSpecWExtKFBL` at the tree multiplier
`wireTreeSyncEditCost L drainUnit + 2`. The dry run uses one tree multiplier for every body of the
solver, and `Update` needs a larger one (`coreTreeMul` in `DryCoreOpenSizes`). A larger multiplier
only weakens the cost bound of the spec, since the number of tree updates only grows. This file
proves that step.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain Chain.Ordered

/-- The deep-shift spec at a tree multiplier `treeMul` gives the spec at any `treeMul' ≥ treeMul`:
the cost bound has the term `treeMul * Δ totalTreeUpdates`, which only grows. -/
theorem ShiftDeepChainSyncSpecWExtKFBL.mono_treeMul
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    {proc deepSpace deepFixed toolMul treeMul treeMul' : ℕ}
    (h : ShiftDeepChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p proc deepSpace deepFixed
      toolMul treeMul)
    (hle : treeMul ≤ treeMul') :
    ShiftDeepChainSyncSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg Rcore p proc deepSpace deepFixed
      toolMul treeMul' := by
  obtain ⟨body, hbody, hrun⟩ := h
  refine ⟨body, hbody, ?_⟩
  intro root heap pos i ω mem0 mem model tok B R
  dsimp only
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
  obtain ⟨nextHeap, cost, out, tok', c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, c17, c18, c19, c20⟩ :=
    hrun root heap pos i ω mem0 mem model tok B R h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
      h15 h16 h17 h18 h19 h20
  refine ⟨nextHeap, cost, out, tok', c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, c17, c18, c19, c20.trans ?_⟩
  have := Nat.mul_le_mul_right
    ((alg2LoopShiftStep cfg model i).chain.totalTreeUpdates - model.chain.totalTreeUpdates) hle
  omega

end MinCostFlow.MinRatio

end
