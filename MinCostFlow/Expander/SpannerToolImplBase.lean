/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Spanner.MGraphSpec
public import MinCostFlow.DynSpanner.Tools
public import MinCostFlow.Expander.ConstructExpanderProg
public import MinCostFlow.Expander.DecomposeProg
public import MinCostFlow.Expander.Section8Static
public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Assembled Word-RAM `SpannerToolImpl` (`Algorithm 4`, page 42)

Assembles `Spanner.SpannerToolImpl` (`MinCostFlow/Spanner/ToolContracts.lean`) from:
- `constructExpanderImpl` (`ConstructExpanderProg.lean`, Theorem 8.4 / Theorem A.1 via `MinCostFlow.ExplicitExpander.explicitExpander`),
- `decomposeImplUsed hDec` (`DecomposeProg.lean`, Theorem 8.5 / Theorem B.1 / Algorithm 5), and
- an arbitrary `pathDS : Spanner.PathDSImpl` (`PathDSContract.lean`, Theorem 8.6, built separately).

Proves determinism (`Stmt.NoRand`), computes the combined word-size multiplier `max 4 pathDS.params.cw`,
establishes cost and parameter agreement lemmas linking `Spanner.spannerTools_of_impl` and
`Spanner.spannerToolCosts_of_impl` to `Section8Static.lean` (`c_deg = 36`, `c_ℓ = 1`,
`K_s = 1 + 36 / Real.log 2`, `p_s = 1`, `p_t = 1`, subpolynomial `decFactor` and `φ_lb⁻¹`),
and provides the parameterized `DynSpanner.SparsifySpec` instantiation matching
`Section8Static.theorem_8_1_concrete`.
-/

namespace MinCostFlow.Expander

open WordRAM

public section

/-! ## 1. Assembly and Component Projections -/

/-- Assembles a full `Spanner.SpannerToolImpl` from `constructExpanderImpl`, `decomposeImplUsed hDec`, and any `pathDS : Spanner.PathDSImpl`. -/
@[expose] noncomputable def spannerToolImpl_of_pathDS
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) : Spanner.SpannerToolImpl where
  constructExpander := constructExpanderImpl
  decompose := decomposeImplUsed hDec
  pathDS := pathDS

@[simp] lemma spannerToolImpl_constructExpander
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (spannerToolImpl_of_pathDS hDec pathDS).constructExpander = constructExpanderImpl := rfl

@[simp] lemma spannerToolImpl_decompose
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (spannerToolImpl_of_pathDS hDec pathDS).decompose = decomposeImplUsed hDec := rfl

@[simp] lemma spannerToolImpl_pathDS
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (spannerToolImpl_of_pathDS hDec pathDS).pathDS = pathDS := rfl

@[simp] lemma spannerTools_of_impl_constructExpander
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).constructExpander =
      Spanner.constructExpanderTool_of_impl constructExpanderImpl := rfl

@[simp] lemma spannerTools_of_impl_decompose
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).decompose =
      Spanner.decomposeTool_of_impl (decomposeImplUsed hDec) := rfl

@[simp] lemma spannerTools_of_impl_pathDS
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).pathDS =
      Spanner.pathDSTool_of_impl pathDS := rfl

@[simp] lemma spannerToolCosts_of_impl_constructExpander
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).constructExpander =
      Spanner.constructExpanderCost_of_impl constructExpanderImpl := rfl

@[simp] lemma spannerToolCosts_of_impl_decompose
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).decompose =
      Spanner.decomposeCost_of_impl (decomposeImplUsed hDec) := rfl

@[simp] lemma spannerToolCosts_of_impl_pathDS
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).pathDS =
      Spanner.pathDSCost_of_impl pathDS := rfl

/-! ## 2. Determinism (`Stmt.NoRand`) -/

theorem spannerToolImpl_constructExpander_noRand
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (b : ℕ) :
    ∀ s ∈ (spannerToolImpl_of_pathDS hDec pathDS).constructExpander.procs b, s.NoRand :=
  constructExpanderImpl_noRand b

theorem spannerToolImpl_decompose_noRand
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (b : ℕ) :
    ∀ s ∈ (spannerToolImpl_of_pathDS hDec pathDS).decompose.procs b, s.NoRand :=
  decomposeImplUsed_noRand hDec b

theorem spannerToolImpl_pathDS_bounds_noRand
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (b : ℕ) :
    ∀ s ∈ (spannerToolImpl_of_pathDS hDec pathDS).pathDS.boundsProcs b, s.NoRand :=
  pathDS.hbounds_noRand b

/-- All procedures of `spannerToolImpl_of_pathDS` are deterministic (`Stmt.NoRand`) whenever
`pathDS.procs` is deterministic. -/
theorem spannerToolImpl_noRand
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl)
    (hPathNoRand : ∀ b, ∀ s ∈ pathDS.procs b, s.NoRand) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    (∀ b, ∀ s ∈ impl.constructExpander.procs b, s.NoRand) ∧
      (∀ b, ∀ s ∈ impl.decompose.procs b, s.NoRand) ∧
      (∀ b, ∀ s ∈ impl.pathDS.boundsProcs b, s.NoRand) ∧
      (∀ b, ∀ s ∈ impl.pathDS.procs b, s.NoRand) :=
  ⟨constructExpanderImpl_noRand, decomposeImplUsed_noRand hDec, pathDS.hbounds_noRand, hPathNoRand⟩

/-! ## 3. Word-Size Multiplier (`cw`) and Parameter Agreements -/

/-- Combined word-size multiplier sufficient to host all three Word RAM tool implementations. -/
@[expose] def spannerToolCombinedCw (impl : Spanner.SpannerToolImpl) : ℕ :=
  max impl.constructExpander.cw (max impl.decompose.cw impl.pathDS.params.cw)

lemma constructExpanderImpl_cw :
    constructExpanderImpl.cw = 4 := rfl

lemma decomposeImpl_cw (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    (decomposeImplUsed hDec).cw = 4 := rfl

lemma spannerToolCombinedCw_eq
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    spannerToolCombinedCw (spannerToolImpl_of_pathDS hDec pathDS) = max 4 pathDS.params.cw := by
  dsimp only [spannerToolCombinedCw, spannerToolImpl_of_pathDS]
  rw [constructExpanderImpl_cw, decomposeImpl_cw hDec, ← max_assoc, max_self]

lemma spannerToolCombinedCw_pos (impl : Spanner.SpannerToolImpl) :
    1 ≤ spannerToolCombinedCw impl :=
  le_trans impl.constructExpander.hcw_pos (le_max_left _ _)

lemma constructExpander_cw_le_combined (impl : Spanner.SpannerToolImpl) :
    impl.constructExpander.cw ≤ spannerToolCombinedCw impl :=
  le_max_left _ _

lemma decompose_cw_le_combined (impl : Spanner.SpannerToolImpl) :
    impl.decompose.cw ≤ spannerToolCombinedCw impl :=
  le_trans (le_max_left _ _) (le_max_right _ _)

lemma pathDS_cw_le_combined (impl : Spanner.SpannerToolImpl) :
    impl.pathDS.params.cw ≤ spannerToolCombinedCw impl :=
  le_trans (le_max_right _ _) (le_max_right _ _)

lemma constructExpanderImpl_c_deg_int :
    constructExpanderImpl.c_deg_int = 18 := rfl

/-- Exact agreement of `c_deg = 36` with `Section8Static.theorem_8_1_concrete`. -/
lemma spannerTools_constructExpander_c_deg
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).constructExpander.c_deg = 36 := by
  dsimp only [Spanner.spannerTools_of_impl, Spanner.constructExpanderTool_of_impl,
    spannerToolImpl_of_pathDS]
  rw [constructExpanderImpl_c_deg_int]
  norm_num

lemma spannerTools_constructExpander_φ_Const
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    let tools := Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)
    0 < tools.constructExpander.φ_Const ∧ tools.constructExpander.φ_Const ≤ 1 := by
  refine ⟨?_, ?_⟩
  · exact (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).constructExpander.hφ_pos
  · exact (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).constructExpander.hφ_le

/-- Exact agreement of `c_ℓ = 1` with `Section8Static.theorem_8_1_concrete`. -/
lemma spannerTools_decompose_c_ℓ
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).decompose.c_ℓ = 1 :=
  decomposeImplUsed_c_ell hDec

lemma decomposeImpl_c_phi (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    (decomposeImplUsed hDec).c_phi = 1 := rfl

lemma decomposeImpl_phi_lb_eq (hDec : ExpanderDecomp.ExpanderDecompositionUsed) (m : ℕ) :
    (decomposeImplUsed hDec).φ_lb m = 1 / ((decomposeImplUsed hDec).maxPhiDen m : ℝ) := rfl

/-- The `DecomposeImpl` lower bound `φ_lb m` has subpolynomial inverse `1 / φ_lb m ≤ C₁ * subpolyB1 C₀ m`. -/
theorem decomposeImpl_phi_lb_subpoly (hDec : ExpanderDecomp.ExpanderDecompositionUsed) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 1 ≤ C₁ ∧ ∀ m : ℕ, 1 / (decomposeImplUsed hDec).φ_lb m ≤ C₁ * subpolyB1 C₀ m := by
  dsimp only [decomposeImplUsed, mkDecomposeImplAux]
  set K := Classical.choose hDec
  set cr := Classical.choose (Classical.choose_spec hDec)
  set K_nat := max 1 ⌈K⌉₊
  set thr := max 200 (thresholdB1 cr)
  have hsub := maxPhiDenOf_le_subpoly K_nat thr
  refine ⟨Classical.choose hsub, max 1 (Classical.choose (Classical.choose_spec hsub)), ?_, le_max_left _ _, fun m => ?_⟩
  · exact (Classical.choose_spec (Classical.choose_spec hsub)).1
  · rw [one_div_one_div]
    have hsb := one_le_subpolyB1 (Classical.choose_spec (Classical.choose_spec hsub)).1.le m
    have hle := (Classical.choose_spec (Classical.choose_spec hsub)).2.2 m
    exact le_trans hle (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

lemma spannerToolCosts_decompose_decFactor_subpoly
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).decompose.decFactor =
        subpolyB1 C₀ :=
  decomposeImplUsed_decFactor_eq hDec

/-! ## 4. Comparison and Agreement with `Section8Static.lean` -/

@[expose] noncomputable def spannerTools_decomposeMonotone
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    Spanner.DecomposeMonotone
      (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).decompose :=
  Spanner.decomposeMonotone_of_impl (decomposeImplUsed hDec)

lemma spannerTools_pathDSMonotone
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) :
    Spanner.PathDSMonotone
      (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS)).pathDS :=
  Spanner.pathDSMonotone_of_impl pathDS

theorem spannerToolImpl_constructExpander_cost_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (n : ℕ) (w : ℕ → ℝ) (hw : ∀ v < n, 1 ≤ w v) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let costs := Spanner.spannerToolCosts_of_impl impl
    ⌈impl.constructExpander.K_ce * (↑n + ↑(List.map (fun v => ⌈w v⌉₊) (List.range n)).sum)⌉₊ ≤
      costs.constructExpander.callCost n (∑ v ∈ Finset.range n, w v) :=
  Spanner.constructExpander_cost_le constructExpanderImpl n w hw

theorem spannerToolImpl_decompose_cost_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) {m : ℕ} (hm : 1 ≤ m) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let costs := Spanner.spannerToolCosts_of_impl impl
    ⌈impl.decompose.K_dec * (↑m * impl.decompose.decFactor m + 1)⌉₊ ≤
      costs.decompose.callCost m :=
  Spanner.decompose_cost_le (decomposeImplUsed hDec) hm

theorem spannerToolImpl_pathDS_init_del_cost_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) {φ_in : ℝ} {M m t : ℕ}
    (hφ : 0 < φ_in) (hm : 1 ≤ m) (ht : t ≤ m) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    ⌈impl.pathDS.params.K_init * ↑m * impl.pathDS.params.γ_ExpPath (Spanner.roundPhi φ_in) M⌉₊ +
        t * ⌈impl.pathDS.params.K_del * impl.pathDS.params.γ_query (Spanner.roundPhi φ_in) M⌉₊ ≤
      costs.pathDS.updateCost m (tools.pathDS.γ_query φ_in M) :=
  Spanner.pathDS_init_del_cost_le pathDS hφ hm ht

theorem spannerToolImpl_pathDS_query_cost_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (φ_in : ℝ) (M : ℕ) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    ⌈impl.pathDS.params.K_query * impl.pathDS.params.γ_query (Spanner.roundPhi φ_in) M⌉₊ ≤
      costs.pathDS.queryCost (tools.pathDS.γ_query φ_in M) :=
  Spanner.pathDS_query_cost_le pathDS φ_in M

/-- Parameter agreement for `sparsifyMGParams` with `Section8Static.theorem_8_1_concrete`:
`K_s = 1 + 36 / Real.log 2`, `p_s = 1`, `p_t = 1`. -/
theorem spannerToolImpl_sparsifyMGParams_agree
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    let P := Spanner.sparsifyMGParams tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax
    P.K_s = 1 + 36 / Real.log 2 ∧ P.p_s = 1 ∧ P.p_t = 1 := by
  dsimp only [Spanner.sparsifyMGParams]
  rw [spannerTools_constructExpander_c_deg, spannerTools_decompose_c_ℓ]
  exact ⟨by ring_nf, rfl, rfl⟩

/-- Parameter agreement for `sparsifyMGParamsWithTime` with `Section8Static.theorem_8_1_concrete_with_time`. -/
theorem spannerToolImpl_sparsifyMGParamsWithTime_agree
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    let P := Spanner.sparsifyMGParamsWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax
    P.K_s = 1 + 36 / Real.log 2 ∧
      P.p_s = 1 ∧
      P.p_t = 1 ∧
      P.γ_t = Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax := by
  dsimp only [Spanner.sparsifyMGParamsWithTime, Spanner.sparsifyMGParams]
  rw [spannerTools_constructExpander_c_deg, spannerTools_decompose_c_ℓ]
  refine ⟨by ring_nf, rfl, rfl, rfl⟩

/-- Parameter agreement for `sparsifyMGParamsOfDec` with `Section8Static.theorem_8_1_concrete`:
`K_s = 1 + 36 / Real.log 2`, `p_s = 1`, `p_t = 1`, and constant `K_t`. -/
theorem spannerToolImpl_sparsifyMGParamsOfDec_agree
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    let P := Spanner.sparsifyMGParamsOfDec tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn
    P.K_s = 1 + 36 / Real.log 2 ∧
      P.p_s = 1 ∧
      P.p_t = 1 ∧
      P.K_t = C_dec * (2 * impl.decompose.K_dec + 1) + Spanner.sparsifyBaseConst 36 costs + 4 := by
  dsimp only [Spanner.sparsifyMGParamsOfDec]
  rw [spannerTools_constructExpander_c_deg, spannerTools_decompose_c_ℓ]
  refine ⟨by ring_nf, rfl, rfl, ?_⟩
  dsimp only [Spanner.spannerToolCosts_of_impl, Spanner.decomposeCost_of_impl, spannerToolImpl_decompose]

/-- Parameter agreement for `sparsifyMGParamsOfDecWithTime` with `Section8Static.theorem_8_1_concrete_with_time`. -/
theorem spannerToolImpl_sparsifyMGParamsOfDecWithTime_agree
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    let P := Spanner.sparsifyMGParamsOfDecWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn
    P.K_s = 1 + 36 / Real.log 2 ∧
      P.p_s = 1 ∧
      P.p_t = 1 ∧
      P.K_t = C_dec * (2 * impl.decompose.K_dec + 1) + Spanner.sparsifyBaseConst 36 costs + 4 ∧
      P.γ_t = Spanner.capGammaQuery 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax := by
  dsimp only [Spanner.sparsifyMGParamsOfDecWithTime, Spanner.sparsifyMGParamsOfDec]
  rw [spannerTools_constructExpander_c_deg, spannerTools_decompose_c_ℓ]
  refine ⟨by ring_nf, rfl, rfl, ?_, rfl⟩
  dsimp only [Spanner.spannerToolCosts_of_impl, Spanner.decomposeCost_of_impl, spannerToolImpl_decompose]

/-- Unconditional time-parametrized `DynSpanner.SparsifySpecWithTime` for `sparsifyMG`
instantiated with `spannerToolImpl_of_pathDS` (covers concrete fallback pruning `γ_query`). -/
theorem spannerToolImpl_sparsifyMG_spec_with_time
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    DynSpanner.SparsifySpecWithTime mMax
      (Spanner.sparsifyMGParamsWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax)
      (Spanner.sparsifyMG tools costs) :=
  Spanner.sparsifyMG_spec_with_time
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (spannerTools_decomposeMonotone hDec pathDS)
    (spannerTools_pathDSMonotone hDec pathDS)
    mMax

/-- Constant-`K_t` `DynSpanner.SparsifySpecWithTime` whenever `decFactor mMax ≤ C_dec * capGammaL^2`. -/
theorem spannerToolImpl_sparsifyMG_spec_of_dec_le_with_time
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec)
    (hdec_le : (decomposeImplUsed hDec).decFactor mMax ≤
      C_dec * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ^ 2) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    DynSpanner.SparsifySpecWithTime mMax
      (Spanner.sparsifyMGParamsOfDecWithTime tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn)
      (Spanner.sparsifyMG tools costs) := by
  apply Spanner.sparsifyMG_spec_of_dec_le_with_time
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (spannerTools_decomposeMonotone hDec pathDS)
    (spannerTools_pathDSMonotone hDec pathDS)
    mMax hC_nn
  dsimp only [Spanner.spannerTools_of_impl, Spanner.spannerToolCosts_of_impl,
    Spanner.constructExpanderTool_of_impl, Spanner.decomposeCost_of_impl,
    spannerTools_decomposeMonotone, Spanner.decomposeMonotone_of_impl,
    spannerToolImpl_of_pathDS]
  rw [constructExpanderImpl_c_deg_int]
  norm_num
  exact hdec_le

/-- `DynSpanner.SparsifySpec` specialization when `γ_query = γ_ExpPath`. -/
theorem spannerToolImpl_sparsifyMG_spec
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ)
    (hγq : ∀ φ M, 0 < φ →
      (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
        (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    DynSpanner.SparsifySpec mMax
      (Spanner.sparsifyMGParams tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax)
      (Spanner.sparsifyMG tools costs) :=
  Spanner.sparsifyMG_spec
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (spannerTools_decomposeMonotone hDec pathDS)
    (spannerTools_pathDSMonotone hDec pathDS)
    mMax hγq

/-- Constant-`K_t` `DynSpanner.SparsifySpec` when `decFactor mMax ≤ C_dec * capGammaL^2`
and `γ_query = γ_ExpPath`. -/
theorem spannerToolImpl_sparsifyMG_spec_of_dec_le
    (hDec : ExpanderDecomp.ExpanderDecompositionUsed)
    (pathDS : Spanner.PathDSImpl) (mMax : ℕ) {C_dec : ℝ} (hC_nn : 0 ≤ C_dec)
    (hdec_le : (decomposeImplUsed hDec).decFactor mMax ≤
      C_dec * Spanner.capGammaL 36 constructExpanderImpl.φ_Const
        (Spanner.pathDSTool_of_impl pathDS) ((decomposeImplUsed hDec).φ_lb mMax) mMax ^ 2)
    (hγq : ∀ φ M, 0 < φ →
      (Spanner.pathDSTool_of_impl pathDS).γ_query φ M =
        (Spanner.pathDSTool_of_impl pathDS).γ_ExpPath φ M) :
    let impl := spannerToolImpl_of_pathDS hDec pathDS
    let tools := Spanner.spannerTools_of_impl impl
    let costs := Spanner.spannerToolCosts_of_impl impl
    let hdec := Spanner.decomposeMonotone_of_impl impl.decompose
    DynSpanner.SparsifySpec mMax
      (Spanner.sparsifyMGParamsOfDec tools costs (hdec.φ_lb mMax) (hdec.hφ_lb_pos mMax) mMax C_dec hC_nn)
      (Spanner.sparsifyMG tools costs) := by
  apply Spanner.sparsifyMG_spec_of_dec_le
    (Spanner.spannerTools_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (Spanner.spannerToolCosts_of_impl (spannerToolImpl_of_pathDS hDec pathDS))
    (spannerTools_decomposeMonotone hDec pathDS)
    (spannerTools_pathDSMonotone hDec pathDS)
    mMax hC_nn _ hγq
  dsimp only [Spanner.spannerTools_of_impl, Spanner.spannerToolCosts_of_impl,
    Spanner.constructExpanderTool_of_impl, Spanner.decomposeCost_of_impl,
    spannerTools_decomposeMonotone, Spanner.decomposeMonotone_of_impl,
    spannerToolImpl_of_pathDS]
  rw [constructExpanderImpl_c_deg_int]
  norm_num
  exact hdec_le


end

end MinCostFlow.Expander
