module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepReadModel
public import MinCostFlow.SparseCore.Program.AssemblyModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchFacts

import MinCostFlow.SparseCore.BundleRecourseBase
import MinCostFlow.SparseCore.Program.OutEditsValid
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Model bound on the size of P4's LSF change record (`ReadChangeBound`)

Bounds the size `lsfChangeSize cs.lsf (compLSFBatch cs U).lsf` (and hence `c.size` for any
`c : LSFChange` meeting `LSFChange.Exact`) in terms of `lsfBatchSize cs U`, `bundleLogFactor`, and
`branchStepCharge`:

1. **Forest counting (`lsfChange_fDel_le_newRoots`, `lsfChangeSize_le_two_mul_newRoots`).**
   Since `cs.RF` and `(compLSFBatch cs U).RF` are rooted spanning forests of `cs.G` and
   `(compLSFBatch cs U).G = cs.G.applyBatch U`, forest counting gives
   `|R| + |F.E| = |V|` before and after. Because `cs.G.V ⊆ cs'.G.V`, `cs'.RF.F.E ⊆ cs.RF.F.E`,
   and `cs.RF.R ⊆ cs'.RF.R`, the number of removed forest edges is at most the number of new roots:
   `|F.E \ F'.E| ≤ |R' \ R|`, so `lsfChangeSize ≤ 2 · |R' \ R|`.
2. **Component-wise root growth (`compLSF_newRoots_le_lsfBatchSize_real`).**
   Summing `applyLSFBatch_inv_with` over `components cs.G₀` (with untouched components contributing
   `0`) gives `|R' \ R| ≤ 56 · lsfBatchSize cs U · (log (cs.G₀.n + 2))²`, and converting natural
   logarithms to `Nat.log 2` (`real_log_sq_le_nat_log_sq`, using `log 2 ≤ 1`) yields the natural
   number bound `lsfChangeSize ≤ 112 · lsfBatchSize cs U · (⌊log₂ (cs.G₀.n + 2)⌋ + 1)²`.
3. **Branch-layer corollaries.**
   * When `cs.G₀.n ≤ M + N` (which holds on every reached nonempty `SparseCoreOrdInput` state,
     `sparseCoreOrdInput_cs_G₀_n_le`):
     `lsfChangeSize ≤ 112 · lsfBatchSize · bundleLogFactor M N ≤ 112 · branchStepCharge`.
   * Directly from `AsmBrModelFacts impl vCap eCap tr ord` and `vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`
     (with no extra hypothesis on `tr.cs.G₀.n`):
     `lsfChangeSize ≤ 112 · capExp² · lsfBatchSize · bundleLogFactor M N ≤ 112 · capExp² · branchStepCharge`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.Bundle
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-! ## 1. Initial vertex set containment and forest counting -/

/-- Under `CompLSFInv`, every vertex of the initial graph `cs.G₀` remains in `cs.G`. -/
theorem compLSF_G₀_V_subset_G_V {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.G₀.V ⊆ cs.G.V := by
  intro v hv
  have hC : compOf cs.G₀ v ∈ components cs.G₀ := compOf_mem_components hv
  have hvC : v ∈ compOf cs.G₀ v := self_mem_compOf hv
  have hCI := (hI.hCompLSF (compOf cs.G₀ v) hC).1
  have hG₀C := (hI.hCompLSF (compOf cs.G₀ v) hC).2.1
  have hvComp : v ∈ (cs.compSt (compOf cs.G₀ v)).G.V := by
    rw [hCI.hGV_eq, hCI.hTV, hG₀C]
    exact Finset.mem_union_left _ hvC
  rw [← hI.hV_eq]
  exact Finset.mem_biUnion.mpr ⟨compOf cs.G₀ v, hC, hvComp⟩

/-- Under `CompLSFInv`, if every vertex of `cs.G` is below `vCap`, then `cs.G₀.n ≤ vCap`. -/
theorem compLSF_G₀_n_le_vCap {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {vCap : ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hV : ∀ x ∈ cs.G.V, x < vCap) :
    cs.G₀.n ≤ vCap := by
  calc cs.G₀.n = cs.G₀.V.card := rfl
    _ ≤ (Finset.range vCap).card :=
          Finset.card_le_card fun x hx => Finset.mem_range.mpr (hV x (compLSF_G₀_V_subset_G_V hI hx))
    _ = vCap := Finset.card_range vCap

/-- **Forest counting:** the number of forest edges removed by `compLSFBatch` is at most the
number of new roots created. -/
theorem lsfChange_fDel_le_newRoots {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    (cs.RF.F.E \ (compLSFBatch cs U).RF.F.E).card ≤
      ((compLSFBatch cs U).RF.R \ cs.RF.R).card := by
  set cs' := compLSFBatch cs U
  have hI' : CompLSFInv C_lsst ℓ₀ cs' := compLSFBatch_inv hI hU
  have hRS := compLSF_RF_isRSF hI
  have hRS' := compLSF_RF_isRSF hI'
  have hcnt : cs.RF.R.card + cs.RF.F.E.card = cs.G.V.card := by
    rw [← rootedForest_components_card hRS]
    exact forest_components_add_edges cs.RF.F hRS.1
  have hcnt' : cs'.RF.R.card + cs'.RF.F.E.card = cs'.G.V.card := by
    rw [← rootedForest_components_card hRS']
    exact forest_components_add_edges cs'.RF.F hRS'.1
  have hVcard : cs.G.V.card ≤ cs'.G.V.card := by
    refine Finset.card_le_card ?_
    rw [compLSFBatch_G]
    exact V_subset_applyBatch cs.G U
  obtain ⟨hFsub, hRsub⟩ := compLSFBatch_decremental hI hU
  have hFdiff : (cs.RF.F.E \ cs'.RF.F.E).card + cs'.RF.F.E.card = cs.RF.F.E.card := by
    have h := Finset.card_sdiff_add_card_inter cs.RF.F.E cs'.RF.F.E
    rwa [Finset.inter_eq_right.mpr hFsub] at h
  have hRdiff : (cs'.RF.R \ cs.RF.R).card + cs.RF.R.card = cs'.RF.R.card := by
    have h := Finset.card_sdiff_add_card_inter cs'.RF.R cs.RF.R
    rwa [Finset.inter_eq_right.mpr hRsub] at h
  omega

/-- `lsfChangeSize` is at most twice the number of new roots. -/
theorem lsfChangeSize_le_two_mul_newRoots {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    lsfChangeSize cs.lsf (compLSFBatch cs U).lsf ≤
      2 * ((compLSFBatch cs U).RF.R \ cs.RF.R).card := by
  have h := lsfChange_fDel_le_newRoots hI hU
  unfold lsfChangeSize
  change ((compLSFBatch cs U).RF.R \ cs.RF.R).card +
      (cs.RF.F.E \ (compLSFBatch cs U).RF.F.E).card ≤ _
  omega

/-! ## 2. Component-wise root growth against `lsfBatchSize` -/

private theorem sum_projCompBatchG_length_le_lsfBatchSize (cs : CompLSFState) (U : List Update) :
    ((components cs.G₀).sum fun C => (projCompBatchG cs.G (cs.compSt C).G U).length) ≤
      lsfBatchSize cs U := by
  classical
  have hzero : ∀ C ∈ components cs.G₀, C ∉ touchedCompsBatch cs U →
      (projCompBatchG cs.G (cs.compSt C).G U).length = 0 := by
    intro C hC hnt
    have hnil : projCompBatchG cs.G (cs.compSt C).G U = [] := by
      by_contra hne
      exact hnt (Finset.mem_filter.mpr ⟨hC, hne⟩)
    simp [hnil]
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hzero]
  exact Finset.sum_le_sum fun C _ => Nat.le_succ _

/-- Real-valued bound on the number of new roots in terms of `lsfBatchSize` and `log (G₀.n + 2)`. -/
theorem compLSF_newRoots_le_lsfBatchSize_real {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    (((compLSFBatch cs U).RF.R \ cs.RF.R).card : ℝ) ≤
      56 * (lsfBatchSize cs U : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := by
  rw [← bundleRec_sum_comp_R_sdiff_eq hI hU, Nat.cast_sum]
  have hC_le : ∀ C ∈ components cs.G₀,
      ((((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card : ℝ) ≤
        56 * ((projCompBatchG cs.G (cs.compSt C).G U).length : ℝ) *
          (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := by
    intro C hC
    have hsp := compLSFBatch_compSt hI hU hC
    have hB := applyLSFBatch_inv_with (projCompBatchG cs.G (cs.compSt C).G U)
      (hI.hCompLSF C hC).1 hsp.2.2.1
    have hR := hB.2.2.2.2.2.2.2.2.2.2
    rw [← hsp.1, (hI.hCompLSF C hC).2.1] at hR
    have hdiff : (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card +
        (cs.compSt C).R.card = ((compLSFBatch cs U).compSt C).R.card := by
      have h := Finset.card_sdiff_add_card_inter ((compLSFBatch cs U).compSt C).R (cs.compSt C).R
      rwa [Finset.inter_eq_right.mpr hsp.2.2.2.1] at h
    have hdiffR : ((((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card : ℝ) +
        ((cs.compSt C).R.card : ℝ) = (((compLSFBatch cs U).compSt C).R.card : ℝ) := by
      exact_mod_cast hdiff
    have hnC_le : (compGraph cs.G₀ C).n ≤ cs.G₀.n := compGraph_n_le hC
    have hlogC : Real.log (((compGraph cs.G₀ C).n : ℝ) + 2) ≤ Real.log ((cs.G₀.n : ℝ) + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have : ((compGraph cs.G₀ C).n : ℝ) ≤ (cs.G₀.n : ℝ) := by exact_mod_cast hnC_le
      linarith
    have hlogC_nn : 0 ≤ Real.log (((compGraph cs.G₀ C).n : ℝ) + 2) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ ((compGraph cs.G₀ C).n : ℝ) := Nat.cast_nonneg _
      linarith
    have hsq : (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 ≤
        (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := pow_le_pow_left₀ hlogC_nn hlogC 2
    have hm_nn : 0 ≤ 56 * ((projCompBatchG cs.G (cs.compSt C).G U).length : ℝ) := by positivity
    linarith [mul_le_mul_of_nonneg_left hsq hm_nn]
  calc (components cs.G₀).sum (fun C =>
          ((((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card : ℝ))
      ≤ (components cs.G₀).sum (fun C =>
          56 * ((projCompBatchG cs.G (cs.compSt C).G U).length : ℝ) *
            (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2) := Finset.sum_le_sum hC_le
    _ = 56 * ((components cs.G₀).sum fun C =>
          ((projCompBatchG cs.G (cs.compSt C).G U).length : ℝ)) *
          (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ 56 * (lsfBatchSize cs U : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := by
        have hsumR : ((components cs.G₀).sum fun C =>
              ((projCompBatchG cs.G (cs.compSt C).G U).length : ℝ)) ≤
            (lsfBatchSize cs U : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast sum_projCompBatchG_length_le_lsfBatchSize cs U
        have hlog2_nn : 0 ≤ (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := sq_nonneg _
        have h56 : 56 * ((components cs.G₀).sum fun C =>
              ((projCompBatchG cs.G (cs.compSt C).G U).length : ℝ)) ≤
            56 * (lsfBatchSize cs U : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_right h56 hlog2_nn

/-! ## 3. Converting `Real.log` to `Nat.log 2` and `bundleLogFactor` -/

private theorem real_log_two_le_one : Real.log 2 ≤ 1 := by
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) h2e
    _ = 1 := Real.log_exp 1

/-- Natural logarithm is bounded by `⌊log₂ (n + 2)⌋ + 1`. -/
theorem real_log_add_two_le_nat_log (n : ℕ) :
    Real.log ((n : ℝ) + 2) ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := by
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) (n + 2)
  have hle : ((n : ℝ) + 2) ≤ (2 : ℝ) ^ (Nat.log 2 (n + 2) + 1) := by
    exact_mod_cast Nat.le_of_lt hlt
  calc Real.log ((n : ℝ) + 2)
      ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 (n + 2) + 1)) := Real.log_le_log (by positivity) hle
    _ = ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 _
    _ ≤ ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left real_log_two_le_one (Nat.cast_nonneg _)
    _ = ((Nat.log 2 (n + 2) + 1 : ℕ) : ℝ) := mul_one _

/-- Squared natural logarithm is bounded by `(⌊log₂ (n + 2)⌋ + 1)²`. -/
theorem real_log_sq_le_nat_log_sq (n : ℕ) :
    (Real.log ((n : ℝ) + 2)) ^ 2 ≤ (((Nat.log 2 (n + 2) + 1) ^ 2 : ℕ) : ℝ) := by
  have hnn : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h := pow_le_pow_left₀ hnn (real_log_add_two_le_nat_log n) 2
  exact_mod_cast h

/-- If `n + 2 ≤ (M + N + 2) ^ capExp`, then `(log (n + 2))² ≤ capExp² · bundleLogFactor M N`. -/
theorem real_log_sq_le_capExp_mul_bundleLogFactor {n M N capExp : ℕ}
    (h : n + 2 ≤ (M + N + 2) ^ capExp) :
    (Real.log ((n : ℝ) + 2)) ^ 2 ≤ ((capExp ^ 2 * bundleLogFactor M N : ℕ) : ℝ) := by
  have hR : ((n : ℝ) + 2) ≤ (((M + N : ℕ) : ℝ) + 2) ^ capExp := by
    have h1 : ((n + 2 : ℕ) : ℝ) ≤ (((M + N + 2) ^ capExp : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h1 ⊢
    exact h1
  have hnn : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hlog : Real.log ((n : ℝ) + 2) ≤ (capExp : ℝ) * ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) := by
    calc Real.log ((n : ℝ) + 2)
        ≤ Real.log ((((M + N : ℕ) : ℝ) + 2) ^ capExp) := Real.log_le_log (by positivity) hR
      _ = (capExp : ℝ) * Real.log (((M + N : ℕ) : ℝ) + 2) := Real.log_pow _ _
      _ ≤ (capExp : ℝ) * ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left (real_log_add_two_le_nat_log (M + N)) (Nat.cast_nonneg _)
  have hsq := pow_le_pow_left₀ hnn hlog 2
  rw [mul_pow] at hsq
  simpa [bundleLogFactor] using hsq

/-! ## 4. Natural-number bounds on `lsfChangeSize` and `c.size` -/

/-- **General `ℕ` bound on `lsfChangeSize`:**
`lsfChangeSize cs.lsf (compLSFBatch cs U).lsf ≤ 112 · lsfBatchSize cs U · (⌊log₂ (cs.G₀.n + 2)⌋ + 1)²`. -/
theorem lsfChangeSize_le_lsfBatchSize {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    lsfChangeSize cs.lsf (compLSFBatch cs U).lsf ≤
      112 * lsfBatchSize cs U * (Nat.log 2 (cs.G₀.n + 2) + 1) ^ 2 := by
  have hR : ((compLSFBatch cs U).RF.R \ cs.RF.R).card ≤
      56 * lsfBatchSize cs U * (Nat.log 2 (cs.G₀.n + 2) + 1) ^ 2 := by
    have hreal := compLSF_newRoots_le_lsfBatchSize_real hI hU
    have hlog := real_log_sq_le_nat_log_sq cs.G₀.n
    have hcomb : (((compLSFBatch cs U).RF.R \ cs.RF.R).card : ℝ) ≤
        ((56 * lsfBatchSize cs U * (Nat.log 2 (cs.G₀.n + 2) + 1) ^ 2 : ℕ) : ℝ) := by
      have h1 := le_trans hreal (mul_le_mul_of_nonneg_left hlog (by positivity))
      push_cast at h1 ⊢
      exact h1
    exact_mod_cast hcomb
  calc lsfChangeSize cs.lsf (compLSFBatch cs U).lsf
      ≤ 2 * ((compLSFBatch cs U).RF.R \ cs.RF.R).card := lsfChangeSize_le_two_mul_newRoots hI hU
    _ ≤ 2 * (56 * lsfBatchSize cs U * (Nat.log 2 (cs.G₀.n + 2) + 1) ^ 2) :=
        Nat.mul_le_mul_left 2 hR
    _ = 112 * lsfBatchSize cs U * (Nat.log 2 (cs.G₀.n + 2) + 1) ^ 2 := by ring

/-- **Bound with `bundleLogFactor M N` when `cs.G₀.n ≤ M + N`:**
`lsfChangeSize cs.lsf (compLSFBatch cs U).lsf ≤ 112 · lsfBatchSize cs U · bundleLogFactor M N`. -/
theorem lsfChangeSize_le_bundleLogFactor {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} {M N : ℕ} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hn : cs.G₀.n ≤ M + N) :
    lsfChangeSize cs.lsf (compLSFBatch cs U).lsf ≤
      112 * lsfBatchSize cs U * bundleLogFactor M N := by
  have hlog : Nat.log 2 (cs.G₀.n + 2) ≤ Nat.log 2 (M + N + 2) :=
    Nat.log_mono_right (by omega)
  have hsq : (Nat.log 2 (cs.G₀.n + 2) + 1) ^ 2 ≤ bundleLogFactor M N :=
    Nat.pow_le_pow_left (by omega) 2
  exact le_trans (lsfChangeSize_le_lsfBatchSize hI hU) (Nat.mul_le_mul_left _ hsq)

/-- **Bound against `branchStepCharge` when `tr.cs.G₀.n ≤ tr.m₀ + tr.n₀`:**
`lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf ≤ 112 · branchStepCharge sparsify tr U ord ord'`. -/
theorem lsfChangeSize_le_branchStepCharge {L : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState L} {U : List Update} {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hn : tr.cs.G₀.n ≤ tr.m₀ + tr.n₀) :
    lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf ≤
      112 * branchStepCharge sparsify tr U ord ord' := by
  have h1 := lsfChangeSize_le_bundleLogFactor hI hU hn
  have h2 : lsfBatchSize tr.cs U * bundleLogFactor tr.m₀ tr.n₀ ≤
      branchStepCharge sparsify tr U ord ord' := by
    unfold branchStepCharge
    exact Nat.mul_le_mul_right _ (by omega)
  calc lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf
      ≤ 112 * (lsfBatchSize tr.cs U * bundleLogFactor tr.m₀ tr.n₀) := by
        simpa [Nat.mul_assoc] using h1
    _ ≤ 112 * branchStepCharge sparsify tr U ord ord' := Nat.mul_le_mul_left _ h2

/-- **Bound directly from `AsmBrModelFacts` and the cap bound** `vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`:
requires no separate hypothesis on `tr.cs.G₀.n`, matching the exact context of `asmBrFull_step_runs`. -/
theorem lsfChangeSize_le_capExp_lsfBatchSize {depth capExp vCap eCap M N : ℕ}
    {impl : SparsifyImpl} {tr : BundleTreeState depth} {ord : ℕ → List End} {U : List Update}
    (hFacts : AsmBrModelFacts impl vCap eCap tr ord) (hU : tr.cs.G.BatchIsValid U)
    (hcap : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf ≤
      112 * capExp ^ 2 * lsfBatchSize tr.cs U * bundleLogFactor M N := by
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -⟩, -, -, -, -, -, hGV, -⟩ := hFacts
  have hn : tr.cs.G₀.n + 2 ≤ (M + N + 2) ^ capExp := by
    have := compLSF_G₀_n_le_vCap hI hGV; omega
  have hR : ((compLSFBatch tr.cs U).RF.R \ tr.cs.RF.R).card ≤
      56 * capExp ^ 2 * lsfBatchSize tr.cs U * bundleLogFactor M N := by
    have hreal := compLSF_newRoots_le_lsfBatchSize_real hI hU
    have hlog := real_log_sq_le_capExp_mul_bundleLogFactor hn
    have hcomb : (((compLSFBatch tr.cs U).RF.R \ tr.cs.RF.R).card : ℝ) ≤
        ((56 * capExp ^ 2 * lsfBatchSize tr.cs U * bundleLogFactor M N : ℕ) : ℝ) := by
      have h1 := le_trans hreal (mul_le_mul_of_nonneg_left hlog (by positivity))
      push_cast at h1 ⊢
      linarith
    exact_mod_cast hcomb
  calc lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf
      ≤ 2 * ((compLSFBatch tr.cs U).RF.R \ tr.cs.RF.R).card := lsfChangeSize_le_two_mul_newRoots hI hU
    _ ≤ 2 * (56 * capExp ^ 2 * lsfBatchSize tr.cs U * bundleLogFactor M N) :=
        Nat.mul_le_mul_left 2 hR
    _ = 112 * capExp ^ 2 * lsfBatchSize tr.cs U * bundleLogFactor M N := by ring

/-- **Branch-charge bound directly from `AsmBrModelFacts` and `vCap + eCap + 2 ≤ (tr.m₀ + tr.n₀ + 2) ^ capExp`.** -/
theorem lsfChangeSize_le_capExp_branchStepCharge {depth capExp vCap eCap : ℕ}
    {impl : SparsifyImpl}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord ord' : ℕ → List End} {U : List Update}
    (hFacts : AsmBrModelFacts impl vCap eCap tr ord) (hU : tr.cs.G.BatchIsValid U)
    (hcap : vCap + eCap + 2 ≤ (tr.m₀ + tr.n₀ + 2) ^ capExp) :
    lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf ≤
      112 * capExp ^ 2 * branchStepCharge sparsify tr U ord ord' := by
  have h1 := lsfChangeSize_le_capExp_lsfBatchSize hFacts hU hcap
  have h2 : lsfBatchSize tr.cs U * bundleLogFactor tr.m₀ tr.n₀ ≤
      branchStepCharge sparsify tr U ord ord' := by
    unfold branchStepCharge
    exact Nat.mul_le_mul_right _ (by omega)
  calc lsfChangeSize tr.cs.lsf (compLSFBatch tr.cs U).lsf
      ≤ (112 * capExp ^ 2) * (lsfBatchSize tr.cs U * bundleLogFactor tr.m₀ tr.n₀) := by
        simpa [Nat.mul_assoc] using h1
    _ ≤ (112 * capExp ^ 2) * branchStepCharge sparsify tr U ord ord' := Nat.mul_le_mul_left _ h2

/-- Exact-record corollary (`c.size`) of `lsfChangeSize_le_bundleLogFactor`. -/
theorem lsfChange_size_le_bundleLogFactor {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} {c : LSFChange} {M N : ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hc : c.Exact cs.lsf (compLSFBatch cs U).lsf) (hn : cs.G₀.n ≤ M + N) :
    c.size ≤ 112 * lsfBatchSize cs U * bundleLogFactor M N :=
  (lsfChange_size_eq hc).symm ▸ lsfChangeSize_le_bundleLogFactor hI hU hn

/-- Exact-record corollary (`c.size`) of `lsfChangeSize_le_capExp_branchStepCharge`. -/
theorem lsfChange_size_le_capExp_branchStepCharge {depth capExp vCap eCap : ℕ}
    {impl : SparsifyImpl}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {ord ord' : ℕ → List End} {U : List Update} {c : LSFChange}
    (hFacts : AsmBrModelFacts impl vCap eCap tr ord) (hU : tr.cs.G.BatchIsValid U)
    (hc : c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf)
    (hcap : vCap + eCap + 2 ≤ (tr.m₀ + tr.n₀ + 2) ^ capExp) :
    c.size ≤ 112 * capExp ^ 2 * branchStepCharge sparsify tr U ord ord' :=
  (lsfChange_size_eq hc).symm ▸ lsfChangeSize_le_capExp_branchStepCharge sparsify hFacts hU hcap

/-! ## 5. Reached-state guarantee on `SparseCoreOrdInput` -/

/-- On every nonempty state reached by `SparseCoreOrdInput`, every branch has `cs.G₀.n ≤ N`. -/
theorem sparseCoreOrdInput_cs_G₀_n_le {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ} {k M N : ℕ}
    {st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hIn : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N st G ord n) :
    SparseCoreBundleState.isNonempty (L := L) st = true →
      ∀ j, (SparseCoreBundleState.trees (L := L) st j).cs.G₀.n ≤ N := by
  induction hIn with
  | init G₀ _ _ _ _ _ hn _ _ =>
    intro _ _
    exact hn
  | @update s₀ _ _ _ _ U _ _ ord' _ _ _ _ ih =>
    intro hne j
    by_cases hs : s₀.isNonempty = true
    · rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst s₀ hs]
      change (compLSFBatch (s₀.trees j).cs U).G₀.n ≤ N
      rw [compLSFBatch_G₀]
      exact ih hs j
    · have hsF : s₀.isNonempty = false := Bool.eq_false_iff.mpr hs
      rw [asm_updateOrd_of_empty lsfInit C_lsst L sparsify params spanConst s₀ hsF] at hne
      exact absurd hne hs
  | @restart s₀ _ _ _ _ j₀ _ ih =>
    have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst L sparsify s₀ j₀
    have key : ∀ x : SparseCoreBundleState L, x =
        (if s₀.isNonempty = true then
          { isNonempty := s₀.isNonempty, k := s₀.k, ord := s₀.ord,
            trees := Function.update s₀.trees j₀
              (restartBundleTree L sparsify (s₀.trees j₀) s₀.ord) }
        else s₀) →
        x.isNonempty = true → ∀ j, (x.trees j).cs.G₀.n ≤ N := by
      intro x hx hne j
      subst hx
      by_cases hs : s₀.isNonempty = true
      · simp only [hs, ↓reduceIte]
        by_cases hjj : j = j₀
        · subst hjj
          simp only [Function.update_self]
          exact ih hs j
        · simp only [Function.update_of_ne hjj]
          exact ih hs j
      · simp only [hs] at hne
        exact absurd hne hs
    exact key _ hR

/-- **Reached-state model bound on P4's change record (`c.size`):**
on every nonempty state reached by `SparseCoreOrdInput`, for any branch `j` satisfying
`CompLSFInv`, any valid batch `U`, and any exact change record `c : LSFChange`:
`c.size ≤ 112 · lsfBatchSize (st.trees j).cs U · bundleLogFactor M N` and
`c.size ≤ 112 · branchStepCharge sparsify (st.trees j) U st.ord ord'`. -/
theorem sparseCoreOrdInput_lsfChange_size_le {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ} {k M N : ℕ}
    {st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord ord' : ℕ → List End} {n : ℕ}
    (hIn : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N st G ord n)
    (hne : SparseCoreBundleState.isNonempty (L := L) st = true)
    (j : ℕ) {ℓ₀ : ℕ → ℝ}
    (hI : CompLSFInv C_lsst ℓ₀ (SparseCoreBundleState.trees (L := L) st j).cs)
    {U : List Update} (hU : (SparseCoreBundleState.trees (L := L) st j).cs.G.BatchIsValid U)
    {c : LSFChange}
    (hc : c.Exact (SparseCoreBundleState.trees (L := L) st j).cs.lsf
      (compLSFBatch (SparseCoreBundleState.trees (L := L) st j).cs U).lsf) :
    c.size ≤ 112 * lsfBatchSize (SparseCoreBundleState.trees (L := L) st j).cs U *
        bundleLogFactor M N ∧
      c.size ≤ 112 * branchStepCharge sparsify (SparseCoreBundleState.trees (L := L) st j) U
        (SparseCoreBundleState.ord (L := L) st) ord' := by
  have hn : (SparseCoreBundleState.trees (L := L) st j).cs.G₀.n ≤ M + N :=
    le_trans (sparseCoreOrdInput_cs_G₀_n_le hIn hne j) (Nat.le_add_left N M)
  have hmn := (asm_input_inv lsfInit C_lsst L sparsify params spanConst hIn).2.2 j
  refine ⟨lsfChange_size_le_bundleLogFactor hI hU hc hn, ?_⟩
  rw [lsfChange_size_eq hc]
  exact lsfChangeSize_le_branchStepCharge sparsify hI hU (by rw [hmn.1, hmn.2.1]; exact hn)

end MinCostFlow.SparseCore.Program.Read
