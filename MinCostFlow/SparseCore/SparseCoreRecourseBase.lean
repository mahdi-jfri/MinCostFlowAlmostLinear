module

public import MinCostFlow.SparseCore.SparseCoreSpannerMetrics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recourse index alignment, `R`-growth, and recourse ratio definitions

Provides the base definitions and alignment lemmas for `SparseCoreRecourse.lean`:
1. `dyn_G_isValid`, `sum_range_eq_sum_Icc_succ`, `sum_range_nat_eq_sum_Icc_succ`,
   `runBatchStepOut_eq_stepOut`, `bucketBatchList_take_flatten_length`,
   `treeRunSeq_R_sdiff_le`, and `treeRunSeq_sum_R_sdiff_eq`.
2. `coreUCRatio`, `coreBucketRecUH`, `coreBucketRecD`, `coreRecoursePerQ`, and positivity bounds.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Validity, index alignment, bucket lengths, and non-cumulative `R` growth -/

lemma dyn_G_isValid {τ : ℕ} {D : DynamicInstance} (hG₀ : (D.G 0).IsValid)
    (hD : D.IsValid τ) : ∀ t ≤ τ, (D.G t).IsValid := by
  intro t ht
  induction t with
  | zero => exact hG₀
  | succ s ih =>
    have hs1 : s + 1 ≤ τ := ht
    have hstep := hD (s + 1) (Nat.succ_pos s) hs1
    simp only [Nat.add_sub_cancel] at hstep
    rw [hstep.2]
    exact applyBatch_isValid (ih (Nat.le_of_succ_le hs1)) hstep.1

lemma sum_range_eq_sum_Icc_succ (f : ℕ → ℝ) (t : ℕ) :
    ∑ s ∈ Finset.range t, f (s + 1) = ∑ s ∈ Finset.Icc 1 t, f s := by
  induction t with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [Finset.sum_range_succ, hIcc, Finset.sum_insert (by simp), ih]
    ring

lemma sum_range_nat_eq_sum_Icc_succ (f : ℕ → ℕ) (t : ℕ) :
    ∑ s ∈ Finset.range t, f (s + 1) = ∑ s ∈ Finset.Icc 1 t, f s := by
  induction t with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [Finset.sum_range_succ, hIcc, Finset.sum_insert (by simp), ih]
    omega

lemma runBatchStepOut_eq_stepOut
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (j : ℕ) (hj : j < k) (C : Finset ℕ) (hC : C ∈ components (D.G 0))
    (b : ℤ) {s : ℕ} (hs : s < τ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let Hb₀ := initBucketGraph (cs₀.compSt C) (D.ℓ 0) b
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
      ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
    DynSpanner.runBatchStepOut Hb₀ (phaseBase (Hb₀.n + splitB) L) (sparsify M) Us_b s =
      (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
        (D.U (s + 1))).stepOut (C, b) := by
  intro cs₀ Hb₀ splitB Us_b
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, _, hStep_full, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hbs := hBase s (Nat.le_of_lt hs)
  have hs1 := (hStep_full (s + 1) (Nat.succ_pos s) hs).2.2.2.1 C hC b
  simp only [Nat.add_sub_cancel] at hs1
  have hget := bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs
  dsimp only [DynSpanner.runBatchStepOut]
  rw [hget]
  change DynSpanner.update
      (DynSpanner.runBatchState Hb₀ (phaseBase (Hb₀.n + splitB) L) (sparsify M) Us_b s)
      ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
        (D.U (s + 1))).U_b (C, b)) (sparsify M) = _
  rw [← (hbs.2.2.2.2.2.2.2.2.2.2.2.2 C hC |>.2.2.2.2 b).2.2.2]
  exact hs1.1.symm

lemma bucketBatchList_take_flatten_length
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (j : ℕ) (C : Finset ℕ) (b : ℤ) {t : ℕ} (ht : t ≤ τ) :
    ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten.length =
      ∑ s ∈ Finset.range t,
        ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
          (D.U (s + 1))).U_b (C, b)).length := by
  induction t with
  | zero => simp
  | succ s ih =>
    have hget := bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b
      (lt_of_lt_of_le (Nat.lt_succ_self s) ht)
    rw [take_succ_of_getElem? hget, List.flatten_append, List.length_append,
      ih (Nat.le_of_succ_le ht), Finset.sum_range_succ]
    simp

lemma treeRunSeq_R_sdiff_le_min
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    ∀ t ≤ τ,
      (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
  intro cs₀ t ht
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hdiff := compLSF_R_diff_le_min oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j t ht
  rw [(hBase t ht).2.2.2.2.2.2.2.1]
  exact hdiff.2.1

lemma treeRunSeq_R_sdiff_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    ∀ t ≤ τ,
      (((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by
  intro cs₀ t ht
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hdiff := compLSF_R_diff_le oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j t ht
  rw [(hBase t ht).2.2.2.2.2.2.2.1]
  exact hdiff.2.1

lemma treeRunSeq_sum_R_sdiff_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    ∀ t ≤ τ,
      (∑ s ∈ Finset.range t,
        ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs.RF.R \
          (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.RF.R).card) =
        ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.RF.R \ cs₀.RF.R).card := by
  intro cs₀ t ht
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  induction t with
  | zero =>
    change 0 = (cs₀.RF.R \ cs₀.RF.R).card
    simp
  | succ s ih =>
    have hs_lt : s < τ := ht
    have hs_le : s ≤ τ := Nat.le_of_succ_le ht
    have hbs := hBase s hs_le
    have hss := hStep s hs_lt
    have hdiff_s := compLSF_R_diff_le oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j s hs_le
    have hsub1 : cs₀.RF.R ⊆ (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.RF.R := by
      rw [hbs.2.2.2.2.2.2.2.1]; exact hdiff_s.1
    have hI_s : CompLSFInv C_lsst (D.ℓ 0) (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs :=
      hbs.2.2.2.2.2.2.2.2.1
    have hsub2 : (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.RF.R ⊆
        (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs.RF.R :=
      (compLSFBatch_decremental hI_s hss.1).2
    have h1 := Finset.card_sdiff_add_card_inter
      (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.RF.R cs₀.RF.R
    have h2 := Finset.card_sdiff_add_card_inter
      (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs.RF.R
      (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.RF.R
    have h3 := Finset.card_sdiff_add_card_inter
      (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs.RF.R cs₀.RF.R
    rw [Finset.inter_eq_right.mpr hsub1] at h1
    rw [Finset.inter_eq_right.mpr hsub2] at h2
    rw [Finset.inter_eq_right.mpr (Finset.Subset.trans hsub1 hsub2)] at h3
    rw [Finset.sum_range_succ, ih hs_le]
    omega

/-! ## 2. Cumulative recourse `∑ |U_S|` and Lemma 2.1 encoding size -/

noncomputable def coreUCRatio (n₀ Δ₀ : ℕ) : ℝ :=
  (Δ₀ : ℝ) + 1 + 56 * (Real.log ((n₀ : ℝ) + 2)) ^ 2

noncomputable def coreBucketRecUH (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) : ℝ :=
  2 + 12 * (L : ℝ) * coreNRoot L m₀ * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀

noncomputable def coreBucketRecD (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) : ℝ :=
  6 * (L : ℝ) * coreNRoot L m₀ * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) *
    coreLambdaS P_b m₀

noncomputable def coreRecoursePerQ (L : ℕ) (P_b : SparsifyParams) (m₀ n₀ Δ₀ B : ℕ) : ℝ :=
  (B : ℝ) * ((3 + 2 * coreE82Len L P_b) * coreBucketRecUH L P_b m₀ +
    2 * coreBucketRecD L P_b m₀) * (2 * coreUCRatio n₀ Δ₀) +
    22 * (B : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b m₀ +
    7 + 224 * (Real.log ((n₀ : ℝ) + 2)) ^ 2

lemma coreUCRatio_pos (n₀ Δ₀ : ℕ) : 0 ≤ coreUCRatio n₀ Δ₀ := by
  unfold coreUCRatio
  have : 0 ≤ Real.log ((n₀ : ℝ) + 2) := (half_lt_log_add_two n₀).le.trans' (by norm_num)
  positivity

lemma coreUCRatio_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (Δ₀ : ℕ) :
    coreUCRatio n₁ Δ₀ ≤ coreUCRatio n₂ Δ₀ := by
  unfold coreUCRatio
  have h1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := (half_lt_log_add_two n₁).le.trans' (by norm_num)
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  linarith

lemma coreLambdaS_pos (P_b : SparsifyParams) (m₀ : ℕ) :
    0 ≤ coreLambdaS P_b m₀ :=
  le_trans zero_le_one (coreLambdaS_ge_one P_b m₀)

lemma coreLambda_ge_one (P_b : SparsifyParams) (m₀ : ℕ) :
    1 ≤ coreLambda P_b m₀ := by
  unfold coreLambda
  refine one_le_pow₀ ?_
  have : (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg this]

lemma coreBucketRec_pos (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) :
    0 ≤ coreBucketRecUH L P_b m₀ ∧ 0 ≤ coreBucketRecD L P_b m₀ ∧
      0 ≤ coreE82Len L P_b := by
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hnr : 0 ≤ coreNRoot L m₀ := by unfold coreNRoot; positivity
  have hlam : 0 ≤ coreLambdaS P_b m₀ := coreLambdaS_pos P_b m₀
  refine ⟨?_, ?_, ?_⟩
  · unfold coreBucketRecUH; positivity
  · unfold coreBucketRecD; positivity
  · unfold coreE82Len; positivity

lemma coreRecoursePerQ_mono_n (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂)
    (Δ₀ B : ℕ) :
    coreRecoursePerQ L P_b m₀ n₁ Δ₀ B ≤ coreRecoursePerQ L P_b m₀ n₂ Δ₀ B := by
  unfold coreRecoursePerQ
  have huc := coreUCRatio_mono h Δ₀
  have h1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := (half_lt_log_add_two n₁).le.trans' (by norm_num)
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  have hcp := coreBucketRec_pos L P_b m₀
  have hc : 0 ≤ (B : ℝ) * ((3 + 2 * coreE82Len L P_b) * coreBucketRecUH L P_b m₀ +
      2 * coreBucketRecD L P_b m₀) := by
    have h1' := hcp.1; have h2' := hcp.2.1; have h3' := hcp.2.2; positivity
  have hmul := mul_le_mul_of_nonneg_left
    (show 2 * coreUCRatio n₁ Δ₀ ≤ 2 * coreUCRatio n₂ Δ₀ by linarith) hc
  linarith


end

end MinCostFlow.SparseCore
