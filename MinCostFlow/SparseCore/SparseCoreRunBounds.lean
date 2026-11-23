module

public import MinCostFlow.SparseCore.SparseCoreMetrics

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spanner parameter abbreviations and unconditional run bounds for `sparseCoreTool`

Defines `coreE82Len`, `coreE82Cong`, `coreE_L`, `coreSplitMax`, `coreNMax`, `coreNRoot`,
`coreLambdaS`, `coreLambda`, initialization bucket-graph bounds, quotient-lifting `qToR`,
and the unconditional trajectory bounds `compLSF_R_diff_le`, `compLSF_crossEdges_run_le`,
and `extraSet_and_tildeV_run_le`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Parameter abbreviations and initialization bounds -/

noncomputable def coreE82Len (L : ℕ) (P_b : SparsifyParams) : ℝ :=
  (3 : ℝ) ^ L * P_b.γ_ℓ ^ (L + 1)

noncomputable def coreE82Cong (L : ℕ) (P_b : SparsifyParams) : ℝ :=
  (3 : ℝ) ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1)

noncomputable def coreE_L (L : ℕ) (P_b : SparsifyParams) : ℝ :=
  (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
    P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)

def coreSplitMax (m₀ : ℕ) : ℕ :=
  m₀ * (2 * m₀ + 1) + 56 * m₀

def coreNMax (m₀ : ℕ) : ℕ :=
  2 * m₀ + coreSplitMax m₀

noncomputable def coreNRoot (L m₀ : ℕ) : ℝ :=
  ((max (coreNMax m₀) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))

noncomputable def coreLambdaS (P_b : SparsifyParams) (m₀ : ℕ) : ℝ :=
  (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ P_b.p_s

lemma coreLambdaS_ge_one (P_b : SparsifyParams) (m₀ : ℕ) :
    1 ≤ coreLambdaS P_b m₀ := by
  unfold coreLambdaS
  refine one_le_pow₀ ?_
  have : (1 : ℝ) ≤ (coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg this]

noncomputable def coreLambda (P_b : SparsifyParams) (m₀ : ℕ) : ℝ :=
  (1 + Real.log ((coreNMax m₀ : ℝ) + (m₀ : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)

lemma splitB_le_coreSplitMax_at {k M N : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N)
    {G₀ : MGraph} (hM : G₀.m ≤ M) :
    Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ coreSplitMax M := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hfl : Nat.floor (SparseCoreTool.updateThreshold k M N) ≤ M := by
    refine Nat.floor_le_of_le ?_
    have hlog3 : (21 / 20 : ℝ) < Real.log (N + 2 : ℝ) :=
      lt_of_lt_of_le real_log_three_gt (Real.log_le_log (by norm_num)
        (by linarith [show (1 : ℝ) ≤ N from by exact_mod_cast hN]))
    have hlog2 : (1 : ℝ) ≤ (Real.log (N + 2 : ℝ)) ^ 2 := by nlinarith
    rw [SparseCoreTool.updateThreshold]
    exact div_le_self (Nat.cast_nonneg _) (by nlinarith)
  have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M := by
    refine Nat.ceil_le.mpr ?_
    exact div_le_self (by positivity) hk1 |>.trans (by norm_cast)
  have hdeg : G₀.maxDeg ≤ 2 * M := le_trans (maxDeg_le_two_m G₀) (Nat.mul_le_mul_left 2 hM)
  unfold coreSplitMax
  exact Nat.add_le_add (Nat.mul_le_mul hfl (by omega)) hceil

lemma splitB_le_coreSplitMax {k : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) :
    Nat.floor (SparseCoreTool.updateThreshold k G₀.m G₀.n) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (G₀.m : ℝ) / (k : ℝ)) ≤ coreSplitMax G₀.m := by
  by_cases hm₀ : G₀.m = 0
  · rw [hm₀, SparseCoreTool.updateThreshold]; simp [coreSplitMax]
  · obtain ⟨e₀, he₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hm₀)
    have hn₀ : 1 ≤ G₀.n := Finset.card_pos.mpr ⟨G₀.tail e₀, (hG₀ e₀ he₀).1⟩
    exact splitB_le_coreSplitMax_at hk hn₀ le_rfl

lemma sum_initBucketGraph_le {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh K_σ ℓ₀ S₀)
    (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    let ts₀ := initTildeState S₀
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen S₀.lsf ℓ₀ e)
    let actB := ts₀.C.E.image origB
    actB.card ≤ S₀.G.m ∧
    (actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).m) ≤ S₀.G.m ∧
    (actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).n) ≤ 2 * S₀.G.m := by
  intro ts₀ origB actB
  have hT₀ := initTildeState_inv hI₀ hCov₀
  have hHb := initBucketGraph_spec hI₀ hCov₀
  have hCE_sub_G : ts₀.C.E ⊆ S₀.G.E :=
    Finset.Subset.trans hT₀.hCE_sub Finset.sdiff_subset
  have hact_le : actB.card ≤ S₀.G.m :=
    le_trans Finset.card_image_le (Finset.card_le_card hCE_sub_G)
  have hdisj : Set.PairwiseDisjoint (↑actB : Set ℤ) (fun b => (initBucketGraph S₀ ℓ₀ b).E) := by
    intro b₁ _ b₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he1 he2
    exact hne (((hHb b₁).2.2.2.1 e he1).symm.trans ((hHb b₂).2.2.2.1 e he2))
  have hm_sum : (actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).m) ≤ S₀.G.m := by
    have heq : (actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).m) =
        (actB.biUnion fun b => (initBucketGraph S₀ ℓ₀ b).E).card := by
      rw [Finset.card_biUnion hdisj]
      rfl
    rw [heq]
    refine Finset.card_le_card (Finset.biUnion_subset.mpr fun b _ => ?_)
    exact Finset.Subset.trans ((hHb b).2.1.2.1) hCE_sub_G
  have hn_sum : (actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).n) ≤ 2 * S₀.G.m := by
    calc (actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).n)
        ≤ actB.sum fun b => 2 * (initBucketGraph S₀ ℓ₀ b).m :=
          Finset.sum_le_sum fun b _ => (hHb b).2.2.2.2.1
      _ = 2 * actB.sum fun b => (initBucketGraph S₀ ℓ₀ b).m := by rw [← Finset.mul_sum]
      _ ≤ 2 * S₀.G.m := Nat.mul_le_mul_left 2 hm_sum
  exact ⟨hact_le, hm_sum, hn_sum⟩

noncomputable def qToR (S : LSFState) (ts : TildeState) (u : ℕ) : ℕ :=
  open Classical in
  if h : ∃ x ∈ S.G.V, ts.m x = u then S.RF.root h.choose else u

lemma qToR_eq_root {S₀ S : LSFState} {ts : TildeState} (hT : TildeInv S₀ S ts)
    {x : ℕ} (hx : x ∈ S.G.V) : qToR S ts (ts.m x) = S.RF.root x := by
  classical
  have h : ∃ y ∈ S.G.V, ts.m y = ts.m x := ⟨x, hx, rfl⟩
  simp only [qToR, h, ↓reduceDIte]
  have hspec := h.choose_spec
  have hrpi := (hT.hRPI h.choose hspec.1 x hx).mp hspec.2
  rcases hrpi with hEq | ⟨_, _, hrt, _⟩
  · rw [hEq]
  · exact hrt

/-! ## 2. Unconditional root, cross-edge, extra-edge, and active-vertex run bounds -/

lemma compLSF_R_diff_le_min_with
    (lsfInit : LSFInit) {C_lsst : ℝ}
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < ℓ₀ e) (hD : D.IsValid τ)
    (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let cs₀ := initCompLSFWith lsfInit (D.G 0) ℓ₀ k j
    ∀ t ≤ τ,
      let cs := compLSFBatch cs₀ (dynBatches D t).flatten
      cs₀.RF.R ⊆ cs.RF.R ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) := by
  intro cs₀ t ht cs
  have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hba := applyBatch_dynBatches hD t ht
  have hBV : cs₀.G.BatchIsValid (dynBatches D t).flatten :=
    (batchIsValid_flatten (D.G 0) (dynBatches D t)).mpr hba.2
  have hsp := compLSFBatch_step_props (dynBatches D t).flatten hI₀ hBV
  have hsub : cs₀.RF.R ⊆ cs.RF.R := hsp.2.2.2.2
  have hsum := compLSF_R_sum_le_min hI₀ hBV
  have hfl : (dynBatches D t).flatten.length = ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
    rw [← totalUpdates_dynBatches D t, MinCostFlow.LSF.totalUpdates, List.length_flatten]
  have hcard : ((cs.RF.R \ cs₀.RF.R).card : ℝ) = (cs.RF.R.card : ℝ) - (cs₀.RF.R.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub]
    exact_mod_cast Nat.cast_sub (Finset.card_le_card hsub)
  have hb1 : ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
      112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
    change (cs.RF.R.card : ℝ) ≤ (cs₀.RF.R.card : ℝ) +
      56 * ((2 * (dynBatches D t).flatten.length : ℕ) : ℝ) *
        (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 at hsum
    rw [hfl] at hsum
    have h2 : ((2 * ∑ s ∈ Finset.Icc 1 t, (D.U s).length : ℕ) : ℝ) =
        2 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [h2] at hsum
    linarith
  have hlog_min_le : (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
      (Real.log ((N : ℝ) + 2)) ^ 2 := by
    have hnn : 0 ≤ Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2) := by
      linarith [half_lt_log_add_two (min (D.G 0).n ((D.G 0).m + 1))]
    refine pow_le_pow_left₀ hnn (Real.log_le_log (by positivity) ?_) 2
    have : ((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (min_le_left _ _) hN
    linarith
  have hsub_icc : Finset.Icc 1 t ⊆ Finset.Icc 1 τ := fun s hs => by
    simp only [Finset.mem_Icc] at hs ⊢; exact ⟨hs.1, le_trans hs.2 ht⟩
  have hq_le : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N :=
    le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hsub_icc) hThresh
  have hlog2_nn : 0 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := sq_nonneg _
  have hmul : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log ((N : ℝ) + 2)) ^ 2 ≤ (M : ℝ) / (k : ℝ) := by
    by_cases hlog0 : (Real.log ((N : ℝ) + 2)) ^ 2 = 0
    · rw [hlog0, mul_zero]; positivity
    · have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hlog_pos : 0 < (Real.log ((N : ℝ) + 2)) ^ 2 :=
        lt_of_le_of_ne hlog2_nn (Ne.symm hlog0)
      rw [SparseCoreTool.updateThreshold, ← div_div] at hq_le
      exact (le_div_iff₀ hlog_pos).mp hq_le
  have hmul' : 112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
        (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
      112 * (M : ℝ) / (k : ℝ) := by
    have h1 : 112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log ((N : ℝ) + 2)) ^ 2 :=
      mul_le_mul_of_nonneg_left hlog_min_le (by positivity)
    calc 112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2
        ≤ 112 * ((((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
            (Real.log ((N : ℝ) + 2)) ^ 2) := by linarith
      _ ≤ 112 * ((M : ℝ) / (k : ℝ)) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = 112 * (M : ℝ) / (k : ℝ) := by ring
  exact ⟨hsub, hb1, le_trans hb1 hmul'⟩

lemma compLSF_R_diff_le_min
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < ℓ₀ e) (hD : D.IsValid τ)
    (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) ℓ₀ k j
    ∀ t ≤ τ,
      let cs := compLSFBatch cs₀ (dynBatches D t).flatten
      cs₀.RF.R ⊆ cs.RF.R ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) :=
  compLSF_R_diff_le_min_with (initLSFOnline oracle C_lsst) hk hG₀ hV₀ hℓ₀ hD hN hThresh
    (initLSFOnline_isValidLSFInitFor hLSST k j)

lemma compLSF_R_diff_le_with
    (lsfInit : LSFInit) {C_lsst : ℝ}
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < ℓ₀ e) (hD : D.IsValid τ)
    (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let cs₀ := initCompLSFWith lsfInit (D.G 0) ℓ₀ k j
    ∀ t ≤ τ,
      let cs := compLSFBatch cs₀ (dynBatches D t).flatten
      cs₀.RF.R ⊆ cs.RF.R ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) := by
  intro cs₀ t ht cs
  obtain ⟨hsub, hb1, hb2⟩ := compLSF_R_diff_le_min_with lsfInit hk hG₀ hV₀ hℓ₀ hD hN hThresh hInit t ht
  have hlog_min_le : (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
      (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by
    have hnn : 0 ≤ Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2) := by
      linarith [half_lt_log_add_two (min (D.G 0).n ((D.G 0).m + 1))]
    refine pow_le_pow_left₀ hnn (Real.log_le_log (by positivity) ?_) 2
    have : ((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) ≤ (D.G 0).n := by exact_mod_cast min_le_left _ _
    linarith
  exact ⟨hsub, le_trans hb1 (mul_le_mul_of_nonneg_left hlog_min_le (by positivity)), hb2⟩

lemma compLSF_R_diff_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < ℓ₀ e) (hD : D.IsValid τ)
    (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) ℓ₀ k j
    ∀ t ≤ τ,
      let cs := compLSFBatch cs₀ (dynBatches D t).flatten
      cs₀.RF.R ⊆ cs.RF.R ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤
        112 * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ∧
      ((cs.RF.R \ cs₀.RF.R).card : ℝ) ≤ 112 * (M : ℝ) / (k : ℝ) :=
  compLSF_R_diff_le_with (initLSFOnline oracle C_lsst) hk hG₀ hV₀ hℓ₀ hD hN hThresh
    (initLSFOnline_isValidLSFInitFor hLSST k j)

lemma compLSF_crossEdges_run_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (j : ℕ) :
    ∀ t : ℕ, (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.crossEdges.card ≤
      ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
  intro t
  induction t with
  | zero =>
    have h0 : (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.cs.crossEdges = ∅ := rfl
    rw [h0, Finset.card_empty]
    simp
  | succ s ih =>
    set st_s := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
    have hcs1 : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs =
        compLSFBatch st_s.cs (D.U (s + 1)) := rfl
    have hsub : (compLSFBatch st_s.cs (D.U (s + 1))).crossEdges ⊆
        st_s.cs.crossEdges ∪ ((compLSFBatch st_s.cs (D.U (s + 1))).crossEdges \ st_s.cs.crossEdges) :=
      fun e he => by
        by_cases h : e ∈ st_s.cs.crossEdges
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, h⟩)
    have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h2 := compLSF_crossEdges_sdiff_cur (D.U (s + 1)) st_s.cs
    have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
      ext x; simp [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    rw [hcs1]
    omega

lemma extraSet_and_tildeV_run_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let G₀ := D.G 0
    let cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    ∀ t ≤ τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      ((components G₀).sum fun C => (extraSet (st.cs.compSt C) (st.ts C)).card) ≤
        2 * (∑ s ∈ Finset.Icc 1 t, (D.U s).length) + (st.cs.RF.R \ cs₀.RF.R).card ∧
      ((components G₀).sum fun C => ((st.ts C).C.V.card - (ts₀ C).C.V.card)) ≤
        2 * (∑ s ∈ Finset.Icc 1 t, (D.U s).length) * (G₀.maxDeg + 1) + (st.cs.RF.R \ cs₀.RF.R).card ∧
      ∀ C ∈ components G₀, (ts₀ C).C.V.card ≤ (st.ts C).C.V.card := by
  intro G₀ cs₀ ts₀ t ht
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀_spec : ∀ C ∈ components G₀,
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀_spec C hC).2
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hR_sub : ∀ s ≤ τ, cs₀.RF.R ⊆ (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.RF.R := by
    intro s hs
    have hcs := (hBase s hs).2.2.2.2.2.2.2.1
    rw [hcs]
    exact (compLSF_R_diff_le oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j s hs).1
  induction t with
  | zero =>
    have hcs0 : (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.cs = cs₀ := rfl
    have hts0 : (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.ts = ts₀ := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hcs0, hts0]
      simp [ts₀, extraSet_init]
    · rw [hts0]; simp
    · intro C _; rw [hts0]
  | succ s ih =>
    have hs_le : s ≤ τ := Nat.le_of_succ_le ht
    have hs_lt : s < τ := ht
    obtain ⟨ih_ex, ih_v, ih_mono⟩ := ih hs_le
    set st_s := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
    set st_s1 := (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1
    have hbs := hBase s hs_le
    have hss := hStep s hs_lt
    have hI_s := hbs.2.2.2.2.2.2.2.2.1
    have hG₀_s : st_s.cs.G₀ = G₀ := by rw [hbs.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hcs1_eq : st_s1.cs = compLSFBatch st_s.cs (D.U (s + 1)) := rfl
    have hI_s1 := (hBase (s + 1) ht).2.2.2.2.2.2.2.2.1
    have hsp_cs := compLSFBatch_step_props (D.U (s + 1)) hI_s hss.1
    have hex_C : ∀ C ∈ components G₀,
        (extraSet (st_s1.cs.compSt C) (st_s1.ts C)).card ≤
          (extraSet (st_s.cs.compSt C) (st_s.ts C)).card +
            projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) +
            ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card := by
      intro C hC
      have hspC := hsp_cs.2.2.1 C (hG₀_s ▸ hC)
      have hC_s := hbs.2.2.2.2.2.2.2.2.2.2.2.2 C hC
      have htw := tildeStepBatch_projCompBatchG_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
        (D.U (s + 1)) hI_s (hG₀_s ▸ hC) hC_s.1 hC_s.2.1 hss.1
      have htd := tildeStepBatch_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
        (hI_s.hCompLSF C (hG₀_s ▸ hC)).1 hC_s.1 hC_s.2.1 hspC.2.2.1
      dsimp only at htw
      rw [htd.1] at htw
      have hcsC : st_s1.cs.compSt C =
          applyLSFBatch (st_s.cs.compSt C) (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1))) := by
        rw [hcs1_eq]; exact hspC.1
      have htsC : st_s1.ts C =
          (tildeStepBatch (st_s.cs.compSt C) (st_s.ts C)
            (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))).2.1 := rfl
      rw [← hcsC, ← htsC] at htw
      have hsub_u : extraSet (st_s1.cs.compSt C) (st_s1.ts C) ⊆
          extraSet (st_s.cs.compSt C) (st_s.ts C) ∪
            (extraSet (st_s1.cs.compSt C) (st_s1.ts C) \ extraSet (st_s.cs.compSt C) (st_s.ts C)) :=
        fun e he => by
          by_cases h : e ∈ extraSet (st_s.cs.compSt C) (st_s.ts C)
          · exact Finset.mem_union_left _ h
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, h⟩)
      have hcu := le_trans (Finset.card_le_card hsub_u) (Finset.card_union_le _ _)
      exact le_trans hcu (by linarith [htw.2.2.1])
    have hv_C : ∀ C ∈ components G₀,
        (st_s1.ts C).C.V.card - (ts₀ C).C.V.card ≤
          ((st_s.ts C).C.V.card - (ts₀ C).C.V.card) +
            projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) * (G₀.maxDeg + 1) +
            ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card ∧
        (ts₀ C).C.V.card ≤ (st_s1.ts C).C.V.card := by
      intro C hC
      have hspC := hsp_cs.2.2.1 C (hG₀_s ▸ hC)
      have hC_s := hbs.2.2.2.2.2.2.2.2.2.2.2.2 C hC
      have htd := tildeStepBatch_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
        (hI_s.hCompLSF C (hG₀_s ▸ hC)).1 hC_s.1 hC_s.2.1 hspC.2.2.1
      have htw := tildeStepBatch_projCompBatchG_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
        (D.U (s + 1)) hI_s (hG₀_s ▸ hC) hC_s.1 hC_s.2.1 hss.1
      have htsC : st_s1.ts C =
          (tildeStepBatch (st_s.cs.compSt C) (st_s.ts C)
            (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))).2.1 := rfl
      have hcsC : st_s1.cs.compSt C =
          applyLSFBatch (st_s.cs.compSt C) (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1))) := by
        rw [hcs1_eq]; exact hspC.1
      have hdeg_le : (cs₀.compSt C).G.maxDeg ≤ G₀.maxDeg := by
        rw [(hS₀_spec C hC).1]
        exact compGraph_maxDeg_le hC
      have hlen_v : (st_s1.ts C).C.V.card =
          (st_s.ts C).C.V.card +
            batchSplitCount (tildeStepBatch (st_s.cs.compSt C) (st_s.ts C)
              (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))).1 := by
        rw [htsC]; exact htd.2.2.2.2.2.2.2.2.2.2.2
      have hsc_le : batchSplitCount (tildeStepBatch (st_s.cs.compSt C) (st_s.ts C)
            (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))).1 ≤
          projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) *
            ((cs₀.compSt C).G.maxDeg + 1) +
            ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card := by
        have h1 := htw.1
        rw [htd.1, ← hcsC] at h1
        exact h1
      have hmul_deg := Nat.mul_le_mul_left
        (projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))
        (Nat.add_le_add_right hdeg_le 1)
      have hmo := ih_mono C hC
      have hge1 : (ts₀ C).C.V.card ≤ (st_s1.ts C).C.V.card := by omega
      have hstep : (st_s1.ts C).C.V.card ≤ (st_s.ts C).C.V.card +
          projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) * (G₀.maxDeg + 1) +
          ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card := by
        omega
      exact ⟨by omega, hge1⟩
    have hsum_proj : ((components G₀).sum fun C =>
        projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1))) ≤
        2 * (D.U (s + 1)).length := by
      rw [← hG₀_s]
      exact sum_projCompBatchWeight_le (D.U (s + 1)) hI_s hss.1
    have hsum_R : ((components G₀).sum fun C =>
        ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card) =
        (st_s1.cs.RF.R \ st_s.cs.RF.R).card := by
      have hR_m : ∀ C ∈ components st_s.cs.G₀, (st_s.cs.compSt C).R ⊆ (st_s1.cs.compSt C).R :=
        fun C hC => (hsp_cs.2.2.1 C hC).2.2.2.1
      rw [← hG₀_s]
      exact compLSF_sum_R_sdiff_eq hI_s hI_s1 (by rw [hcs1_eq, compLSFBatch_G₀]) hR_m
    have hR_tel : (st_s.cs.RF.R \ cs₀.RF.R).card + (st_s1.cs.RF.R \ st_s.cs.RF.R).card =
        (st_s1.cs.RF.R \ cs₀.RF.R).card := by
      have h1 : cs₀.RF.R ⊆ st_s.cs.RF.R := hR_sub s hs_le
      have h2 : st_s.cs.RF.R ⊆ st_s1.cs.RF.R := by rw [hcs1_eq]; exact hsp_cs.2.2.2.2
      have h12 := Finset.Subset.trans h1 h2
      rw [Finset.card_sdiff_of_subset h1, Finset.card_sdiff_of_subset h2, Finset.card_sdiff_of_subset h12]
      have c1 := Finset.card_le_card h1
      have c2 := Finset.card_le_card h2
      omega
    have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
      ext x; simp [Finset.mem_Icc]; omega
    have hSum_ex : ((components G₀).sum fun C => (extraSet (st_s1.cs.compSt C) (st_s1.ts C)).card) ≤
        2 * (∑ i ∈ Finset.Icc 1 (s + 1), (D.U i).length) + (st_s1.cs.RF.R \ cs₀.RF.R).card := by
      calc (components G₀).sum (fun C => (extraSet (st_s1.cs.compSt C) (st_s1.ts C)).card)
          ≤ (components G₀).sum (fun C =>
              (extraSet (st_s.cs.compSt C) (st_s.ts C)).card +
                projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) +
                ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card) :=
              Finset.sum_le_sum fun C hC => hex_C C hC
        _ = ((components G₀).sum fun C => (extraSet (st_s.cs.compSt C) (st_s.ts C)).card) +
              ((components G₀).sum fun C =>
                projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1))) +
              ((components G₀).sum fun C =>
                ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card) := by
            simp only [Finset.sum_add_distrib]
        _ ≤ (2 * (∑ i ∈ Finset.Icc 1 s, (D.U i).length) + (st_s.cs.RF.R \ cs₀.RF.R).card) +
              2 * (D.U (s + 1)).length + (st_s1.cs.RF.R \ st_s.cs.RF.R).card := by
            rw [hsum_R]
            exact Nat.add_le_add_right (Nat.add_le_add ih_ex hsum_proj) _
        _ = 2 * (∑ i ∈ Finset.Icc 1 (s + 1), (D.U i).length) + (st_s1.cs.RF.R \ cs₀.RF.R).card := by
            rw [hIcc, Finset.sum_insert (by simp)]
            omega
    have hSum_v : ((components G₀).sum fun C => ((st_s1.ts C).C.V.card - (ts₀ C).C.V.card)) ≤
        2 * (∑ i ∈ Finset.Icc 1 (s + 1), (D.U i).length) * (G₀.maxDeg + 1) +
          (st_s1.cs.RF.R \ cs₀.RF.R).card := by
      calc (components G₀).sum (fun C => (st_s1.ts C).C.V.card - (ts₀ C).C.V.card)
          ≤ (components G₀).sum (fun C =>
              ((st_s.ts C).C.V.card - (ts₀ C).C.V.card) +
                projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)) * (G₀.maxDeg + 1) +
                ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card) :=
              Finset.sum_le_sum fun C hC => (hv_C C hC).1
        _ = ((components G₀).sum fun C => (st_s.ts C).C.V.card - (ts₀ C).C.V.card) +
              ((components G₀).sum fun C =>
                projCompBatchWeight st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1))) * (G₀.maxDeg + 1) +
              ((components G₀).sum fun C =>
                ((st_s1.cs.compSt C).R \ (st_s.cs.compSt C).R).card) := by
            simp only [Finset.sum_add_distrib, Finset.sum_mul]
        _ ≤ (2 * (∑ i ∈ Finset.Icc 1 s, (D.U i).length) * (G₀.maxDeg + 1) + (st_s.cs.RF.R \ cs₀.RF.R).card) +
              2 * (D.U (s + 1)).length * (G₀.maxDeg + 1) + (st_s1.cs.RF.R \ st_s.cs.RF.R).card := by
            rw [hsum_R]
            exact Nat.add_le_add_right (Nat.add_le_add ih_v (Nat.mul_le_mul_right _ hsum_proj)) _
        _ = 2 * (∑ i ∈ Finset.Icc 1 (s + 1), (D.U i).length) * (G₀.maxDeg + 1) +
              (st_s1.cs.RF.R \ cs₀.RF.R).card := by
            rw [hIcc, Finset.sum_insert (by simp)]
            nlinarith
    exact ⟨hSum_ex, hSum_v, fun C hC => (hv_C C hC).2⟩


end

end MinCostFlow.SparseCore
