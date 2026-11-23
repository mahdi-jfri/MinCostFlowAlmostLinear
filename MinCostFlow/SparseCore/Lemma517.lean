module

public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.SparseCore.SparseCoreCostEnv
public import MinCostFlow.SparseCore.SparseCoreStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 5.17, Variants, Exponent Arithmetic, and Counterexamples (`jtree.tex`, pages 23–24)

This file proves the specifications of `sparseCoreTool` (**Lemma 5.17**, pages 23–24;
`[chen2022maximum]` v2 Lemma 7.5):
* `lemma_5_17_noHidden` / `lemma_5_17_isSpecNoHidden`: **unconditional** `IsSpecNoHidden` under
  `SparseCoreInstanceHyps` (requiring no `hBroken_bound`, no `hK_card_bound`, no `NonCanceling`, and
  only positive edge lengths `∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e`).
* `lemma_5_17_weakHidden_items124`: **unconditional** clauses 1 (`IsCirculation`), 2 (`IsValidPair`),
  and 4 (`0 < w^S, |log w^S| ≤ Ψ_S, 0 < ℓ^S, |log ℓ^S| ≤ Ψ_S`) of `WeakHiddenStable`.
* `lemma_5_17`: **unconditional** full `SparseCoreTool.IsSpec` conclusion (including
  `WeakHiddenStable` item 2 / clause 3) under `SparseCoreInstanceHyps`.
* `lemma_5_17_mwu`: unconditional `ToolMWU` average stretch bound under `(D.G 0).m + 2 ≤ ((D.G 0).n + 2) ^ μ`.
* `lemma_5_17_embedsSurviving`: unconditional `ToolEmbedsSurviving` proof.
* `lemma_5_17_noReinsert` / `lemma_5_17_toolNoReinsert` / `lemma_5_17_toolNoReinsertNoHidden`:
  **unconditional** `NoBatchReinsert` propagation with no disjointness hypothesis on `D_total`.
* `lemma_5_17_exponent_arithmetic`: balancing `L` gives `8/9` for the paper's `log^{2/3}` sparsifier
  and `23/24` (`7/8 + 2/24 = 23/24`) for Theorem 8.6's `exp(O(log^{7/8} m))` bound.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Main Lemma 5.17 theorems (`lemma_5_17_noHidden`, items 1/2/4, and `lemma_5_17`) -/

/-- **Lemma 5.17 without `WeakHiddenStable`** (needed by Theorem 5.1 for worst-case runtime on
arbitrary valid inputs): establishes every clause of `IsSpecNoHidden` unconditionally under
`SparseCoreInstanceHyps`, requiring no `hBroken_bound` and no `hK_card_bound`. -/
theorem lemma_5_17_noHidden (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : SparseCoreInstanceHyps E oracle sparsify k τ D) :
    let T := sparseCoreTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let st := fun t => (T.run k D t).1
    let U_S := fun t => (T.run k D t).2
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ m₀) (P.γ_c m₀) m₀
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r m₀ * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T) := by
  intro T P st U_S m₀ n₀
  have hValP := sparseCoreParams_valid E
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := sparseCoreTool_run_eq_treeRunSeq oracle E.C_lsst E.L sparsify k D hV₀
    have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
    have hLSF := sparseCore_lsf_guarantees oracle E.C_lsst E.L sparsify hHyps.hLSST
      k τ hk D hG₀ hD hℓ hLen
    have hn₀_pos : 1 ≤ n₀ := Finset.card_pos.mpr hV₀
    have hS_eq : ∀ t j, T.S (st t) j =
        (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j t).1.S_cur := fun t j => by
      have h1 : (st t).isNonempty = true := (hrun t).1
      change (if (st t).isNonempty = true then ((st t).trees j).S_cur else emptyGraph) = _
      split_ifs
      rw [(hrun t).2.2.1 j]
    have hEmb_eq : ∀ t j, T.emb (st t) j =
        (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j t).1.emb := fun t j => by
      have h1 : (st t).isNonempty = true := (hrun t).1
      change (if (st t).isNonempty = true then ((st t).trees j).emb else fun _ => []) = _
      split_ifs
      rw [(hrun t).2.2.1 j]
    have hL_eq : ∀ t j, T.lsfs (st t) j =
        (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j t).1.cs.lsf := fun t j => by
      have h1 : (st t).isNonempty = true := (hrun t).1
      change (if (st t).isNonempty = true then ((st t).trees j).cs.lsf else emptyLSF) = _
      split_ifs
      rw [(hrun t).2.2.1 j]
    have hUS_eq : ∀ t, 1 ≤ t → ∀ j, U_S t j =
        (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j t).2 := fun t ht j =>
      (hrun t).2.2.2 t ht j
    -- Clause 1: LSF holds, IsSparsifiedCoreGraph, connected root count
    have hC1 : ∀ t ≤ τ, ∀ j < k,
        (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
        IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ m₀) (P.γ_c m₀) m₀
          (T.S (st t) j) (T.emb (st t) j) ∧
        ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
          ((T.lsfs (st t) j).F.R.card : ℝ) ≤
            P.c_R * ((m₀ : ℝ) / (k : ℝ) +
              (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
                (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1)) := by
      intro t ht j hj
      have hlsf_tj := hLSF.1 t ht j hj
      have hholds := holds_mono_sigma hlsf_tj.1 (le_max_right (1 : ℝ) _)
      have hsp := treeRunSeq_isSparsifiedCoreGraph oracle E.C_lsst E.L E.hL (E.P_fn m₀)
        sparsify hHyps.hLSST k m₀ n₀ τ hk D hG₀ hV₀ hD hℓ hLen le_rfl le_rfl hThresh hHyps.hSp j hj t ht
      dsimp only at hsp
      rw [← hL_eq t j, ← hS_eq t j, ← hEmb_eq t j] at hsp
      have hlen : ((T.emb (st t) j).length (coreGraph (D.G t) (T.lsfs (st t) j)) : ℝ) ≤ P.γ_ℓ m₀ :=
        le_trans hsp.2.2.2.1 (le_max_left _ _)
      have hcong : (T.emb (st t) j).econg (coreGraph (D.G t) (T.lsfs (st t) j)) (T.S (st t) j)
          (fun _ => 1) (fun _ => 1) ≤ (k : ℝ) * P.γ_c m₀ := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        set cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
        have hdeg_le : (((components (D.G 0)).sup fun C =>
            (initTildeState (cs₀.compSt C)).C.maxDeg : ℕ) : ℝ) ≤ (E.d_fn m₀ : ℝ) := by
          exact_mod_cast hHyps.hDeg_bound.2 j hj
        have hce_nn := coreE82Cong_nonneg E.L (E.P_fn m₀)
        have h1 : 1 + coreE82Cong E.L (E.P_fn m₀) *
            (((components (D.G 0)).sup fun C =>
              (initTildeState (cs₀.compSt C)).C.maxDeg : ℕ) : ℝ) ≤ P.γ_c m₀ := by
          dsimp only [P, sparseCoreParams]
          nlinarith
        have hγc_ge1 : 1 ≤ P.γ_c m₀ := by
          dsimp only [P, sparseCoreParams]
          have : 0 ≤ (E.d_fn m₀ : ℝ) := Nat.cast_nonneg _
          nlinarith
        calc _ ≤ 1 + coreE82Cong E.L (E.P_fn m₀) *
              (((components (D.G 0)).sup fun C =>
                (initTildeState (cs₀.compSt C)).C.maxDeg : ℕ) : ℝ) := hsp.2.2.2.2.1
          _ ≤ P.γ_c m₀ := h1
          _ = 1 * P.γ_c m₀ := (one_mul _).symm
          _ ≤ (k : ℝ) * P.γ_c m₀ := by nlinarith
      have hcard : ((T.S (st t) j).E.card : ℝ) ≤ (m₀ : ℝ) * P.γ_ℓ m₀ / (k : ℝ) := by
        have hC_sp := hsp.2.2.2.2.2.2 (E.B_fn m₀) (hHyps.hB_bound j hj)
        have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
        have hdeg_le : ((D.G 0).maxDeg : ℝ) ≤ (E.d_fn m₀ : ℝ) := by
          exact_mod_cast hHyps.hDeg_bound.1
        have hKs_nn := (E.P_fn m₀).hK_s
        have hγ_nn : 0 ≤ (E.P_fn m₀).γ_ℓ := by linarith [(E.P_fn m₀).hγ_ℓ]
        have hlam_nn := coreLambdaS_pos (E.P_fn m₀) m₀
        have hB_nn : (0 : ℝ) ≤ (E.B_fn m₀ : ℝ) := Nat.cast_nonneg _
        have hm_nn : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
        have hcoef :
            (((E.L : ℝ) + 1) * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
                coreLambdaS (E.P_fn m₀) m₀ * (E.B_fn m₀ : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) ≤
              P.γ_ℓ m₀ := by
          have h11 : (((E.L : ℝ) + 1) * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
              coreLambdaS (E.P_fn m₀) m₀ * (E.B_fn m₀ : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) ≤
              11 * (((E.L : ℝ) + 1) * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
                coreLambdaS (E.P_fn m₀) m₀ * (E.B_fn m₀ : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) := by
            have : (0 : ℝ) ≤ ((E.L : ℝ) + 1) * (E.P_fn m₀).K_s * (E.P_fn m₀).γ_ℓ *
                coreLambdaS (E.P_fn m₀) m₀ * (E.B_fn m₀ : ℝ) * (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115 := by
              positivity
            linarith
          refine le_trans h11 (le_trans ?_ (le_max_right _ _))
          gcongr
        exact le_trans hC_sp (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef hm_nn) (le_of_lt hk_pos) |>.trans_eq (by ring))
      have hisSp : IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ)
          (P.γ_ℓ m₀) (P.γ_c m₀) m₀ (T.S (st t) j) (T.emb (st t) j) :=
        ⟨hsp.1, hsp.2.1, hsp.2.2.1, hlen, hcong, hcard⟩
      exact ⟨hholds, hisSp, hlsf_tj.2⟩
    -- Clause 2: decremental forest, wstr, valid spanner batch transition
    have hC2 : ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
        (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
        (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
          (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
        (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
        (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
        T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j) := by
      intro t ht1 htτ j hj
      have h2_lsf := hLSF.2.1 t ht1 htτ j hj
      have hStep := (treeRunSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn m₀)
        sparsify hHyps.hLSST k m₀ n₀ τ hk D hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hHyps.hSp j hj).2.2.1 t ht1 htτ
      have hUS_info : U_S t j =
          (stepTreeCoreAux sparsify (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j (t - 1)).1
            (D.U t)).U_S := by
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
        rw [hUS_eq s.succ ht1 j]
        rfl
      rw [hUS_info, hS_eq (t - 1) j, hS_eq t j]
      exact ⟨h2_lsf.1, h2_lsf.2.1, h2_lsf.2.2, hStep.1, hStep.2.1⟩
    -- Clause 3: recourse |U_S| and encoding size sum Enc(U_S)
    have hC3 : ∀ t ≤ τ, ∀ j < k,
        (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
          P.γ_r m₀ * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
        (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
          P.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) := by
      intro t ht j hj
      have hRec := treeRunSeq_recourse_and_enc oracle E.C_lsst E.L E.hL (E.P_fn m₀)
        sparsify hHyps.hLSST k m₀ n₀ τ hk D hG₀ hV₀ hℓ₀ hD le_rfl le_rfl hThresh hHyps.hSp j hj
        (E.B_fn m₀) (hHyps.hB_bound j hj) t ht
      have hUS_sum_eq :
          (Finset.Icc 1 t).sum (fun s => (U_S s j).length) =
            (Finset.Icc 1 t).sum (fun s => (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length) :=
        Finset.sum_congr rfl fun s hs => by rw [hUS_eq s (Finset.mem_Icc.mp hs).1 j]
      have hEnc_sum_eq :
          (Finset.Icc 1 t).sum (fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j)) =
            (Finset.Icc 1 t).sum (fun s =>
              (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j (s - 1)).1.S_cur.batchEnc
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2) :=
        Finset.sum_congr rfl fun s hs => by
          rw [hS_eq (s - 1) j, hUS_eq s (Finset.mem_Icc.mp hs).1 j]
      rw [hUS_sum_eq, hEnc_sum_eq]
      set q_t := (Finset.Icc 1 t).sum fun s => (D.U s).length
      have hRec_le : coreRecoursePerQ E.L (E.P_fn m₀) m₀ n₀ (D.G 0).maxDeg (E.B_fn m₀) ≤
          recEnv E m₀ := by
        have huc_le : coreUCRatio n₀ (D.G 0).maxDeg ≤ ucRatioHi E m₀ := by
          unfold coreUCRatio ucRatioHi
          have hd_le : ((D.G 0).maxDeg : ℝ) ≤ (E.d_fn m₀ : ℝ) := by exact_mod_cast hHyps.hDeg_bound.1
          have hlog1 : 0 ≤ Real.log ((n₀ : ℝ) + 2) := Real.log_nonneg (by linarith)
          have hlog_le : Real.log ((n₀ : ℝ) + 2) ≤ Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2) :=
            Real.log_le_log (by linarith) (by linarith [hHyps.hComp_bound])
          gcongr
        have hlog1' : 0 ≤ Real.log ((n₀ : ℝ) + 2) := Real.log_nonneg (by linarith)
        have hlog_le' : Real.log ((n₀ : ℝ) + 2) ≤ Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2) :=
          Real.log_le_log (by linarith) (by linarith [hHyps.hComp_bound])
        have hcp := coreBucketRec_pos E.L (E.P_fn m₀) m₀
        have h3_nn : 0 ≤ (3 + 2 * coreE82Len E.L (E.P_fn m₀)) *
            coreBucketRecUH E.L (E.P_fn m₀) m₀ + 2 * coreBucketRecD E.L (E.P_fn m₀) m₀ := by
          nlinarith [hcp.1, hcp.2.1, hcp.2.2]
        have hB_nn : (0 : ℝ) ≤ (E.B_fn m₀ : ℝ) := Nat.cast_nonneg _
        have huc_nn := coreUCRatio_pos n₀ (D.G 0).maxDeg
        have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huc_le (by norm_num : (0 : ℝ) ≤ 2))
          (mul_nonneg hB_nn h3_nn)
        have hsq : (Real.log ((n₀ : ℝ) + 2)) ^ 2 ≤ (Real.log (E.c_n * ((m₀ : ℝ) + 1) + 2)) ^ 2 :=
          pow_le_pow_left₀ hlog1' hlog_le' 2
        unfold coreRecoursePerQ recEnv
        linarith
      have hlen_rec :
          (((Finset.Icc 1 t).sum fun s =>
              (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) ≤
            recEnv E m₀ * (q_t : ℝ) :=
        le_trans hRec.1 (mul_le_mul_of_nonneg_right hRec_le (Nat.cast_nonneg _))
      have hlen_le_γr :
          (((Finset.Icc 1 t).sum fun s =>
              (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) ≤
            P.γ_r m₀ * (q_t : ℝ) := by
        have hq_nn : 0 ≤ (q_t : ℝ) := Nat.cast_nonneg _
        have hrec_le_γr : recEnv E m₀ ≤ P.γ_r m₀ := by
          dsimp only [P, sparseCoreParams]
          have hcm := costMult_ge_one E m₀
          have hrb : recEnv E m₀ ≤ recBase E m₀ := le_max_left _ _
          have hr_nn : 0 ≤ recEnv E m₀ := by linarith [recEnv_ge_four E m₀]
          nlinarith
        exact le_trans hlen_rec (mul_le_mul_of_nonneg_right hrec_le_γr hq_nn)
      refine ⟨hlen_le_γr, ?_⟩
      by_cases hq0 : q_t = 0
      · obtain ⟨_, hEnc0⟩ := hRec.2.2 hq0
        rw [hEnc0, Nat.cast_zero]
        have hγr_nn : 0 ≤ P.γ_r m₀ := by
          have := hValP.2.2.2.2.2.2.1 m₀
          linarith
        exact mul_nonneg hγr_nn (by positivity)
      · have hm₀_le_S₀ : ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) ≤
            (m₀ : ℝ) * gammaLEnv E m₀ / (k : ℝ) := by
          have h0 := (hC1 0 (Nat.zero_le τ) j hj).2.1.2.2.2.2.2
          rw [hS_eq 0 j] at h0
          simpa [MGraph.m, m₀, P, sparseCoreParams] using h0
        have hm₀_le_raw : ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) ≤ (m₀ : ℝ) := by
          have hc0 := (hC1 0 (Nat.zero_le τ) j hj).2.1.1.2.1
          have hsub : (coreGraph (D.G 0) (T.lsfs (st 0) j)).E ⊆ (D.G 0).E := Finset.sdiff_subset
          have : (T.S (st 0) j).E.card ≤ (D.G 0).E.card :=
            Finset.card_le_card (Finset.Subset.trans hc0 hsub)
          rw [hS_eq 0 j] at this
          exact_mod_cast this
        have hq_le_m0 : q_t ≤ m₀ := (updateThreshold_le_div_k hk hG₀ hThresh t ht).2
        have hqR_le : (q_t : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hq_le_m0
        have hrec_nn : 0 ≤ recEnv E m₀ := by linarith [recEnv_ge_four E m₀]
        have hsum_in :
            ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) +
              (((Finset.Icc 1 t).sum fun s =>
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) ≤
              max (gammaLEnv E m₀) (recEnv E m₀) * ((m₀ : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
          have hm_nn : 0 ≤ (m₀ : ℝ) / (k : ℝ) := by positivity
          have hq_nn : 0 ≤ (q_t : ℝ) := Nat.cast_nonneg _
          have hM1 := mul_le_mul_of_nonneg_right (le_max_left (gammaLEnv E m₀) (recEnv E m₀)) hm_nn
          have hM2 := mul_le_mul_of_nonneg_right (le_max_right (gammaLEnv E m₀) (recEnv E m₀)) hq_nn
          have hS0_le : ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) ≤
              gammaLEnv E m₀ * ((m₀ : ℝ) / (k : ℝ)) := by
            linarith [hm₀_le_S₀, show (m₀ : ℝ) * gammaLEnv E m₀ / (k : ℝ) =
              gammaLEnv E m₀ * ((m₀ : ℝ) / (k : ℝ)) from by ring]
          linarith [hS0_le, hlen_rec, hM1, hM2]
        have hlog_arg :
            ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) +
              (((Finset.Icc 1 t).sum fun s =>
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) + 2 ≤
              (m₀ : ℝ) + recEnv E m₀ * (m₀ : ℝ) + 2 := by
          nlinarith [hm₀_le_raw, hlen_rec, hqR_le]
        have hlog1 : 0 ≤ Real.log
            (((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) +
              (((Finset.Icc 1 t).sum fun s =>
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) + 2) := by
          apply Real.log_nonneg
          have h0a : (0 : ℝ) ≤ ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) :=
            Nat.cast_nonneg _
          have h0b : (0 : ℝ) ≤ (((Finset.Icc 1 t).sum fun s =>
              (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) :=
            Nat.cast_nonneg _
          linarith
        have harg_pos : 0 < ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) +
              (((Finset.Icc 1 t).sum fun s =>
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) + 2 := by
          positivity
        have hlog_le :
            Real.log (((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) +
              (((Finset.Icc 1 t).sum fun s =>
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ) + 2) ≤
              Real.log ((m₀ : ℝ) + recEnv E m₀ * (m₀ : ℝ) + 2) :=
          Real.log_le_log harg_pos hlog_arg
        have hlog_outer : 0 ≤ Real.log ((m₀ : ℝ) + recEnv E m₀ * (m₀ : ℝ) + 2) := by
          apply Real.log_nonneg
          have : (0 : ℝ) ≤ (m₀ : ℝ) := Nat.cast_nonneg _
          nlinarith
        have hmax_nn : 0 ≤ max (gammaLEnv E m₀) (recEnv E m₀) :=
          le_trans hrec_nn (le_max_right _ _)
        have henc_bound :
            (((Finset.Icc 1 t).sum fun s =>
              (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j (s - 1)).1.S_cur.batchEnc
                (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2 : ℕ) : ℝ) ≤
              encEnv E m₀ * ((m₀ : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
          have hm1 :
              20 * (((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j 0).1.S_cur.m : ℝ) +
                (((Finset.Icc 1 t).sum fun s =>
                  (treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j s).2.length : ℕ) : ℝ)) ≤
                20 * max (gammaLEnv E m₀) (recEnv E m₀) *
                  ((m₀ : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
            linarith
          have hm2 := mul_le_mul hm1 hlog_le hlog1 (by positivity)
          have heq : 20 * max (gammaLEnv E m₀) (recEnv E m₀) *
              ((m₀ : ℝ) / (k : ℝ) + (q_t : ℝ)) * Real.log ((m₀ : ℝ) + recEnv E m₀ * (m₀ : ℝ) + 2) =
              encEnv E m₀ * ((m₀ : ℝ) / (k : ℝ) + (q_t : ℝ)) := by
            unfold encEnv; ring
          exact le_trans hRec.2.1 (heq ▸ hm2)
        have henc_le_γr : encEnv E m₀ ≤ P.γ_r m₀ := by
          dsimp only [P, sparseCoreParams]
          have h1 : encEnv E m₀ ≤ recBase E m₀ := le_max_right _ _
          have h2 : 1 ≤ costMult E m₀ := costMult_ge_one E m₀
          have h3 : 0 ≤ encEnv E m₀ := by
            unfold encEnv; exact mul_nonneg (mul_nonneg (by norm_num) hmax_nn) hlog_outer
          nlinarith
        exact le_trans henc_bound (mul_le_mul_of_nonneg_right henc_le_γr (by positivity))
    -- Clause 4: total cost ≤ c_T * (m₀ + 1) * k * γ_r(m₀) * log^{p_T}(m₀ + n₀ + 2)
    have hC4 : (T.cost (st τ) : ℝ) ≤
        P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * P.γ_r m₀ *
          (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T := by
      have hcost_eq : (T.cost (st τ) : ℝ) =
          (Finset.range k).sum fun j =>
            ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j τ).1.cost : ℝ) := by
        have h1 : (st τ).isNonempty = true := (hrun τ).1
        change ((if (st τ).isNonempty = true then
            (Finset.range (st τ).k).sum (fun j => ((st τ).trees j).cost) else 0 : ℕ) : ℝ) = _
        split_ifs
        rw [(hrun τ).2.1, Nat.cast_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [(hrun τ).2.2.1 j]
      rw [hcost_eq]
      calc (Finset.range k).sum (fun j => ((treeRunSeq oracle E.C_lsst E.L sparsify k m₀ n₀ D j τ).1.cost : ℝ))
          ≤ (Finset.range k).sum (fun _ =>
              P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ * (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T) :=
            Finset.sum_le_sum fun j hj => treeRunSeq_cost_le_params E oracle sparsify k τ D hk
              hG₀ hV₀ hℓ₀ hD hThresh hHyps j (Finset.mem_range.mp hj)
        _ = (k : ℝ) * (P.c_T * ((m₀ : ℝ) + 1) * P.γ_r m₀ *
              (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * P.γ_r m₀ *
              (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T := by ring
    exact ⟨hC1, hC2, hC3, hC4⟩
  · -- Empty vertex set case: `(D.G 0).V = ∅`, all updates are `[]`, and `T` runs trivially cleanly
    obtain ⟨hG_empty, _⟩ := empty_dyn_eq hG₀ hV₀ hD
    have hrunE := sparseCoreTool_run_empty oracle E.C_lsst E.L sparsify k D hV₀
    have hS_eq : ∀ t j, T.S (st t) j = emptyGraph := fun t j => by
      have h1 : (st t).isNonempty = false := (hrunE t).1
      change (if (st t).isNonempty = true then ((st t).trees j).S_cur else emptyGraph) = emptyGraph
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    have hL_eq : ∀ t j, T.lsfs (st t) j = emptyLSF := fun t j => by
      have h1 : (st t).isNonempty = false := (hrunE t).1
      change (if (st t).isNonempty = true then ((st t).trees j).cs.lsf else emptyLSF) = emptyLSF
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    have hEmb_eq : ∀ t j, T.emb (st t) j = fun _ => [] := fun t j => by
      have h1 : (st t).isNonempty = false := (hrunE t).1
      change (if (st t).isNonempty = true then ((st t).trees j).emb else fun _ => []) = fun _ => []
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    have hUS_eq : ∀ t j, U_S t j = [] := fun t j => by
      dsimp only [U_S]
      rw [(hrunE t).2]
    have hcost0 : T.cost (st τ) = 0 := by
      have h1 : (st τ).isNonempty = false := (hrunE τ).1
      change (if (st τ).isNonempty = true then
          (Finset.range (st τ).k).sum (fun j => ((st τ).trees j).cost) else 0) = 0
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht j _
      have hGt := hG_empty t ht
      rw [hL_eq t j, hS_eq t j, hEmb_eq t j]
      refine ⟨emptyLSF_holds hGt.left hGt.right.left (D.ℓ t) (P.σ k (D.G t).n), ?_, ?_⟩
      · have hCG_V : (coreGraph (D.G t) emptyLSF).V = ∅ := rfl
        have hCG_E : (coreGraph (D.G t) emptyLSF).E = ∅ := by
          simp [coreGraph, emptyLSF, hGt.2.2]
        refine ⟨⟨Finset.empty_subset _, Finset.empty_subset _, fun _ h => by simp [emptyGraph] at h⟩,
          ⟨by simp [hCG_V, emptyGraph], fun _ h => by simp [hCG_E] at h⟩,
          fun _ h => by simp [hCG_E] at h, ?_, ?_, ?_⟩
        · have hlen0 : Embedding.length (fun _ => []) (coreGraph (D.G t) emptyLSF) = 0 := by
            unfold Embedding.length
            rw [hCG_E]
            simp
          rw [hlen0, Nat.cast_zero]
          linarith [hValP.2.2.1 m₀]
        · have hecong0 : Embedding.econg (fun _ => []) (coreGraph (D.G t) emptyLSF) emptyGraph
              (fun _ => 1) (fun _ => 1) = 0 := by
            unfold Embedding.econg
            simp [emptyGraph]
          rw [hecong0]
          have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          have : 1 ≤ P.γ_c m₀ := hValP.2.2.2.2.1 m₀
          nlinarith
        · simp [emptyGraph]
          have : 1 ≤ P.γ_ℓ m₀ := hValP.2.2.1 m₀
          positivity
      · intro _
        simp only [emptyLSF, Finset.card_empty, Nat.cast_zero]
        have : 0 ≤ P.c_R := hValP.2.2.2.2.2.2.2.2.1
        positivity
    · intro t ht1 htτ j _
      rw [hL_eq t j, hL_eq (t - 1) j, hS_eq t j, hS_eq (t - 1) j, hUS_eq t j]
      have hGtE := (hG_empty t htτ).2.2
      refine ⟨Finset.Subset.rfl, fun e he => by simp [hGtE] at he,
        fun e he => by simp [hGtE] at he, trivial, rfl⟩
    · intro t _ j _
      simp only [hUS_eq, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, MGraph.batchEnc]
      have hγr : 0 ≤ P.γ_r m₀ := by linarith [hValP.2.2.2.2.2.2.1 m₀]
      exact ⟨mul_nonneg hγr (Nat.cast_nonneg _), mul_nonneg hγr (by positivity)⟩
    · rw [hcost0, Nat.cast_zero]
      have hcT : 0 ≤ P.c_T := hValP.2.2.2.2.2.2.2.2.2
      have hγr : 0 ≤ P.γ_r m₀ := by linarith [hValP.2.2.2.2.2.2.1 m₀]
      have hlog : 0 ≤ Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2) := by
        apply Real.log_nonneg
        linarith [Nat.cast_nonneg (α := ℝ) m₀, Nat.cast_nonneg (α := ℝ) n₀]
      positivity

/-- Uniform `IsSpecNoHidden` packaging of `lemma_5_17_noHidden` across any family of valid
instances satisfying `SparseCoreInstanceHyps`. -/
theorem lemma_5_17_isSpecNoHidden (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ : ℕ) (D : DynamicInstance),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n →
      SparseCoreInstanceHyps E oracle sparsify k τ D) :
    IsSpecNoHidden (sparseCoreTool oracle E.C_lsst E.L sparsify) (sparseCoreParams E) :=
  fun k τ D hk hG₀ hD hLen hℓ hThresh =>
    lemma_5_17_noHidden E oracle sparsify k τ D hk hG₀ hD hLen hℓ hThresh
      (hHyps k τ D hk hG₀ hD hLen hℓ hThresh)

/-- **Unconditional `WeakHiddenStable` clauses 1, 2, and 4** on `coreInstance` under
`SparseCoreInstanceHyps` alone (no `NonCanceling`, no `StepDisjoint`, no disjointness). -/
theorem lemma_5_17_weakHidden_items124 (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : SparseCoreInstanceHyps E oracle sparsify k τ D) :
    let T := sparseCoreTool oracle E.C_lsst E.L sparsify
    ∀ j < k, ∃ Ψ_S : ℝ, ∀ t ≤ τ,
      ((T.coreInstance k D j).G t).IsCirculation (T.coreC k D c j t) ∧
      IsValidPair ((T.coreInstance k D j).G t) ((T.coreInstance k D j).ℓ t)
        (T.coreC k D c j t) (T.coreW k D w j t) ∧
      ∀ e' ∈ ((T.coreInstance k D j).G t).E,
        0 < T.coreW k D w j t e' ∧ |Real.log (T.coreW k D w j t e')| ≤ Ψ_S ∧
        0 < (T.coreInstance k D j).ℓ t e' ∧ |Real.log ((T.coreInstance k D j).ℓ t e')| ≤ Ψ_S := by
  intro T j hj
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact ⟨_, treeRunSeq_weakHidden_items124 oracle E.C_lsst E.L E.hL (E.P_fn (D.G 0).m) sparsify
      hHyps.hLSST k τ hk D hG₀ hV₀ hD hLen hThresh hHyps.hSp Ψ c w hWeak j hj⟩
  · have hrunE := sparseCoreTool_run_empty oracle E.C_lsst E.L sparsify k D hV₀
    refine ⟨max Ψ 0, fun t _ => ?_⟩
    have hSE : ((T.coreInstance k D j).G t).E = ∅ := by
      have h1 : (T.run k D t).1.isNonempty = false := (hrunE t).1
      change (if (T.run k D t).1.isNonempty = true then ((T.run k D t).1.trees j).S_cur else emptyGraph).E = ∅
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    have hSV : ((T.coreInstance k D j).G t).V = ∅ := by
      have h1 : (T.run k D t).1.isNonempty = false := (hrunE t).1
      change (if (T.run k D t).1.isNonempty = true then ((T.run k D t).1.trees j).S_cur else emptyGraph).V = ∅
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    exact ⟨fun v hv => by simp [hSV] at hv,
      ⟨fun v hv => by simp [hSV] at hv, fun e he => by simp [hSE] at he⟩,
      fun e he => by simp [hSE] at he⟩

/-- **Lemma 5.17 (`IsSpec`, `jtree.tex`, pages 23–24)**: unconditional full specification of
`sparseCoreTool` including `WeakHiddenStable` item 2, proved from `lemma_5_17_noHidden` and
`treeRunSeq_weakHiddenStable` under `SparseCoreInstanceHyps`. -/
theorem lemma_5_17 (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hHyps : SparseCoreInstanceHyps E oracle sparsify k τ D) :
    let T := sparseCoreTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let st := fun t => (T.run k D t).1
    let U_S := fun t => (T.run k D t).2
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ m₀) (P.γ_c m₀) m₀
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r m₀ * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, ∃ Ψ' : ℝ,
      WeakHiddenStable (T.coreInstance k D j) τ Ψ' (T.coreC k D c j) (T.coreW k D w j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T) := by
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    (hWeak t ht).2.2.2 e he |>.2.2.1
  have hNH := lemma_5_17_noHidden E oracle sparsify k τ D hk hG₀ hD hLen hℓ hThresh hHyps
  refine ⟨hNH.1, hNH.2.1, hNH.2.2.1, ?_, hNH.2.2.2⟩
  intro j hj
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact ⟨_, treeRunSeq_weakHiddenStable oracle E.C_lsst E.L E.hL (E.P_fn (D.G 0).m) sparsify
      hHyps.hLSST k τ hk D hG₀ hV₀ hD hLen hThresh hHyps.hSp Ψ c w hWeak j hj⟩
  · have hrunE := sparseCoreTool_run_empty oracle E.C_lsst E.L sparsify k D hV₀
    refine ⟨max Ψ 0, fun t _ => ?_⟩
    have hSE : ((sparseCoreTool oracle E.C_lsst E.L sparsify).coreInstance k D j |>.G t).E = ∅ := by
      have h1 : ((sparseCoreTool oracle E.C_lsst E.L sparsify).run k D t).1.isNonempty = false :=
        (hrunE t).1
      change (if ((sparseCoreTool oracle E.C_lsst E.L sparsify).run k D t).1.isNonempty = true then
        (((sparseCoreTool oracle E.C_lsst E.L sparsify).run k D t).1.trees j).S_cur else emptyGraph).E = ∅
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    have hSV : ((sparseCoreTool oracle E.C_lsst E.L sparsify).coreInstance k D j |>.G t).V = ∅ := by
      have h1 : ((sparseCoreTool oracle E.C_lsst E.L sparsify).run k D t).1.isNonempty = false :=
        (hrunE t).1
      change (if ((sparseCoreTool oracle E.C_lsst E.L sparsify).run k D t).1.isNonempty = true then
        (((sparseCoreTool oracle E.C_lsst E.L sparsify).run k D t).1.trees j).S_cur else emptyGraph).V = ∅
      split_ifs with hne
      · exact False.elim (by rw [h1] at hne; cases hne)
      · rfl
    refine ⟨fun v hv => by simp [hSV] at hv,
      ⟨fun v hv => by simp [hSV] at hv, fun e he => by simp [hSE] at he⟩,
      fun e he => by simp [hSE] at he,
      fun e he => by simp [hSE] at he⟩

/-! ## 2. Side properties (`ToolMWU`, `ToolEmbedsSurviving`, unconditional `ToolNoReinsert`) -/

/-- Lemma 5.5 MWU average stretch bound (`ToolMWU`), using `(D.G 0).m + 2 ≤ ((D.G 0).n + 2)^μ`. -/
theorem lemma_5_17_mwu (C_lsst : ℝ) (L μ : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k τ : ℕ} {D : DynamicInstance} (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let σ_mwu := fun n => (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.run k D t).1 j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n := by
  intro T σ_mwu t ht e he
  have hLSF := sparseCore_lsf_guarantees oracle C_lsst L sparsify hLSST k τ hk D hG₀ hD hℓ hLen
  have hraw := hLSF.2.2 t ht e he
  have hV_sub : (D.G 0).V ⊆ (D.G t).V := dyn_G_V_sub hD (Nat.zero_le t) ht
  have hn_le : ((D.G 0).n : ℝ) ≤ ((D.G t).n : ℝ) := by exact_mod_cast Finset.card_le_card hV_sub
  have hlog_n0 : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := by
    linarith [half_lt_log_add_two (D.G 0).n]
  have hlog_nt : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log (((D.G t).n : ℝ) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).n]) (by linarith)
  have hlog_m : Real.log (((D.G 0).m : ℝ) + 2) ≤ (μ : ℝ) * Real.log (((D.G t).n : ℝ) + 2) := by
    have hm_pos : (0 : ℝ) < ((D.G 0).m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).m]
    calc Real.log (((D.G 0).m : ℝ) + 2)
        ≤ Real.log ((((D.G 0).n : ℝ) + 2) ^ μ) := Real.log_le_log hm_pos hM_poly
      _ = (μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2) := Real.log_pow _ _
      _ ≤ (μ : ℝ) * Real.log (((D.G t).n : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlog_nt (Nat.cast_nonneg μ)
  have hK₀ : 0 ≤ 26 * mwuK0 C_lsst + 128 := by linarith [mwuK0_pos C_lsst]
  have hpow6 : (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 ≤ (Real.log (((D.G t).n : ℝ) + 2)) ^ 6 :=
    pow_le_pow_left₀ hlog_n0 hlog_nt 6
  have hmul : (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 *
        Real.log (((D.G 0).m : ℝ) + 2) ≤
      (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 7 := by
    have hlog_m_nn : 0 ≤ Real.log (((D.G 0).m : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (D.G 0).m])
    have hp := mul_le_mul (mul_le_mul_of_nonneg_left hpow6 hK₀) hlog_m hlog_m_nn (by positivity)
    have hEq : (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 6 *
        ((μ : ℝ) * Real.log (((D.G t).n : ℝ) + 2)) =
        (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 7 := by ring
    exact le_trans hp (le_of_eq hEq)
  exact le_trans hraw hmul

/-- Unconditional `ToolEmbedsSurviving` proof for `sparseCoreTool`: every edge in the maintained
spanner embeds as itself `[(e, true)]`. -/
theorem lemma_5_17_embedsSurviving
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreTool oracle C_lsst L sparsify).ToolEmbedsSurviving := by
  intro k τ D Ψ c w hk hG₀ hD hLen hWeak hThresh t ht j hj e he
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact sparseCore_embedsSurviving oracle C_lsst L sparsify k D hV₀ t j e he
  · have hrunE := sparseCoreTool_run_empty oracle C_lsst L sparsify k D hV₀ t
    have h1 : ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.isNonempty = false := hrunE.1
    change e ∈ (if ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.isNonempty = true then
      (((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.trees j).S_cur else emptyGraph).E at he
    split_ifs at he with hne
    · exact False.elim (by rw [h1] at hne; cases hne)
    · simp [emptyGraph] at he

/-- Legacy strict step-wise `NoBatchReinsert` for `sparseCoreToolKeep`. -/
theorem lemma_5_17_noReinsert_strict
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hSp : SparsifySpec (D.G 0).m P_b (sparsify (D.G 0).m))
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k)
    (hNoReins_in : NoBatchReinsert (D.G (t - 1)) (D.U t)) :
    let T := sparseCoreToolKeep oracle C_lsst L sparsify
    NoBatchReinsert (T.S (T.run k D (t - 1)).1 j) ((T.run k D t).2 j) := by
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact sparseCore_noReinsert_step_strict oracle C_lsst L hL P_b sparsify hLSST k τ hk D
      hG₀ hV₀ hℓ₀ hD hThresh hSp t ht1 htτ j hj hNoReins_in
  · have hrunE := sparseCoreToolWith_run_empty false oracle C_lsst L sparsify k D hV₀ t
    intro T e _ u hu
    change u ∈ ((sparseCoreToolKeep oracle C_lsst L sparsify).run k D t).2 j at hu
    rw [hrunE.2] at hu
    exact False.elim (List.not_mem_nil hu)

/-- **Unconditional** surviving-edge insertion propagation for `sparseCoreTool`,
requiring no `NoBatchReinsert` or disjointness assumption on `D_total`. -/
theorem lemma_5_17_noReinsert
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hSp : SparsifySpec (D.G 0).m P_b (sparsify (D.G 0).m))
    (t : ℕ) (ht1 : 1 ≤ t) (htτ : t ≤ τ) (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    ∀ e ∈ (T.S (T.run k D (t - 1)).1 j).E,
      e ∈ (T.S (T.run k D t).1 j).E →
      (∀ u ∈ (T.run k D t).2 j, ¬ u.Inserts e) →
      ∀ u ∈ D.U t, ¬ u.Inserts e := by
  by_cases hV₀ : (D.G 0).V.Nonempty
  · exact sparseCore_noReinsert_step oracle C_lsst L hL P_b sparsify hLSST k τ hk D
      hG₀ hV₀ hℓ₀ hD hThresh hSp t ht1 htτ j hj
  · have hrunE := sparseCoreTool_run_empty oracle C_lsst L sparsify k D hV₀ (t - 1)
    intro T e he _ _
    have h1 : ((sparseCoreTool oracle C_lsst L sparsify).run k D (t - 1)).1.isNonempty = false :=
      hrunE.1
    change e ∈ (if ((sparseCoreTool oracle C_lsst L sparsify).run k D (t - 1)).1.isNonempty = true then
      (((sparseCoreTool oracle C_lsst L sparsify).run k D (t - 1)).1.trees j).S_cur else emptyGraph).E at he
    split_ifs at he with hne
    · exact False.elim (by rw [h1] at hne; cases hne)
    · simp [emptyGraph] at he

/-- Global `SparseCoreTool.ToolNoReinsert` for `sparseCoreTool` across all instances when
`sparsify m` satisfies `SparsifySpec m (P_fn m)` for every `m`. -/
theorem lemma_5_17_toolNoReinsert
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreTool oracle C_lsst L sparsify).ToolNoReinsert := by
  intro k τ D Ψ c w hk hG₀ hD _ hWeak hThresh t ht1 htτ j hj
  exact lemma_5_17_noReinsert oracle C_lsst L hL (P_fn (D.G 0).m) sparsify hLSST k τ hk D hG₀
    (fun e he => ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1) hD hThresh (hSp (D.G 0).m)
    t ht1 htτ j hj

/-- Global `SparseCoreTool.ToolNoReinsertNoHidden` for `sparseCoreTool`. -/
theorem lemma_5_17_toolNoReinsertNoHidden
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreTool oracle C_lsst L sparsify).ToolNoReinsertNoHidden :=
  (lemma_5_17_toolNoReinsert oracle C_lsst L hL P_fn sparsify hLSST hSp).toNoHidden

/-! ## 3. Exponent arithmetic (`8/9` vs `23/24`) and necessity counterexamples -/

/-- Balancing `m^{1/L}` against `γ^{L²}` in Theorem 8.2 / Lemma 5.17:
* With Theorem 8.1's paper bound `γ = exp(O(log^{2/3} m log log m))` and `L = Θ(log^{1/9} m)`,
  both `m^{1/L}` and `γ^{O(L²)}` have exponent `2/3 + 2/9 = 8/9 = 1 - 1/9`.
* With Theorem 8.6's formalized bound `γ = exp(O(log^{7/8} m))` and `L = Θ(log^{1/24} m)`,
  both `m^{1/L}` and `γ^{O(L²)}` have exponent `7/8 + 2/24 = 23/24 = 1 - 1/24`. -/
theorem lemma_5_17_exponent_arithmetic :
    (1 : ℚ) - 1 / 9 = 8 / 9 ∧ (2 : ℚ) / 3 + 2 * (1 / 9) = 8 / 9 ∧
    (1 : ℚ) - 1 / 24 = 23 / 24 ∧ (7 : ℚ) / 8 + 2 * (1 / 24) = 23 / 24 := by
  norm_num

end

end MinCostFlow.SparseCore
