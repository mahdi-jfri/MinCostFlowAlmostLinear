module

public import MinCostFlow.SparseCore.SparseCoreStabilityStep

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional `WeakHiddenStable` clauses 1, 2, and 4 for `sparseCoreTool`

Proves `treeCoreState_weakHidden_items124` and `treeRunSeq_weakHidden_items124`: unconditional
circulation, valid-pair, and log-bound guarantees for `sparseCoreTool` without any non-canceling
or disjointness assumption.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma tool_S_eq_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) (j s : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).S
      ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1 j =
      (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.S_cur := by
  have hrun := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀ s
  change (if ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.isNonempty = true then
    (((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.trees j).S_cur else emptyGraph) = _
  rw [hrun.1]; exact congrArg TreeCoreState.S_cur (hrun.2.2.1 j)

lemma tool_S_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) (j s : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).S
      ((sparseCoreTool oracle C_lsst L sparsify).run k D s).1 j =
      (treeRunSeq oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j s).1.S_cur :=
  tool_S_eq_at oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D hV₀ j s

lemma tool_lsfs_eq_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) (j s : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).lsfs
      ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1 j =
      (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs.lsf := by
  have hrun := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀ s
  change (if ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.isNonempty = true then
    (((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.trees j).cs.lsf else emptyLSF) = _
  rw [hrun.1]; exact congrArg (fun x => x.cs.lsf) (hrun.2.2.1 j)

lemma tool_lsfs_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) (j s : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).lsfs
      ((sparseCoreTool oracle C_lsst L sparsify).run k D s).1 j =
      (treeRunSeq oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j s).1.cs.lsf :=
  tool_lsfs_eq_at oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D hV₀ j s

lemma tool_emb_eq_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) (j s : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).emb
      ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1 j =
      (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.emb := by
  have hrun := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀ s
  change (if ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.isNonempty = true then
    (((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.trees j).emb else fun _ => []) = _
  rw [hrun.1]; exact congrArg TreeCoreState.emb (hrun.2.2.1 j)

lemma tool_emb_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k : ℕ) (D : DynamicInstance) (hV₀ : (D.G 0).V.Nonempty) (j s : ℕ) :
    (sparseCoreTool oracle C_lsst L sparsify).emb
      ((sparseCoreTool oracle C_lsst L sparsify).run k D s).1 j =
      (treeRunSeq oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D j s).1.emb :=
  tool_emb_eq_at oracle C_lsst L sparsify k (D.G 0).m (D.G 0).n D hV₀ j s

/-- Single-state **unconditional** proof of `WeakHiddenStable` clauses 1 (`IsCirculation`),
2 (`IsValidPair`), and 4 (`0 < w^S, |log w^S| ≤ Ψ_S, 0 < ℓ^S, |log ℓ^S| ≤ Ψ_S`) for any
`st : TreeCoreState L` at global step `r ≤ τ` whose `cs.lsf`, `S_cur`, and `emb` satisfy the
LSF and spanner-metric guarantees. -/
theorem treeCoreState_weakHidden_items124
    (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L) (P_b : SparsifyParams)
    (k M τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (r : ℕ) (hr : r ≤ τ) (st : TreeCoreState L)
    (hRF_sub : (D.G r).IsSubgraph st.cs.RF.F)
    (hL_holds : st.cs.lsf.Holds (D.G r) (D.ℓ r)
      (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G r).n : ℝ) + 2)) ^ 6))
    (hSp_sub : (coreGraph (D.G r) st.cs.lsf).IsSubgraph st.S_cur)
    (hSp_emb : st.emb.IsEmbedding (coreGraph (D.G r) st.cs.lsf) st.S_cur)
    (hSp_app : ∀ e ∈ (coreGraph (D.G r) st.cs.lsf).E, ∀ e' ∈ walkEdges (st.emb e),
      approx2 (coreLen st.cs.lsf (D.ℓ r) e) (coreLen st.cs.lsf (D.ℓ r) e'))
    (hSp_len : (st.emb.length (coreGraph (D.G r) st.cs.lsf) : ℝ) ≤ coreE82Len L P_b)
    (hSp_cong : st.emb.econg (coreGraph (D.G r) st.cs.lsf) st.S_cur (fun _ => 1) (fun _ => 1) ≤
      1 + coreE82Cong L P_b * (2 * (M : ℝ))) :
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top + 2)
    let coreC := passSparseCoreC (coreGraph (D.G r) st.cs.lsf) st.emb (passCoreC (c r))
    let coreW := passSparseCoreW (coreGraph (D.G r) st.cs.lsf) st.emb (passCoreW st.cs.lsf (w r))
    st.S_cur.IsCirculation coreC ∧
    IsValidPair st.S_cur (coreLen st.cs.lsf (D.ℓ r)) coreC coreW ∧
    ∀ e' ∈ st.S_cur.E,
      0 < coreW e' ∧ |Real.log (coreW e')| ≤ Ψ_S ∧
      0 < coreLen st.cs.lsf (D.ℓ r) e' ∧ |Real.log (coreLen st.cs.lsf (D.ℓ r) e')| ≤ Ψ_S := by
  intro σ_top Ψ_S coreC coreW
  have hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e := fun s hs e he =>
    ((hWeak s hs).2.2.2 e he).2.2.1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hS_sp_valid :
      IsSparsifiedCoreGraph (D.G r) st.cs.lsf (D.ℓ r) (k : ℝ) (max (coreE82Len L P_b) (k : ℝ))
        ((1 + coreE82Cong L P_b * (2 * (M : ℝ))) / (k : ℝ)) st.S_cur st.emb := by
    refine ⟨hSp_sub, hSp_emb, hSp_app, le_trans hSp_len (le_max_left _ _), ?_, ?_⟩
    · rw [mul_div_cancel₀ _ (ne_of_gt hk_pos)]; exact hSp_cong
    · have hSE_sub : st.S_cur.E ⊆ (D.G r).E := Finset.Subset.trans hSp_sub.2.1 Finset.sdiff_subset
      have hcard_m : (st.S_cur.E.card : ℝ) ≤ ((D.G r).m : ℝ) := by
        exact_mod_cast Finset.card_le_card hSE_sub
      calc (st.S_cur.E.card : ℝ)
          ≤ ((D.G r).m : ℝ) := hcard_m
        _ = ((D.G r).m : ℝ) * (k : ℝ) / (k : ℝ) := by rw [mul_div_cancel_right₀ _ (ne_of_gt hk_pos)]
        _ ≤ ((D.G r).m : ℝ) * max (coreE82Len L P_b) (k : ℝ) / (k : ℝ) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _)
              (Nat.cast_nonneg _)) (le_of_lt hk_pos)
  have hGr_val : (D.G r).IsValid := dyn_G_isValid hG₀ hD r hr
  have h513 := lemma_5_13 hGr_val hL_holds hRF_sub (fun e he => le_of_lt (hℓ r hr e he)) (hWeak r hr).2.1
  have h516 := lemma_5_16 hS_sp_valid h513.1
  refine ⟨h516.1.1, h516.1, fun e' he' => ?_⟩
  have he'_C : e' ∈ (coreGraph (D.G r) st.cs.lsf).E := hSp_sub.2.1 he'
  have he'_G : e' ∈ (D.G r).E := (Finset.mem_sdiff.mp he'_C).1
  have hσ_ge : ∀ x ∈ (D.G r).E, 1 ≤ st.cs.lsf.wstr x ∧ st.cs.lsf.wstr x ≤ σ_top := by
    intro x hx
    have h1 := one_le_stretch hRF_sub (fun y hy => le_of_lt (hℓ r hr y hy)) hx
    have hH1 := (hL_holds.2.2.2 x hx).1
    have hH2 := (hL_holds.2.2.2 x hx).2
    have hn_le : (D.G r).n ≤ (D.G τ).n := dyn_G_n_mono hD hr le_rfl
    have hlog1 : 0 ≤ Real.log (((D.G r).n : ℝ) + 2) :=
      (half_lt_log_add_two (D.G r).n).le.trans' (by norm_num)
    have hlog_le : Real.log (((D.G r).n : ℝ) + 2) ≤ Real.log (((D.G τ).n : ℝ) + 2) :=
      Real.log_le_log (by positivity)
        (by linarith [show ((D.G r).n : ℝ) ≤ (D.G τ).n from by exact_mod_cast hn_le])
    have hK0 := (mwuK0_pos C_lsst).le
    have hpow_le := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog1 hlog_le 6)
      (mul_nonneg hK0 (Nat.cast_nonneg k))
    change st.cs.RF.stretch (D.G r) (D.ℓ r) x ≤ st.cs.lsf.wstr x at hH1
    exact ⟨le_trans h1 hH1, le_trans hH2 (le_trans hpow_le (le_max_right _ _))⟩
  have hℓ_pos' : 0 < coreLen st.cs.lsf (D.ℓ r) e' :=
    mul_pos (lt_of_lt_of_le zero_lt_one (hσ_ge e' he'_G).1) (hℓ r hr e' he'_G)
  have h3_le : (3 : ℝ) ≤ coreE82Len L P_b := by
    unfold coreE82Len
    have h3p : (3 : ℝ) ≤ (3 : ℝ) ^ L := by
      calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (3 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hL
    have hγ : 1 ≤ P_b.γ_ℓ ^ (L + 1) := one_le_pow₀ P_b.hγ_ℓ
    nlinarith
  have hce : 0 ≤ coreE82Cong L P_b := by
    have := P_b.hγ_ℓ
    have := P_b.hγ_c
    unfold coreE82Cong
    positivity
  have hM_ge2 : (2 : ℝ) ≤ 2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
      coreE82Len L P_b * σ_top := by
    have hσ_ge1 : 1 ≤ σ_top := le_max_left _ _
    have hc_ge1 : 1 ≤ 1 + coreE82Cong L P_b * (2 * (M : ℝ)) := by
      linarith [show 0 ≤ coreE82Cong L P_b * (2 * (M : ℝ)) by positivity]
    have hm1 := one_le_mul_of_one_le_of_one_le hc_ge1 (by linarith : 1 ≤ coreE82Len L P_b)
    have hm2 := one_le_mul_of_one_le_of_one_le hm1 hσ_ge1
    linarith
  have hℓ_bound : |Real.log (coreLen st.cs.lsf (D.ℓ r) e')| ≤ Ψ_S := by
    have hw_bounds := hσ_ge e' he'_G
    have hℓw := (hWeak r hr).2.2.2 e' he'_G
    have hwstr_pos : 0 < st.cs.lsf.wstr e' := lt_of_lt_of_le zero_lt_one hw_bounds.1
    have h1 : Real.log (coreLen st.cs.lsf (D.ℓ r) e') =
        Real.log (st.cs.lsf.wstr e') + Real.log (D.ℓ r e') := by
      unfold coreLen; exact Real.log_mul (ne_of_gt hwstr_pos) (ne_of_gt hℓw.2.2.1)
    have h2 : |Real.log (st.cs.lsf.wstr e')| ≤
        Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top + 2) := by
      rw [abs_of_nonneg (Real.log_nonneg hw_bounds.1)]
      refine Real.log_le_log hwstr_pos ?_
      have hσ_pos : 0 < σ_top := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have hσ_le : σ_top ≤ (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top := by
        have hc_ge1 : 1 ≤ 1 + coreE82Cong L P_b * (2 * (M : ℝ)) := by
          linarith [show 0 ≤ coreE82Cong L P_b * (2 * (M : ℝ)) by positivity]
        have hm1 := one_le_mul_of_one_le_of_one_le hc_ge1 (by linarith : 1 ≤ coreE82Len L P_b)
        exact le_mul_of_one_le_left (le_of_lt hσ_pos) hm1
      linarith
    rw [h1]
    exact le_trans (abs_add_le _ _) (by linarith [h2, hℓw.2.2.2, le_max_left Ψ (0 : ℝ)])
  have hW_lo : 2 * Real.exp (-max Ψ 0) ≤ coreW e' := by
    dsimp only [coreW, passSparseCoreW, passCoreW]
    have hsingle : st.cs.lsf.wstr e' * w r e' * walkCount (st.emb e') e' ≤
        ∑ e ∈ (coreGraph (D.G r) st.cs.lsf).E,
          st.cs.lsf.wstr e * w r e * walkCount (st.emb e) e' := by
      refine Finset.single_le_sum (f := fun e =>
        st.cs.lsf.wstr e * w r e * walkCount (st.emb e) e') (fun e he => ?_) he'_C
      have heG := (Finset.mem_sdiff.mp he).1
      have hw1 := (hσ_ge e heG).1
      have hw2 := ((hWeak r hr).2.2.2 e heG).1
      have hwc := walkCount_nonneg (st.emb e) e'
      positivity
    have hemb' : st.emb e' = [(e', true)] := by
      dsimp only [TreeCoreState.emb]; simp only [he', ↓reduceIte]
    have hfl1 : walkCount (st.emb e') e' = 1 := by
      rw [hemb']; simp [walkCount]
    have hw_lo : Real.exp (-max Ψ 0) ≤ w r e' := by
      have hlogw := ((hWeak r hr).2.2.2 e' he'_G).2.1
      have hw_pos' := ((hWeak r hr).2.2.2 e' he'_G).1
      have : -max Ψ 0 ≤ Real.log (w r e') := by linarith [(abs_le.mp hlogw).1, le_max_left Ψ (0 : ℝ)]
      calc Real.exp (-max Ψ 0) ≤ Real.exp (Real.log (w r e')) := Real.exp_le_exp.mpr this
        _ = w r e' := Real.exp_log hw_pos'
    have hmain : Real.exp (-max Ψ 0) ≤
        st.cs.lsf.wstr e' * w r e' * walkCount (st.emb e') e' := by
      rw [hfl1, mul_one]
      calc Real.exp (-max Ψ 0) ≤ 1 * w r e' := by linarith [hw_lo]
        _ ≤ st.cs.lsf.wstr e' * w r e' :=
            mul_le_mul_of_nonneg_right (hσ_ge e' he'_G).1 (le_of_lt ((hWeak r hr).2.2.2 e' he'_G).1)
    linarith
  have hW_hi : coreW e' ≤
      2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top * Real.exp (max Ψ 0) := by
    dsimp only [coreW, passSparseCoreW, passCoreW]
    have hfilt_sum :
        ∑ e ∈ (coreGraph (D.G r) st.cs.lsf).E,
          st.cs.lsf.wstr e * w r e * walkCount (st.emb e) e' ≤
        ∑ e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e)),
          st.cs.lsf.wstr e * w r e * coreE82Len L P_b := by
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e he => ?_
      have heG := (Finset.mem_sdiff.mp he).1
      have hww_nn : 0 ≤ st.cs.lsf.wstr e * w r e :=
        mul_nonneg (by linarith [(hσ_ge e heG).1]) (le_of_lt ((hWeak r hr).2.2.2 e heG).1)
      split_ifs with hew
      · have hlen_le : ((st.emb e).length : ℝ) ≤ coreE82Len L P_b :=
          le_trans (by exact_mod_cast Finset.le_sup (f := fun x => (st.emb x).length) he) hSp_len
        exact mul_le_mul_of_nonneg_left (le_trans (walkCount_le_length _ e') hlen_le) hww_nn
      · rw [walkCount_eq_zero_of_not_mem hew, mul_zero]
    have hE_at :
        (((coreGraph (D.G r) st.cs.lsf).E.filter (fun e => e' ∈ walkEdges (st.emb e))).card : ℝ) ≤
          (1 + coreE82Cong L P_b * (2 * (M : ℝ))) := by
      unfold Embedding.econg at hSp_cong
      split_ifs at hSp_cong with hne
      · have he_at := le_trans (Finset.le_sup' (Embedding.econgAt st.emb
          (coreGraph (D.G r) st.cs.lsf) (fun _ => 1) (fun _ => 1)) he') hSp_cong
        unfold Embedding.econgAt at he_at
        simpa [Finset.sum_const, nsmul_eq_mul] using he_at
      · exact absurd ⟨e', he'⟩ hne
    have hterm_le : ∀ e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter
        (fun e => e' ∈ walkEdges (st.emb e)),
        st.cs.lsf.wstr e * w r e * coreE82Len L P_b ≤
          coreE82Len L P_b * σ_top * Real.exp (max Ψ 0) := by
      intro e he
      have heG := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
      have hw_up : w r e ≤ Real.exp (max Ψ 0) := by
        have hlogw := ((hWeak r hr).2.2.2 e heG).2.1
        have hw_pos' := ((hWeak r hr).2.2.2 e heG).1
        have : Real.log (w r e) ≤ max Ψ 0 := le_trans (abs_le.mp hlogw).2 (le_max_left Ψ 0)
        calc w r e = Real.exp (Real.log (w r e)) := (Real.exp_log hw_pos').symm
          _ ≤ Real.exp (max Ψ 0) := Real.exp_le_exp.mpr this
      have hmul := mul_le_mul (hσ_ge e heG).2 hw_up (le_of_lt ((hWeak r hr).2.2.2 e heG).1)
        (le_trans zero_le_one (le_max_left _ _))
      have hmul2 := mul_le_mul_of_nonneg_right hmul (by linarith : 0 ≤ coreE82Len L P_b)
      linarith [hmul2]
    calc 2 * ∑ e ∈ (coreGraph (D.G r) st.cs.lsf).E,
          st.cs.lsf.wstr e * w r e * walkCount (st.emb e) e'
        ≤ 2 * ∑ e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)),
            st.cs.lsf.wstr e * w r e * coreE82Len L P_b := by linarith [hfilt_sum]
      _ ≤ 2 * ∑ _e ∈ (coreGraph (D.G r) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e)),
            (coreE82Len L P_b * σ_top * Real.exp (max Ψ 0)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => hterm_le e he) (by norm_num)
      _ = 2 * (((coreGraph (D.G r) st.cs.lsf).E.filter
            (fun e => e' ∈ walkEdges (st.emb e))).card : ℝ) *
            (coreE82Len L P_b * σ_top * Real.exp (max Ψ 0)) := by
          simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
            (coreE82Len L P_b * σ_top * Real.exp (max Ψ 0)) := by
          gcongr
      _ = _ := by ring
  have hW_pos : 0 < coreW e' :=
    lt_of_lt_of_le (mul_pos (by norm_num) (Real.exp_pos _)) hW_lo
  have hW_log_abs : |Real.log (coreW e')| ≤ Ψ_S := by
    have h_lo_bound : -Ψ_S ≤ Real.log (coreW e') := by
      have hlo1 : Real.log (2 * Real.exp (-max Ψ 0)) ≤ Real.log (coreW e') :=
        Real.log_le_log (mul_pos (by norm_num) (Real.exp_pos _)) hW_lo
      have hlo2 : Real.log (2 * Real.exp (-max Ψ 0)) = Real.log 2 - max Ψ 0 := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
        ring
      have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlogM_nn : 0 ≤ Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
          coreE82Len L P_b * σ_top + 2) := Real.log_nonneg (by linarith)
      dsimp only [Ψ_S]
      linarith
    have h_hi_bound : Real.log (coreW e') ≤ Ψ_S := by
      have hhi1 : Real.log (coreW e') ≤
          Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
            coreE82Len L P_b * σ_top * Real.exp (max Ψ 0)) :=
        Real.log_le_log hW_pos hW_hi
      have hhi2 : Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
            coreE82Len L P_b * σ_top * Real.exp (max Ψ 0)) =
          Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
            coreE82Len L P_b * σ_top) + max Ψ 0 := by
        rw [Real.log_mul (by linarith) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      have hlog_add2 : Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
            coreE82Len L P_b * σ_top) ≤
          Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) *
            coreE82Len L P_b * σ_top + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      dsimp only [Ψ_S]
      linarith
    exact abs_le.mpr ⟨h_lo_bound, h_hi_bound⟩
  exact ⟨hW_pos, hW_log_abs, hℓ_pos', hℓ_bound⟩

/-- **Unconditional** clauses 1 (`IsCirculation`), 2 (`IsValidPair`), and 4 (`0 < w^S,
|log w^S| ≤ Ψ_S, 0 < ℓ^S, |log ℓ^S| ≤ Ψ_S`) of `WeakHiddenStable` on `coreInstanceAt`,
requiring no `NonCanceling`, no `StepDisjoint`, and no disjointness hypothesis. -/
theorem treeRunSeq_weakHidden_items124_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (2 * (M : ℝ))) * coreE82Len L P_b * σ_top + 2)
    ∀ t ≤ τ,
      ((T.coreInstanceAt k M N D j).G t).IsCirculation (T.coreCAt k M N D c j t) ∧
      IsValidPair ((T.coreInstanceAt k M N D j).G t) ((T.coreInstanceAt k M N D j).ℓ t)
        (T.coreCAt k M N D c j t) (T.coreWAt k M N D w j t) ∧
      ∀ e' ∈ ((T.coreInstanceAt k M N D j).G t).E,
        0 < T.coreWAt k M N D w j t e' ∧ |Real.log (T.coreWAt k M N D w j t e')| ≤ Ψ_S ∧
        0 < (T.coreInstanceAt k M N D j).ℓ t e' ∧
        |Real.log ((T.coreInstanceAt k M N D j).ℓ t e')| ≤ Ψ_S := by
  intro T σ_top Ψ_S t ht
  have hℓ : ∀ s ≤ τ, ∀ e ∈ (D.G s).E, 0 < D.ℓ s e := fun s hs e he =>
    ((hWeak s hs).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hS_eq := tool_S_eq_at oracle C_lsst L sparsify k M N D hV₀ j t
  have hL_eq := tool_lsfs_eq_at oracle C_lsst L sparsify k M N D hV₀ j t
  have hEmb_eq := tool_emb_eq_at oracle C_lsst L sparsify k M N D hV₀ j t
  have hG_lsf := sparseCore_lsf_guarantees_at oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hD hℓ hLen
  have hSpCore := treeRunSeq_isSparsifiedCoreGraph oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hD hℓ hLen hM hN hThresh hSp j hj t ht
  obtain ⟨hBase, _, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hRF_sub : (D.G t).IsSubgraph (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.RF.F := by
    rw [← (hBase t ht).2.2.2.2.2.2.2.2.2.1]
    exact (compLSF_RF_isRSF (hBase t ht).2.2.2.2.2.2.2.2.1).2.2.2.2
  have hL_holds : (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs.lsf.Holds (D.G t) (D.ℓ t)
      (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 6) := by
    have h0 := (hG_lsf.1 t ht j hj).1
    rwa [hL_eq] at h0
  rcases hSpCore with ⟨h1, h2, h3, h4, _, h6, _⟩
  have h124 := treeCoreState_weakHidden_items124 C_lsst L hL P_b k M τ hk D hG₀ hD Ψ c w hWeak t ht
    (treeRunSeq oracle C_lsst L sparsify k M N D j t).1 hRF_sub hL_holds h1 h2 h3 h4 h6
  change (T.S (T.runAt k M N D t).1 j).IsCirculation (T.coreCAt k M N D c j t) ∧
    IsValidPair (T.S (T.runAt k M N D t).1 j) (coreLen (T.lsfs (T.runAt k M N D t).1 j) (D.ℓ t))
      (T.coreCAt k M N D c j t) (T.coreWAt k M N D w j t) ∧
    ∀ e' ∈ (T.S (T.runAt k M N D t).1 j).E,
      0 < T.coreWAt k M N D w j t e' ∧ |Real.log (T.coreWAt k M N D w j t e')| ≤ Ψ_S ∧
      0 < coreLen (T.lsfs (T.runAt k M N D t).1 j) (D.ℓ t) e' ∧
      |Real.log (coreLen (T.lsfs (T.runAt k M N D t).1 j) (D.ℓ t) e')| ≤ Ψ_S
  dsimp only [SparseCoreTool.coreCAt, SparseCoreTool.coreWAt]
  rw [hS_eq, hL_eq, hEmb_eq]
  exact h124

theorem treeRunSeq_weakHidden_items124
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hD : D.IsValid τ) (hLen : LengthsStable D τ)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n)
    (hSp : SparsifySpec (D.G 0).m P_b (sparsify (D.G 0).m))
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (j : ℕ) (hj : j < k) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let σ_top := max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G τ).n : ℝ) + 2)) ^ 6)
    let Ψ_S := max Ψ 0 +
      Real.log (2 * (1 + coreE82Cong L P_b * (2 * ((D.G 0).m : ℝ))) * coreE82Len L P_b * σ_top + 2)
    ∀ t ≤ τ,
      ((T.coreInstance k D j).G t).IsCirculation (T.coreC k D c j t) ∧
      IsValidPair ((T.coreInstance k D j).G t) ((T.coreInstance k D j).ℓ t)
        (T.coreC k D c j t) (T.coreW k D w j t) ∧
      ∀ e' ∈ ((T.coreInstance k D j).G t).E,
        0 < T.coreW k D w j t e' ∧ |Real.log (T.coreW k D w j t e')| ≤ Ψ_S ∧
        0 < (T.coreInstance k D j).ℓ t e' ∧ |Real.log ((T.coreInstance k D j).ℓ t e')| ≤ Ψ_S :=
  treeRunSeq_weakHidden_items124_at oracle C_lsst L hL P_b sparsify hLSST
    k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hD hLen le_rfl le_rfl hThresh hSp Ψ c w hWeak j hj


end

end MinCostFlow.SparseCore
