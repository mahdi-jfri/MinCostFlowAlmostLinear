module

public import MinCostFlow.LSF.Lemma54

/-!
# Multiplicative Weights Update over Dynamic Low Stretch Forests (Lemma 5.5)

This file formalizes **Lemma 5.5** (page 17) and its multiplicative-weights proof in
**Appendix A.2** (pages 48–49, Equation `(5.1)`) of the paper.

Given `k ≥ 1` copies of the dynamic LSF data structure from Lemma 5.4 (`lemma_5_4`), we initialize
them sequentially on `G₀` using exponentially increasing edge weights:
* `v₀(e) = 1` for all `e ∈ E(G₀)`,
* `v_{j+1}(e) = v_j(e) * exp(wstr_j(e) / ρ)` with `ρ = 10 * U`, where `U = K₀ * k * log^6(n + 2)`
  and `W = K₀ * log^4(n + 2)` are the upper bounds from Lemma 5.4.

Then all `k` instances process the same valid dynamic sequence of update batches `Us`, preserving
every guarantee of Lemma 5.4 per copy while bounding the uniform average upper-bound stretch
`(1 / k) ∑_{j < k} wstr_j(e)` by `O(log^6(n + 2) log(m + 2))` (`O(log^7 n)` when `m ≤ poly(n)`).
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Dynamic tracking of inserted edges independent of weights -/

/-- Exact set of edges inserted and not yet deleted after one update. -/
def updateInserted (I : Finset ℕ) : Update → Finset ℕ
  | .insert e _ _ => insert e I
  | .delete e => I.erase e
  | .split _ _ _ _ => I

/-- Exact set of edges inserted and not yet deleted after a sequence of update batches. -/
def batchesInserted (Us : List (List Update)) : Finset ℕ :=
  Us.foldl (List.foldl updateInserted) ∅

private lemma applyLSFUpdate_insertedEdges (S : LSFState) (u : Update) :
    (applyLSFUpdate S u).insertedEdges = updateInserted S.insertedEdges u := by
  cases u <;> rfl

private lemma applyLSFBatch_insertedEdges (U : List Update) (S : LSFState) :
    (applyLSFBatch S U).insertedEdges = U.foldl updateInserted S.insertedEdges := by
  induction U generalizing S with
  | nil => rfl
  | cons u U ih =>
    change (applyLSFBatch (applyLSFUpdate S u) U).insertedEdges = _
    rw [ih, applyLSFUpdate_insertedEdges]
    rfl

private lemma applyLSFBatches_insertedEdges (Us : List (List Update)) (S : LSFState) :
    (applyLSFBatches S Us).insertedEdges = Us.foldl (List.foldl updateInserted) S.insertedEdges := by
  induction Us generalizing S with
  | nil => rfl
  | cons U Us ih =>
    change (applyLSFBatches (applyLSFBatch S U) Us).insertedEdges = _
    rw [ih, applyLSFBatch_insertedEdges]
    rfl

private lemma applyUpdate_E_sub_inserted (G : MGraph) (I : Finset ℕ) (u : Update) :
    (G.applyUpdate u).E ⊆ G.E ∪ updateInserted I u ∧
    ∀ e ∈ (G.applyUpdate u).E, e ∉ updateInserted I u → e ∈ G.E ∧ e ∉ I := by
  cases u with
  | insert e_new a b =>
    refine ⟨?_, ?_⟩
    · intro e he
      dsimp only [MGraph.applyUpdate] at he
      rw [Finset.mem_insert] at he
      rcases he with rfl | heG
      · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      · exact Finset.mem_union_left _ heG
    · intro e he he_nins
      dsimp only [MGraph.applyUpdate] at he
      dsimp only [updateInserted] at he_nins
      rw [Finset.mem_insert] at he he_nins
      obtain ⟨hne, heI⟩ := not_or.mp he_nins
      exact ⟨he.resolve_left hne, heI⟩
  | delete e_del =>
    refine ⟨?_, ?_⟩
    · intro e he
      exact Finset.mem_union_left _ (Finset.erase_subset _ _ he)
    · intro e he he_nins
      dsimp only [MGraph.applyUpdate] at he
      dsimp only [updateInserted] at he_nins
      rw [Finset.mem_erase] at he
      exact ⟨he.2, fun h => he_nins (Finset.mem_erase.mpr ⟨he.1, h⟩)⟩
  | split v v' St Sh =>
    exact ⟨Finset.subset_union_left, fun _ he h => ⟨he, h⟩⟩

private lemma applyBatch_E_surv_orig (G₀ : MGraph) :
    ∀ (U : List Update) (G : MGraph) (I : Finset ℕ),
      (∀ e ∈ G.E, e ∉ I → e ∈ G₀.E) →
      ∀ e ∈ (G.applyBatch U).E, e ∉ U.foldl updateInserted I → e ∈ G₀.E
  | [], G, _, h => fun e he hn => h e he hn
  | u :: U, G, I, h => by
    intro e he hn
    change e ∈ ((G.applyUpdate u).applyBatch U).E at he
    change e ∉ U.foldl updateInserted (updateInserted I u) at hn
    exact applyBatch_E_surv_orig G₀ U (G.applyUpdate u) (updateInserted I u)
      (fun f hf hfn =>
        have hf' := (applyUpdate_E_sub_inserted G I u).2 f hf hfn
        h f hf'.1 hf'.2)
      e he hn

private lemma batches_E_surv_orig (G₀ : MGraph) :
    ∀ (Us : List (List Update)) (G : MGraph) (I : Finset ℕ),
      (∀ e ∈ G.E, e ∉ I → e ∈ G₀.E) →
      ∀ e ∈ (Us.foldl MGraph.applyBatch G).E,
        e ∉ Us.foldl (List.foldl updateInserted) I → e ∈ G₀.E
  | [], G, _, h => fun e he hn => h e he hn
  | U :: Us, G, I, h => by
    intro e he hn
    change e ∈ (Us.foldl MGraph.applyBatch (G.applyBatch U)).E at he
    change e ∉ Us.foldl (List.foldl updateInserted) (U.foldl updateInserted I) at hn
    exact batches_E_surv_orig G₀ Us (G.applyBatch U) (U.foldl updateInserted I)
      (applyBatch_E_surv_orig G₀ U G I h) e he hn

/-! ## Elementary MWU inequality and weight helpers -/

private lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1mx_pos : 0 < 1 - x := by linarith
  have hexp_neg : 1 - x ≤ Real.exp (-x) := by
    linarith [Real.add_one_le_exp (-x)]
  have hexp_le_inv : Real.exp x ≤ (1 - x)⁻¹ := by
    rw [← inv_inv (Real.exp x), ← Real.exp_neg]
    exact (inv_anti₀ h1mx_pos hexp_neg)
  have hprod : 1 ≤ (1 - x) * (1 + 2 * x) := by
    nlinarith
  have hinv_le : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ h1mx_pos]
    simpa [mul_comm] using hprod
  exact hexp_le_inv.trans hinv_le

private lemma one_le_stretch_safeLen {RF : RootedForest} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) {e : ℕ} (he : e ∈ G₀.E) :
    1 ≤ RF.stretch G₀ (safeLen G₀ ℓ₀) e := by
  unfold RootedForest.stretch
  dsimp only
  have he_pos : 0 < safeLen G₀ ℓ₀ e := by
    rw [safeLen_eq_of_mem ℓ₀ he]
    exact hℓ₀ e he
  have hw_nn : ∀ P, 0 ≤ walkLength (safeLen G₀ ℓ₀) P := fun P =>
    Finset.sum_nonneg (fun f _ => mul_nonneg (safeLen_nonneg hℓ₀ f) (abs_nonneg _))
  split_ifs
  · exact le_add_of_nonneg_right (div_nonneg (hw_nn _) he_pos.le)
  · exact le_add_of_nonneg_right (div_nonneg (add_nonneg (hw_nn _) (hw_nn _)) he_pos.le)

/-- Sequentially constructed MWU weight vectors `v_j` on edges, starting at `v_0 ≡ 1`. -/
private noncomputable def mwuWeights
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) (ρ : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, e =>
    let vj := mwuWeights oracle C_lsst G₀ ℓ₀ k ρ j
    vj e * Real.exp ((initLSF oracle C_lsst G₀ ℓ₀ vj (k : ℝ)).wstr e / ρ)

private lemma mwuWeights_pos (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) (ρ : ℝ) :
    ∀ j e, 0 < mwuWeights oracle C_lsst G₀ ℓ₀ k ρ j e
  | 0, _ => zero_lt_one
  | j + 1, e =>
    mul_pos (mwuWeights_pos oracle C_lsst G₀ ℓ₀ k ρ j e) (Real.exp_pos _)

private lemma mwuWeights_eq_exp (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) (ρ : ℝ) (j e : ℕ) :
    mwuWeights oracle C_lsst G₀ ℓ₀ k ρ j e =
      Real.exp ((∑ i ∈ Finset.range j,
        (initLSF oracle C_lsst G₀ ℓ₀ (mwuWeights oracle C_lsst G₀ ℓ₀ k ρ i) (k : ℝ)).wstr e) / ρ) := by
  induction j with
  | zero => simp [mwuWeights]
  | succ j ih =>
    unfold mwuWeights
    dsimp only
    rw [ih, ← Real.exp_add, Finset.sum_range_succ, add_div]

/-! ## Main Theorem: Lemma 5.5 -/

open Classical in
/-- **Lemma 5.5** (MWU over Dynamic LSFs, page 17, Appendix A.2 eq. `(5.1)` pages 48–49):
Given a static LSST oracle with parameter `C_lsst`, there is a constant `K > 0` such that for any
valid nonempty graph `G₀`, positive initial lengths `ℓ₀`, integer `k ≥ 1`, valid batch sequence
`Us`, and positive lengths `ℓ` agreeing with `ℓ₀` on surviving un-inserted original edges, there
exist `k` dynamic LSF states `S₀ j` (initial) and `S j` (after `Us`) satisfying every guarantee
of Lemma 5.4 for each `j < k` together with the uniform-average stretch bound (Equation `(5.1)`):
`∑ j ∈ Finset.range k, (1 / k) * (S j).wstr e ≤ K * log^6(G₀.n + 2) * log(G₀.E.card + 2)`.
(Note: for multigraphs with arbitrarily many parallel edges `m`, Appendix A.2 yields `log m` rather
than `log n`; when `m ≤ n^{O(1)}` this equals `O(log^7 n)`.) -/
theorem lemma_5_5 (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G₀ : MGraph), G₀.IsValid → G₀.V.Nonempty →
        ∀ (ℓ₀ : ℕ → ℝ), (∀ e ∈ G₀.E, 0 < ℓ₀ e) →
        ∀ (k : ℕ), 1 ≤ k →
        ∀ (Us : List (List Update)), BatchesIsValid G₀ Us →
        ∀ (ℓ : ℕ → ℝ),
        (∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e) →
        (∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
          e ∉ batchesInserted Us → ℓ e = ℓ₀ e) →
        let G := Us.foldl MGraph.applyBatch G₀
        let q := totalUpdates Us
        ∃ S₀ S : ℕ → LSFState,
          (∀ j < k,
            S j = applyLSFBatches (S₀ j) Us ∧
            (S j).G = G ∧
            (S j).insertedEdges = batchesInserted Us ∧
            (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
            G.IsSubgraph (S j).RF.F ∧
            (S j).T.IsSubgraph (S j).RF.F ∧
            (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
            (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
            ((components (S₀ j).RF.F).card : ℝ) ≤
              (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
                else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
                K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
            ((components (S j).RF.F).card : ℝ) ≤ ((components (S₀ j).RF.F).card : ℝ) +
              K * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
            (S j).lsf.Holds G ℓ (K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
            ((S j).W_init.card : ℝ) ≤
              6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
                else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
                K * ((G₀.E.card : ℝ) / (k : ℝ)) ∧
            (S j).W_init.biUnion (inducedEdges (S₀ j).RF.F) = (S₀ j).RF.F.E ∧
            (∀ W₁ ∈ (S j).W_init, ∀ W₂ ∈ (S j).W_init, W₁ ≠ W₂ →
              Disjoint (inducedEdges (S₀ j).RF.F W₁) (inducedEdges (S₀ j).RF.F W₂)) ∧
            boundary (S j).W_init ⊆ (S j).R ∧
            ∀ W ∈ (S j).W_init, PathConvex (S j).T₀ W ∧ W ⊆ G.V ∧
              (pieceBoundary (S j).W_init W).card ≤ 1 ∧
              (G.vol (W \ (S j).R) : ℝ) ≤ K * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
          ∀ e ∈ G.E,
            ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e ≤
              K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
  obtain ⟨K₀, hK₀_pos, h54⟩ := lemma_5_4 oracle C_lsst hLSST
  refine ⟨26 * K₀ + 128, by linarith, ?_⟩
  intro G₀ hG₀ hV₀ ℓ₀ hℓ₀ k hk Us hUs ℓ hℓ hℓ_orig G q
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real
  have hL : (1 / 2 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := half_lt_log_add_two G₀.n
  have hL_pos : 0 < Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hLm : (1 / 2 : ℝ) < Real.log ((G₀.E.card : ℝ) + 2) := half_lt_log_add_two G₀.E.card
  have hLm_pos : 0 < Real.log ((G₀.E.card : ℝ) + 2) := by linarith
  let L := Real.log ((G₀.n : ℝ) + 2)
  let W := K₀ * L ^ 4
  let U := K₀ * (k : ℝ) * L ^ 6
  let ρ := 10 * U
  have hU_pos : 0 < U := mul_pos (mul_pos hK₀_pos hk_pos) (pow_pos hL_pos 6)
  have hρ_pos : 0 < ρ := by linarith
  let v := mwuWeights oracle C_lsst G₀ ℓ₀ k ρ
  let S₀ : ℕ → LSFState := fun j => initLSF oracle C_lsst G₀ ℓ₀ (v j) (k : ℝ)
  let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
  have hv_pos : ∀ j e, 0 < v j e := fun j e => mwuWeights_pos oracle C_lsst G₀ ℓ₀ k ρ j e
  have hins_eq : ∀ j, (S j).insertedEdges = batchesInserted Us := by
    intro j
    rw [show (S j).insertedEdges = (applyLSFBatches (S₀ j) Us).insertedEdges from rfl,
      applyLSFBatches_insertedEdges]
    rfl
  refine ⟨S₀, S, ?_, ?_⟩
  · intro j _
    have hℓ_orig' : ∀ e ∈ G₀.E, e ∈ G.E → e ∉ (S j).insertedEdges → ℓ e = ℓ₀ e := by
      intro e he₀ heG hn
      rw [hins_eq j] at hn
      exact hℓ_orig e he₀ heG hn
    have hsp := h54 G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (fun e _ => hv_pos j e) (k : ℝ) hk_real
      Us hUs ℓ hℓ hℓ_orig'
    rcases hsp with ⟨hG_eq, hFE_sub, hG_sub, hT_sub, hins_w, hsurv_w, hcomp₀, hcomp_gr,
      hholds, _, hW_card, hcov, hdisj, hb_W, hW_props⟩
    have hK₀_le : K₀ ≤ 26 * K₀ + 128 := by linarith
    have hC0 : 0 ≤ (G₀.E.card : ℝ) / (k : ℝ) := div_nonneg (Nat.cast_nonneg _) hk_pos.le
    have hqL2 : 0 ≤ (q : ℝ) * L ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hkL6 : 0 ≤ (k : ℝ) * L ^ 6 := mul_nonneg hk_pos.le (pow_nonneg hL_pos.le 6)
    have hkL2 : 0 ≤ (k : ℝ) * L ^ 2 := mul_nonneg hk_pos.le (sq_nonneg _)
    have hcomp_if : (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then (1 : ℝ)
        else ((components G₀).card : ℝ) * K₀ * L ^ 2) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
        else ((components G₀).card : ℝ) * (26 * K₀ + 128) * L ^ 2) := by
      split_ifs
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hK₀_le (Nat.cast_nonneg _)) (sq_nonneg _)
    refine ⟨rfl, hG_eq, hins_eq j, hFE_sub, hG_sub, hT_sub, hins_w, hsurv_w, ?_, ?_, ?_, ?_,
      hcov, hdisj, hb_W, ?_⟩
    · exact hcomp₀.trans (add_le_add hcomp_if (mul_le_mul_of_nonneg_right hK₀_le hC0))
    · exact hcomp_gr.trans (add_le_add le_rfl
        (by nlinarith [mul_le_mul_of_nonneg_right hK₀_le hqL2]))
    · refine ⟨hholds.1, hholds.2.1, hholds.2.2.1, fun e he => ?_⟩
      have hhe := hholds.2.2.2 e he
      exact ⟨hhe.1, hhe.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hK₀_le hkL6])⟩
    · exact hW_card.trans (add_le_add (add_le_add le_rfl hcomp_if) (mul_le_mul_of_nonneg_right hK₀_le hC0))
    · intro Wp hWp
      have hwp := hW_props Wp hWp
      exact ⟨hwp.1, hwp.2.1, hwp.2.2.1,
        hwp.2.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_right hK₀_le hkL2])⟩
  · have hsafe_pos : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
      rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
    have hsafe_eq : ∀ e ∈ G₀.E, e ∈ G₀.E → e ∉ (applyLSFBatches (initLSF oracle C_lsst G₀ ℓ₀ (v 0) (k : ℝ)) []).insertedEdges →
        safeLen G₀ ℓ₀ e = ℓ₀ e := fun e he _ _ => safeLen_eq_of_mem ℓ₀ he
    have hw₀_bounds : ∀ j e, e ∈ G₀.E → 1 ≤ (S₀ j).wstr e ∧ (S₀ j).wstr e ≤ U := by
      intro j e he
      have hsp0 := h54 G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (fun e _ => hv_pos j e) (k : ℝ) hk_real
        [] trivial (safeLen G₀ ℓ₀) hsafe_pos (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)
      have hholds0 := hsp0.2.2.2.2.2.2.2.2.1
      have hstr := hholds0.2.2.2 e he
      exact ⟨(one_le_stretch_safeLen hℓ₀ he).trans hstr.1, hstr.2⟩
    have hw₀_sum : ∀ j, ∑ e ∈ G₀.E, v j e * (S₀ j).wstr e ≤ W * G₀.norm1 (v j) := by
      intro j
      have hsp0 := h54 G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (fun e _ => hv_pos j e) (k : ℝ) hk_real
        [] trivial (safeLen G₀ ℓ₀) hsafe_pos (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)
      have hbd := hsp0.2.2.2.2.2.2.2.2.2.1
      linarith [hbd, show K₀ * G₀.norm1 (v j) * L ^ 4 = W * G₀.norm1 (v j) by ring]
    have hnorm1_eq : ∀ j, G₀.norm1 (v j) = ∑ e ∈ G₀.E, v j e := by
      intro j
      refine Finset.sum_congr rfl (fun e _ => abs_of_pos (hv_pos j e))
    have hnorm1_step : ∀ j, G₀.norm1 (v (j + 1)) ≤ Real.exp (2 * W / ρ) * G₀.norm1 (v j) := by
      intro j
      have hpt : ∀ e ∈ G₀.E, v (j + 1) e ≤ v j e + (2 / ρ) * (v j e * (S₀ j).wstr e) := by
        intro e he
        have hb := hw₀_bounds j e he
        have hx0 : 0 ≤ (S₀ j).wstr e / ρ := div_nonneg (by linarith [hb.1]) hρ_pos.le
        have hx1 : (S₀ j).wstr e / ρ ≤ 1 / 2 := by
          rw [div_le_iff₀ hρ_pos]
          linarith [hb.2]
        have hexp := exp_le_one_add_two_mul hx0 hx1
        have hmul := mul_le_mul_of_nonneg_left hexp (hv_pos j e).le
        have hdef : v (j + 1) e = v j e * Real.exp ((S₀ j).wstr e / ρ) := rfl
        rw [hdef]
        linarith [show v j e * (1 + 2 * ((S₀ j).wstr e / ρ)) =
          v j e + (2 / ρ) * (v j e * (S₀ j).wstr e) by ring]
      have hsum : G₀.norm1 (v (j + 1)) ≤ G₀.norm1 (v j) + (2 / ρ) * (W * G₀.norm1 (v j)) := by
        calc G₀.norm1 (v (j + 1))
            = ∑ e ∈ G₀.E, v (j + 1) e := hnorm1_eq (j + 1)
          _ ≤ ∑ e ∈ G₀.E, (v j e + (2 / ρ) * (v j e * (S₀ j).wstr e)) := Finset.sum_le_sum hpt
          _ = (∑ e ∈ G₀.E, v j e) + (2 / ρ) * ∑ e ∈ G₀.E, v j e * (S₀ j).wstr e := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ = G₀.norm1 (v j) + (2 / ρ) * ∑ e ∈ G₀.E, v j e * (S₀ j).wstr e := by
              rw [← hnorm1_eq j]
          _ ≤ G₀.norm1 (v j) + (2 / ρ) * (W * G₀.norm1 (v j)) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_left (hw₀_sum j)
                (div_nonneg zero_le_two hρ_pos.le))
      have hfactor : G₀.norm1 (v j) + (2 / ρ) * (W * G₀.norm1 (v j)) =
          (1 + 2 * W / ρ) * G₀.norm1 (v j) := by ring
      have hexp1 : 1 + 2 * W / ρ ≤ Real.exp (2 * W / ρ) := by
        linarith [Real.add_one_le_exp (2 * W / ρ)]
      have hnorm_nn : 0 ≤ G₀.norm1 (v j) := by
        rw [hnorm1_eq j]
        exact Finset.sum_nonneg (fun e _ => (hv_pos j e).le)
      exact hsum.trans (hfactor ▸ mul_le_mul_of_nonneg_right hexp1 hnorm_nn)
    have hnorm1_le : ∀ j, G₀.norm1 (v j) ≤ Real.exp ((j : ℝ) * (2 * W / ρ)) * (G₀.E.card : ℝ) := by
      intro j
      induction j with
      | zero =>
        rw [hnorm1_eq 0]
        simp [v, mwuWeights]
      | succ j ih =>
        calc G₀.norm1 (v (j + 1))
            ≤ Real.exp (2 * W / ρ) * G₀.norm1 (v j) := hnorm1_step j
          _ ≤ Real.exp (2 * W / ρ) * (Real.exp ((j : ℝ) * (2 * W / ρ)) * (G₀.E.card : ℝ)) :=
              mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
          _ = Real.exp (((j + 1 : ℕ) : ℝ) * (2 * W / ρ)) * (G₀.E.card : ℝ) := by
              push_cast
              rw [← mul_assoc, ← Real.exp_add]
              congr 2
              ring
    intro e heG
    by_cases hins : e ∈ batchesInserted Us
    · have havg_one : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e = 1 := by
        have hcongr : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e =
            ∑ _j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          have hse := (h54 G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (fun f _ => hv_pos j f) (k : ℝ) hk_real
            Us hUs ℓ hℓ (fun f hf₀ hfG hn => by rw [hins_eq j] at hn; exact hℓ_orig f hf₀ hfG hn)).2.2.2.2.1
            e (by rw [hins_eq j]; exact hins)
          rw [hse, mul_one]
        rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [ne_of_gt hk_pos]
      rw [havg_one]
      have hpow6 : (1 / 64 : ℝ) ≤ L ^ 6 := by
        have hsq : (1 / 2 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL.le 6
        linarith [show (1 / 2 : ℝ) ^ 6 = 1 / 64 by norm_num]
      have h1_le_128 : (1 : ℝ) ≤ 128 * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by
        nlinarith [mul_le_mul hpow6 hLm.le (by norm_num) (pow_nonneg hL_pos.le 6)]
      have hK128 : (128 : ℝ) ≤ 26 * K₀ + 128 := by linarith
      have hnonneg : 0 ≤ L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) :=
        mul_nonneg (pow_nonneg hL_pos.le 6) hLm_pos.le
      calc (1 : ℝ)
          ≤ 128 * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := h1_le_128
        _ ≤ (26 * K₀ + 128) * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right hK128 hnonneg
        _ = (26 * K₀ + 128) * Real.log ((G₀.n : ℝ) + 2) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
            ring
    · have heG₀ : e ∈ G₀.E :=
        batches_E_surv_orig G₀ Us G₀ ∅ (fun _ hf _ => hf) e heG hins
      have hcard_pos : (0 : ℝ) < (G₀.E.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨e, heG₀⟩
      have hle_norm : v k e ≤ G₀.norm1 (v k) := by
        rw [hnorm1_eq k]
        exact Finset.single_le_sum (fun f _ => (hv_pos k f).le) heG₀
      have hexp_le : Real.exp ((∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ) ≤
          Real.exp ((k : ℝ) * (2 * W / ρ) + Real.log (G₀.E.card : ℝ)) := by
        rw [Real.exp_add, Real.exp_log hcard_pos, ← mwuWeights_eq_exp]
        exact hle_norm.trans (hnorm1_le k)
      have hlog_le : (∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ ≤
          (k : ℝ) * (2 * W / ρ) + Real.log (G₀.E.card : ℝ) := Real.exp_le_exp.mp hexp_le
      have havg_orig : ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e ≤
          2 * W + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_le (div_nonneg hρ_pos.le hk_pos.le)
        calc ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e
            = (ρ / (k : ℝ)) * ((∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ) := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hρ_pos]
          _ ≤ (ρ / (k : ℝ)) * ((k : ℝ) * (2 * W / ρ) + Real.log (G₀.E.card : ℝ)) := hmul
          _ = 2 * W + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := by
                field_simp [ne_of_gt hk_pos, ne_of_gt hρ_pos]
      have hL2_ge : (1 : ℝ) ≤ 4 * L ^ 2 := by nlinarith
      have hLm_ge : (1 : ℝ) ≤ 2 * Real.log ((G₀.E.card : ℝ) + 2) := by linarith
      have hlog_m : Real.log (G₀.E.card : ℝ) ≤ Real.log ((G₀.E.card : ℝ) + 2) :=
        Real.log_le_log hcard_pos (by linarith)
      have h2W_le : 2 * W ≤ 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        calc 2 * W
            = 2 * K₀ * L ^ 4 * 1 * 1 := by ring
          _ ≤ 2 * K₀ * L ^ 4 * (4 * L ^ 2) * (2 * Real.log ((G₀.E.card : ℝ) + 2)) := by
              have h4nn : 0 ≤ 2 * K₀ * L ^ 4 := mul_nonneg (by linarith) (pow_nonneg hL_pos.le 4)
              have h4L2_nn : 0 ≤ 4 * L ^ 2 := by positivity
              exact mul_le_mul
                (mul_le_mul_of_nonneg_left hL2_ge h4nn)
                hLm_ge zero_le_one (mul_nonneg h4nn h4L2_nn)
          _ = 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring
      have hρk_eq : ρ / (k : ℝ) = 10 * K₀ * L ^ 6 := by
        dsimp only [ρ, U]
        field_simp [ne_of_gt hk_pos]
      have hρ_term : (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) ≤
          10 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
        rw [hρk_eq]
        exact mul_le_mul_of_nonneg_left hlog_m (mul_nonneg (by linarith) (pow_nonneg hL_pos.le 6))
      have havg_eq : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e =
          ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hsurv := (h54 G₀ hG₀ hV₀ ℓ₀ (v j) hℓ₀ (fun f _ => hv_pos j f) (k : ℝ) hk_real
          Us hUs ℓ hℓ (fun f hf₀ hfG hn => by rw [hins_eq j] at hn; exact hℓ_orig f hf₀ hfG hn)).2.2.2.2.2.1
          e heG (by rw [hins_eq j]; exact hins)
        rw [hsurv]
      rw [havg_eq]
      have hnonneg : 0 ≤ L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) :=
        mul_nonneg (pow_nonneg hL_pos.le 6) hLm_pos.le
      calc ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e
          ≤ 2 * W + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := havg_orig
        _ ≤ 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) +
              10 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := add_le_add h2W_le hρ_term
        _ = (26 * K₀) * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by ring
        _ ≤ (26 * K₀ + 128) * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) :=
              mul_le_mul_of_nonneg_right (by linarith) hnonneg
        _ = (26 * K₀ + 128) * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring

end MinCostFlow.LSF
