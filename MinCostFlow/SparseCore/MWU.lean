module

public import MinCostFlow.LSF.Lemma55
public import MinCostFlow.Chain.SparseCoreTool
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Online MWU Dynamic LSF Sequence (`Lemma 5.5` / `SparseCore` Foundation)

`MinCostFlow.LSF.Lemma55.lemma_5_5` states the existential guarantee over `S₀, S : ℕ → LSFState`
inside `∀ Us`. For `SparseCoreTool.init` and `update`, we need an online state construction whose
initial states `initLSFOnline` depend **only** on `(oracle, C_lsst, G₀, ℓ₀, k)` and whose per-batch
transition is `applyLSFBatch`.

This file exposes `mwuWeights`, `initLSFOnline`, `lemma_5_5_online`, and `DynamicInstance` batch
bridge helpers so both `CoreModel` (Lemma 5.14) and `SplitSpanner` / `Lemma517` (Lemma 5.17)
inherit `LSFInv`, `LSF.Holds`, `ToolMWU`, and `R.card` directly from `LSF.Lemma54`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

/-! ## Online MWU weight schedule and initial LSF states -/

/-- Base constant `K₀ = 6272 * max 1 C_lsst` from `LSF.Lemma54.lemma_5_4`. -/
def mwuK0 (C_lsst : ℝ) : ℝ :=
  6272 * max 1 C_lsst

lemma mwuK0_pos (C_lsst : ℝ) : 0 < mwuK0 C_lsst := by
  unfold mwuK0
  have : (1 : ℝ) ≤ max 1 C_lsst := le_max_left _ _
  linarith

/-- Per-edge upper bound `U = K₀ * k * log^6(G₀.n + 2)` from `LSF.Lemma55`. -/
noncomputable def mwuU (C_lsst : ℝ) (G₀ : MGraph) (k : ℕ) : ℝ :=
  mwuK0 C_lsst * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6

lemma mwuU_pos {C_lsst : ℝ} {G₀ : MGraph} {k : ℕ} (hk : 0 < k) : 0 < mwuU C_lsst G₀ k := by
  unfold mwuU
  have hL : (1 / 2 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := half_lt_log_add_two G₀.n
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  exact mul_pos (mul_pos (mwuK0_pos C_lsst) hk_pos) (pow_pos (by linarith) 6)

/-- MWU step scale `ρ = 10 * U` from `LSF.Lemma55`. -/
noncomputable def mwuRho (C_lsst : ℝ) (G₀ : MGraph) (k : ℕ) : ℝ :=
  10 * mwuU C_lsst G₀ k

lemma mwuRho_pos {C_lsst : ℝ} {G₀ : MGraph} {k : ℕ} (hk : 0 < k) : 0 < mwuRho C_lsst G₀ k := by
  unfold mwuRho
  exact mul_pos (by norm_num) (mwuU_pos hk)

/-- Online MWU weight vectors `v_j` on edges, identical to `LSF.Lemma55.mwuWeights`:
`v₀(e) = 1` and `v_{j+1}(e) = v_j(e) * exp(wstr_j(e) / ρ)`. -/
noncomputable def mwuWeights
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | j + 1, e =>
    let vj := mwuWeights oracle C_lsst G₀ ℓ₀ k j
    vj e * Real.exp ((initLSF oracle C_lsst G₀ ℓ₀ vj (k : ℝ)).wstr e / mwuRho C_lsst G₀ k)

lemma mwuWeights_pos (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) :
    ∀ j e, 0 < mwuWeights oracle C_lsst G₀ ℓ₀ k j e
  | 0, _ => zero_lt_one
  | j + 1, e =>
    mul_pos (mwuWeights_pos oracle C_lsst G₀ ℓ₀ k j e) (Real.exp_pos _)

lemma mwuWeights_eq_exp (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j e : ℕ) :
    mwuWeights oracle C_lsst G₀ ℓ₀ k j e =
      Real.exp ((∑ i ∈ Finset.range j,
        (initLSF oracle C_lsst G₀ ℓ₀ (mwuWeights oracle C_lsst G₀ ℓ₀ k i) (k : ℝ)).wstr e) /
          mwuRho C_lsst G₀ k) := by
  induction j with
  | zero => simp [mwuWeights]
  | succ j ih =>
    unfold mwuWeights
    dsimp only
    rw [ih, ← Real.exp_add, Finset.sum_range_succ, add_div]

/-- Online initial LSF state for branch `j`, depending **only** on `(oracle, C_lsst, G₀, ℓ₀, k, j)`. -/
noncomputable def initLSFOnline
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j : ℕ) : LSFState :=
  initLSF oracle C_lsst G₀ ℓ₀ (mwuWeights oracle C_lsst G₀ ℓ₀ k j) (k : ℝ)

/-! ## Helpers for `insertedEdges`, `DynamicInstance` batching, and MWU inequality -/

lemma applyLSFUpdate_insertedEdges (S : LSFState) (u : Update) :
    (applyLSFUpdate S u).insertedEdges = updateInserted S.insertedEdges u := by
  cases u <;> rfl

lemma applyLSFBatch_insertedEdges (U : List Update) (S : LSFState) :
    (applyLSFBatch S U).insertedEdges = U.foldl updateInserted S.insertedEdges := by
  induction U generalizing S with
  | nil => rfl
  | cons u U ih =>
    change (applyLSFBatch (applyLSFUpdate S u) U).insertedEdges = _
    rw [ih, applyLSFUpdate_insertedEdges]
    rfl

lemma applyLSFBatches_insertedEdges (Us : List (List Update)) (S : LSFState) :
    (applyLSFBatches S Us).insertedEdges = Us.foldl (List.foldl updateInserted) S.insertedEdges := by
  induction Us generalizing S with
  | nil => rfl
  | cons U Us ih =>
    change (applyLSFBatches (applyLSFBatch S U) Us).insertedEdges = _
    rw [ih, applyLSFBatch_insertedEdges]
    rfl

lemma applyUpdate_E_sub_inserted (G : MGraph) (I : Finset ℕ) (u : Update) :
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
  | split _ _ _ _ =>
    exact ⟨Finset.subset_union_left, fun _ he h => ⟨he, h⟩⟩

lemma applyBatch_E_surv_orig (G₀ : MGraph) :
    ∀ (U : List Update) (G : MGraph) (I : Finset ℕ),
      (∀ e ∈ G.E, e ∉ I → e ∈ G₀.E) →
      ∀ e ∈ (G.applyBatch U).E, e ∉ U.foldl updateInserted I → e ∈ G₀.E
  | [], _, _, h => fun e he hn => h e he hn
  | u :: U, G, I, h => fun e he hn => by
    change e ∈ ((G.applyUpdate u).applyBatch U).E at he
    change e ∉ U.foldl updateInserted (updateInserted I u) at hn
    exact applyBatch_E_surv_orig G₀ U (G.applyUpdate u) (updateInserted I u)
      (fun f hf hfn =>
        have hf' := (applyUpdate_E_sub_inserted G I u).2 f hf hfn
        h f hf'.1 hf'.2)
      e he hn

lemma batches_E_surv_orig (G₀ : MGraph) :
    ∀ (Us : List (List Update)) (G : MGraph) (I : Finset ℕ),
      (∀ e ∈ G.E, e ∉ I → e ∈ G₀.E) →
      ∀ e ∈ (Us.foldl MGraph.applyBatch G).E,
        e ∉ Us.foldl (List.foldl updateInserted) I → e ∈ G₀.E
  | [], _, _, h => fun e he hn => h e he hn
  | U :: Us, G, I, h => fun e he hn => by
    change e ∈ (Us.foldl MGraph.applyBatch (G.applyBatch U)).E at he
    change e ∉ Us.foldl (List.foldl updateInserted) (U.foldl updateInserted I) at hn
    exact batches_E_surv_orig G₀ Us (G.applyBatch U) (U.foldl updateInserted I)
      (applyBatch_E_surv_orig G₀ U G I h) e he hn

lemma applyBatch_not_inserted_of_not_foldl :
    ∀ (U : List Update) (G : MGraph) (I : Finset ℕ) (e : ℕ),
      e ∈ (G.applyBatch U).E → e ∉ U.foldl updateInserted I →
      e ∈ G.E ∧ e ∉ I ∧ ∀ u ∈ U, ¬ u.Inserts e
  | [], _, _, _, he, hn => ⟨he, hn, fun _ h => by cases h⟩
  | u :: U, G, I, e, he, hn => by
    change e ∈ ((G.applyUpdate u).applyBatch U).E at he
    change e ∉ U.foldl updateInserted (updateInserted I u) at hn
    obtain ⟨he1, hn1, hU⟩ :=
      applyBatch_not_inserted_of_not_foldl U (G.applyUpdate u) (updateInserted I u) e he hn
    obtain ⟨heG, hnI⟩ := (applyUpdate_E_sub_inserted G I u).2 e he1 hn1
    refine ⟨heG, hnI, fun w hw => ?_⟩
    rcases List.mem_cons.mp hw with rfl | hwU
    · intro hwi
      cases w with
      | insert e' a b =>
        change e' = e at hwi
        subst hwi
        exact hn1 (by simp [updateInserted])
      | delete _ => cases hwi
      | split _ _ _ _ => cases hwi
    · exact hU w hwU

private lemma exp_le_one_add_two_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have h1mx_pos : 0 < 1 - x := by linarith
  have hexp_neg : 1 - x ≤ Real.exp (-x) := by
    linarith [Real.add_one_le_exp (-x)]
  have hexp_le_inv : Real.exp x ≤ (1 - x)⁻¹ := by
    rw [← inv_inv (Real.exp x), ← Real.exp_neg]
    exact inv_anti₀ h1mx_pos hexp_neg
  have hprod : 1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
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
  have hnn : ∀ u v, 0 ≤ walkLength (safeLen G₀ ℓ₀) (MGraph.forestPath RF.F u v) := by
    intro u v
    unfold walkLength
    refine Finset.sum_nonneg (fun f _ => mul_nonneg (safeLen_nonneg hℓ₀ f) (abs_nonneg _))
  split_ifs
  · exact le_add_of_nonneg_right (div_nonneg (hnn _ _) he_pos.le)
  · exact le_add_of_nonneg_right (div_nonneg (add_nonneg (hnn _ _) (hnn _ _)) he_pos.le)

/-- Prefix list `[D.U 1, ..., D.U t]` corresponding to stages `1..t` of a `DynamicInstance`. -/
def dynBatches (D : DynamicInstance) (t : ℕ) : List (List Update) :=
  (List.range t).map (fun s => D.U (s + 1))

lemma dynBatches_succ (D : DynamicInstance) (t : ℕ) :
    dynBatches D (t + 1) = dynBatches D t ++ [D.U (t + 1)] := by
  simp [dynBatches, List.range_succ]

lemma applyLSFBatches_dyn_succ (D : DynamicInstance) (S₀ : LSFState) (t : ℕ) :
    applyLSFBatches S₀ (dynBatches D (t + 1)) =
      applyLSFBatch (applyLSFBatches S₀ (dynBatches D t)) (D.U (t + 1)) := by
  unfold applyLSFBatches
  rw [dynBatches_succ, List.foldl_append]
  rfl

lemma applyBatch_dynBatches {D : DynamicInstance} {τ : ℕ} (hD : D.IsValid τ) :
    ∀ t ≤ τ,
      (dynBatches D t).foldl MGraph.applyBatch (D.G 0) = D.G t ∧
      BatchesIsValid (D.G 0) (dynBatches D t) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨rfl, trivial⟩
  | succ t ih =>
    intro ht
    obtain ⟨hG_eq, hBV⟩ := ih (Nat.le_of_succ_le ht)
    have hstep := hD (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hstep
    have hBV_app : BatchesIsValid (D.G 0) (dynBatches D t ++ [D.U (t + 1)]) := by
      clear hG_eq
      suffices ∀ (Us : List (List Update)) (G : MGraph),
          BatchesIsValid G Us →
          (Us.foldl MGraph.applyBatch G).BatchIsValid (D.U (t + 1)) →
          BatchesIsValid G (Us ++ [D.U (t + 1)]) from
        this (dynBatches D t) (D.G 0) hBV
          (by rw [← (ih (Nat.le_of_succ_le ht)).1] at hstep; exact hstep.1)
      intro Us
      induction Us with
      | nil =>
        intro G _ hU
        exact ⟨hU, trivial⟩
      | cons U Us ihUs =>
        intro G hUs hU
        exact ⟨hUs.1, ihUs (G.applyBatch U) hUs.2 hU⟩
    refine ⟨?_, ?_⟩
    · rw [dynBatches_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hG_eq]
      exact hstep.2.symm
    · rwa [dynBatches_succ]

lemma totalUpdates_dynBatches (D : DynamicInstance) (t : ℕ) :
    totalUpdates (dynBatches D t) = ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
  induction t with
  | zero => simp [dynBatches, totalUpdates]
  | succ t ih =>
    rw [dynBatches_succ, totalUpdates, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]
    change totalUpdates (dynBatches D t) + (D.U (t + 1)).length = _
    rw [ih]
    have hIcc : Finset.Icc 1 (t + 1) = insert (t + 1) (Finset.Icc 1 t) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), add_comm]

lemma length_eq_init_of_not_batchesInserted {D : DynamicInstance} {τ : ℕ}
    (hD : D.IsValid τ) (hLen : LengthsStable D τ) :
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E, e ∉ batchesInserted (dynBatches D t) →
      D.ℓ t e = D.ℓ 0 e := by
  intro t
  induction t with
  | zero => intro _ _ _ _; rfl
  | succ t ih =>
    intro ht e he hnins
    have hstep := hD (t + 1) (Nat.succ_pos t) ht
    simp only [Nat.add_sub_cancel] at hstep
    rw [dynBatches_succ, batchesInserted, List.foldl_append, List.foldl_cons, List.foldl_nil] at hnins
    change e ∉ (D.U (t + 1)).foldl updateInserted (batchesInserted (dynBatches D t)) at hnins
    obtain ⟨hePrev, hnPrev, hNoLast⟩ := applyBatch_not_inserted_of_not_foldl
      (D.U (t + 1)) (D.G t) (batchesInserted (dynBatches D t)) e (hstep.2 ▸ he) hnins
    have hlen1 := hLen (t + 1) (Nat.succ_pos t) ht e he (by simpa using hePrev) hNoLast
    simp only [Nat.add_sub_cancel] at hlen1
    rw [hlen1, ih (Nat.le_of_succ_le ht) e hePrev hnPrev]

lemma applyLSFBatches_eq_dyn (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k : ℕ) (D : DynamicInstance) :
    ∀ t j,
      let S₀ := initLSFOnline oracle C_lsst G₀ ℓ₀ k j
      (applyLSFBatches S₀ (dynBatches D t)).insertedEdges = batchesInserted (dynBatches D t) := by
  intro t j
  dsimp only
  rw [applyLSFBatches_insertedEdges]
  rfl

/-! ## Online Lemma 5.5 (`lemma_5_5_online`) -/

open Classical in
/-- **Online Lemma 5.5**: for fixed `S₀ j := initLSFOnline oracle C_lsst G₀ ℓ₀ k j` (independent of
future batches `Us`), after any valid sequence of update batches `Us`, every `j < k` preserves
`LSFInv`, decremental `F`, `wstr` immutability, `LSF.Holds`, `R.card` growth, and
`S j := applyLSFBatches (S₀ j) Us` satisfies the MWU average stretch bound
`(∑ j < k, (1 / k) * (S j).wstr e) ≤ K_mwu * log^6(G₀.n + 2) * log(G₀.m + 2)`. -/
theorem lemma_5_5_online (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (k : ℕ) (hk : 1 ≤ k)
    (Us : List (List Update)) (hUs : BatchesIsValid G₀ Us)
    (ℓ : ℕ → ℝ)
    (hℓ : ∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e)
    (hℓ_orig : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
      e ∉ batchesInserted Us → ℓ e = ℓ₀ e) :
    let K₀ := mwuK0 C_lsst
    let K := 26 * K₀ + 128
    let S₀ : ℕ → LSFState := fun j => initLSFOnline oracle C_lsst G₀ ℓ₀ k j
    let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
    let G := Us.foldl MGraph.applyBatch G₀
    let q := totalUpdates Us
    (∀ j < k,
      LSFInv C_lsst ℓ₀ (S₀ j) ∧
      LSFInv C_lsst ℓ₀ (S j) ∧
      (S j).G = G ∧
      (S j).insertedEdges = batchesInserted Us ∧
      (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
      G.IsSubgraph (S j).RF.F ∧
      (S j).T.IsSubgraph (S j).RF.F ∧
      (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
      (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
      ((S₀ j).R.card : ℝ) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          4 * (G₀.E.card : ℝ) / (k : ℝ) ∧
      ((S j).R.card : ℝ) ≤ ((S₀ j).R.card : ℝ) +
        56 * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      (S j).lsf.Holds G ℓ (K₀ * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
      ((S j).W_init.card : ℝ) ≤
        6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          10 * (G₀.E.card : ℝ) / (k : ℝ) ∧
      ∀ W ∈ (S j).W_init, (G.vol (W \ (S j).R) : ℝ) ≤
        2240 * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
    ∀ e ∈ G.E,
      ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e ≤
        K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
  intro K₀ K S₀ S G q
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk_real
  have hL : (1 / 2 : ℝ) < Real.log ((G₀.n : ℝ) + 2) := half_lt_log_add_two G₀.n
  have hL_pos : 0 < Real.log ((G₀.n : ℝ) + 2) := by linarith
  have hLm : (1 / 2 : ℝ) < Real.log ((G₀.E.card : ℝ) + 2) := half_lt_log_add_two G₀.E.card
  have hLm_pos : 0 < Real.log ((G₀.E.card : ℝ) + 2) := by linarith
  let L := Real.log ((G₀.n : ℝ) + 2)
  let W := K₀ * L ^ 4
  let U := mwuU C_lsst G₀ k
  let ρ := mwuRho C_lsst G₀ k
  have hK₀_pos : 0 < K₀ := mwuK0_pos C_lsst
  have hU_pos : 0 < U := mwuU_pos (by omega)
  have hρ_pos : 0 < ρ := mwuRho_pos (by omega)
  let v := mwuWeights oracle C_lsst G₀ ℓ₀ k
  have hv_pos : ∀ j e, 0 < v j e := fun j e => mwuWeights_pos oracle C_lsst G₀ ℓ₀ k j e
  have hins_eq : ∀ j, (S j).insertedEdges = batchesInserted Us := fun j => by
    rw [show (S j).insertedEdges = (applyLSFBatches (S₀ j) Us).insertedEdges from rfl,
      applyLSFBatches_insertedEdges]
    rfl
  have hPerBranch : ∀ j,
      LSFInv C_lsst ℓ₀ (S₀ j) ∧
      LSFInv C_lsst ℓ₀ (S j) ∧
      (S j).G = G ∧
      (S j).insertedEdges = batchesInserted Us ∧
      (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
      G.IsSubgraph (S j).RF.F ∧
      (S j).T.IsSubgraph (S j).RF.F ∧
      (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
      (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
      ((S₀ j).R.card : ℝ) ≤
        (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          4 * (G₀.E.card : ℝ) / (k : ℝ) ∧
      ((S j).R.card : ℝ) ≤ ((S₀ j).R.card : ℝ) +
        56 * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
      (S j).lsf.Holds G ℓ (K₀ * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
      ((S j).W_init.card : ℝ) ≤
        6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          10 * (G₀.E.card : ℝ) / (k : ℝ) ∧
      ∀ Wp ∈ (S j).W_init, (G.vol (Wp \ (S j).R) : ℝ) ≤
        2240 * (k : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    intro j
    have hsp0 := initLSF_spec hLSST hG₀ hV₀ hℓ₀ (fun e _ => hv_pos j e) hk_real
    rcases hsp0 with ⟨hG₀₀', hG₀_eq', _, hk₀', _, hins₀', _, _, _, _, _, _, _, _, _, _, _, _,
      hR₀_card', _, _, _, hW₀_card', _, _, _, _⟩
    have hG₀₀ : (S₀ j).G₀ = G₀ := hG₀₀'
    have hG₀_eq : (S₀ j).G = G₀ := hG₀_eq'
    have hk₀ : (S₀ j).k = (k : ℝ) := hk₀'
    have hins₀ : (S₀ j).insertedEdges = ∅ := hins₀'
    have hI₀ : LSFInv C_lsst ℓ₀ (S₀ j) :=
      initLSF_inv hLSST hG₀ hV₀ hℓ₀ (fun e _ => hv_pos j e) hk_real
    have hbatches := applyLSFBatches_inv Us hI₀ (hG₀_eq.symm ▸ hUs)
    rcases hbatches with ⟨hI, hSG, hG₀_eq', hT₀_eq', hr₀_eq', hπ_eq', hk_eq', hW_eq, _, hFE_sub,
      hR_growth⟩
    have hSG' : (S j).G = G := hSG.trans (by rw [hG₀_eq])
    have hℓ_G : ∀ e ∈ G.E, 0 < ℓ e := hℓ
    have hℓ_S : ∀ e ∈ (S j).G.E, 0 < ℓ e := fun e he => hℓ_G e (hSG' ▸ he)
    have hℓ_orig_S : ∀ e ∈ (S j).G₀.E, e ∈ (S j).G.E → e ∉ (S j).insertedEdges → ℓ e = ℓ₀ e := by
      intro e he₀ heS he_nins
      have heG₀ : e ∈ G₀.E := by
        change e ∈ (applyLSFBatches (S₀ j) Us).G₀.E at he₀
        rw [hG₀_eq', hG₀₀] at he₀
        exact he₀
      have heG : e ∈ G.E := by rw [← hSG']; exact heS
      exact hℓ_orig e heG₀ heG (by rw [← hins_eq j]; exact he_nins)
    have hholds := hI.to_Holds hℓ_S hℓ_orig_S
    change (S j).lsf.Holds (S j).G ℓ (6272 * max 1 C_lsst * (S j).k * Real.log ((S j).G₀.n + 2) ^ 6) at hholds
    rw [hSG', hG₀_eq', hG₀₀, hk_eq', hk₀] at hholds
    have hw_ins : ∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1 := fun e he =>
      (hI.hins_wstr e he).1
    have hw_surv : ∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e := by
      intro e he he_nins
      have heS : e ∈ (S j).G.E := by rw [hSG']; exact he
      have hsurv := hI.hsurv_edge e heS he_nins
      have heG₀ : e ∈ (S₀ j).G.E := by
        rw [hG₀_eq, ← hG₀₀, ← hG₀_eq']
        exact hsurv.1
      have he₀_nins : e ∉ (S₀ j).insertedEdges := by rw [hins₀]; exact Finset.notMem_empty _
      have hsurv₀ := hI₀.hsurv_edge e heG₀ he₀_nins
      rw [hsurv.2.1, hsurv₀.2.1]
      have h_eq1 :
          levelStretchBound (S j).T₀ (S j).r₀ (S j).π (S j).G₀ (safeLen (S j).G₀ ℓ₀) e =
          levelStretchBound (S₀ j).T₀ (S₀ j).r₀ (S₀ j).π (S₀ j).G₀ (safeLen (S₀ j).G₀ ℓ₀) e := by
        dsimp only [S] at hT₀_eq' hr₀_eq' hπ_eq' hG₀_eq' ⊢
        rw [hT₀_eq', hr₀_eq', hπ_eq', hG₀_eq']
      have h_th_eq :
          wstrThresh C_lsst (S j).G₀.n (S j).k = wstrThresh C_lsst (S₀ j).G₀.n (S₀ j).k := by
        dsimp only [S] at hG₀_eq' hk_eq' ⊢
        rw [hG₀_eq', hk_eq']
      rw [h_eq1, h_th_eq]
    have hW_card' : ((S j).W_init.card : ℝ) ≤
        6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
          else ((components G₀).card : ℝ) * 28 * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
          10 * (G₀.E.card : ℝ) / (k : ℝ) := by
      change ((applyLSFBatches (S₀ j) Us).W_init.card : ℝ) ≤ _
      rw [hW_eq]
      exact hW₀_card'
    refine ⟨hI₀, hI, hSG', hins_eq j, hFE_sub, hholds.2.1.2.2.2.2, hholds.2.2.1, hw_ins, hw_surv,
      hR₀_card', by simpa only [hG₀₀] using hR_growth, hholds, hW_card', fun Wp hWp => ?_⟩
    have hwp := hI.hW_props Wp hWp
    have hsub_diff : Wp \ (S j).R ⊆ Wp \ (S j).R_orig := fun x hx =>
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
        fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)⟩
    have hdeg : ∀ x ∈ Wp \ (S j).R, (S j).G.deg x ≤ (S j).G₀.deg x := fun x hx =>
      hI.hdeg_le x (hwp.2.1 (Finset.mem_sdiff.mp hx).1) (Finset.mem_sdiff.mp hx).2
    have hG₀_full : (S j).G₀ = G₀ := by dsimp only [S]; exact hG₀_eq'.trans hG₀₀
    have hvol_le : G.vol (Wp \ (S j).R) ≤ G₀.vol (Wp \ (S j).R_orig) := by
      rw [← hSG', ← hG₀_full]
      unfold MGraph.vol
      exact (Finset.sum_le_sum hdeg).trans (Finset.sum_le_sum_of_subset hsub_diff)
    have hcast : (G.vol (Wp \ (S j).R) : ℝ) ≤ (G₀.vol (Wp \ (S j).R_orig) : ℝ) :=
      Nat.cast_le.mpr hvol_le
    have hbd := hwp.2.2.2
    have hk_full : (S j).k = (k : ℝ) := by dsimp only [S]; exact hk_eq'.trans hk₀
    rw [hG₀_full, hk_full] at hbd
    exact hcast.trans hbd
  refine ⟨fun j _ => hPerBranch j, ?_⟩
  have hsafe_pos : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
    rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
  have hw₀_bounds : ∀ j e, e ∈ G₀.E → 1 ≤ (S₀ j).wstr e ∧ (S₀ j).wstr e ≤ U := by
    intro j e he
    have hI₀ := (hPerBranch j).1
    have hholds0 := hI₀.to_Holds hsafe_pos (fun f hf _ _ => safeLen_eq_of_mem ℓ₀ hf)
    have hGeq : (S₀ j).G = G₀ :=
      (initLSF_spec hLSST hG₀ hV₀ hℓ₀ (fun f _ => hv_pos j f) hk_real).2.1
    have hG₀eq : (S₀ j).G₀ = G₀ :=
      (initLSF_spec hLSST hG₀ hV₀ hℓ₀ (fun f _ => hv_pos j f) hk_real).1
    have hkeq : (S₀ j).k = (k : ℝ) :=
      (initLSF_spec hLSST hG₀ hV₀ hℓ₀ (fun f _ => hv_pos j f) hk_real).2.2.2.1
    rw [hGeq, hG₀eq, hkeq] at hholds0
    have hstr := hholds0.2.2.2 e he
    exact ⟨(one_le_stretch_safeLen hℓ₀ he).trans hstr.1, hstr.2⟩
  have hw₀_sum : ∀ j, ∑ e ∈ G₀.E, v j e * (S₀ j).wstr e ≤ W * G₀.norm1 (v j) := by
    intro j
    have hsp0 := initLSF_spec hLSST hG₀ hV₀ hℓ₀ (fun e _ => hv_pos j e) hk_real
    have hbd := hsp0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h224_le : 224 * max 1 C_lsst ≤ K₀ := by unfold K₀ mwuK0; linarith [le_max_left (1 : ℝ) C_lsst]
    have hnorm_nn : 0 ≤ G₀.norm1 (v j) := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h224_le hnorm_nn) (pow_nonneg hL_pos.le 4)
    refine hbd.trans (hmul.trans_eq (by dsimp only [W]; ring))
  have hnorm1_eq : ∀ j, G₀.norm1 (v j) = ∑ e ∈ G₀.E, v j e := fun j =>
    Finset.sum_congr rfl (fun e _ => abs_of_pos (hv_pos j e))
  have hnorm1_step : ∀ j, G₀.norm1 (v (j + 1)) ≤ Real.exp (2 * W / ρ) * G₀.norm1 (v j) := by
    intro j
    have hpt : ∀ e ∈ G₀.E, v (j + 1) e ≤ v j e + (2 / ρ) * (v j e * (S₀ j).wstr e) := by
      intro e he
      have hb := hw₀_bounds j e he
      have hx0 : 0 ≤ (S₀ j).wstr e / ρ := div_nonneg (by linarith [hb.1]) hρ_pos.le
      have hx1 : (S₀ j).wstr e / ρ ≤ 1 / 2 := by
        rw [div_le_iff₀ hρ_pos]
        dsimp only [ρ, mwuRho]
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
        have hse := (hPerBranch j).2.2.2.2.2.2.2.1 e ((hins_eq j).symm ▸ hins)
        rw [hse, mul_one]
      rw [hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [ne_of_gt hk_pos]
    rw [havg_one]
    have hpow6 : (1 / 64 : ℝ) ≤ L ^ 6 := by
      have hsq : (1 / 2 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL.le 6
      linarith [show (1 / 2 : ℝ) ^ 6 = 1 / 64 by norm_num]
    have h1_le_128 : (1 : ℝ) ≤ 128 * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by
      nlinarith [mul_le_mul hpow6 hLm.le (by norm_num) (pow_nonneg hL_pos.le 6)]
    have hK128 : (128 : ℝ) ≤ K := by dsimp only [K]; linarith
    have hnonneg : 0 ≤ L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) :=
      mul_nonneg (pow_nonneg hL_pos.le 6) hLm_pos.le
    calc (1 : ℝ)
        ≤ 128 * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := h1_le_128
      _ ≤ K * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := mul_le_mul_of_nonneg_right hK128 hnonneg
      _ = K * Real.log ((G₀.n : ℝ) + 2) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring
  · have heG₀ : e ∈ G₀.E :=
      batches_E_surv_orig G₀ Us G₀ ∅ (fun _ hf _ => hf) e heG hins
    have hcard_pos : (0 : ℝ) < (G₀.E.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨e, heG₀⟩
    have hle_norm : v k e ≤ G₀.norm1 (v k) := by
      rw [hnorm1_eq k]
      exact Finset.single_le_sum (fun f _ => (hv_pos k f).le) heG₀
    have hexp_le : Real.exp ((∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ) ≤
        Real.exp ((k : ℝ) * (2 * W / ρ) + Real.log (G₀.E.card : ℝ)) := by
      have hv_eq : Real.exp ((∑ j ∈ Finset.range k, (S₀ j).wstr e) / ρ) = v k e :=
        (mwuWeights_eq_exp oracle C_lsst G₀ ℓ₀ k k e).symm
      rw [hv_eq, Real.exp_add, Real.exp_log hcard_pos]
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
      dsimp only [ρ, mwuRho, U, mwuU, K₀, L]
      field_simp [ne_of_gt hk_pos]
    have hρ_term : (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) ≤
        10 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by
      rw [hρk_eq]
      exact mul_le_mul_of_nonneg_left hlog_m (mul_nonneg (by linarith) (pow_nonneg hL_pos.le 6))
    have havg_eq : ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (S j).wstr e =
        ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hsurv := (hPerBranch j).2.2.2.2.2.2.2.2.1 e heG ((hins_eq j).symm ▸ hins)
      rw [hsurv]
    rw [havg_eq]
    have hnonneg : 0 ≤ L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) :=
      mul_nonneg (pow_nonneg hL_pos.le 6) hLm_pos.le
    calc ((1 : ℝ) / (k : ℝ)) * ∑ j ∈ Finset.range k, (S₀ j).wstr e
        ≤ 2 * W + (ρ / (k : ℝ)) * Real.log (G₀.E.card : ℝ) := havg_orig
      _ ≤ 16 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) +
            10 * K₀ * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := add_le_add h2W_le hρ_term
      _ = (26 * K₀) * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by ring
      _ ≤ K * (L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) hnonneg
      _ = K * L ^ 6 * Real.log ((G₀.E.card : ℝ) + 2) := by ring

end MinCostFlow.SparseCore
