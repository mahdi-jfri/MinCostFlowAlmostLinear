module

public import MinCostFlow.SparseCore.SparseCoreBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Graph growth, walk-lifting, and LSF/MWU metrics for `sparseCoreTool`

Building on `treeRunSeq_inv` (`SparseCoreBounds.lean`) and `CompLSFBridge` (`compLSF_mwu_bound`),
this file proves:
1. Graph-growth, `updateThreshold`, walk-lifting (`isWalk_map`), congestion (`econg ≤ vcong`),
   `batchesInserted`/`flatten`, and `CompLSF` weight-preservation utilities.
2. `sparseCore_lsf_guarantees`: LSF `Holds`, connected-graph root count, decremental forest, `wstr`
   immutability, and exact Lemma 5.5 MWU average stretch bound across `t ≤ τ` and `j < k`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Graph growth, `batchesInserted`, walk lifting, and congestion utilities -/

lemma applyUpdate_V_sub (G : MGraph) (u : Update) :
    G.V ⊆ (G.applyUpdate u).V := by
  cases u with
  | insert e v₁ v₂ => exact Finset.Subset.rfl
  | delete e => exact Finset.Subset.rfl
  | split _ v' _ _ => exact Finset.subset_insert v' G.V

lemma applyBatch_V_sub (G : MGraph) (U : List Update) :
    G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u rest ih =>
    simpa [MGraph.applyBatch] using
      Finset.Subset.trans (applyUpdate_V_sub G u) (ih (G.applyUpdate u))

lemma dyn_G_V_sub {τ : ℕ} {D : DynamicInstance} (hD : D.IsValid τ) :
    ∀ {t₁ t₂ : ℕ}, t₁ ≤ t₂ → t₂ ≤ τ → (D.G t₁).V ⊆ (D.G t₂).V := by
  intro t₁ t₂ h12 h2τ
  induction t₂ with
  | zero =>
    obtain rfl : t₁ = 0 := Nat.le_zero.mp h12
    exact Finset.Subset.rfl
  | succ s ih =>
    rcases Nat.eq_or_lt_of_le h12 with rfl | hlt
    · exact Finset.Subset.rfl
    · have hs := hD (s + 1) (Nat.succ_pos s) h2τ
      simp only [Nat.add_sub_cancel] at hs
      refine Finset.Subset.trans (ih (Nat.lt_succ_iff.mp hlt) (Nat.le_of_succ_le h2τ)) ?_
      rw [hs.2]
      exact applyBatch_V_sub (D.G s) (D.U (s + 1))

lemma dyn_G_n_mono {τ : ℕ} {D : DynamicInstance} (hD : D.IsValid τ)
    {t₁ t₂ : ℕ} (h12 : t₁ ≤ t₂) (h2τ : t₂ ≤ τ) : (D.G t₁).n ≤ (D.G t₂).n :=
  Finset.card_le_card (dyn_G_V_sub hD h12 h2τ)

lemma m_applyBatch_le_add_length (G : MGraph) (U : List Update) :
    (G.applyBatch U).m ≤ G.m + U.length := by
  have h := symmDiff_applyBatch_card_le G U
  have hsub : (G.applyBatch U).E ⊆ ((G.applyBatch U).E \ G.E) ∪ G.E := fun e he => by
    by_cases h' : e ∈ G.E <;> simp [he, h']
  have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  unfold MGraph.m at *
  omega

lemma dyn_G_m_le {τ : ℕ} {D : DynamicInstance} (hD : D.IsValid τ) :
    ∀ t ≤ τ, (D.G t).m ≤ (D.G 0).m + ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
  intro t ht
  induction t with
  | zero => simp
  | succ s ih =>
    have hs := hD (s + 1) (Nat.succ_pos s) ht
    simp only [Nat.add_sub_cancel] at hs
    have h1 := m_applyBatch_le_add_length (D.G s) (D.U (s + 1))
    rw [← hs.2] at h1
    have ih' := ih (Nat.le_of_succ_le ht)
    have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp)]
    omega

lemma q_sum_le_M_div_k {k M N τ : ℕ} (hk : 1 ≤ k) (hN : 1 ≤ N) {D : DynamicInstance}
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N) :
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      (M : ℝ) / (k : ℝ) := by
  have hlog3 : (21 / 20 : ℝ) < Real.log ((N : ℝ) + 2) := by
    refine lt_of_lt_of_le real_log_three_gt (Real.log_le_log (by norm_num) ?_)
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog2 : (1 : ℝ) ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := by nlinarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  refine le_trans hThresh ?_
  rw [SparseCoreTool.updateThreshold]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk_pos
    (le_mul_of_one_le_right (le_of_lt hk_pos) hlog2)

lemma q_sum_le_m0_div_k {k τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n) :
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      ((D.G 0).m : ℝ) / (k : ℝ) := by
  by_cases hm₀ : (D.G 0).m = 0
  · refine le_trans hThresh ?_
    rw [SparseCoreTool.updateThreshold, hm₀, Nat.cast_zero, zero_div, zero_div]
  · have hne₀ : (D.G 0).E.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hm₀)
    obtain ⟨e₀, he₀⟩ := hne₀
    have hn₀ : 1 ≤ (D.G 0).n := Finset.card_pos.mpr ⟨(D.G 0).tail e₀, (hG₀ e₀ he₀).1⟩
    exact q_sum_le_M_div_k hk hn₀ hThresh

lemma log_sq_le_m0_div_k_of_pos {k τ t : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (ht : t ≤ τ)
    (hpos : 1 ≤ ∑ s ∈ Finset.Icc 1 t, (D.U s).length)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k (D.G 0).m (D.G 0).n) :
    (k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 ≤ ((D.G 0).m : ℝ) := by
  have hlog_pos : (1 / 2 : ℝ) < Real.log (((D.G 0).n : ℝ) + 2) := half_lt_log_add_two (D.G 0).n
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hdenom_pos : 0 < (k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 := by positivity
  have hsub : Finset.Icc 1 t ⊆ Finset.Icc 1 τ := fun s hs => by
    simp only [Finset.mem_Icc] at hs ⊢
    exact ⟨hs.1, le_trans hs.2 ht⟩
  have h1 : (1 : ℝ) ≤ (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) := by
    exact_mod_cast le_trans hpos (Finset.sum_le_sum_of_subset hsub)
  have hle : (1 : ℝ) ≤ ((D.G 0).m : ℝ) / ((k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2) :=
    le_trans h1 (by simpa [SparseCoreTool.updateThreshold] using hThresh)
  exact (one_le_div hdenom_pos).mp hle

lemma not_mem_applyBatch_of_not_mem_of_not_inserts {G : MGraph} {U : List Update} {e : ℕ}
    (he : e ∉ G.E) (hni : ∀ u ∈ U, ¬ u.Inserts e) : e ∉ (G.applyBatch U).E := by
  induction U generalizing G with
  | nil => exact he
  | cons u rest ih =>
    refine ih ?_ (fun v hv => hni v (List.mem_cons_of_mem u hv))
    cases u with
    | insert e₀ _ _ =>
      have hne : e ≠ e₀ := fun heq => hni _ List.mem_cons_self heq.symm
      simpa [MGraph.applyUpdate, hne] using he
    | delete e₀ =>
      simp [MGraph.applyUpdate, he]
    | split _ _ _ _ =>
      simpa [MGraph.applyUpdate] using he

lemma not_delete_of_mem_applyBatch_of_not_inserts {G : MGraph} {U : List Update} {e : ℕ}
    (heG' : e ∈ (G.applyBatch U).E) (hni : ∀ u ∈ U, ¬ u.Inserts e) :
    ∀ u ∈ U, u ≠ .delete e := by
  induction U generalizing G with
  | nil => intro _ hu; cases hu
  | cons u rest ih =>
    intro v hv heq
    have hni_rest : ∀ w ∈ rest, ¬ w.Inserts e := fun w hw => hni w (List.mem_cons_of_mem u hw)
    rcases List.mem_cons.mp hv with rfl | hrest
    · subst heq
      apply not_mem_applyBatch_of_not_mem_of_not_inserts (G := G.applyUpdate (.delete e)) _ hni_rest heG'
      simp [MGraph.applyUpdate]
    · exact ih heG' hni_rest v hrest heq

lemma mem_foldl_updateInserted_iff_of_no_del_no_ins {U : List Update} {S : Finset ℕ} {e : ℕ}
    (hni : ∀ u ∈ U, ¬ u.Inserts e) (hnd : ∀ u ∈ U, u ≠ .delete e) :
    e ∈ U.foldl updateInserted S ↔ e ∈ S := by
  induction U generalizing S with
  | nil => rfl
  | cons u rest ih =>
    simp only [List.foldl_cons]
    rw [ih (fun w hw => hni w (List.mem_cons_of_mem u hw))
      (fun w hw => hnd w (List.mem_cons_of_mem u hw))]
    cases u with
    | insert e₀ _ _ =>
      have hne : e ≠ e₀ := fun heq => hni _ List.mem_cons_self heq.symm
      simp [updateInserted, hne]
    | delete e₀ =>
      have hne : e ≠ e₀ := fun heq => hnd _ List.mem_cons_self (by simp [heq])
      simp [updateInserted, hne]
    | split _ _ _ _ => rfl

lemma mem_foldl_updateInserted_iff_of_mem_applyBatch_no_ins
    {G : MGraph} {U : List Update} {S : Finset ℕ} {e : ℕ}
    (heG' : e ∈ (G.applyBatch U).E) (hni : ∀ u ∈ U, ¬ u.Inserts e) :
    e ∈ U.foldl updateInserted S ↔ e ∈ S :=
  mem_foldl_updateInserted_iff_of_no_del_no_ins hni
    (not_delete_of_mem_applyBatch_of_not_inserts heG' hni)

lemma mem_foldl_updateInserted_of_mem_applyBatch_inserts
    {G : MGraph} {U : List Update} {S : Finset ℕ} {u : Update} {e : ℕ}
    (heG' : e ∈ (G.applyBatch U).E) (hu : u ∈ U) (hi : u.Inserts e) :
    e ∈ U.foldl updateInserted S := by
  induction U generalizing G S u with
  | nil => cases hu
  | cons u₀ rest ih =>
    simp only [List.foldl_cons]
    by_cases hex : ∃ v ∈ rest, v.Inserts e
    · rcases hex with ⟨v, hv, hvi⟩
      exact ih heG' hv hvi
    · push Not at hex
      rw [mem_foldl_updateInserted_iff_of_mem_applyBatch_no_ins (G := G.applyUpdate u₀) heG' hex]
      rcases List.mem_cons.mp hu with rfl | hrest
      · cases u with
        | insert e₀ _ _ =>
          simp only [Update.Inserts] at hi
          subst hi
          simp [updateInserted]
        | delete _ => cases hi
        | split _ _ _ _ => cases hi
      · exact absurd hi (hex u hrest)

lemma not_inserts_of_not_mem_batchDeletes {G : MGraph} {U : List Update} {e : ℕ}
    (hBU : G.BatchIsValid U) (heG : e ∈ G.E) (hnd : e ∉ batchDeletes U) :
    ∀ u ∈ U, ¬ u.Inserts e := by
  induction U generalizing G with
  | nil => intro _ hu; cases hu
  | cons u rest ih =>
    rcases hBU with ⟨huV, hrestV⟩
    intro v hv hvi
    rcases List.mem_cons.mp hv with rfl | hrest
    · cases v with
      | insert e₀ _ _ =>
        simp only [Update.Inserts] at hvi; subst hvi
        exact huV.1 heG
      | delete _ => exact hvi
      | split _ _ _ _ => exact hvi
    · have hnd' : e ∉ batchDeletes rest := by
        intro hmem
        apply hnd
        rw [mem_batchDeletes_iff] at hmem ⊢
        rcases hmem with ⟨w, hw, hwe⟩
        exact ⟨w, List.mem_cons_of_mem u hw, hwe⟩
      have heG' : e ∈ (G.applyUpdate u).E := by
        cases u with
        | insert e₀ _ _ => exact Finset.mem_insert_of_mem heG
        | delete e₀ =>
          have hne : e ≠ e₀ := fun heq => hnd ((mem_batchDeletes_iff _ e).mpr ⟨_, List.mem_cons_self, by simp [heq]⟩)
          exact Finset.mem_erase.mpr ⟨hne, heG⟩
        | split _ _ _ _ => exact heG
      exact ih hrestV heG' hnd' v hrest hvi

lemma isWalk_map {H₁ H₂ : MGraph} (φ : ℕ → ℕ)
    (hmap : ∀ e ∈ H₁.E, e ∈ H₂.E ∧ φ (H₁.tail e) = H₂.tail e ∧ φ (H₁.head e) = H₂.head e) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H₁.IsWalk u v P → H₂.IsWalk (φ u) (φ v) P := by
  intro u v P hw
  induction hw with
  | nil u => exact MGraph.IsWalk.nil (φ u)
  | @cons u _ x P' hE hsrc _ ih =>
    rcases x with ⟨e_x, dir⟩
    obtain ⟨hE2, ht, hh⟩ := hmap e_x hE
    have hsrc2 : H₂.src (e_x, dir) = φ u := by
      unfold MGraph.src at hsrc ⊢
      cases dir <;> dsimp only at hsrc ⊢
      · simp only [Bool.false_eq_true, ↓reduceIte] at hsrc ⊢; rw [← hh, hsrc]
      · simp only [↓reduceIte] at hsrc ⊢; rw [← ht, hsrc]
    have hdst2 : φ (H₁.dst (e_x, dir)) = H₂.dst (e_x, dir) := by
      unfold MGraph.dst
      cases dir <;> simp_all
    rw [hdst2] at ih
    exact MGraph.IsWalk.cons hE2 hsrc2 ih

lemma walkEdges_subset_of_isWalk {H : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P → walkEdges P ⊆ H.E := by
  intro u v P hw
  induction hw with
  | nil => simp [walkEdges]
  | cons hE _ _ ih =>
    intro e he
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert] at he
    rcases he with rfl | he'
    · exact hE
    · exact ih (by simpa [walkEdges] using he')

lemma mem_walkVertices_of_mem_walkEdges {H : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)} {e' : ℕ},
      H.IsWalk u v P → e' ∈ walkEdges P → H.tail e' ∈ H.walkVertices u P := by
  intro u v P e' hw he'
  induction hw with
  | nil => simp [walkEdges] at he'
  | @cons u _ x P' hE hsrc _ ih =>
    rcases x with ⟨e_x, dir⟩
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert] at he'
    rcases he' with rfl | he_rest
    · simp only [MGraph.walkVertices, List.map_cons, List.mem_cons]
      cases dir
      · right; left
        unfold MGraph.dst; simp
      · left
        unfold MGraph.src at hsrc; simp at hsrc; exact hsrc
    · have ih' := ih (by simp only [walkEdges]; exact he_rest)
      exact List.mem_cons_of_mem u ih'

lemma walkFlow_eq_zero_of_not_mem {P : List (ℕ × Bool)} {e : ℕ}
    (he : e ∉ walkEdges P) : walkFlow P e = 0 := by
  unfold walkFlow
  rw [List.sum_eq_zero]
  intro y hy
  rw [List.mem_map] at hy
  rcases hy with ⟨x, hx, rfl⟩
  have hne : x.1 ≠ e := fun h => he (by
    unfold walkEdges
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨x, hx, h⟩)
  simp [hne]

lemma econgAt_le_vcongAt_tail {emb : Embedding} {G H : MGraph}
    (hEmb : emb.IsEmbedding G H) {eH : ℕ} (_heH : eH ∈ H.E) :
    emb.econgAt G (fun _ => 1) (fun _ => 1) eH ≤
      emb.vcongAt G H (fun _ => 1) (H.tail eH) := by
  unfold Embedding.econgAt Embedding.vcongAt
  rw [div_one]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => zero_le_one)
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, mem_walkVertices_of_mem_walkEdges (hEmb.2 e he.1) he.2⟩

lemma lsfHolds_mono_stretch {L : LSF} {G : MGraph} {ℓ : ℕ → ℝ} {σ₁ σ₂ : ℝ}
    (h : L.Holds G ℓ σ₁) (hσ : σ₁ ≤ σ₂) : L.Holds G ℓ σ₂ :=
  ⟨h.1, h.2.1, h.2.2.1, fun e he => ⟨(h.2.2.2 e he).1, le_trans (h.2.2.2 e he).2 hσ⟩⟩

lemma applyBatch_flatten (G : MGraph) (Us : List (List Update)) :
    G.applyBatch Us.flatten = Us.foldl MGraph.applyBatch G := by
  induction Us generalizing G with
  | nil => rfl
  | cons U rest ih =>
    simp only [List.flatten_cons, applyBatch_append, List.foldl_cons]
    exact ih (G.applyBatch U)

lemma batchIsValid_flatten (G : MGraph) (Us : List (List Update)) :
    G.BatchIsValid Us.flatten ↔ BatchesIsValid G Us := by
  induction Us generalizing G with
  | nil => simp [BatchesIsValid, MGraph.BatchIsValid]
  | cons U rest ih =>
    simp only [List.flatten_cons, batchIsValid_append, BatchesIsValid]
    rw [ih (G.applyBatch U)]

lemma foldl_updateInserted_flatten (Us : List (List Update)) (S : Finset ℕ) :
    Us.flatten.foldl updateInserted S = Us.foldl (fun acc U => U.foldl updateInserted acc) S := by
  induction Us generalizing S with
  | nil => rfl
  | cons U rest ih =>
    simp only [List.flatten_cons, List.foldl_append, List.foldl_cons]
    exact ih (U.foldl updateInserted S)

lemma treeRunSeq_cs_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (j : ℕ) :
    ∀ t : ℕ, (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs =
      compLSFBatch (initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j) (dynBatches D t).flatten := by
  intro t
  induction t with
  | zero => rfl
  | succ s ih =>
    change compLSFBatch (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs (D.U (s + 1)) = _
    rw [ih, compLSFBatch_dynBatches_succ]

lemma compLSFBatch_wstr_eq_init_of_not_inserted (cs₀ : CompLSFState)
    (hIns₀ : cs₀.insertedGlobal = ∅) (U : List Update) {e : ℕ}
    (he : e ∈ (compLSFBatch cs₀ U).G.E)
    (hni : e ∉ (compLSFBatch cs₀ U).insertedGlobal) :
    (compLSFBatch cs₀ U).wstrGlobal e = cs₀.wstrGlobal e := by
  rw [compLSFBatch_G] at he
  rw [compLSFBatch_insertedGlobal, hIns₀] at hni
  have hno := (applyBatch_not_inserted_of_not_foldl U cs₀.G ∅ e he hni).2.2
  exact compLSFBatch_wstr_of_not_inserts cs₀ U hno

/-! ## 2. LSF and MWU bridge (`sparseCore_lsf_guarantees`) -/

lemma sparseCore_lsf_guarantees_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let st := fun t => (T.runAt k M N D t).1
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t)
        (mwuK0 C_lsst * (k : ℝ) * (Real.log ((D.G t).n + 2 : ℝ)) ^ 6) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1)) ∧
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) ≤
        (26 * mwuK0 C_lsst + 128) *
          (Real.log ((D.G 0).n + 2 : ℝ)) ^ 6 * (Real.log ((D.G 0).m + 2 : ℝ))) := by
  classical
  intro T st m₀ n₀
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀
    let cs₀ := fun j => initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let cs := fun t j => compLSFBatch (cs₀ j) (dynBatches D t).flatten
    have hL_eq : ∀ t j, T.lsfs (st t) j = (cs t j).lsf := by
      intro t j
      have h1 := (hrun t).1
      have h3 := (hrun t).2.2.1 j
      dsimp only [T, sparseCoreTool, sparseCoreToolWith]
      change (st t).isNonempty = true at h1
      simp only [show (st t).isNonempty = true from h1, ↓reduceIte]
      rw [h3, treeRunSeq_cs_eq]
    have hBat : ∀ t ≤ τ, (D.G 0).BatchIsValid (dynBatches D t).flatten ∧
        (D.G 0).applyBatch (dynBatches D t).flatten = D.G t := by
      intro t ht
      have hba := applyBatch_dynBatches hD t ht
      exact ⟨(batchIsValid_flatten (D.G 0) (dynBatches D t)).mpr hba.2,
        (applyBatch_flatten (D.G 0) (dynBatches D t)).trans hba.1⟩
    have hI₀ : ∀ j, CompLSFInv C_lsst (D.ℓ 0) (cs₀ j) :=
      fun j => compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
    have hI_t : ∀ t ≤ τ, ∀ j, CompLSFInv C_lsst (D.ℓ 0) (cs t j) :=
      fun t ht j => compLSFBatch_inv (hI₀ j) (hBat t ht).1
    have hG_t : ∀ t ≤ τ, ∀ j, (cs t j).G = D.G t := fun t ht j => by
      dsimp only [cs, cs₀]
      rw [compLSFBatch_G]
      exact (hBat t ht).2
    have hIns_t : ∀ t j, (cs t j).insertedGlobal = batchesInserted (dynBatches D t) := by
      intro t j
      dsimp only [cs, cs₀]
      rw [compLSFBatch_insertedGlobal]
      exact foldl_updateInserted_flatten (dynBatches D t) ∅
    refine ⟨fun t ht j hj => ?_, fun t ht1 htτ j hj => ?_, fun t ht e he => ?_⟩
    · have hIt := hI_t t ht j
      have hGt := hG_t t ht j
      have hℓt : ∀ e ∈ (cs t j).G.E, 0 < D.ℓ t e := by rw [hGt]; exact hℓ t ht
      have hℓo : ∀ e ∈ (cs t j).G₀.E, e ∈ (cs t j).G.E → e ∉ (cs t j).insertedGlobal →
          D.ℓ t e = D.ℓ 0 e := by
        intro e _ he hni
        rw [hGt] at he
        rw [hIns_t t j] at hni
        exact length_eq_init_of_not_batchesInserted hD hLen t ht e he hni
      have hH := hIt.to_Holds hℓt hℓo
      have hcs₀_n : (cs t j).G₀.n = n₀ := by
        dsimp only [cs, cs₀]; rw [compLSFBatch_G₀]; rfl
      have hcs_k : (cs t j).k = k := by
        dsimp only [cs, cs₀]; rw [compLSFBatch_k]; rfl
      rw [hL_eq t j]
      refine ⟨?_, ?_⟩
      · rw [hGt, hcs₀_n, hcs_k] at hH
        refine lsfHolds_mono_stretch hH ?_
        have hK_eq : mwuK0 C_lsst = 6272 * max 1 C_lsst := rfl
        rw [← hK_eq]
        have hlog1 : (0 : ℝ) ≤ Real.log ((n₀ : ℝ) + 2) := (half_lt_log_add_two n₀).le.trans' (by norm_num)
        have hlog_le : Real.log ((n₀ : ℝ) + 2) ≤ Real.log ((D.G t).n + 2 : ℝ) :=
          Real.log_le_log (by positivity) (by
            have hn_mono : n₀ ≤ (D.G t).n := dyn_G_n_mono hD (Nat.zero_le t) ht
            linarith [show (n₀ : ℝ) ≤ (D.G t).n from by exact_mod_cast hn_mono])
        have hK₀ := (mwuK0_pos C_lsst).le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog1 hlog_le 6) (by positivity)
      · intro hConn
        have hRc := compLSF_connected_R_card_le oracle hLSST hG₀ hV₀ hConn hℓ₀ hk j (hBat t ht).1
        dsimp only at hRc
        change ((cs t j).RF.R.card : ℝ) ≤ 1 + 4 * ((D.G 0).m : ℝ) / (k : ℝ) +
          112 * ((dynBatches D t).flatten.length : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 at hRc
        have hfl_len : (dynBatches D t).flatten.length =
            ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
          rw [← totalUpdates_dynBatches D t, MinCostFlow.LSF.totalUpdates, List.length_flatten]
        rw [hfl_len, mul_div_assoc] at hRc
        have hlog_pos : (0 : ℝ) ≤ Real.log ((n₀ : ℝ) + 2) :=
          (half_lt_log_add_two n₀).le.trans' (by norm_num)
        have hm₀_nn : (0 : ℝ) ≤ (m₀ : ℝ) / (k : ℝ) := by positivity
        have hsum_nn : (0 : ℝ) ≤
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 := by positivity
        change ((cs t j).RF.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1)
        dsimp only [m₀, n₀]
        linarith
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      simp only [Nat.add_sub_cancel]
      have hs_le : s ≤ τ := Nat.le_of_lt htτ
      have hBV_U : (cs s j).G.BatchIsValid (D.U (s + 1)) := by
        rw [hG_t s hs_le j]
        exact (hD (s + 1) (Nat.succ_pos s) htτ).1
      have hstep : cs (s + 1) j = compLSFBatch (cs s j) (D.U (s + 1)) := by
        dsimp only [cs]; exact compLSFBatch_dynBatches_succ D (cs₀ j) s
      have hsp := compLSFBatch_step_props (D.U (s + 1)) (hI_t s hs_le j) hBV_U
      refine ⟨?_, ?_, ?_⟩
      · rw [hL_eq (s + 1) j, hL_eq s j, hstep]
        exact hsp.2.2.2.1
      · intro e _ _ hni
        rw [hL_eq (s + 1) j, hL_eq s j, hstep]
        exact compLSFBatch_wstr_of_not_inserts (cs s j) (D.U (s + 1)) hni
      · intro e het ⟨u, hu, hins⟩
        rw [hL_eq (s + 1) j]
        have hs := hD (s + 1) (Nat.succ_pos s) htτ
        simp only [Nat.add_sub_cancel] at hs
        have het' : e ∈ ((D.G s).applyBatch (D.U (s + 1))).E := hs.2 ▸ het
        have heins : e ∈ (cs (s + 1) j).insertedGlobal := by
          rw [hstep, compLSFBatch_insertedGlobal]
          exact mem_foldl_updateInserted_of_mem_applyBatch_inserts het' hu hins
        exact ((hI_t (s + 1) htτ j).hIns_wstr_R e heins).1
    · have hmwu := compLSF_mwu_bound oracle C_lsst hLSST (D.G 0) hG₀ hV₀ (D.ℓ 0) hℓ₀ k hk
        (dynBatches D t).flatten (hBat t ht).1 e ((hBat t ht).2.symm ▸ he)
      have hsum_eq : (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) =
          ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) * (cs t j).wstrGlobal e := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hL_eq t j, div_eq_mul_inv, one_div, mul_comm]
        rfl
      rw [hsum_eq]
      exact hmwu
  · have hVempty : ∀ t ≤ τ, ¬ (D.G t).V.Nonempty ∧ (D.G t).IsValid := by
      intro t ht
      induction t with
      | zero => exact ⟨hV₀, hG₀⟩
      | succ s ih =>
        obtain ⟨hnV, hGs⟩ := ih (Nat.le_of_succ_le ht)
        have hVs : (D.G s).V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnV
        have hEs : (D.G s).E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
          Finset.notMem_empty _ (hVs ▸ (hGs e he).1)
        have hs := hD (s + 1) (Nat.succ_pos s) ht
        simp only [Nat.add_sub_cancel] at hs
        have hUs_nil : D.U (s + 1) = [] := by
          cases hU : D.U (s + 1) with
          | nil => rfl
          | cons u rest =>
            exfalso
            have hu : (D.G s).UpdateIsValid u := (hU ▸ hs.1).1
            cases u with
            | insert _ u1 _ => exact Finset.notMem_empty u1 (hVs ▸ hu.2.1)
            | delete e => exact Finset.notMem_empty e (hEs ▸ hu)
            | split v _ _ _ => exact Finset.notMem_empty v (hVs ▸ hu.1)
        have hGeq : D.G (s + 1) = D.G s := by rw [hs.2, hUs_nil]; rfl
        rw [hGeq]
        exact ⟨hnV, hGs⟩
    have hL_empty : ∀ t j, T.lsfs (st t) j = emptyLSF := by
      intro t j
      have hfalse : (st t).isNonempty = false := by
        induction t with
        | zero => simp [st, SparseCoreTool.runAt, T, sparseCoreTool, sparseCoreToolWith, hV₀]
        | succ s ih =>
          change (T.update (st s) (D.U (s + 1)) (D.ℓ (s + 1)) (D.g (s + 1))).1.isNonempty = false
          dsimp only [T, sparseCoreTool, sparseCoreToolWith]
          split_ifs with h
          · exact absurd h (by rw [ih]; decide)
          · exact ih
      dsimp only [T, sparseCoreTool, sparseCoreToolWith]
      split_ifs with h
      · exact absurd h (by rw [hfalse]; decide)
      · rfl
    refine ⟨fun t ht j _ => ?_, fun t _ htτ j _ => ?_, fun t ht e he => ?_⟩
    · obtain ⟨hnV, hGt⟩ := hVempty t ht
      rw [hL_empty t j]
      refine ⟨emptyLSF_holds hnV hGt _ _, fun _ => ?_⟩
      simp only [emptyLSF, emptyGraph, Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ Real.log ((n₀ : ℝ) + 2) := (half_lt_log_add_two n₀).le.trans' (by norm_num)
      positivity
    · obtain ⟨hnV, hGt⟩ := hVempty t htτ
      have hEt : (D.G t).E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
        hnV ⟨(D.G t).tail e, (hGt e he).1⟩
      rw [hL_empty t j, hL_empty (t - 1) j]
      exact ⟨Finset.Subset.rfl, fun e he => absurd he (hEt ▸ Finset.notMem_empty e),
        fun e he => absurd he (hEt ▸ Finset.notMem_empty e)⟩
    · obtain ⟨hnV, hGt⟩ := hVempty t ht
      exact absurd he (Finset.eq_empty_iff_forall_notMem.mpr (fun e' he' =>
        hnV ⟨(D.G t).tail e', (hGt e' he').1⟩) ▸ Finset.notMem_empty e)

lemma sparseCore_lsf_guarantees
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ) :
    let T := sparseCoreTool oracle C_lsst L sparsify
    let st := fun t => (T.run k D t).1
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t)
        (mwuK0 C_lsst * (k : ℝ) * (Real.log ((D.G t).n + 2 : ℝ)) ^ 6) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1)) ∧
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) ≤
        (26 * mwuK0 C_lsst + 128) *
          (Real.log ((D.G 0).n + 2 : ℝ)) ^ 6 * (Real.log ((D.G 0).m + 2 : ℝ))) :=
  sparseCore_lsf_guarantees_at oracle C_lsst L sparsify hLSST k (D.G 0).m (D.G 0).n τ hk D hG₀ hD hℓ hLen

end

end MinCostFlow.SparseCore
