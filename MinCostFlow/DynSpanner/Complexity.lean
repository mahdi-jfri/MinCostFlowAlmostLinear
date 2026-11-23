module

public import MinCostFlow.DynSpanner.ComplexitySum

import MinCostFlow.DynSpanner.Potential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complexity, recourse, and Theorem 8.2 for the dynamic spanner

This file formalizes [chen2022maximum] Lemma 5.9 (arXiv:2203.00671v2, Section 5.1) adapted to the
deterministic static sparsifier of Theorem 8.1, and derives Theorem 8.2
(*A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*, arXiv:2309.16629v1, page 39).

Main results:
* `sparsity_H`: initial spanner sparsity `Õ(|V(G₀)| γ_ℓ)` and stage-`k` spanner sparsity
  `O((L + 1) K_s n_k γ_ℓ Λ_s)`.
* `lemma_5_9`: amortized bounds along any prefix `[0, T)` of a valid sequence of deletions and
  vertex splits for inserts, deletes, total recourse `∑ |U_H|`, encoding recourse `∑ Enc(U_H)` (via
  Lemma 2.1's `degPot`), re-embedded set sizes `∑ |D|`, and total operation cost.
* `theorem_8_2_general` and `theorem_8_2`: batched Theorem 8.2 for `q = phaseBase (G₀.n + splitBound) L`,
  establishing Items 1–3, initialization time, and amortized update time while separating `|U^{(t)}|`
  recourse (independent of `Δ_max(G)`) from `Enc(U^{(t)})` runtime.
-/

namespace MinCostFlow.DynSpanner

section Helpers

private theorem touchedVertices_card_le_two (G : MGraph) (u : Update) (hds : isDelOrSplit u) :
    (touchedVertices G u).card ≤ 2 := by
  cases u with
  | insert _ _ _ => exact hds.elim
  | delete e =>
    simpa [touchedVertices] using Finset.card_insert_le (G.tail e) {G.head e}
  | split v v' _ _ =>
    simpa [touchedVertices] using Finset.card_insert_le v {v'}

private theorem allTouched_card_le :
    ∀ (xs : List Update) (G : MGraph),
      (∀ u ∈ xs, isDelOrSplit u) → (allTouched G xs).card ≤ 2 * xs.length
  | [], _, _ => by simp [allTouched]
  | u :: xs, G, hds => by
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ xs, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have ih := allTouched_card_le xs (G.applyUpdate u) hds'
    have hu := touchedVertices_card_le_two G u hdu
    have hle := Finset.card_union_le (touchedVertices G u) (allTouched (G.applyUpdate u) xs)
    simp only [allTouched, List.length_cons] at hle ⊢
    omega

private theorem log_mono_nm {n₁ n₂ m₁ m₂ : ℕ} (hn : n₁ ≤ n₂) (hm : m₁ ≤ m₂) (p : ℕ) :
    (1 + Real.log ((n₁ : ℝ) + (m₁ : ℝ) + 2)) ^ p ≤
      (1 + Real.log ((n₂ : ℝ) + (m₂ : ℝ) + 2)) ^ p := by
  have h1 : (1 : ℝ) ≤ (n₁ : ℝ) + (m₁ : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) m₁]
  have harg : (n₁ : ℝ) + (m₁ : ℝ) + 2 ≤ (n₂ : ℝ) + (m₂ : ℝ) + 2 := by gcongr
  have hpos : (0 : ℝ) < (n₁ : ℝ) + (m₁ : ℝ) + 2 := by linarith
  have hlog_le : 1 + Real.log ((n₁ : ℝ) + (m₁ : ℝ) + 2) ≤
      1 + Real.log ((n₂ : ℝ) + (m₂ : ℝ) + 2) := by
    linarith [Real.log_le_log hpos harg]
  exact pow_le_pow_left₀ (by linarith [Real.log_nonneg h1]) hlog_le p

private theorem restrictUpdate_length_le_one (u : Update) (H : MGraph) :
    (restrictUpdate u H).length ≤ 1 := by
  cases u with
  | delete e => by_cases he : e ∈ H.E <;> simp [restrictUpdate, he]
  | insert _ _ _ => simp [restrictUpdate]
  | split _ _ _ _ => simp [restrictUpdate]

private theorem map_delete_counts (xs : List ℕ) :
    (xs.map Update.delete).length = xs.length ∧
    batchDeleteCount (xs.map Update.delete) = xs.length ∧
    batchInsertCount (xs.map Update.delete) = 0 := by
  induction xs with
  | nil => simp [batchDeleteCount, batchInsertCount]
  | cons x xs ih =>
    have h1 : batchDeleteCount (Update.delete x :: xs.map Update.delete) =
        1 + batchDeleteCount (xs.map Update.delete) := by
      simp [batchDeleteCount, Nat.add_comm]
    have h2 : batchInsertCount (Update.delete x :: xs.map Update.delete) =
        batchInsertCount (xs.map Update.delete) := by
      simp [batchInsertCount]
    refine ⟨by simp [ih.1], ?_, ?_⟩
    · rw [List.map_cons, h1, ih.2.1, List.length_cons]; omega
    · rw [List.map_cons, h2, ih.2.2]

private theorem map_insert_counts (xs : List ℕ) (t h : ℕ → ℕ) :
    (xs.map fun e => Update.insert e (t e) (h e)).length = xs.length ∧
    batchInsertCount (xs.map fun e => Update.insert e (t e) (h e)) = xs.length ∧
    batchDeleteCount (xs.map fun e => Update.insert e (t e) (h e)) = 0 := by
  induction xs with
  | nil => simp [batchInsertCount, batchDeleteCount]
  | cons x xs ih =>
    have h1 : batchInsertCount (Update.insert x (t x) (h x) :: xs.map fun e => Update.insert e (t e) (h e)) =
        1 + batchInsertCount (xs.map fun e => Update.insert e (t e) (h e)) := by
      simp [batchInsertCount, Nat.add_comm]
    have h2 : batchDeleteCount (Update.insert x (t x) (h x) :: xs.map fun e => Update.insert e (t e) (h e)) =
        batchDeleteCount (xs.map fun e => Update.insert e (t e) (h e)) := by
      simp [batchDeleteCount]
    refine ⟨by simp [ih.1], ?_, ?_⟩
    · rw [List.map_cons, h1, ih.2.1, List.length_cons]; omega
    · rw [List.map_cons, h2, ih.2.2]

private theorem uh_counts_aux (H : MGraph) (u : Update) (X : Finset ℕ) (t h : ℕ → ℕ) :
    let H_mid := H.applyBatch (restrictUpdate u H)
    let uh := restrictUpdate u H ++ ((H_mid.E \ X).sort (· ≤ ·)).map Update.delete ++
      ((X \ H_mid.E).sort (· ≤ ·)).map (fun e => Update.insert e (t e) (h e))
    uh.length ≤ 1 + batchDeleteCount uh + batchInsertCount uh ∧
    batchDeleteCount uh ≤ 1 + H.E.card := by
  intro H_mid uh
  have hPrefLen : (restrictUpdate u H).length ≤ 1 := restrictUpdate_length_le_one u H
  have hPrefDel : batchDeleteCount (restrictUpdate u H) ≤ 1 := (restrictUpdate_counts H u).2.1
  have hHmid_card : H_mid.E.card ≤ H.E.card := by
    cases u with
    | insert _ _ _ => simp [H_mid, restrictUpdate, MGraph.applyBatch]
    | delete e =>
      by_cases he : e ∈ H.E
      · simp only [H_mid, restrictUpdate, he, ↓reduceIte, MGraph.applyBatch, MGraph.applyUpdate,
          List.foldl_cons, List.foldl_nil]
        exact Finset.card_erase_le
      · simp [H_mid, restrictUpdate, he, MGraph.applyBatch]
    | split v v' St Sh =>
      simp [H_mid, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]
  obtain ⟨hDl, hDd, _⟩ := map_delete_counts ((H_mid.E \ X).sort (· ≤ ·))
  obtain ⟨hIl, hIi, hId⟩ := map_insert_counts ((X \ H_mid.E).sort (· ≤ ·)) t h
  have hcard_del : ((H_mid.E \ X).sort (· ≤ ·)).length ≤ H.E.card := by
    rw [Finset.length_sort]
    exact le_trans (Finset.card_le_card Finset.sdiff_subset) hHmid_card
  simp only [uh, List.length_append, batchDeleteCount_append, batchInsertCount_append,
    hDl, hDd, hIl, hIi, hId]
  omega

private theorem step_UH_counts {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    let res := step st u sparsify
    res.UH.length ≤ 1 + batchDeleteCount res.UH + batchInsertCount res.UH ∧
    batchDeleteCount res.UH ≤ 1 + st.H.E.card := by
  dsimp only [step]
  split_ifs
  · exact uh_counts_aux st.H u _ _ _
  · exact uh_counts_aux st.H u _ _ _
  · exact uh_counts_aux st.H u _ _ _

private theorem sum_range_stepOut_UH_counts {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us : List Update) :
    ∀ T ≤ us.length,
      ∑ k ∈ Finset.range T, (runStepOut (L := L) G₀ q sparsify us k).UH.length ≤
        T + ∑ k ∈ Finset.range T, batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH +
        ∑ k ∈ Finset.range T, batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH
  | 0, _ => by simp
  | T + 1, hT => by
    have ih := sum_range_stepOut_UH_counts (L := L) G₀ q sparsify us T (Nat.le_of_succ_le hT)
    have hu : us[T]? = some (us[T]'hT) := List.getElem?_eq_getElem hT
    have hstep := (step_UH_counts (runState (L := L) G₀ q sparsify us T) (us[T]'hT) sparsify).1
    have hres : runStepOut (L := L) G₀ q sparsify us T =
        step (runState (L := L) G₀ q sparsify us T) (us[T]'hT) sparsify := by
      simp [runStepOut, hu]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hres]
    omega

private theorem step_rebuild_recourse_sharp {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj_pos : 0 < chooseLevel L q (k + 1)) :
    let res := runStepOut (L := L) G₀ q sparsify us k
    let G' := G₀.applyBatch (us.take (k + 1))
    let j := chooseLevel L q (k + 1)
    let sLen := k + 1 - lastRebuild q L (j - 1) (k + 1)
    let Λ_s := (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    (batchInsertCount res.UH : ℝ) ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * Λ_s ∧
    (res.D.card : ℝ) ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * Λ_s * (lenBound P.γ_ℓ (j - 1) + 1) := by
  intro res G' j sLen Λ_s
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hu_some : us[k]? = some (us[k]'hk) := List.getElem?_eq_getElem hk
  set u := us[k]'hk
  set st := runState (L := L) G₀ q sparsify us k
  have hres_eq : res = step st u sparsify := by simp [res, runStepOut, hu_some, st, u]
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (Nat.le_of_lt hk)).1
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hj0 : chooseLevel L q (k + 1) ≠ 0 := Nat.ne_of_gt hj_pos
  obtain ⟨hBV_k1, hds_k1, _⟩ := batchIsValid_take us G₀ (k + 1) hBV hds
  obtain ⟨hBV_k, hds_k, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_valid, hdu⟩ := hU_valid u hu_some
  have htake_succ : us.take (k + 1) = us.take k ++ [u] := take_succ_of_getElem? hu_some
  set Gk := G₀.applyBatch (us.take k)
  have hVGk : Gk.IsValid := (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).1
  have hG'_eq : G' = Gk.applyUpdate u := by
    dsimp only [G', Gk]; rw [htake_succ, applyBatch_append]; rfl
  have hinv_k1 := batch_delOrSplit_invariants (us.take (k + 1)) G₀ hVG₀ hBV_k1 hds_k1
  have hVG' : G'.IsValid := hinv_k1.1
  have hG'm_le0 : G'.m ≤ G₀.m := Finset.card_le_card hinv_k1.2.1
  have hG'E_sub : G'.E ⊆ Gk.E := by
    have h1 := (batch_delOrSplit_invariants [u] Gk hVGk ⟨hu_valid, True.intro⟩
      (fun x hx => by simp at hx; rwa [hx])).2.1
    simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil] at h1
    rwa [← hG'_eq] at h1
  set r := lastRebuild q L (j - 1) (k + 1)
  have hr_not_dvd : ¬ phasePeriod q L (j - 1) ∣ k + 1 := fun hdvd => by
    have := (chooseLevel_le_iff_dvd hq (le_trans (Nat.sub_le j 1) hj_le)).mpr hdvd
    omega
  have hr_eq_k : r = lastRebuild q L (j - 1) k := lastRebuild_eq_of_not_dvd hr_not_dvd
  have hr_le_k : r ≤ k := by rw [hr_eq_k]; exact lastRebuild_le q L (j - 1) k
  have hInv_r := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds r (le_trans hr_le_k (Nat.le_of_lt hk))).1
  have hr_ch : chooseLevel L q r ≤ j - 1 :=
    lastRebuild_chooseLevel_le hq (le_trans (Nat.sub_le j 1) hj_le)
  set st_r := runState (L := L) G₀ q sparsify us r
  set G_r := G₀.applyBatch (us.take r)
  set delta := (us.take (k + 1)).drop r
  have htake_k1 : us.take (k + 1) = us.take r ++ delta := by
    have h1 : (us.take (k + 1)).take r = us.take r := by
      rw [List.take_take, min_eq_left (le_trans hr_le_k (Nat.le_succ k))]
    rw [← h1]; exact (List.take_append_drop r (us.take (k + 1))).symm
  have hBV_split := (batchIsValid_append G₀ (us.take r) delta).mp (htake_k1 ▸ hBV_k1)
  have hBV_r : G₀.BatchIsValid (us.take r) := hBV_split.1
  have hBV_d : G_r.BatchIsValid delta := hBV_split.2
  have hds_d : ∀ x ∈ delta, isDelOrSplit x := fun x hx =>
    hds_k1 x (by rw [htake_k1]; exact List.mem_append_right _ hx)
  have hds_r : ∀ x ∈ us.take r, isDelOrSplit x := fun x hx =>
    hds_k1 x (by rw [htake_k1]; exact List.mem_append_left _ hx)
  have hinv_r_d := batch_delOrSplit_invariants (us.take r) G₀ hVG₀ hBV_r hds_r
  have hVG_r : G_r.IsValid := hinv_r_d.1
  have hG_r_m : G_r.m ≤ mMax := le_trans (Finset.card_le_card hinv_r_d.2.1) hGm₀
  have hG'_delta : G' = G_r.applyBatch delta := by
    dsimp only [G', G_r]; rw [htake_k1, applyBatch_append]
  have hinv_d := batch_delOrSplit_invariants delta G_r hVG_r hBV_d hds_d
  have hrk_eq_lt : ∀ {m : ℕ}, m < j →
      lastRebuild q L m (k + 1) = lastRebuild q L m k ∧
      lastRebuild q L m r = lastRebuild q L m k := fun {m} hm => by
    have hm_le : m ≤ j - 1 := Nat.le_pred_of_lt hm
    have h1 : lastRebuild q L m (k + 1) = lastRebuild q L m k := by
      refine lastRebuild_eq_of_not_dvd fun hdvd => hr_not_dvd ?_
      exact dvd_trans (phasePeriod_dvd_of_le hm_le (le_trans (Nat.sub_le j 1) hj_le)) hdvd
    have hmr_le : lastRebuild q L m k ≤ r := by
      rw [hr_eq_k]
      exact lastRebuild_mono_level hq hm_le (le_trans (Nat.sub_le j 1) hj_le)
    exact ⟨h1, lastRebuild_idempotent_le hq hmr_le hr_le_k⟩
  set H_mid : Fin (L + 1) → MGraph := fun i => (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  have hH_mid_props : ∀ i : Fin (L + 1),
      G'.IsSubgraph (H_mid i) ∧ (H_mid i).V = G'.V ∧ (H_mid i).E = (st.H_level i).E ∩ G'.E :=
    fun i => by
      obtain ⟨_, h1, h2, h3, _, _⟩ :=
        isSubgraph_restrictUpdate (hk_inv.H_level_sub i) (hk_inv.H_level_V i) hu_valid hdu
      exact ⟨hG'_eq ▸ h1, hG'_eq ▸ h2, hG'_eq ▸ h3⟩
  set H_lt := unionGraphLt G' H_mid j
  set H_lt_r := unionGraphLt G_r st_r.H_level j
  have hSub_lt_r : G_r.IsSubgraph H_lt_r := by
    refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    intro e he
    simp only [H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at he
    rcases he with ⟨i, _, hei⟩
    exact (hInv_r.H_level_sub i).2.1 hei
  have hHLt_E : H_lt.E = H_lt_r.E ∩ G'.E := by
    ext e
    simp only [H_lt, H_lt_r, unionGraphLt, unionEdgesLt, Finset.mem_inter, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hij, hei⟩
      rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2] at hei
      have hei' := Finset.mem_inter.mp hei
      have hei1 := Finset.mem_inter.mp hei'.1
      have hei_r : e ∈ (st_r.H_level i).E := by
        rw [hInv_r.H_level_E i]
        exact Finset.mem_inter.mpr ⟨hei1.1, hinv_d.2.1 (hG'_delta ▸ hei'.2)⟩
      exact ⟨⟨i, hij, hei_r⟩, hei'.2⟩
    · rintro ⟨⟨i, hij, hei_r⟩, heG'⟩
      refine ⟨i, hij, ?_⟩
      rw [(hH_mid_props i).2.2, hk_inv.H_level_E i, ← (hrk_eq_lt hij).2]
      rw [hInv_r.H_level_E i, Finset.mem_inter] at hei_r
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hei_r.1, hG'E_sub heG'⟩, heG'⟩
  have hSub_lt : G'.IsSubgraph H_lt := ⟨Finset.Subset.rfl, hHLt_E ▸ Finset.inter_subset_right,
    fun _ _ => ⟨rfl, rfl⟩⟩
  set inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
  set piLt_mid : Embedding := piLtFrom st.Pi_level inDom_mid j
  set S_prev : Finset ℕ := st.S_level ⟨j - 1, by omega⟩ ∪ touchedVertices st.G u
  have hS_prev_eq : S_prev = allTouched G_r delta := by
    dsimp only [S_prev]
    rw [hk_inv.S_level_eq ⟨j - 1, by omega⟩, ← hr_eq_k]
    have hdrop_app : (us.take (k + 1)).drop r = (us.take k).drop r ++ [u] := by
      rw [htake_succ, List.drop_append_of_le_length]
      rw [List.length_take]; exact le_trans hr_le_k (Nat.le_min.mpr ⟨le_rfl, Nat.le_of_lt hk⟩)
    have hGapp : G_r.applyBatch ((us.take k).drop r) = Gk := by
      have htk : us.take k = us.take r ++ (us.take k).drop r := by
        have h1 : (us.take k).take r = us.take r := by rw [List.take_take, min_eq_left hr_le_k]
        rw [← h1]; exact (List.take_append_drop r (us.take k)).symm
      dsimp only [Gk, G_r]; conv_rhs => rw [htk]
      exact (applyBatch_append _ _ _).symm
    dsimp only [delta]
    rw [hdrop_app, allTouched_append, hGapp]
    dsimp only [Gk, G_r]
    rw [hk_inv.G_eq]
    simp [allTouched]
  have hpi_eq : ∀ e ∈ G'.E, piLt_mid e = piLe st_r (j - 1) e := fun e heG'' => by
    change piLtFrom st.Pi_level inDom_mid j e = piLtFrom st_r.Pi_level st_r.inDom ((j - 1) + 1) e
    have hsub1 : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
    rw [hsub1]
    have h0_mid : e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩ := by
      dsimp only [inDom_mid]; rw [Finset.mem_inter, hk_inv.inDom0]; exact ⟨hG'E_sub heG'', heG''⟩
    have h0_r : e ∈ st_r.inDom ⟨0, Nat.zero_lt_succ L⟩ := by
      rw [hInv_r.inDom0]; exact hinv_d.2.1 (hG'_delta ▸ heG'')
    have hcongr_in : ∀ m : Fin (L + 1), m.1 < j → (e ∈ inDom_mid m ↔ e ∈ st_r.inDom m) := by
      intro m hm
      have h1 := hk_inv.inDom_eq m
      have h2 := hInv_r.inDom_eq m
      rw [← (hrk_eq_lt hm).2] at h1
      have heGk : e ∈ Gk.E := hG'E_sub heG''
      have heGr : e ∈ G_r.E := hinv_d.2.1 (hG'_delta ▸ heG'')
      constructor
      · intro h; rw [Finset.mem_inter] at h; have h' := h.1; rw [h1, Finset.mem_inter] at h'
        rw [h2]; exact Finset.mem_inter.mpr ⟨h'.1, heGr⟩
      · intro h; rw [h2, Finset.mem_inter] at h
        refine Finset.mem_inter.mpr ⟨?_, heG''⟩
        rw [h1]; exact Finset.mem_inter.mpr ⟨h.1, heGk⟩
    obtain ⟨m₁, hm₁j, hm₁d, hm₁none, heq₁⟩ := piLtFrom_eq st.Pi_level inDom_mid hj_pos h0_mid
    obtain ⟨m₂, hm₂j, hm₂d, hm₂none, heq₂⟩ := piLtFrom_eq st_r.Pi_level st_r.inDom hj_pos h0_r
    have hm_eq : m₁ = m₂ := by
      by_contra hne
      rcases Nat.lt_or_lt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
      · exact hm₁none m₂ hlt hm₂j ((hcongr_in m₂ hm₂j).mpr hm₂d)
      · exact hm₂none m₁ hlt hm₁j ((hcongr_in m₁ hm₁j).mp hm₁d)
    rw [heq₁, heq₂, hm_eq, hk_inv.Pi_level_eq m₂, ← (hrk_eq_lt hm₂j).2, hInv_r.Pi_level_eq m₂]
  have hj1_succ : (j - 1) + 1 = j := Nat.sub_add_cancel hj_pos
  have hEmbr := hInv_r.emb_at ⟨j - 1, by omega⟩ hr_ch
  have hLenr := hInv_r.len_at ⟨j - 1, by omega⟩ hr_ch
  have hVcr := hInv_r.vcong_at ⟨j - 1, by omega⟩ hr_ch
  dsimp only at hEmbr hLenr hVcr
  rw [hj1_succ] at hEmbr hVcr
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hPW := projWalk_spec hSpec hVG_r hBV_d hds_d hG_r_m hSub_lt_r hEmbr hLenr hVcr
    (vcongBound_nonneg hγc hγl G₀.maxDeg (j - 1))
    (vcongBound_step P.hγ_c P.hγ_ℓ G₀.maxDeg (j - 1))
    (by simp [H_lt, unionGraphLt, hG'_delta]) (hG'_delta ▸ hHLt_E)
    (by simp [H_lt, unionGraphLt, hG'_delta]) (by simp [H_lt, unionGraphLt, hG'_delta])
    (hG'_delta ▸ hSub_lt) hS_prev_eq.symm.subset (fun e he => hpi_eq e (hG'_delta ▸ he))
  dsimp only at hPW
  rw [← hG'_delta] at hPW
  rcases hPW with ⟨_, hJm, _, hOut_aff, _, _, _, _, _, _, _, _, hNonempty_bnd, _, hEmpty_bnd, _⟩
  set E_aff := affectedEdges G' H_lt piLt_mid S_prev
  set J := buildProjGraph G' H_lt piLt_mid S_prev E_aff
  set H_aux := buildAuxHost G' H_lt E_aff
  set embJH : Embedding := projWalk G' H_lt piLt_mid S_prev
  set out := if E_aff.Nonempty then sparsify H_aux J embJH else ⟨J, idEmb, 0⟩
  have hS_card : S_prev.card ≤ 2 * sLen := by
    rw [hS_prev_eq]
    calc (allTouched G_r delta).card ≤ 2 * delta.length := allTouched_card_le delta G_r hds_d
      _ = 2 * sLen := by
        congr 1
        dsimp only [delta, sLen]
        rw [List.length_drop, List.length_take, min_eq_left (Nat.succ_le_of_lt hk)]
  have hEnds_lt : ∀ e ∈ H_lt_r.E, H_lt.tail e = (G_r.applyBatch delta).tail e ∧
      H_lt.head e = (G_r.applyBatch delta).head e := fun _ _ => by
    simp [H_lt, unionGraphLt, hG'_delta]
  have hSub_lt_delta : (G_r.applyBatch delta).IsSubgraph H_lt := hG'_delta ▸ hSub_lt
  have hHLt_V_delta : H_lt.V = (G_r.applyBatch delta).V := by
    simp [H_lt, unionGraphLt, hG'_delta]
  have hHLt_E_delta : H_lt.E = H_lt_r.E ∩ (G_r.applyBatch delta).E := hG'_delta ▸ hHLt_E
  have hJV_sub : J.V ⊆ S_prev ∧ J.V ⊆ G'.V := by
    suffices h : ∀ v ∈ J.V, v ∈ S_prev ∧ v ∈ G'.V from
      ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩
    intro v hv
    simp only [J, buildProjGraph, Finset.mem_biUnion] at hv
    rcases hv with ⟨e, he, hv_e⟩
    have heG' : e ∈ G'.E := (Finset.mem_filter.mp he).1
    have hhit1 : ∃ z ∈ H_lt.walkVertices (G'.tail e) (piLt_mid e), z ∈ S_prev := by
      simpa [E_aff, affectedEdges, decide_eq_true_eq] using (Finset.mem_filter.mp he).2
    set S_r := allTouched G_r delta
    set p_r := piLe st_r (j - 1) e
    have hpi_r : piLt_mid e = p_r := hpi_eq e heG'
    have hw_r : H_lt_r.IsWalk (G_r.tail e) (G_r.head e) p_r :=
      hEmbr.2 e (hinv_d.2.1 (hG'_delta ▸ heG'))
    have hanc_ends := hinv_d.2.2.2.2.2.2 e (hinv_d.2.1 (hG'_delta ▸ heG'))
    have hV_tail : G'.tail e ∈ (G_r.applyBatch delta).V := by
      rw [← hG'_delta]; exact (hVG' e heG').1
    have hV_head : G'.head e ∈ (G_r.applyBatch delta).V := by
      rw [← hG'_delta]; exact (hVG' e heG').2
    have hanc_t : batchAnc delta (G'.tail e) = G_r.tail e := by
      rw [hG'_delta]; exact hanc_ends.1
    have hanc_h : batchAnc delta (G'.head e) = G_r.head e := by
      rw [hG'_delta]; exact hanc_ends.2
    have hVw1 := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge hw_r) hV_tail
    have h1 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      Finset.Subset.rfl (IsWalk.mem_edge hw_r) hV_tail hanc_t hVw1).mp
      (by simpa [hpi_r, hS_prev_eq] using hhit1)
    have h2 : ∃ z₀ ∈ H_lt_r.walkVertices (G_r.head e) (walkRev p_r), z₀ ∈ S_r := by
      obtain ⟨z₀, hz₀, hz₀S⟩ := h1
      exact ⟨z₀, (mem_walkVertices_walkRev hw_r z₀).mpr hz₀, hz₀S⟩
    have hVw2 := walkVertices_subset_V_of_batch hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      (IsWalk.mem_edge (isWalk_walkRev hw_r)) hV_head
    have hhit2 := (exists_mem_walkVertices_iff_anc hVG_r hBV_d hds_d hSub_lt_r hEnds_lt
      Finset.Subset.rfl (IsWalk.mem_edge (isWalk_walkRev hw_r)) hV_head hanc_h hVw2).mpr h2
    have hp₁_prop := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
      hHLt_E_delta hEnds_lt Finset.Subset.rfl p_r (G_r.tail e) (G_r.head e) (G'.tail e)
      (hVG_r e (hinv_d.2.1 (hG'_delta ▸ heG'))).1
      (hVG_r e (hinv_d.2.1 (hG'_delta ▸ heG'))).2 hw_r hV_tail hanc_t
    have hq₂_prop := prefixWalk_spec hVG_r hBV_d hds_d hSub_lt_r hSub_lt_delta hHLt_V_delta
      hHLt_E_delta hEnds_lt Finset.Subset.rfl (walkRev p_r) (G_r.head e) (G_r.tail e) (G'.head e)
      (hVG_r e (hinv_d.2.1 (hG'_delta ▸ heG'))).2
      (hVG_r e (hinv_d.2.1 (hG'_delta ▸ heG'))).1 (isWalk_walkRev hw_r) hV_head hanc_h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv_e
    rcases hv_e with rfl | rfl
    · have hp1_s := hp₁_prop.2 (by simpa [hpi_r, hS_prev_eq] using hhit1)
      have h_a : (prefixWalk H_lt (G'.tail e) p_r S_r).1 ∈ S_r := hp1_s.1
      have h_b : (prefixWalk H_lt (G'.tail e) p_r S_r).1 ∈ (G_r.applyBatch delta).V := hp1_s.2.1
      rw [← hpi_r, show S_r = S_prev from hS_prev_eq.symm] at h_a h_b
      rw [← hG'_delta] at h_b
      exact ⟨h_a, h_b⟩
    · have hq2_s := hq₂_prop.2 hhit2
      have h_a : (prefixWalk H_lt (G'.head e) (walkRev p_r) S_r).1 ∈ S_r := hq2_s.1
      have h_b : (prefixWalk H_lt (G'.head e) (walkRev p_r) S_r).1 ∈ (G_r.applyBatch delta).V := hq2_s.2.1
      rw [← hpi_r, show S_r = S_prev from hS_prev_eq.symm] at h_a h_b
      rw [← hG'_delta] at h_b
      exact ⟨h_a, h_b⟩
  have hJn_le_sLen : J.n ≤ 2 * sLen := le_trans (Finset.card_le_card hJV_sub.1) hS_card
  have hJn_le_G' : J.n ≤ G'.n := Finset.card_le_card hJV_sub.2
  have hJm_le_G₀ : J.m ≤ G₀.m := le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hG'm_le0
  have hΛs_ge1 : 1 ≤ Λ_s := by
    have h1 : (1 : ℝ) ≤ (G'.n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) G₀.m]
    exact one_le_pow₀ (by linarith [Real.log_nonneg h1])
  have hJt_card : (out.Jtilde.E.card : ℝ) ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * Λ_s := by
    by_cases hEne : E_aff.Nonempty
    · obtain ⟨_, hSpars_out, _⟩ := hNonempty_bnd hEne
      have hlog := log_mono_nm hJn_le_G' hJm_le_G₀ P.p_s
      have harg1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m]
      have hΛ_Jnn : 0 ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s :=
        pow_nonneg (by linarith [Real.log_nonneg harg1]) _
      have hJn_r : (J.n : ℝ) ≤ 2 * (sLen : ℝ) := by exact_mod_cast hJn_le_sLen
      have hkn : 0 ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ :=
        mul_nonneg (mul_nonneg P.hK_s (by positivity)) hγl
      calc (out.Jtilde.E.card : ℝ) = (out.Jtilde.m : ℝ) := rfl
        _ ≤ P.K_s * (J.n : ℝ) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s := hSpars_out
        _ ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P.p_s :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJn_r P.hK_s) hγl) hΛ_Jnn
        _ ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * Λ_s := mul_le_mul_of_nonneg_left hlog hkn
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      rw [(hEmpty_bnd hEne).2, Finset.card_empty, CharP.cast_eq_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (by positivity)) hγl) (by linarith)
  have hst_eq : st.q = q ∧ st.t = k ∧ st.G = Gk := ⟨hk_inv.q_eq, hk_inv.t_eq, hk_inv.G_eq⟩
  have hch_ne : ¬ chooseLevel L st.q (st.t + 1) = 0 := by
    rw [hst_eq.1, hst_eq.2.1]; exact hj0
  have hch_step : chooseLevel L st.q (st.t + 1) = j := by rw [hst_eq.1, hst_eq.2.1]
  have hstG' : st.G.applyUpdate u = G' := by rw [hst_eq.2.2, ← hG'_eq]
  set H_mid_union := st.H.applyBatch (restrictUpdate u st.H)
  set H_j : MGraph := { V := G'.V, E := out.Jtilde.E, tail := G'.tail, head := G'.head }
  set H_level' : Fin (L + 1) → MGraph := fun i =>
    if i.1 < j then H_mid i else if i.1 = j then H_j else emptyGraphOn G'
  set H_new_E := unionEdgesLt H_level' (L + 1)
  have hUH_eq : res.UH = restrictUpdate u st.H ++
      ((H_mid_union.E \ H_new_E).sort (· ≤ ·)).map Update.delete ++
      ((H_new_E \ H_mid_union.E).sort (· ≤ ·)).map (fun e => Update.insert e (G'.tail e) (G'.head e)) := by
    rw [hres_eq]; dsimp only [step]
    simp only [hch_ne, ↓reduceDIte]
    simp only [hch_step, hstG', H_mid, H_lt, S_prev, inDom_mid, piLt_mid,
      E_aff, J, H_aux, embJH, out, H_j, H_level', H_new_E, H_mid_union, st]
  have hD_eq : res.D = out.Jtilde.E.biUnion fun e => walkEdges (embJH e) := by
    rw [hres_eq]; dsimp only [step]
    simp only [hch_ne, ↓reduceDIte]
    simp only [hch_step, hstG', H_mid, H_lt, S_prev, inDom_mid, piLt_mid,
      E_aff, J, H_aux, embJH, out, st]
  have hNew_sub : H_new_E ⊆ H_mid_union.E ∪ out.Jtilde.E := by
    intro e he
    rw [Finset.mem_union]
    simp only [H_new_E, unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and] at he
    rcases he with ⟨i, _, hei⟩
    dsimp only [H_level'] at hei
    split_ifs at hei with h1 h2
    · left
      have hHmU : H_mid_union.E = st.H.E ∩ G'.E := by
        obtain ⟨_, _, _, h3, _, _⟩ := isSubgraph_restrictUpdate hk_inv.H_sub hk_inv.H_V hu_valid hdu
        simpa [H_mid_union, hG'_eq] using h3
      rw [(hH_mid_props i).2.2] at hei
      rw [hHmU, Finset.mem_inter]
      have hei' := Finset.mem_inter.mp hei
      refine ⟨?_, hei'.2⟩
      rw [hk_inv.H_E]
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, Nat.lt_succ_of_le (Fin.is_le i), hei'.1⟩
    · right; exact hei
    · simp [emptyGraphOn] at hei
  have hIns_le_nat : batchInsertCount res.UH ≤ out.Jtilde.E.card := by
    rw [hUH_eq, batchInsertCount_append, batchInsertCount_append,
      (restrictUpdate_counts st.H u).1]
    have hd0 : batchInsertCount (((H_mid_union.E \ H_new_E).sort (· ≤ ·)).map Update.delete) = 0 :=
      (map_delete_counts _).2.2
    have hi1 := (map_insert_counts ((H_new_E \ H_mid_union.E).sort (· ≤ ·)) G'.tail G'.head).2.1
    rw [hd0, hi1, zero_add, zero_add, Finset.length_sort]
    refine Finset.card_le_card fun e he => ?_
    rw [Finset.mem_sdiff] at he
    rcases Finset.mem_union.mp (hNew_sub he.1) with hm | ho
    · exact absurd hm he.2
    · exact ho
  have hIns_real : (batchInsertCount res.UH : ℝ) ≤ P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * Λ_s :=
    le_trans (Nat.cast_le.mpr hIns_le_nat) hJt_card
  have hD_real : (res.D.card : ℝ) ≤
      P.K_s * (2 * (sLen : ℝ)) * P.γ_ℓ * Λ_s * (lenBound P.γ_ℓ (j - 1) + 1) := by
    by_cases hEne : E_aff.Nonempty
    · obtain ⟨hLen_bnd, _, _⟩ := hNonempty_bnd hEne
      have hlen_each : ∀ e ∈ out.Jtilde.E, (walkEdges (embJH e)).card ≤ (embJH e).length :=
        fun e _ => walkEdges_card_le_length (embJH e)
      have hJne : J.E.Nonempty := hEne
      have hlen_bnd' : ∀ e ∈ out.Jtilde.E, ((embJH e).length : ℝ) ≤ lenBound P.γ_ℓ (j - 1) + 1 := by
        intro e he
        have heJ : e ∈ J.E := hOut_aff he
        have hsup : (embJH e).length ≤ embJH.length J :=
          Finset.le_sup (f := fun x => (embJH x).length) heJ
        exact le_trans (Nat.cast_le.mpr hsup) hLen_bnd
      have hD_card_le : (res.D.card : ℝ) ≤ ∑ _ ∈ out.Jtilde.E, (lenBound P.γ_ℓ (j - 1) + 1) := by
        calc (res.D.card : ℝ) ≤ (∑ e ∈ out.Jtilde.E, (walkEdges (embJH e)).card : ℕ) := by
              exact_mod_cast (hD_eq ▸ Finset.card_biUnion_le)
          _ = ∑ e ∈ out.Jtilde.E, ((walkEdges (embJH e)).card : ℝ) := by push_cast; rfl
          _ ≤ ∑ e ∈ out.Jtilde.E, ((embJH e).length : ℝ) :=
              Finset.sum_le_sum fun e he => Nat.cast_le.mpr (hlen_each e he)
          _ ≤ ∑ _ ∈ out.Jtilde.E, (lenBound P.γ_ℓ (j - 1) + 1) :=
              Finset.sum_le_sum hlen_bnd'
      rw [Finset.sum_const, nsmul_eq_mul] at hD_card_le
      have hlnn : 0 ≤ lenBound P.γ_ℓ (j - 1) + 1 := by linarith [lenBound_nonneg hγl (j - 1)]
      exact le_trans hD_card_le (mul_le_mul_of_nonneg_right hJt_card hlnn)
    · rw [Finset.not_nonempty_iff_eq_empty] at hEne
      rw [hD_eq, (hEmpty_bnd hEne).2, Finset.biUnion_empty, Finset.card_empty, CharP.cast_eq_zero]
      have hlnn : 0 ≤ lenBound P.γ_ℓ (j - 1) + 1 := by linarith [lenBound_nonneg hγl (j - 1)]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg P.hK_s (by positivity)) hγl) (by linarith)) hlnn
  exact ⟨hIns_real, hD_real⟩

private theorem step_H_level_zero_card_diff {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {k : ℕ} (hk : k < us.length) (hj_pos : 0 < chooseLevel L q (k + 1)) :
    ((runState (L := L) G₀ q sparsify us k).H_level ⟨0, Nat.zero_lt_succ L⟩).E.card ≤
      ((runState (L := L) G₀ q sparsify us (k + 1)).H_level ⟨0, Nat.zero_lt_succ L⟩).E.card + 1 := by
  have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k (Nat.le_of_lt hk)).1
  have hk1_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk)).1
  have hr_not_dvd : ¬ phasePeriod q L 0 ∣ k + 1 := fun hdvd => by
    have := (chooseLevel_le_iff_dvd hq (Nat.zero_le L)).mpr hdvd
    omega
  have hr_eq : lastRebuild q L 0 (k + 1) = lastRebuild q L 0 k :=
    lastRebuild_eq_of_not_dvd hr_not_dvd
  have hk_E := hk_inv.H_level_E ⟨0, Nat.zero_lt_succ L⟩
  have hk1_E := hk1_inv.H_level_E ⟨0, Nat.zero_lt_succ L⟩
  rw [hr_eq] at hk1_E
  have hu_some : us[k]? = some (us[k]'hk) := List.getElem?_eq_getElem hk
  have htake : us.take (k + 1) = us.take k ++ [us[k]'hk] := take_succ_of_getElem? hu_some
  obtain ⟨_, _, hU_valid⟩ := batchIsValid_take us G₀ k hBV hds
  have hdu := (hU_valid (us[k]'hk) hu_some).2
  set Gk := G₀.applyBatch (us.take k)
  set Gk1 := G₀.applyBatch (us.take (k + 1))
  have hGk1_eq : Gk1 = Gk.applyUpdate (us[k]'hk) := by
    dsimp only [Gk1, Gk]; rw [htake, applyBatch_append]; rfl
  cases hu : us[k]'hk with
  | insert _ _ _ => rw [hu] at hdu; exact hdu.elim
  | split v v' St Sh =>
    have hE_eq : Gk1.E = Gk.E := by rw [hGk1_eq, hu]; rfl
    rw [hk_E, hk1_E, hE_eq]; exact le_add_right le_rfl
  | delete e =>
    have hsub : ((runState (L := L) G₀ q sparsify us k).H_level ⟨0, Nat.zero_lt_succ L⟩).E ⊆
        insert e ((runState (L := L) G₀ q sparsify us (k + 1)).H_level
          ⟨0, Nat.zero_lt_succ L⟩).E := by
      intro x hx
      rw [hk_E, Finset.mem_inter] at hx
      by_cases hxe : x = e
      · subst hxe; exact Finset.mem_insert_self _ _
      · rw [Finset.mem_insert]
        right
        rw [hk1_E, Finset.mem_inter]
        refine ⟨hx.1, ?_⟩
        rw [hGk1_eq, hu]
        exact Finset.mem_erase.mpr ⟨hxe, hx.2⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

private def Egt0 {L : ℕ} (st : DynSpannerState L) : Finset ℕ :=
  st.H.E \ (st.H_level ⟨0, Nat.zero_lt_succ L⟩).E

private theorem sum_batchDeleteCount_le {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    ∀ T ≤ us.length,
      ∑ k ∈ Finset.range T, batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH +
          (Egt0 (runState (L := L) G₀ q sparsify us T)).card ≤
        T + ∑ k ∈ Finset.range T, batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH +
        ∑ k ∈ (Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0),
          (runState (L := L) G₀ q sparsify us k).H.E.card
  | 0, _ => by
    have h0 : Egt0 (runState (L := L) G₀ q sparsify us 0) = ∅ := by
      have hP := initAt_state_props (L := L) (q := q) (t := 0) hSpec hVG₀ hGm₀ le_rfl
      rcases hP with ⟨_, _, _, _, _, hHE, _, _, _, _, _, hinact, _⟩
      ext e
      simp only [Egt0, runState, init, Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and,
        Decidable.not_not]
      rw [hHE]
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨i, _, hei⟩
      by_cases hi0 : i.1 = 0
      · rwa [show i = ⟨0, Nat.zero_lt_succ L⟩ from Fin.ext hi0] at hei
      · exfalso
        have := (hinact i (Nat.pos_of_ne_zero hi0)).2
        rw [this] at hei
        simp at hei
    simp [h0]
  | T + 1, hT => by
    have ih := sum_batchDeleteCount_le hVG₀ hL hq hGm₀ hSpec hBV hds T (Nat.le_of_succ_le hT)
    have hu : us[T]? = some (us[T]'hT) := List.getElem?_eq_getElem hT
    have hInv := runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (T + 1) hT
    have hRec := hInv.2 T (Nat.lt_succ_self T) (us[T]'hT) hu
    have hk_inv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds T (Nat.le_of_succ_le hT)).1
    have hk1_inv := hInv.1
    have hadd := card_E_applyBatch_add_del (runStepOut (L := L) G₀ q sparsify us T).UH
      (runState (L := L) G₀ q sparsify us T).H hRec.uh_valid
    rw [hRec.uh_apply] at hadd
    have hsplit_T : (runState (L := L) G₀ q sparsify us T).H.E.card =
        ((runState (L := L) G₀ q sparsify us T).H_level ⟨0, Nat.zero_lt_succ L⟩).E.card +
        (Egt0 (runState (L := L) G₀ q sparsify us T)).card := by
      have hsub : ((runState (L := L) G₀ q sparsify us T).H_level ⟨0, Nat.zero_lt_succ L⟩).E ⊆
          (runState (L := L) G₀ q sparsify us T).H.E := by
        intro e he
        rw [hk_inv.H_E]
        simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨0, Nat.zero_lt_succ L⟩, Nat.zero_lt_succ L, he⟩
      have hcard := Finset.card_sdiff_add_card_inter (runState (L := L) G₀ q sparsify us T).H.E
        ((runState (L := L) G₀ q sparsify us T).H_level ⟨0, Nat.zero_lt_succ L⟩).E
      rw [Finset.inter_eq_right.mpr hsub] at hcard
      dsimp only [Egt0]
      omega
    have hsplit_T1 : (runState (L := L) G₀ q sparsify us (T + 1)).H.E.card =
        ((runState (L := L) G₀ q sparsify us (T + 1)).H_level ⟨0, Nat.zero_lt_succ L⟩).E.card +
        (Egt0 (runState (L := L) G₀ q sparsify us (T + 1))).card := by
      have hsub : ((runState (L := L) G₀ q sparsify us (T + 1)).H_level ⟨0, Nat.zero_lt_succ L⟩).E ⊆
          (runState (L := L) G₀ q sparsify us (T + 1)).H.E := by
        intro e he
        rw [hk1_inv.H_E]
        simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨0, Nat.zero_lt_succ L⟩, Nat.zero_lt_succ L, he⟩
      have hcard := Finset.card_sdiff_add_card_inter (runState (L := L) G₀ q sparsify us (T + 1)).H.E
        ((runState (L := L) G₀ q sparsify us (T + 1)).H_level ⟨0, Nat.zero_lt_succ L⟩).E
      rw [Finset.inter_eq_right.mpr hsub] at hcard
      dsimp only [Egt0]
      omega
    by_cases hj0 : chooseLevel L q (T + 1) = 0
    · have hEgt0_T1 : Egt0 (runState (L := L) G₀ q sparsify us (T + 1)) = ∅ := by
        ext e
        simp only [Egt0, Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and,
          Decidable.not_not]
        intro he
        rw [hk1_inv.H_E] at he
        simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ⟨i, _, hei⟩
        by_cases hi0 : i.1 = 0
        · rwa [show i = ⟨0, Nat.zero_lt_succ L⟩ from Fin.ext hi0] at hei
        · exfalso
          have hlr : lastRebuild q L i.1 (T + 1) = T + 1 := by
            have hdvd : phasePeriod q L i.1 ∣ T + 1 :=
              (chooseLevel_le_iff_dvd hq (Fin.is_le i)).mp (by omega)
            exact lastRebuild_eq_self_of_dvd hdvd
          have hlt_i : chooseLevel L q (lastRebuild q L i.1 (T + 1)) < i.1 := by
            rw [hlr, hj0]; exact Nat.pos_of_ne_zero hi0
          rw [(hk1_inv.inactive i hlt_i).2] at hei
          simp at hei
      have hfilt : ((Finset.range (T + 1)).filter (fun k => chooseLevel L q (k + 1) = 0)) =
          insert T ((Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [hj0]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hEgt0_T1, Finset.card_empty,
        hfilt, Finset.sum_insert (by simp)]
      omega
    · have hdiff := step_H_level_zero_card_diff hVG₀ hL hq hGm₀ hSpec hBV hds hT
        (Nat.pos_of_ne_zero hj0)
      have hfilt : ((Finset.range (T + 1)).filter (fun k => chooseLevel L q (k + 1) = 0)) =
          (Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        simp [hj0]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hfilt]
      omega

end Helpers

section MainComplexity

@[expose] public section

/-- **Spanner sparsity** ([chen2022maximum] / Theorem 8.2 Item 1):
* The initial spanner `H^{(0)}` satisfies `|E(H^{(0)})| ≤ K_s |V(G₀)| γ_ℓ (1 + log(|V(G₀)| + m + 2))^{p_s}`.
* After any `k ≤ us.length` single updates, `|E(H^{(k)})| ≤ (L + 1) K_s |V(G^{(k)})| γ_ℓ (1 + log(|V(G^{(k)})| + m + 2))^{p_s}`. -/
theorem sparsity_H {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) :
    (((init G₀ L q sparsify).state.H.m : ℝ) ≤
      P.K_s * (G₀.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) ∧
    (∀ k ≤ us.length,
      let st := runState (L := L) G₀ q sparsify us k
      let Gk := G₀.applyBatch (us.take k)
      (st.H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (Gk.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((Gk.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) := by
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  constructor
  · have hP := initAt_state_props (L := L) (q := q) (t := 0) hSpec hVG₀ hGm₀ le_rfl
    rcases hP with ⟨_, _, _, _, _, hHE, _, _, _, _, _, hinact, hHlsp, _⟩
    have hE0 : (init G₀ L q sparsify).state.H.E =
        ((initAt G₀ L q 0 sparsify).state.H_level ⟨0, Nat.zero_lt_succ L⟩).E := by
      ext e
      change e ∈ (initAt G₀ L q 0 sparsify).state.H.E ↔
        e ∈ ((initAt G₀ L q 0 sparsify).state.H_level ⟨0, Nat.zero_lt_succ L⟩).E
      rw [hHE]
      simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, _, hei⟩
        by_cases hi0 : i.1 = 0
        · rwa [show i = ⟨0, Nat.zero_lt_succ L⟩ from Fin.ext hi0] at hei
        · exfalso; rw [(hinact i (Nat.pos_of_ne_zero hi0)).2] at hei; simp at hei
      · intro he; exact ⟨⟨0, Nat.zero_lt_succ L⟩, Nat.zero_lt_succ L, he⟩
    have hSp0 : ((init G₀ L q sparsify).state.H.m : ℝ) ≤
        P.K_s * ((activeSubgraph G₀).n : ℝ) * P.γ_ℓ *
          (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := by
      have h0 := hHlsp ⟨0, Nat.zero_lt_succ L⟩
      dsimp only [MGraph.m] at h0 ⊢
      rw [hE0]
      exact h0
    have hn_le := activeSubgraph_n_le G₀
    have hlog := log_mono_nm hn_le (le_rfl : G₀.m ≤ G₀.m) P.p_s
    have h1 : (1 : ℝ) ≤ ((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G₀).n, Nat.cast_nonneg (α := ℝ) G₀.m]
    have hΛnn : 0 ≤ (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
      pow_nonneg (by linarith [Real.log_nonneg h1]) _
    have hn_r : ((activeSubgraph G₀).n : ℝ) ≤ (G₀.n : ℝ) := by exact_mod_cast hn_le
    have hkn : 0 ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ :=
      mul_nonneg (mul_nonneg P.hK_s (Nat.cast_nonneg _)) hγl
    calc ((init G₀ L q sparsify).state.H.m : ℝ)
        ≤ P.K_s * ((activeSubgraph G₀).n : ℝ) * P.γ_ℓ *
            (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := hSp0
      _ ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
            (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn_r P.hK_s) hγl) hΛnn
      _ ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ * (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
          mul_le_mul_of_nonneg_left hlog hkn
  · intro k hk st Gk
    have hinv := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds k hk).1
    have hcard : st.H.E.card ≤ ∑ i : Fin (L + 1), (st.H_level i).E.card := by
      rw [hinv.H_E]
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    calc (st.H.m : ℝ) = (st.H.E.card : ℝ) := rfl
      _ ≤ ∑ i : Fin (L + 1), ((st.H_level i).m : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ _ : Fin (L + 1), P.K_s * (Gk.n : ℝ) * P.γ_ℓ *
            (1 + Real.log ((Gk.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
          Finset.sum_le_sum fun i _ => hinv.H_level_spars i
      _ = (L + 1 : ℝ) * P.K_s * (Gk.n : ℝ) * P.γ_ℓ *
            (1 + Real.log ((Gk.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end

end MainComplexity

section Lemma59Helpers

private theorem lemma_5_9_restart_extra {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {T nMax : ℕ} (hT : T ≤ us.length)
    (hn_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).n ≤ nMax)
    (hm_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).m ≤ G₀.m)
    (hH_card : ∀ k ≤ T, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) ≤
      (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s)
    {k : ℕ} (hkT : k < T) (hj0 : chooseLevel L q (k + 1) = 0) :
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let N_1 : ℝ := ((max nMax 1 : ℕ) : ℝ)
    let deg1 : ℝ := (G₀.maxDeg : ℝ) + 1
    let K1 : ℝ := P.K_t + P.K_s + 1
    let u := us[k]'(lt_of_lt_of_le hkT hT)
    let extra := ((runStepOut (L := L) G₀ q sparsify us k).cost : ℝ) -
      ((L : ℝ) + 1) * ((G₀.applyBatch (us.take k)).updateEnc u : ℝ) -
      ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) -
      ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
    extra ≤ N_1 * (12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ) := by
  intro Λ E_L N_1 deg1 K1 u extra
  set Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hL_r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hq_r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hLq_ge2 : (2 : ℝ) ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have hL1 : (L : ℝ) + 1 ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have hk_lt : k < us.length := lt_of_lt_of_le hkT hT
  have hu_some : us[k]? = some u := List.getElem?_eq_getElem hk_lt
  have hInvk := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds k (Nat.le_of_lt hk_lt)).1
  have hInvk1 := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)
  have hRec := hInvk1.2 k (Nat.lt_succ_self k) u hu_some
  obtain ⟨_, hcard, _, hrcost⟩ := hRec.restart_bounds hj0
  have hst' : (runStepOut (L := L) G₀ q sparsify us k).state =
      runState (L := L) G₀ q sparsify us (k + 1) := by
    simp [runStepOut, runState, hu_some]
  set G' := G₀.applyBatch (us.take (k + 1))
  have hG'eq : (runStepOut (L := L) G₀ q sparsify us k).state.G = G' := by
    rw [hst']; exact hInvk1.1.G_eq
  rw [hG'eq] at hcard hrcost
  have henc_eq : ((runState (L := L) G₀ q sparsify us k).G.updateEnc u : ℝ) =
      ((G₀.applyBatch (us.take k)).updateEnc u : ℝ) := by
    rw [hInvk.G_eq]
  have hn_N1 : (nMax : ℝ) ≤ N_1 := by dsimp only [N_1]; exact_mod_cast le_max_left nMax 1
  have h1_N1 : (1 : ℝ) ≤ N_1 := by dsimp only [N_1]; exact_mod_cast le_max_right nMax 1
  have hGm_N1 : (G₀.m : ℝ) ≤ N_1 * (G₀.maxDeg : ℝ) := by
    have hhs := two_mul_m_le_n_mul_maxDeg hVG₀
    have h1 : (2 : ℝ) * (G₀.m : ℝ) ≤ (G₀.n : ℝ) * (G₀.maxDeg : ℝ) := by exact_mod_cast hhs
    have hGn : (G₀.n : ℝ) ≤ (nMax : ℝ) := by
      exact_mod_cast le_trans (by simpa [MGraph.applyBatch] using hn_k 0 (Nat.zero_le T)) le_rfl
    have hmd : 0 ≤ (G₀.maxDeg : ℝ) := Nat.cast_nonneg _
    nlinarith [Nat.cast_nonneg (α := ℝ) G₀.m]
  have hn_act : (activeSubgraph G').n ≤ nMax := le_trans (activeSubgraph_n_le G') (hn_k (k + 1) hkT)
  have hG'm : G'.m ≤ G₀.m := hm_k (k + 1) hkT
  have hlog_t := log_mono_nm hn_act hG'm P.p_t
  have hlog_s := log_mono_nm hn_act hG'm P.p_s
  have h1a : (1 : ℝ) ≤ ((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G').n, Nat.cast_nonneg (α := ℝ) G'.m]
  have hΛtnn : 0 ≤ (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_t :=
    pow_nonneg (by linarith [Real.log_nonneg h1a]) _
  have hΛsnn : 0 ≤ (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
    pow_nonneg (by linarith [Real.log_nonneg h1a]) _
  have h1nm : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hlog_nm : 0 ≤ Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := Real.log_nonneg h1nm
  set Λ_t := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t
  have hΛs_ge1 : 1 ≤ Λ_s := one_le_pow₀ (by linarith)
  have hΛt_ge1 : 1 ≤ Λ_t := one_le_pow₀ (by linarith)
  have hΛ_ge1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  have hΛs_le : Λ_s ≤ Λ := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have hΛt_le : Λ_t ≤ Λ := pow_le_pow_right₀ (by linarith) (le_max_right _ _)
  have hn_r : ((activeSubgraph G').n : ℝ) ≤ N_1 := le_trans (Nat.cast_le.mpr hn_act) hn_N1
  have hG'n_r : (G'.n : ℝ) ≤ N_1 := le_trans (Nat.cast_le.mpr (hn_k (k + 1) hkT)) hn_N1
  have hG'm_r : (G'.m : ℝ) ≤ N_1 * (G₀.maxDeg : ℝ) :=
    le_trans (Nat.cast_le.mpr hG'm) hGm_N1
  have hHm_r : ((runState (L := L) G₀ q sparsify us k).H.m : ℝ) ≤
      N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by
    have h0 := hH_card k (Nat.le_of_lt hkT)
    have h1 : ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s) =
        (nMax : ℝ) * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by ring
    have hnn : 0 ≤ (L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) P.hK_s) hγl) (by linarith)
    calc ((runState (L := L) G₀ q sparsify us k).H.m : ℝ)
        = ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) := rfl
      _ ≤ (nMax : ℝ) * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := h1 ▸ h0
      _ ≤ N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := mul_le_mul_of_nonneg_right hn_N1 hnn
  have hcard' : ((runStepOut (L := L) G₀ q sparsify us k).state.H.E.card : ℝ) ≤
      N_1 * P.K_s * P.γ_ℓ * Λ_s := by
    have hkn : 0 ≤ P.K_s * N_1 * P.γ_ℓ := mul_nonneg (mul_nonneg P.hK_s (by linarith)) hγl
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn_r P.hK_s) hγl) hΛsnn
    have h2 := le_trans h1 (mul_le_mul_of_nonneg_left hlog_s hkn)
    exact le_trans hcard (le_trans h2 (le_of_eq (by ring)))
  have hkt : P.K_t * (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) * P.γ_ℓ ^ 2) *
      (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_t ≤
      P.K_t * (N_1 + N_1 * (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) * Λ_t := by
    have h1 := add_le_add hn_r (mul_le_mul_of_nonneg_right hG'm_r (sq_nonneg P.γ_ℓ))
    have h2 := mul_le_mul_of_nonneg_left h1 P.hK_t
    have h3 := mul_le_mul_of_nonneg_right h2 hΛtnn
    have hkn : 0 ≤ P.K_t * (N_1 + N_1 * (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) :=
      mul_nonneg P.hK_t (by positivity)
    exact le_trans h3 (mul_le_mul_of_nonneg_left hlog_t hkn)
  have hgm_l : (G'.m : ℝ) * lenBound P.γ_ℓ 0 ≤ N_1 * (G₀.maxDeg : ℝ) * lenBound P.γ_ℓ 0 :=
    mul_le_mul_of_nonneg_right hG'm_r (lenBound_nonneg hγl 0)
  have hL_N1 : (L : ℝ) + 1 ≤ ((L : ℝ) + 1) * N_1 :=
    le_mul_of_one_le_right (by linarith) h1_N1
  have hex_le : extra ≤ N_1 * (
      P.K_t * (1 + (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) * Λ_t +
      (1 + (G₀.maxDeg : ℝ)) +
      2 * P.K_s * P.γ_ℓ * Λ_s +
      (G₀.maxDeg : ℝ) * P.γ_ℓ +
      ((L : ℝ) + 1) +
      2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) := by
    have hlen0 : lenBound P.γ_ℓ 0 = P.γ_ℓ := by simp [lenBound]
    dsimp only [extra]
    rw [henc_eq, hlen0] at hrcost
    rw [hlen0] at hgm_l
    have h1 : extra ≤ P.K_t * (N_1 + N_1 * (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) * Λ_t +
        N_1 + N_1 * (G₀.maxDeg : ℝ) + 2 * (N_1 * P.K_s * P.γ_ℓ * Λ_s) +
        N_1 * (G₀.maxDeg : ℝ) * P.γ_ℓ + ((L : ℝ) + 1) * N_1 +
        2 * (N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) := by
      dsimp only [extra]
      linarith only [hrcost, hkt, hG'n_r, hG'm_r, hcard', hgm_l, hL_N1, hHm_r]
    exact le_trans h1 (le_of_eq (by ring))
  obtain ⟨hEL1, hEL_l, hEL_l2, _⟩ := expFactor_bounds P.hγ_c P.hγ_ℓ L G₀.maxDeg
  have hEL_nn : 0 ≤ E_L := by linarith
  have hdeg_le : (G₀.maxDeg : ℝ) ≤ deg1 := by dsimp only [deg1]; linarith
  have hdeg1_nn : 0 ≤ deg1 := by dsimp only [deg1]; positivity
  have h1_d : (1 : ℝ) ≤ deg1 := by
    dsimp only [deg1]; linarith [Nat.cast_nonneg (α := ℝ) G₀.maxDeg]
  have hKt_le : P.K_t ≤ K1 := by dsimp only [K1]; linarith [P.hK_s]
  have hKs_le : P.K_s ≤ K1 := by dsimp only [K1]; linarith [P.hK_t]
  have h1_le : (1 : ℝ) ≤ K1 := by dsimp only [K1]; linarith [P.hK_t, P.hK_s]
  have hK1_nn : 0 ≤ K1 := by linarith
  have hM : 0 ≤ K1 * E_L * deg1 * Λ := by positivity
  have hterm1 : P.K_t * (1 + (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) * Λ_t ≤ 2 * (K1 * E_L * deg1 * Λ) := by
    have h1 : 1 + (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2 ≤ 2 * (E_L * deg1) := by
      have : (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2 ≤ deg1 * E_L :=
        mul_le_mul hdeg_le hEL_l2 (sq_nonneg P.γ_ℓ) hdeg1_nn
      have : (1 : ℝ) ≤ E_L * deg1 := one_le_mul_of_one_le_of_one_le hEL1 h1_d
      linarith
    have hA : P.K_t * (1 + (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) ≤ K1 * (2 * (E_L * deg1)) :=
      mul_le_mul hKt_le h1 (by positivity) hK1_nn
    have hB : (K1 * (2 * (E_L * deg1))) * Λ_t ≤ (K1 * (2 * (E_L * deg1))) * Λ :=
      mul_le_mul_of_nonneg_left hΛt_le (mul_nonneg hK1_nn (mul_nonneg (by norm_num) (mul_nonneg hEL_nn hdeg1_nn)))
    calc P.K_t * (1 + (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) * Λ_t
        ≤ (K1 * (2 * (E_L * deg1))) * Λ_t := mul_le_mul_of_nonneg_right hA (by linarith)
      _ ≤ (K1 * (2 * (E_L * deg1))) * Λ := hB
      _ = 2 * (K1 * E_L * deg1 * Λ) := by ring
  have hterm2 : 1 + (G₀.maxDeg : ℝ) ≤ K1 * E_L * deg1 * Λ := by
    have h1' : 1 ≤ K1 * E_L * Λ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1_le hEL1) hΛ_ge1
    calc 1 + (G₀.maxDeg : ℝ) = 1 * deg1 := by dsimp only [deg1]; ring
      _ ≤ (K1 * E_L * Λ) * deg1 := mul_le_mul_of_nonneg_right h1' hdeg1_nn
      _ = K1 * E_L * deg1 * Λ := by ring
  have hterm3 : 2 * P.K_s * P.γ_ℓ * Λ_s ≤ 2 * (K1 * E_L * deg1 * Λ) := by
    have hA : 2 * P.K_s * P.γ_ℓ ≤ 2 * K1 * E_L :=
      mul_le_mul (mul_le_mul_of_nonneg_left hKs_le (by norm_num)) hEL_l hγl (mul_nonneg (by norm_num) hK1_nn)
    have hB : 2 * K1 * E_L * Λ_s ≤ 2 * K1 * E_L * Λ :=
      mul_le_mul_of_nonneg_left hΛs_le (mul_nonneg (mul_nonneg (by norm_num) hK1_nn) hEL_nn)
    calc 2 * P.K_s * P.γ_ℓ * Λ_s
        ≤ 2 * K1 * E_L * Λ_s := mul_le_mul_of_nonneg_right hA (by linarith)
      _ ≤ 2 * K1 * E_L * Λ := hB
      _ = 2 * (K1 * E_L * 1 * Λ) := by ring
      _ ≤ 2 * (K1 * E_L * deg1 * Λ) := by gcongr
  have hterm4 : (G₀.maxDeg : ℝ) * P.γ_ℓ ≤ K1 * E_L * deg1 * Λ := by
    calc (G₀.maxDeg : ℝ) * P.γ_ℓ ≤ deg1 * E_L := mul_le_mul hdeg_le hEL_l hγl hdeg1_nn
      _ = 1 * E_L * deg1 * 1 := by ring
      _ ≤ K1 * E_L * deg1 * Λ := by gcongr
  have hterm5 : (L : ℝ) + 1 ≤ ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := by
    have : 1 ≤ K1 * E_L * deg1 * Λ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le h1_le hEL1) h1_d) hΛ_ge1
    calc (L : ℝ) + 1 ≤ (L : ℝ) * (q : ℝ) := hL1
      _ ≤ ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) :=
          le_mul_of_one_le_right (by linarith) this
  have hterm6 : 2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) ≤
      2 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := by
    have hA : (L + 1 : ℝ) * P.K_s ≤ (L : ℝ) * (q : ℝ) * K1 :=
      mul_le_mul hL1 hKs_le P.hK_s (by linarith)
    have hB : ((L : ℝ) * (q : ℝ) * K1) * P.γ_ℓ ≤ ((L : ℝ) * (q : ℝ) * K1) * E_L :=
      mul_le_mul_of_nonneg_left hEL_l (mul_nonneg (by linarith) hK1_nn)
    have hC : ((L : ℝ) * (q : ℝ) * K1 * E_L) * Λ_s ≤ ((L : ℝ) * (q : ℝ) * K1 * E_L) * Λ :=
      mul_le_mul_of_nonneg_left hΛs_le (mul_nonneg (mul_nonneg (by linarith) hK1_nn) hEL_nn)
    have hD : 2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) ≤ 2 * ((L : ℝ) * (q : ℝ) * K1 * E_L * Λ) := by
      have hAB := mul_le_mul_of_nonneg_right hA hγl
      have hABE := le_trans (mul_le_mul_of_nonneg_right (le_trans hAB hB) (by linarith)) hC
      linarith only [hABE]
    calc 2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)
        ≤ 2 * ((L : ℝ) * (q : ℝ) * K1 * E_L * Λ) := hD
      _ = 2 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * 1 * Λ) := by ring
      _ ≤ 2 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := by gcongr
  have h6M : 6 * (K1 * E_L * deg1 * Λ) ≤ 3 * ((L : ℝ) * (q : ℝ)) * (K1 * E_L * deg1 * Λ) := by
    have h2 : (6 : ℝ) ≤ 3 * ((L : ℝ) * (q : ℝ)) := by linarith
    exact mul_le_mul_of_nonneg_right h2 hM
  have hsum_coef :
      P.K_t * (1 + (G₀.maxDeg : ℝ) * P.γ_ℓ ^ 2) * Λ_t +
      (1 + (G₀.maxDeg : ℝ)) +
      2 * P.K_s * P.γ_ℓ * Λ_s +
      (G₀.maxDeg : ℝ) * P.γ_ℓ +
      ((L : ℝ) + 1) +
      2 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) ≤
      12 * ((L : ℝ) * (q : ℝ)) * K1 * E_L * deg1 * Λ := by
    linarith [hterm1, hterm2, hterm3, hterm4, hterm5, hterm6, h6M]
  exact le_trans hex_le (mul_le_mul_of_nonneg_left hsum_coef (by linarith))

private theorem lemma_5_9_rebuild_extra {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {T nMax : ℕ} (hT : T ≤ us.length)
    (hn_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).n ≤ nMax)
    {k : ℕ} (hkT : k < T) (hj_pos : 0 < chooseLevel L q (k + 1)) :
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let deg1 : ℝ := (G₀.maxDeg : ℝ) + 1
    let K1 : ℝ := P.K_t + P.K_s + 1
    let sLen := k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1)
    let u := us[k]'(lt_of_lt_of_le hkT hT)
    let extra := ((runStepOut (L := L) G₀ q sparsify us k).cost : ℝ) -
      ((L : ℝ) + 1) * ((G₀.applyBatch (us.take k)).updateEnc u : ℝ) -
      ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) -
      ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
    extra ≤ (sLen : ℝ) * (22 * K1 * E_L * deg1 * Λ) := by
  intro Λ E_L deg1 K1 sLen u extra
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hk_lt : k < us.length := lt_of_lt_of_le hkT hT
  have hu_some : us[k]? = some u := List.getElem?_eq_getElem hk_lt
  have hInvk := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds k (Nat.le_of_lt hk_lt)).1
  have hInvk1 := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)
  have hRec := hInvk1.2 k (Nat.lt_succ_self k) u hu_some
  obtain ⟨_, _, hrcost⟩ := hRec.rebuild_bounds hj_pos
  have hst' : (runStepOut (L := L) G₀ q sparsify us k).state =
      runState (L := L) G₀ q sparsify us (k + 1) := by
    simp [runStepOut, runState, hu_some]
  set G' := G₀.applyBatch (us.take (k + 1))
  have hG'eq : (runStepOut (L := L) G₀ q sparsify us k).state.G = G' := by
    rw [hst']; exact hInvk1.1.G_eq
  rw [hG'eq] at hrcost
  have henc_eq : ((runState (L := L) G₀ q sparsify us k).G.updateEnc u : ℝ) =
      ((G₀.applyBatch (us.take k)).updateEnc u : ℝ) := by
    rw [hInvk.G_eq]
  set j := chooseLevel L q (k + 1)
  have hj_le : j ≤ L := chooseLevel_le L q (k + 1)
  have hV_mono : vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1) ≤
      vcongBound P.γ_c P.γ_ℓ G₀.maxDeg L :=
    vcongBound_mono P.hγ_c P.hγ_ℓ G₀.maxDeg (le_trans (Nat.sub_le j 1) hj_le)
  have hlen1_mono : lenBound P.γ_ℓ (j - 1) ≤ lenBound P.γ_ℓ L :=
    lenBound_mono P.hγ_ℓ (le_trans (Nat.sub_le j 1) hj_le)
  have hlen_mono : lenBound P.γ_ℓ j ≤ lenBound P.γ_ℓ L := lenBound_mono P.hγ_ℓ hj_le
  set V_L := vcongBound P.γ_c P.γ_ℓ G₀.maxDeg L
  set ℓ_L := lenBound P.γ_ℓ L
  have hVnn : 0 ≤ V_L := vcongBound_nonneg hγc hγl G₀.maxDeg L
  have hℓnn : 0 ≤ ℓ_L := lenBound_nonneg hγl L
  have hlog_t := log_mono_nm (hn_k (k + 1) hkT) (le_rfl : G₀.m ≤ G₀.m) P.p_t
  have hlog_s := log_mono_nm (hn_k (k + 1) hkT) (le_rfl : G₀.m ≤ G₀.m) P.p_s
  have h1a : (1 : ℝ) ≤ (G'.n : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) G'.n, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hΛtnn : 0 ≤ (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t :=
    pow_nonneg (by linarith [Real.log_nonneg h1a]) _
  have hΛsnn : 0 ≤ (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
    pow_nonneg (by linarith [Real.log_nonneg h1a]) _
  have h1nm : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hlog_nm : 0 ≤ Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := Real.log_nonneg h1nm
  set Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
  set Λ_t := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t
  have hΛs_le : Λ_s ≤ Λ := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
  have hΛt_le : Λ_t ≤ Λ := pow_le_pow_right₀ (by linarith) (le_max_right _ _)
  have hΛ_ge1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  have hsLen_nn : 0 ≤ (sLen : ℝ) := Nat.cast_nonneg _
  have hea_bnd : 2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1) ≤
      (sLen : ℝ) * (2 * V_L) := by
    calc 2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)
        ≤ 2 * (sLen : ℝ) * V_L := by gcongr
      _ = (sLen : ℝ) * (2 * V_L) := by ring
  have hea_sum :
      2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1) *
        (lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j) ≤
      (sLen : ℝ) * (4 * V_L * ℓ_L) := by
    have h1 : lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j ≤ 2 * ℓ_L := by linarith
    have h2 : 0 ≤ lenBound P.γ_ℓ (j - 1) + lenBound P.γ_ℓ j := by
      linarith [lenBound_nonneg hγl (j - 1), lenBound_nonneg hγl j]
    calc _ ≤ ((sLen : ℝ) * (2 * V_L)) * (2 * ℓ_L) := mul_le_mul hea_bnd h1 h2 (by positivity)
      _ = (sLen : ℝ) * (4 * V_L * ℓ_L) := by ring
  have hea_cost :
      P.K_t * (2 * (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) +
          (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) * P.γ_ℓ ^ 2 *
            (lenBound P.γ_ℓ (j - 1) + 1)) *
        (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t ≤
      (sLen : ℝ) * (P.K_t * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) * Λ_t) := by
    have hℓ1 : lenBound P.γ_ℓ (j - 1) + 1 ≤ ℓ_L + 1 := by linarith
    have hℓ1_nn : 0 ≤ lenBound P.γ_ℓ (j - 1) + 1 := by linarith [lenBound_nonneg hγl (j - 1)]
    have hinner :
        2 * (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) +
          (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) * P.γ_ℓ ^ 2 *
            (lenBound P.γ_ℓ (j - 1) + 1) ≤
        (sLen : ℝ) * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) := by
      have hA : 2 * (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) ≤
          (sLen : ℝ) * (4 * V_L) := by
        calc _ ≤ 2 * ((sLen : ℝ) * (2 * V_L)) := by gcongr
          _ = _ := by ring
      have hB : (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1)) * P.γ_ℓ ^ 2 *
            (lenBound P.γ_ℓ (j - 1) + 1) ≤
          (sLen : ℝ) * (2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) := by
        have := mul_le_mul (mul_le_mul_of_nonneg_right hea_bnd (sq_nonneg P.γ_ℓ)) hℓ1 hℓ1_nn
          (by positivity)
        exact le_trans this (le_of_eq (by ring))
      linarith
    have hkm := mul_le_mul (mul_le_mul_of_nonneg_left hinner P.hK_t) hlog_t hΛtnn
      (mul_nonneg P.hK_t (mul_nonneg hsLen_nn (add_nonneg (mul_nonneg (by norm_num) hVnn)
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hVnn) (sq_nonneg P.γ_ℓ)) (by linarith [hℓnn])))))
    exact le_trans hkm (le_of_eq (by ring))
  have hjt_bnd :
      P.K_s * (2 * (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1))) * P.γ_ℓ *
        (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
      (sLen : ℝ) * (4 * P.K_s * V_L * P.γ_ℓ * Λ_s) := by
    have h1 : P.K_s * (2 * (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1))) * P.γ_ℓ ≤
        (sLen : ℝ) * (4 * P.K_s * V_L * P.γ_ℓ) := by
      have h0 := mul_le_mul_of_nonneg_left hea_bnd (by norm_num : (0 : ℝ) ≤ 2)
      have h0' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h0 P.hK_s) hγl
      exact le_trans (le_of_eq (by ring)) (le_trans h0' (le_of_eq (by ring)))
    have hnn : 0 ≤ (sLen : ℝ) * (4 * P.K_s * V_L * P.γ_ℓ) :=
      mul_nonneg hsLen_nn (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.hK_s) hVnn) hγl)
    have h2 := mul_le_mul h1 hlog_s hΛsnn hnn
    exact le_trans h2 (le_of_eq (by ring))
  have hjt_D_bnd :
      P.K_s * (2 * (2 * (sLen : ℝ) * vcongBound P.γ_c P.γ_ℓ G₀.maxDeg (j - 1))) * P.γ_ℓ *
        (1 + Real.log ((G'.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s *
        (lenBound P.γ_ℓ (j - 1) + 1) ≤
      (sLen : ℝ) * (4 * P.K_s * V_L * P.γ_ℓ * (ℓ_L + 1) * Λ_s) := by
    have hℓ1 : lenBound P.γ_ℓ (j - 1) + 1 ≤ ℓ_L + 1 := by linarith
    have hℓ1_nn : 0 ≤ lenBound P.γ_ℓ (j - 1) + 1 := by linarith [lenBound_nonneg hγl (j - 1)]
    have hnn : 0 ≤ (sLen : ℝ) * (4 * P.K_s * V_L * P.γ_ℓ * Λ_s) :=
      mul_nonneg hsLen_nn (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.hK_s) hVnn) hγl) (by linarith [hlog_nm]))
    have h2 := mul_le_mul hjt_bnd hℓ1 hℓ1_nn hnn
    exact le_trans h2 (le_of_eq (by ring))
  have hex_le : extra ≤ (sLen : ℝ) * (2 + 2 * V_L + 4 * V_L * ℓ_L +
      P.K_t * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) * Λ_t +
      4 * P.K_s * V_L * P.γ_ℓ * Λ_s + 4 * P.K_s * V_L * P.γ_ℓ * (ℓ_L + 1) * Λ_s) := by
    dsimp only [extra]
    rw [henc_eq] at hrcost
    linarith only [hrcost, hea_bnd, hea_sum, hea_cost, hjt_bnd, hjt_D_bnd]
  obtain ⟨hEL1, _, _, _, _, hEL_V, hEL_Vlen, hEL_V2, hEL_V1, _⟩ :=
    expFactor_bounds P.hγ_c P.hγ_ℓ L G₀.maxDeg
  have hEL_nn : 0 ≤ E_L := by linarith
  have hdeg1_nn : 0 ≤ deg1 := by dsimp only [deg1]; positivity
  have h1_d : (1 : ℝ) ≤ deg1 := by
    dsimp only [deg1]; linarith [Nat.cast_nonneg (α := ℝ) G₀.maxDeg]
  have hK1_nn : 0 ≤ K1 := by dsimp only [K1]; linarith [P.hK_t, P.hK_s]
  have hKt_le : P.K_t ≤ K1 := by dsimp only [K1]; linarith [P.hK_s]
  have hKs_le : P.K_s ≤ K1 := by dsimp only [K1]; linarith [P.hK_t]
  have h1_le : (1 : ℝ) ≤ K1 := by dsimp only [K1]; linarith [P.hK_t, P.hK_s]
  have h1 : (2 : ℝ) ≤ 2 * (K1 * E_L * deg1 * Λ) := by
    have : 1 ≤ K1 * E_L * deg1 * Λ :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le h1_le hEL1) h1_d) hΛ_ge1
    linarith
  have h2 : 2 * V_L ≤ 2 * (K1 * E_L * deg1 * Λ) := by
    have hV1 : V_L ≤ K1 * E_L * deg1 * Λ := by
      have hA : E_L * deg1 ≤ K1 * (E_L * deg1) :=
        le_mul_of_one_le_left (mul_nonneg hEL_nn hdeg1_nn) h1_le
      have hB : K1 * (E_L * deg1) ≤ K1 * (E_L * deg1) * Λ :=
        le_mul_of_one_le_right (mul_nonneg hK1_nn (mul_nonneg hEL_nn hdeg1_nn)) hΛ_ge1
      calc V_L ≤ E_L * deg1 := hEL_V
        _ ≤ K1 * (E_L * deg1) * Λ := le_trans hA hB
        _ = K1 * E_L * deg1 * Λ := by ring
    linarith only [hV1]
  have h3 : 4 * V_L * ℓ_L ≤ 4 * (K1 * E_L * deg1 * Λ) := by
    have hV2 : V_L * ℓ_L ≤ K1 * E_L * deg1 * Λ := by
      have hA : E_L * deg1 ≤ K1 * (E_L * deg1) :=
        le_mul_of_one_le_left (mul_nonneg hEL_nn hdeg1_nn) h1_le
      have hB : K1 * (E_L * deg1) ≤ K1 * (E_L * deg1) * Λ :=
        le_mul_of_one_le_right (mul_nonneg hK1_nn (mul_nonneg hEL_nn hdeg1_nn)) hΛ_ge1
      calc V_L * ℓ_L ≤ E_L * deg1 := hEL_Vlen
        _ ≤ K1 * (E_L * deg1) * Λ := le_trans hA hB
        _ = K1 * E_L * deg1 * Λ := by ring
    linarith only [hV2]
  have h4 : P.K_t * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) * Λ_t ≤
      6 * (K1 * E_L * deg1 * Λ) := by
    have h46 : 4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1) ≤ 6 * (E_L * deg1) := by linarith
    have h46_nn : 0 ≤ 4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1) := by positivity
    have hA : P.K_t * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) ≤ K1 * (6 * (E_L * deg1)) :=
      mul_le_mul hKt_le h46 h46_nn hK1_nn
    have hB : K1 * (6 * (E_L * deg1)) * Λ_t ≤ K1 * (6 * (E_L * deg1)) * Λ :=
      mul_le_mul_of_nonneg_left hΛt_le (mul_nonneg hK1_nn (mul_nonneg (by norm_num) (mul_nonneg hEL_nn hdeg1_nn)))
    calc P.K_t * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) * Λ_t
        ≤ K1 * (6 * (E_L * deg1)) * Λ_t := mul_le_mul_of_nonneg_right hA (by linarith)
      _ ≤ K1 * (6 * (E_L * deg1)) * Λ := hB
      _ = 6 * (K1 * E_L * deg1 * Λ) := by ring
  have h5 : 4 * P.K_s * V_L * P.γ_ℓ * Λ_s ≤ 4 * (K1 * E_L * deg1 * Λ) := by
    have hVℓ0 : V_L * P.γ_ℓ ≤ E_L * deg1 := by
      have : 1 ≤ ℓ_L + 1 := by linarith [one_le_lenBound P.hγ_ℓ L]
      calc V_L * P.γ_ℓ ≤ V_L * P.γ_ℓ * (ℓ_L + 1) := le_mul_of_one_le_right (by positivity) this
        _ ≤ E_L * deg1 := hEL_V1
    have hA : P.K_s * (V_L * P.γ_ℓ) ≤ K1 * (E_L * deg1) :=
      mul_le_mul hKs_le hVℓ0 (mul_nonneg hVnn hγl) hK1_nn
    have hB : K1 * (E_L * deg1) * Λ_s ≤ K1 * (E_L * deg1) * Λ :=
      mul_le_mul_of_nonneg_left hΛs_le (mul_nonneg hK1_nn (mul_nonneg hEL_nn hdeg1_nn))
    have hC : P.K_s * (V_L * P.γ_ℓ) * Λ_s ≤ K1 * (E_L * deg1) * Λ :=
      le_trans (mul_le_mul_of_nonneg_right hA (by linarith)) hB
    linarith
  have h6 : 4 * P.K_s * V_L * P.γ_ℓ * (ℓ_L + 1) * Λ_s ≤ 4 * (K1 * E_L * deg1 * Λ) := by
    have hA : P.K_s * (V_L * P.γ_ℓ * (ℓ_L + 1)) ≤ K1 * (E_L * deg1) :=
      mul_le_mul hKs_le hEL_V1 (mul_nonneg (mul_nonneg hVnn hγl) (by positivity)) hK1_nn
    have hB : K1 * (E_L * deg1) * Λ_s ≤ K1 * (E_L * deg1) * Λ :=
      mul_le_mul_of_nonneg_left hΛs_le (mul_nonneg hK1_nn (mul_nonneg hEL_nn hdeg1_nn))
    have hC : P.K_s * (V_L * P.γ_ℓ * (ℓ_L + 1)) * Λ_s ≤ K1 * (E_L * deg1) * Λ :=
      le_trans (mul_le_mul_of_nonneg_right hA (by linarith)) hB
    linarith
  have hcoef : 2 + 2 * V_L + 4 * V_L * ℓ_L +
      P.K_t * (4 * V_L + 2 * V_L * P.γ_ℓ ^ 2 * (ℓ_L + 1)) * Λ_t +
      4 * P.K_s * V_L * P.γ_ℓ * Λ_s + 4 * P.K_s * V_L * P.γ_ℓ * (ℓ_L + 1) * Λ_s ≤
      22 * K1 * E_L * deg1 * Λ := by linarith
  exact le_trans hex_le (mul_le_mul_of_nonneg_left hcoef hsLen_nn)

private theorem lemma_5_9_cost_total {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {T nMax : ℕ} (hT : T ≤ us.length)
    (hn_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).n ≤ nMax)
    (hm_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).m ≤ G₀.m)
    (hH_card : ∀ k ≤ T, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) ≤
      (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s)
    (hn_pow : max nMax 1 ≤ q ^ L)
    (hTotal_UH : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) ≤
      (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) * (T : ℝ))
    (hTotal_D : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
      3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) *
        (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s * (T : ℝ)) :
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).cost : ℝ) ≤
      45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
        (G₀.batchEnc (us.take T) : ℝ) := by
  intro Λ E_L
  refine lemma_5_9_sum_of_step_bounds hL hq hT hn_pow hTotal_UH hTotal_D _ (fun k hk hj0 => ?_)
    (fun k hk hj => ?_)
  · have h0 := lemma_5_9_restart_extra hVG₀ hL hq hGm₀ hSpec hBV hds hT hn_k hm_k hH_card hk hj0
    dsimp only at h0
    linarith
  · have h0 := lemma_5_9_rebuild_extra hVG₀ hL hq hGm₀ hSpec hBV hds hT hn_k hk hj
    dsimp only at h0
    linarith

end Lemma59Helpers

section Lemma59Main

@[expose] public section

/-- **[chen2022maximum] Lemma 5.9 (adapted to Theorem 8.1)**:
Along any prefix `[0, T)` of a valid deletion-and-split sequence `us` with vertex count at most
`nMax` (`max nMax 1 ≤ q ^ L` and `2 ≤ q`), we bound the cumulative inserts, deletes, spanner
recourse `∑ |U_H|`, spanner update encoding `Enc(U_H)` (via Lemma 2.1's `degPot`), re-embedded
set sizes `∑ |D|`, and total operation cost. -/
theorem lemma_5_9 {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    {T nMax : ℕ} (hT : T ≤ us.length)
    (hnMax : G₀.n + batchSplitCount (us.take T) ≤ nMax)
    (hn_pow : max nMax 1 ≤ q ^ L) :
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    (∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
      3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) ∧
    (∑ k ∈ Finset.range T, (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
      (1 + 4 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ)) ∧
    (∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) ≤
      (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ)) ∧
    (((runState (L := L) G₀ q sparsify us 0).H.batchEnc
        ((List.range T).flatMap fun k => (runStepOut (L := L) G₀ q sparsify us k).UH) : ℝ) ≤
      4 * ((init G₀ L q sparsify).state.H.m : ℝ) *
        Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2) +
      (2 + (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ)) ∧
    (∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
      3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s * (T : ℝ)) ∧
    (∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).cost : ℝ) ≤
      45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
        (G₀.batchEnc (us.take T) : ℝ)) := by
  intro Λ_s Λ M_H degΛ E_L
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hL_r : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hq_r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hLq_ge2 : (2 : ℝ) ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have hL1 : (L : ℝ) + 1 ≤ (L : ℝ) * (q : ℝ) := by nlinarith [hL_r, hq_r]
  have h1nm : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hlog_nm_nn : 0 ≤ Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := Real.log_nonneg h1nm
  have hΛs_ge1 : 1 ≤ Λ_s := one_le_pow₀ (by linarith)
  have hΛ_ge1 : 1 ≤ Λ := one_le_pow₀ (by linarith)
  have hN1_pow : ((max nMax 1 : ℕ) : ℝ) ≤ (q ^ L : ℝ) := by exact_mod_cast hn_pow
  set N_1 : ℝ := ((max nMax 1 : ℕ) : ℝ)
  have hn_N1 : (nMax : ℝ) ≤ N_1 := by dsimp only [N_1]; exact_mod_cast le_max_left nMax 1
  have hn_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).n ≤ nMax := fun k hk => by
    obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
    have hne := n_applyBatch_of_delOrSplit (us.take k) G₀ hBV_k hds_k
    have htake : (us.take T).take k = us.take k := by rw [List.take_take, min_eq_left hk]
    have hsp : batchSplitCount (us.take k) ≤ batchSplitCount (us.take T) := by
      rw [← htake]; exact batchSplitCount_take_le (us.take T) k
    omega
  have hm_k : ∀ k ≤ T, (G₀.applyBatch (us.take k)).m ≤ G₀.m := fun k hk => by
    obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
    exact Finset.card_le_card (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).2.1
  have hH_card_le : ∀ k ≤ T, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) ≤ M_H := by
    intro k hk
    have hsp := (sparsity_H hVG₀ hL hq1 hGm₀ hSpec hBV hds).2 k (le_trans hk hT)
    dsimp only at hsp
    have hkn : ((G₀.applyBatch (us.take k)).n : ℝ) ≤ (nMax : ℝ) := by exact_mod_cast hn_k k hk
    have hlog := log_mono_nm (hn_k k hk) (le_rfl : G₀.m ≤ G₀.m) P.p_s
    have h1 : (1 : ℝ) ≤ ((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (G₀.applyBatch (us.take k)).n, Nat.cast_nonneg (α := ℝ) G₀.m]
    have hΛkn : 0 ≤ (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
      pow_nonneg (by linarith [Real.log_nonneg h1]) _
    have hLk : 0 ≤ (L + 1 : ℝ) * P.K_s := mul_nonneg (by linarith) P.hK_s
    have hknm : 0 ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ :=
      mul_nonneg (mul_nonneg hLk (Nat.cast_nonneg _)) hγl
    calc ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ)
        = ((runState (L := L) G₀ q sparsify us k).H.m : ℝ) := rfl
      _ ≤ (L + 1 : ℝ) * P.K_s * ((G₀.applyBatch (us.take k)).n : ℝ) * P.γ_ℓ *
            (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := hsp
      _ ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
            (1 + Real.log (((G₀.applyBatch (us.take k)).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkn hLk) hγl) hΛkn
      _ ≤ M_H := mul_le_mul_of_nonneg_left hlog hknm
  set F0 := (Finset.range T).filter (fun k => chooseLevel L q (k + 1) = 0)
  set Fpos := (Finset.range T).filter (fun k => 0 < chooseLevel L q (k + 1))
  have hsplit_sum : ∀ f : ℕ → ℝ,
      ∑ k ∈ Finset.range T, f k = (∑ k ∈ F0, f k) + (∑ k ∈ Fpos, f k) := fun f => by
    have h := (Finset.sum_filter_add_sum_filter_not (Finset.range T)
      (fun k => chooseLevel L q (k + 1) = 0) f).symm
    have hFpos : (Finset.range T).filter (fun k => ¬ chooseLevel L q (k + 1) = 0) = Fpos := by
      ext k; simp only [Fpos, Finset.mem_filter, Nat.pos_iff_ne_zero]
    rwa [hFpos] at h
  -- 1. Inserts:
  have hIns_F0 : ∀ k ∈ F0,
      (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
        N_1 * (P.K_s * P.γ_ℓ * Λ_s) := fun k hk => by
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk_lt : k < us.length := lt_of_lt_of_le hk.1 hT
    have hu : us[k]? = some (us[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    have hRec := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)).2
      k (Nat.lt_succ_self k) (us[k]'hk_lt) hu
    obtain ⟨hins, hcard, _, _⟩ := hRec.restart_bounds hk.2
    have hinv1 := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)).1
    set G' := G₀.applyBatch (us.take (k + 1))
    have hG'eq : (runStepOut (L := L) G₀ q sparsify us k).state.G = G' := by
      have hst' : (runStepOut (L := L) G₀ q sparsify us k).state =
          runState (L := L) G₀ q sparsify us (k + 1) := by
        simp [runStepOut, runState, hu]
      rw [hst']; exact hinv1.G_eq
    rw [hG'eq] at hcard
    have hn_act : (activeSubgraph G').n ≤ nMax :=
      le_trans (activeSubgraph_n_le G') (hn_k (k + 1) hk.1)
    have hlog := log_mono_nm hn_act (hm_k (k + 1) hk.1) P.p_s
    have h1a : (1 : ℝ) ≤ ((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G').n, Nat.cast_nonneg (α := ℝ) G'.m]
    have hΛnn : 0 ≤ (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
      pow_nonneg (by linarith [Real.log_nonneg h1a]) _
    have hn_r : ((activeSubgraph G').n : ℝ) ≤ N_1 := le_trans (Nat.cast_le.mpr hn_act) hn_N1
    have hkn : 0 ≤ P.K_s * N_1 * P.γ_ℓ := mul_nonneg (mul_nonneg P.hK_s (by linarith)) hγl
    have h2 : P.K_s * ((activeSubgraph G').n : ℝ) * P.γ_ℓ *
        (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s ≤
        N_1 * (P.K_s * P.γ_ℓ * Λ_s) := by
      calc P.K_s * ((activeSubgraph G').n : ℝ) * P.γ_ℓ *
            (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s
          ≤ P.K_s * N_1 * P.γ_ℓ *
              (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn_r P.hK_s) hγl) hΛnn
        _ ≤ P.K_s * N_1 * P.γ_ℓ * Λ_s := mul_le_mul_of_nonneg_left hlog hkn
        _ = N_1 * (P.K_s * P.γ_ℓ * Λ_s) := by ring
    exact le_trans hins (le_trans hcard h2)
  have hIns_Fpos : ∀ k ∈ Fpos,
      (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
        ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
          (2 * P.K_s * P.γ_ℓ * Λ_s) := fun k hk => by
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk_lt : k < us.length := lt_of_lt_of_le hk.1 hT
    have hsh := (step_rebuild_recourse_sharp hVG₀ hL hq1 hGm₀ hSpec hBV hds hk_lt hk.2).1
    have hlog := log_mono_nm (hn_k (k + 1) hk.1) (le_rfl : G₀.m ≤ G₀.m) P.p_s
    have hkn : 0 ≤ P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) * P.γ_ℓ :=
      mul_nonneg (mul_nonneg P.hK_s (by positivity)) hγl
    have h1 : P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
        P.γ_ℓ * (1 + Real.log (((G₀.applyBatch (us.take (k + 1))).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
        P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
          P.γ_ℓ * Λ_s := mul_le_mul_of_nonneg_left hlog hkn
    have h2 : P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
        P.γ_ℓ * Λ_s =
        ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
          (2 * P.K_s * P.γ_ℓ * Λ_s) := by ring
    exact le_trans hsh (le_trans h1 (le_of_eq h2))
  have hSum_F0_ins : ∑ k ∈ F0, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
      (T : ℝ) * (P.K_s * P.γ_ℓ * Λ_s) := by
    have hA_nn : 0 ≤ N_1 * (P.K_s * P.γ_ℓ * Λ_s) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg P.hK_s hγl) (by linarith))
    calc ∑ k ∈ F0, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)
        ≤ ∑ _ ∈ F0, N_1 * (P.K_s * P.γ_ℓ * Λ_s) := Finset.sum_le_sum hIns_F0
      _ = (F0.card : ℝ) * (N_1 * (P.K_s * P.γ_ℓ * Λ_s)) := by simp
      _ ≤ (T : ℝ) * ((N_1 * (P.K_s * P.γ_ℓ * Λ_s)) / (q ^ L : ℝ)) :=
          sum_range_restart_factor hq1 hA_nn
      _ ≤ (T : ℝ) * (P.K_s * P.γ_ℓ * Λ_s) := by
          gcongr
          have hBpos : (0 : ℝ) < (q ^ L : ℝ) := by exact_mod_cast Nat.pow_pos (by omega : 0 < q)
          have : 0 ≤ P.K_s * P.γ_ℓ * Λ_s := mul_nonneg (mul_nonneg P.hK_s hγl) (by linarith)
          calc (N_1 * (P.K_s * P.γ_ℓ * Λ_s)) / (q ^ L : ℝ)
              = (N_1 / (q ^ L : ℝ)) * (P.K_s * P.γ_ℓ * Λ_s) := by ring
            _ ≤ 1 * (P.K_s * P.γ_ℓ * Λ_s) := by gcongr; exact (div_le_one hBpos).mpr hN1_pow
            _ = P.K_s * P.γ_ℓ * Λ_s := one_mul _
  have hSum_Fpos_ins : ∑ k ∈ Fpos, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
      (L : ℝ) * (q : ℝ) * (T : ℝ) * (2 * P.K_s * P.γ_ℓ * Λ_s) := by
    have hnn : 0 ≤ 2 * P.K_s * P.γ_ℓ * Λ_s := mul_nonneg (mul_nonneg (by linarith [P.hK_s]) hγl) (by linarith)
    calc ∑ k ∈ Fpos, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)
        ≤ ∑ k ∈ Fpos, ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
            (2 * P.K_s * P.γ_ℓ * Λ_s) := Finset.sum_le_sum hIns_Fpos
      _ = (∑ k ∈ Fpos, ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
            (2 * P.K_s * P.γ_ℓ * Λ_s) := by rw [← Finset.sum_mul]
      _ ≤ ((L : ℝ) * (q : ℝ) * (T : ℝ)) * (2 * P.K_s * P.γ_ℓ * Λ_s) :=
            mul_le_mul_of_nonneg_right (sum_sLen_le hq1 T) hnn
  have hTotal_ins :
      ∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
        3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) := by
    rw [hsplit_sum]
    have hKsγ : 0 ≤ P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) (by linarith)) (Nat.cast_nonneg _)
    have h2 : 1 + 2 * ((L : ℝ) * (q : ℝ)) ≤ 3 * ((L : ℝ) * (q : ℝ)) := by linarith only [hLq_ge2]
    calc ∑ k ∈ F0, _ + ∑ k ∈ Fpos, _
        ≤ (T : ℝ) * (P.K_s * P.γ_ℓ * Λ_s) + (L : ℝ) * (q : ℝ) * (T : ℝ) * (2 * P.K_s * P.γ_ℓ * Λ_s) :=
          add_le_add hSum_F0_ins hSum_Fpos_ins
      _ = (1 + 2 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) := by ring
      _ ≤ (3 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 hKsγ
      _ = _ := by ring
  -- 2. Deletes:
  have hSum_F0_H : ∑ k ∈ F0, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) ≤
      (L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) := by
    have hterm : ∀ k ∈ F0, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) ≤
        N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := fun k hk => by
      rw [Finset.mem_filter, Finset.mem_range] at hk
      calc ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ)
          ≤ M_H := hH_card_le k (Nat.le_of_lt hk.1)
        _ = (nMax : ℝ) * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by dsimp only [M_H]; ring
        _ ≤ N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by
            gcongr
            exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) P.hK_s) hγl) (by linarith)
    have hAnn : 0 ≤ N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) P.hK_s) hγl) (by linarith))
    calc ∑ k ∈ F0, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ)
        ≤ ∑ _ ∈ F0, N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := Finset.sum_le_sum hterm
      _ = (F0.card : ℝ) * (N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) := by simp
      _ ≤ (T : ℝ) * ((N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) / (q ^ L : ℝ)) :=
          sum_range_restart_factor hq1 hAnn
      _ ≤ (T : ℝ) * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by
          gcongr
          have hBpos : (0 : ℝ) < (q ^ L : ℝ) := by exact_mod_cast Nat.pow_pos (by omega : 0 < q)
          have : 0 ≤ (L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s :=
            mul_nonneg (mul_nonneg (mul_nonneg (by linarith) P.hK_s) hγl) (by linarith)
          calc (N_1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s)) / (q ^ L : ℝ)
              = (N_1 / (q ^ L : ℝ)) * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by ring
            _ ≤ 1 * ((L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s) := by gcongr; exact (div_le_one hBpos).mpr hN1_pow
            _ = (L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s := one_mul _
      _ = _ := by ring
  have hDel_raw :
      ∑ k ∈ Finset.range T, (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
        (T : ℝ) + ∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) +
        ∑ k ∈ F0, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) := by
    have hnat := sum_batchDeleteCount_le hVG₀ hL hq1 hGm₀ hSpec hBV hds T hT
    have hreal : (∑ k ∈ Finset.range T, (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)) +
        ((Egt0 (runState (L := L) G₀ q sparsify us T)).card : ℝ) ≤
        (T : ℝ) + ∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) +
        ∑ k ∈ F0, ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) := by
      exact_mod_cast hnat
    linarith [Nat.cast_nonneg (α := ℝ) (Egt0 (runState (L := L) G₀ q sparsify us T)).card]
  have hTotal_del :
      ∑ k ∈ Finset.range T, (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
        (1 + 4 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ) := by
    have hKsγ : 0 ≤ P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) (by linarith)) (Nat.cast_nonneg _)
    calc ∑ k ∈ Finset.range T, (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)
        ≤ (T : ℝ) + 3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) +
            (L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) := by
          linarith [hDel_raw, hTotal_ins, hSum_F0_H]
      _ = (T : ℝ) + (3 * ((L : ℝ) * (q : ℝ)) + (L + 1)) * (P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) := by ring
      _ ≤ (T : ℝ) + (4 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) := by
          gcongr
          linarith [hL1]
      _ = _ := by ring
  -- 3. `|U_H|`:
  have hTotal_UH :
      ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) ≤
        (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ) := by
    have hnat : (∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ)) ≤
        (T : ℝ) + ∑ k ∈ Finset.range T, (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) +
        ∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) := by
      exact_mod_cast sum_range_stepOut_UH_counts (L := L) G₀ q sparsify us T hT
    have hKsγ : 0 ≤ P.K_s * P.γ_ℓ * Λ_s * (T : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) (by linarith)) (Nat.cast_nonneg _)
    have hins12 : ∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
        (T : ℝ) * (P.K_s * P.γ_ℓ * Λ_s) + (L : ℝ) * (q : ℝ) * (T : ℝ) * (2 * P.K_s * P.γ_ℓ * Λ_s) := by
      rw [hsplit_sum]; exact add_le_add hSum_F0_ins hSum_Fpos_ins
    have hcomb : (3 + (L : ℝ) + 4 * ((L : ℝ) * (q : ℝ))) ≤ 6 * ((L : ℝ) * (q : ℝ)) := by
      nlinarith [hL_r, hq_r]
    calc ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ)
        ≤ (T : ℝ) + ((T : ℝ) + 2 * ((T : ℝ) * (P.K_s * P.γ_ℓ * Λ_s) +
              (L : ℝ) * (q : ℝ) * (T : ℝ) * (2 * P.K_s * P.γ_ℓ * Λ_s)) +
            (L + 1 : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) := by linarith [hnat, hDel_raw, hSum_F0_H, hins12]
      _ = 2 * (T : ℝ) + (3 + (L : ℝ) + 4 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) := by
          ring
      _ ≤ 2 * (T : ℝ) + (6 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) := by
          gcongr
      _ = _ := by ring
  -- 4. `Enc(U_H)`:
  have hTotal_enc :
      ((runState (L := L) G₀ q sparsify us 0).H.batchEnc
        ((List.range T).flatMap fun k => (runStepOut (L := L) G₀ q sparsify us k).UH) : ℝ) ≤
      4 * ((init G₀ L q sparsify).state.H.m : ℝ) *
        Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2) +
      (2 + (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ) := by
    set mBound : ℕ := 3 * Nat.ceil M_H + 1
    have hM_nn : 0 ≤ M_H := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) P.hK_s)
      (Nat.cast_nonneg _)) hγl) (by linarith)
    have hmBound_le : (mBound : ℝ) ≤ 3 * M_H + 4 := by
      have hceil : (Nat.ceil M_H : ℝ) < M_H + 1 := Nat.ceil_lt_add_one hM_nn
      dsimp only [mBound]; push_cast; linarith
    have hlog_bnd : 4 * Real.log (2 * (mBound : ℝ) + 2) + 4 ≤ degΛ := by
      have hpos : (0 : ℝ) < 2 * (mBound : ℝ) + 2 := by positivity
      have hle : 2 * (mBound : ℝ) + 2 ≤ 6 * M_H + 10 := by linarith
      dsimp only [degΛ]
      linarith [Real.log_le_log hpos hle]
    have hflat_enc : (runState (L := L) G₀ q sparsify us 0).H.batchEnc
          ((List.range T).flatMap fun k => (runStepOut (L := L) G₀ q sparsify us k).UH) =
        ∑ k ∈ Finset.range T,
          (runState (L := L) G₀ q sparsify us k).H.batchEnc
            (runStepOut (L := L) G₀ q sparsify us k).UH := by
      refine (applyBatch_and_batchEnc_flatMap
        (fun k => (runStepOut (L := L) G₀ q sparsify us k).UH)
        (fun k => (runState (L := L) G₀ q sparsify us k).H) T fun k hk => ?_).2
      have hk_lt : k < us.length := lt_of_lt_of_le hk hT
      have hu : us[k]? = some (us[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
      exact (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)).2
        k (Nat.lt_succ_self k) (us[k]'hk_lt) hu |>.uh_apply
    have hstep_pot : ∀ k < T,
        ((runState (L := L) G₀ q sparsify us k).H.batchEnc
            (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) +
          degPot (runState (L := L) G₀ q sparsify us (k + 1)).H ≤
        ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) +
          degPot (runState (L := L) G₀ q sparsify us k).H +
          (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) * degΛ := by
      intro k hk
      have hk_lt : k < us.length := lt_of_lt_of_le hk hT
      have hu : us[k]? = some (us[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
      have hInvk := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds k (Nat.le_of_lt hk_lt)).1
      have hInvk1 := runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)
      have hRec := hInvk1.2 k (Nat.lt_succ_self k) (us[k]'hk_lt) hu
      have hpfx : ∀ pfx sfx, (runStepOut (L := L) G₀ q sparsify us k).UH = pfx ++ sfx →
          ((runState (L := L) G₀ q sparsify us k).H.applyBatch pfx).m ≤ mBound := by
        intro pfx sfx heq
        have hBV_p := (batchIsValid_append _ pfx sfx).mp (heq ▸ hRec.uh_valid) |>.1
        have h1 := card_E_applyBatch_add_del pfx (runState (L := L) G₀ q sparsify us k).H hBV_p
        have h2 := card_E_applyBatch_add_del (runStepOut (L := L) G₀ q sparsify us k).UH
          (runState (L := L) G₀ q sparsify us k).H hRec.uh_valid
        rw [hRec.uh_apply] at h2
        have hins_p : batchInsertCount pfx ≤ batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH := by
          rw [heq, batchInsertCount_append]; exact Nat.le_add_right _ _
        have hdel_le := (step_UH_counts (runState (L := L) G₀ q sparsify us k) (us[k]'hk_lt) sparsify).2
        have hres_eq : runStepOut (L := L) G₀ q sparsify us k =
            step (runState (L := L) G₀ q sparsify us k) (us[k]'hk_lt) sparsify := by
          simp [runStepOut, hu]
        rw [← hres_eq] at hdel_le
        have hr : (((runState (L := L) G₀ q sparsify us k).H.applyBatch pfx).m : ℝ) ≤ (mBound : ℝ) := by
          have hk0 : ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) ≤ M_H :=
            hH_card_le k (Nat.le_of_lt hk)
          have hk1 : ((runState (L := L) G₀ q sparsify us (k + 1)).H.E.card : ℝ) ≤ M_H :=
            hH_card_le (k + 1) hk
          have h1r : (((runState (L := L) G₀ q sparsify us k).H.applyBatch pfx).E.card : ℝ) ≤
              ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) + (batchInsertCount pfx : ℝ) := by
            exact_mod_cast (by omega : ((runState (L := L) G₀ q sparsify us k).H.applyBatch pfx).E.card ≤ _)
          have h2r : (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
              ((runState (L := L) G₀ q sparsify us (k + 1)).H.E.card : ℝ) +
                (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) := by
            exact_mod_cast (by omega : batchInsertCount _ ≤ _)
          have hdelr : (batchDeleteCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) ≤
              1 + ((runState (L := L) G₀ q sparsify us k).H.E.card : ℝ) := by
            exact_mod_cast hdel_le
          have hins_pr : (batchInsertCount pfx : ℝ) ≤
              (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) := by
            exact_mod_cast hins_p
          have hm_ceil : M_H ≤ (Nat.ceil M_H : ℝ) := Nat.le_ceil M_H
          dsimp only [mBound, MGraph.m]
          push_cast
          linarith
        exact_mod_cast hr
      have hdp := batchEnc_le_degPot (runStepOut (L := L) G₀ q sparsify us k).UH
        (runState (L := L) G₀ q sparsify us k).H mBound hInvk.H_valid hRec.uh_valid hpfx
      rw [hRec.uh_apply] at hdp
      have hins_nn : 0 ≤ (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ) :=
        Nat.cast_nonneg _
      nlinarith
    have hSum_pot :
        (∑ k ∈ Finset.range T, ((runState (L := L) G₀ q sparsify us k).H.batchEnc
            (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)) +
          degPot (runState (L := L) G₀ q sparsify us T).H ≤
        (∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ)) +
          degPot (runState (L := L) G₀ q sparsify us 0).H +
          (∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)) *
            degΛ := by
      have hgen : ∀ m ≤ T,
          (∑ k ∈ Finset.range m, ((runState (L := L) G₀ q sparsify us k).H.batchEnc
              (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)) +
            degPot (runState (L := L) G₀ q sparsify us m).H ≤
          (∑ k ∈ Finset.range m, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ)) +
            degPot (runState (L := L) G₀ q sparsify us 0).H +
            (∑ k ∈ Finset.range m, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)) *
              degΛ := by
        intro m
        induction m with
        | zero => intro _; simp
        | succ m ih =>
          intro hm
          have ih' := ih (Nat.le_of_succ_le hm)
          have hlast := hstep_pot m hm
          rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, add_mul]
          linarith only [ih', hlast]
      exact hgen T le_rfl
    have hdeg0_nn : 0 ≤ degΛ := by
      have : (1 : ℝ) ≤ 6 * M_H + 10 := by linarith
      linarith [Real.log_nonneg this]
    have hdegT_nn : 0 ≤ degPot (runState (L := L) G₀ q sparsify us T).H := degPot_nonneg _
    have hInv0 := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds 0 (Nat.zero_le _)).1
    have hdp0 : degPot (runState (L := L) G₀ q sparsify us 0).H ≤
        4 * ((init G₀ L q sparsify).state.H.m : ℝ) *
          Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2) := by
      have heq : (runState (L := L) G₀ q sparsify us 0).H = (init G₀ L q sparsify).state.H := rfl
      have h1 : degPot (init G₀ L q sparsify).state.H ≤
          2 * ((init G₀ L q sparsify).state.H.m : ℝ) *
            (2 * Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2)) := by
        simpa [heq] using degPot_le hInv0.H_valid
      have h2 : 2 * ((init G₀ L q sparsify).state.H.m : ℝ) *
          (2 * Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2)) =
          4 * ((init G₀ L q sparsify).state.H.m : ℝ) *
            Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2) := by ring
      change degPot (init G₀ L q sparsify).state.H ≤ _
      linarith only [h1, h2]
    rw [hflat_enc]; push_cast
    calc ∑ k ∈ Finset.range T,
          ((runState (L := L) G₀ q sparsify us k).H.batchEnc
            (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)
        ≤ ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).UH.length : ℝ) +
            degPot (runState (L := L) G₀ q sparsify us 0).H +
            (∑ k ∈ Finset.range T, (batchInsertCount (runStepOut (L := L) G₀ q sparsify us k).UH : ℝ)) *
              degΛ := by linarith
      _ ≤ (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * (T : ℝ) +
            4 * ((init G₀ L q sparsify).state.H.m : ℝ) *
              Real.log (2 * ((init G₀ L q sparsify).state.H.m : ℝ) + 2) +
            (3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s * (T : ℝ)) * degΛ := by
          gcongr
      _ = _ := by ring
  -- 5. `|D|`:
  have hD_F0 : ∀ k ∈ F0,
      ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
        N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := fun k hk => by
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk_lt : k < us.length := lt_of_lt_of_le hk.1 hT
    have hu : us[k]? = some (us[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
    have hRec := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)).2
      k (Nat.lt_succ_self k) (us[k]'hk_lt) hu
    obtain ⟨_, hcard, hDeq, _⟩ := hRec.restart_bounds hk.2
    have hinv1 := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)).1
    set G' := G₀.applyBatch (us.take (k + 1))
    have hG'eq : (runStepOut (L := L) G₀ q sparsify us k).state.G = G' := by
      have hst' : (runStepOut (L := L) G₀ q sparsify us k).state =
          runState (L := L) G₀ q sparsify us (k + 1) := by
        simp [runStepOut, runState, hu]
      rw [hst']; exact hinv1.G_eq
    rw [hG'eq] at hcard
    have hn_act : (activeSubgraph G').n ≤ nMax :=
      le_trans (activeSubgraph_n_le G') (hn_k (k + 1) hk.1)
    have hlog := log_mono_nm hn_act (hm_k (k + 1) hk.1) P.p_s
    have h1a : (1 : ℝ) ≤ ((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph G').n, Nat.cast_nonneg (α := ℝ) G'.m]
    have hΛnn : 0 ≤ (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
      pow_nonneg (by linarith [Real.log_nonneg h1a]) _
    have hn_r : ((activeSubgraph G').n : ℝ) ≤ N_1 := le_trans (Nat.cast_le.mpr hn_act) hn_N1
    have hkn : 0 ≤ P.K_s * N_1 * P.γ_ℓ := mul_nonneg (mul_nonneg P.hK_s (by linarith)) hγl
    have h1ℓ : (1 : ℝ) ≤ lenBound P.γ_ℓ L + 1 := by linarith [one_le_lenBound P.hγ_ℓ L]
    have hD1 : ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
        N_1 * (P.K_s * P.γ_ℓ * Λ_s) := by
      calc ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
          = ((runStepOut (L := L) G₀ q sparsify us k).state.H.E.card : ℝ) := hDeq
        _ ≤ P.K_s * ((activeSubgraph G').n : ℝ) * P.γ_ℓ *
              (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s := hcard
        _ ≤ (P.K_s * N_1 * P.γ_ℓ) *
              (1 + Real.log (((activeSubgraph G').n : ℝ) + (G'.m : ℝ) + 2)) ^ P.p_s :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn_r P.hK_s) hγl) hΛnn
        _ ≤ P.K_s * N_1 * P.γ_ℓ * Λ_s := mul_le_mul_of_nonneg_left hlog hkn
        _ = N_1 * (P.K_s * P.γ_ℓ * Λ_s) := by ring
    have hnn : 0 ≤ N_1 * (P.K_s * P.γ_ℓ * Λ_s) :=
      mul_nonneg (by linarith) (mul_nonneg (mul_nonneg P.hK_s hγl) (by linarith))
    have hmul := le_mul_of_one_le_right hnn h1ℓ
    have h_eq : N_1 * (P.K_s * P.γ_ℓ * Λ_s) * (lenBound P.γ_ℓ L + 1) =
        N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by ring
    exact le_trans hD1 (h_eq ▸ hmul)
  have hD_Fpos : ∀ k ∈ Fpos,
      ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
        ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
          (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := fun k hk => by
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hk_lt : k < us.length := lt_of_lt_of_le hk.1 hT
    have hsh := (step_rebuild_recourse_sharp hVG₀ hL hq1 hGm₀ hSpec hBV hds hk_lt hk.2).2
    have hlog := log_mono_nm (hn_k (k + 1) hk.1) (le_rfl : G₀.m ≤ G₀.m) P.p_s
    have hlen_mono : lenBound P.γ_ℓ (chooseLevel L q (k + 1) - 1) + 1 ≤ lenBound P.γ_ℓ L + 1 := by
      gcongr; exact lenBound_mono P.hγ_ℓ (le_trans (Nat.sub_le _ 1) (chooseLevel_le L q (k + 1)))
    have hlnn : 0 ≤ lenBound P.γ_ℓ (chooseLevel L q (k + 1) - 1) + 1 := by
      linarith [lenBound_nonneg hγl (chooseLevel L q (k + 1) - 1)]
    have hkn : 0 ≤ P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
        P.γ_ℓ := mul_nonneg (mul_nonneg P.hK_s (by positivity)) hγl
    have h1 : P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
        P.γ_ℓ * (1 + Real.log (((G₀.applyBatch (us.take (k + 1))).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s *
        (lenBound P.γ_ℓ (chooseLevel L q (k + 1) - 1) + 1) ≤
        P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
          P.γ_ℓ * Λ_s * (lenBound P.γ_ℓ L + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlog hkn) hlen_mono hlnn (mul_nonneg hkn (by linarith))
    have h2 : P.K_s * (2 * ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
        P.γ_ℓ * Λ_s * (lenBound P.γ_ℓ L + 1) =
        ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
          (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by ring
    exact le_trans hsh (le_trans h1 (le_of_eq h2))
  have hTotal_D :
      ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
        3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s * (T : ℝ) := by
    have h1ℓ : 0 ≤ lenBound P.γ_ℓ L + 1 := by linarith [lenBound_nonneg hγl L]
    have hAF0_nn : 0 ≤ N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) h1ℓ) (by linarith))
    have hSum0 : ∑ k ∈ F0, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
        (T : ℝ) * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by
      calc ∑ k ∈ F0, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
          ≤ ∑ _ ∈ F0, N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) :=
            Finset.sum_le_sum hD_F0
        _ = (F0.card : ℝ) * (N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s)) := by simp
        _ ≤ (T : ℝ) * ((N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s)) / (q ^ L : ℝ)) :=
            sum_range_restart_factor hq1 hAF0_nn
        _ ≤ (T : ℝ) * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by
            gcongr
            have hBpos : (0 : ℝ) < (q ^ L : ℝ) := by exact_mod_cast Nat.pow_pos (by omega : 0 < q)
            have : 0 ≤ P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s :=
              mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) h1ℓ) (by linarith)
            calc (N_1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s)) / (q ^ L : ℝ)
                = (N_1 / (q ^ L : ℝ)) * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by ring
              _ ≤ 1 * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by
                  gcongr; exact (div_le_one hBpos).mpr hN1_pow
              _ = P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s := one_mul _
    have hSumnn : 0 ≤ 2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith [P.hK_s]) hγl) h1ℓ) (by linarith)
    have hSumpos : ∑ k ∈ Fpos, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ) ≤
        (L : ℝ) * (q : ℝ) * (T : ℝ) * (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by
      calc ∑ k ∈ Fpos, ((runStepOut (L := L) G₀ q sparsify us k).D.card : ℝ)
          ≤ ∑ k ∈ Fpos, ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ) *
              (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := Finset.sum_le_sum hD_Fpos
        _ = (∑ k ∈ Fpos, ((k + 1 - lastRebuild q L (chooseLevel L q (k + 1) - 1) (k + 1) : ℕ) : ℝ)) *
              (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) := by rw [← Finset.sum_mul]
        _ ≤ ((L : ℝ) * (q : ℝ) * (T : ℝ)) * (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) :=
            mul_le_mul_of_nonneg_right (sum_sLen_le hq1 T) hSumnn
    rw [hsplit_sum]
    have hKℓ : 0 ≤ P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s * (T : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) h1ℓ) (by linarith)) (Nat.cast_nonneg _)
    have h2 : 1 + 2 * ((L : ℝ) * (q : ℝ)) ≤ 3 * ((L : ℝ) * (q : ℝ)) := by linarith only [hLq_ge2]
    calc ∑ k ∈ F0, _ + ∑ k ∈ Fpos, _
        ≤ (T : ℝ) * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) +
            (L : ℝ) * (q : ℝ) * (T : ℝ) * (2 * P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s) :=
          add_le_add hSum0 hSumpos
      _ = (1 + 2 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s * (T : ℝ)) := by
          ring
      _ ≤ (3 * ((L : ℝ) * (q : ℝ))) * (P.K_s * P.γ_ℓ * (lenBound P.γ_ℓ L + 1) * Λ_s * (T : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 hKℓ
      _ = _ := by ring
  -- 6. Total operation cost:
  have hCost_total :
      ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify us k).cost : ℝ) ≤
        45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          (G₀.batchEnc (us.take T) : ℝ) :=
    lemma_5_9_cost_total hVG₀ hL hq hGm₀ hSpec hBV hds hT hn_k hm_k hH_card_le hn_pow
      hTotal_UH hTotal_D
  refine ⟨hTotal_ins, hTotal_del, hTotal_UH, hTotal_enc, hTotal_D, hCost_total⟩

end

end Lemma59Main

section Theorem8_2

private theorem batchPrefixLen_succ {Us : List (List Update)} {t : ℕ} {U : List Update}
    (ht : Us[t]? = some U) :
    batchPrefixLen Us (t + 1) = batchPrefixLen Us t + U.length := by
  dsimp only [batchPrefixLen]
  rw [take_succ_of_getElem? ht, List.flatten_append, List.length_append, List.flatten_singleton]

private theorem sum_range_batch_eq (Us : List (List Update)) (f : ℕ → ℝ)
    (g : ℕ → List Update → ℝ)
    (h : ∀ (t : ℕ) (U : List Update), Us[t]? = some U →
      g t U = ∑ i ∈ Finset.range U.length, f ((Us.take t).flatten.length + i)) :
    ∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, match Us[t']? with | some U => g t' U | none => 0) =
      ∑ k ∈ Finset.range (batchPrefixLen Us t), f k
  | 0, _ => by simp [batchPrefixLen]
  | t + 1, ht => by
    have ht_le : t ≤ Us.length := Nat.le_of_succ_le ht
    have ht_lt : t < Us.length := ht
    have ht_some : Us[t]? = some (Us[t]'ht_lt) := List.getElem?_eq_getElem ht_lt
    have ih := sum_range_batch_eq Us f g h t ht_le
    have hbp := batchPrefixLen_succ ht_some
    rw [Finset.sum_range_succ, ih, hbp, Finset.sum_range_add, ht_some]
    dsimp only
    rw [h t (Us[t]'ht_lt) ht_some]
    rfl

private theorem batchPrefixLen_le (Us : List (List Update)) (t : ℕ) :
    batchPrefixLen Us t ≤ Us.flatten.length := by
  have h1 : Us = Us.take t ++ Us.drop t := (List.take_append_drop t Us).symm
  conv_rhs => rw [h1, List.flatten_append, List.length_append]
  exact Nat.le_add_right _ _

private theorem getElem?_flatten_of_take_succ {Us : List (List Update)} {t : ℕ} {U : List Update}
    (ht : Us[t]? = some U) :
    ∀ (i : ℕ) (hi : i < U.length), Us.flatten[batchPrefixLen Us t + i]? = some (U[i]'hi) := by
  intro i hi
  have hsplit : Us = Us.take (t + 1) ++ Us.drop (t + 1) := (List.take_append_drop (t + 1) Us).symm
  have hflat : Us.flatten =
      (Us.take t).flatten ++ U ++ (Us.drop (t + 1)).flatten := by
    conv_lhs => rw [hsplit, take_succ_of_getElem? ht, List.flatten_append, List.flatten_append]
    simp [List.append_assoc]
  rw [hflat, List.append_assoc]
  have hlt_pref : (Us.take t).flatten.length ≤ batchPrefixLen Us t + i := by simp [batchPrefixLen]
  rw [List.getElem?_append_right hlt_pref]
  have hidx : batchPrefixLen Us t + i - (Us.take t).flatten.length = i := by simp [batchPrefixLen]
  rw [hidx, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

private theorem flatten_take_batchPrefixLen (Us : List (List Update)) (t : ℕ) :
    Us.flatten.take (batchPrefixLen Us t) = (Us.take t).flatten := by
  have hsplit : Us = Us.take t ++ Us.drop t := (List.take_append_drop t Us).symm
  have h1 : Us.flatten = (Us.take t).flatten ++ (Us.drop t).flatten := by
    conv_lhs => rw [hsplit, List.flatten_append]
  change Us.flatten.take (Us.take t).flatten.length = (Us.take t).flatten
  rw [h1]
  exact List.take_left

@[expose] public section

/-- **Theorem 8.2 (general branching factor `q ≥ 2`, page 39)**:
Batched dynamic spanner maintenance over valid update batches `Us` consisting of edge deletions and
vertex splits with `G₀.n + batchSplitCount Us.flatten ≤ nMax` and `max nMax 1 ≤ q ^ L`. -/
theorem theorem_8_2_general {G₀ : MGraph} {L q mMax nMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {Us : List (List Update)} (hBV : G₀.BatchIsValid Us.flatten)
    (hds : ∀ u ∈ Us.flatten, isDelOrSplit u)
    (hnMax : G₀.n + batchSplitCount Us.flatten ≤ nMax)
    (hn_pow : max nMax 1 ≤ q ^ L) :
    let initOut := init G₀ L q sparsify
    let st := fun t => runBatchState (L := L) G₀ q sparsify Us t
    let res := fun t => runBatchStepOut (L := L) G₀ q sparsify Us t
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
      | some U => ((st t').G.batchEnc U : ℝ)
      | none => 0
    -- Initialization sparsity and time:
    ((initOut.state.H.m : ℝ) ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) ∧
    ((initOut.cost : ℝ) ≤ P.K_t * (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
        (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) ∧
    -- Stage invariants and Item 2 (embedding length & vertex congestion):
    (∀ t ≤ Us.length,
      (st t).G = G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t)) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s ∧
      Embedding.IsEmbedding (piTotal (st t)) (st t).G (st t).H ∧
      (Embedding.length (piTotal (st t)) (st t).G : ℝ) ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P.γ_ℓ ^ (L * (L + 1) / 2) * P.γ_c ^ (L + 1) *
          (G₀.maxDeg : ℝ)) ∧
    -- Batch transitions and Item 3 re-embedding guarantee:
    (∀ t < Us.length, ∀ U, Us[t]? = some U →
      res t = update (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify ∧
      (res t).state = st (t + 1) ∧
      (st t).H.BatchIsValid (res t).UH ∧
      (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
      (res t).D ⊆ (st (t + 1)).H.E ∧
      (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
        eH ∈ walkEdges (piTotal (st (t + 1)) eG) → eH ∉ (res t).D →
        eH ∈ walkEdges (piTotal (st t) eG))) ∧
    -- Cumulative Item 1 (recourse `|U_H|` and `Enc(U_H)`), Item 3 (`|D|`), and update runtime:
    (∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤
        (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s *
          batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        45 * (L : ℝ) * (q : ℝ) * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          encTotal t)) := by
  intro initOut st res Λ_s Λ M_H degΛ E_L batchTotal encTotal
  have hq1 : 1 ≤ q := le_trans (by omega) hq
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hTrace := batchTrace_spec hVG₀ hL hq1 hGm₀ hSpec hBV hds
  have hInit := initAt_state_props (L := L) (q := q) (t := 0) hSpec hVG₀ hGm₀ le_rfl
  have hSpars := sparsity_H hVG₀ hL hq1 hGm₀ hSpec hBV hds
  have hInitCost : (initOut.cost : ℝ) ≤
      P.K_t * (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
      (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1 := by
    rcases hInit with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCost0⟩
    change ((initAt G₀ L q 0 sparsify).cost : ℝ) ≤ _
    dsimp only [initOut, init]
    simpa [lenBound] using hCost0
  have hStep_trace :
      ∀ t < Us.length, ∀ U, Us[t]? = some U →
        res t = update (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify ∧
        (res t).state = st (t + 1) ∧
        (st t).H.BatchIsValid (res t).UH ∧
        (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
        (res t).D ⊆ (st (t + 1)).H.E ∧
        (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (st (t + 1)) eG) → eH ∉ (res t).D →
          eH ∈ walkEdges (piTotal (st t) eG)) := fun t ht U hU => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hTrace.2 t ht U hU
    have h4' : (st t).H.applyBatch (res t).UH = (st (t + 1)).H :=
      h4.trans (congrArg DynSpannerState.H h2)
    have h5' : (res t).D ⊆ (st (t + 1)).H.E := by
      dsimp only [st, res]; rw [← h2]; exact h5
    refine ⟨h1, h2, h3, h4', h5', fun eG heG eH heH hnD => ?_⟩
    dsimp only [st, res] at heG heH hnD ⊢
    rw [← h2] at heG heH
    exact h6 eG heG eH heH hnD
  refine ⟨hSpars.1, hInitCost, ?_, hStep_trace, ?_⟩
  · intro t ht
    obtain ⟨hst_eq, hG, hEmb, hLen, hVc⟩ := hTrace.1 t ht
    have hT_le := batchPrefixLen_le Us t
    have hInv_t := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (batchPrefixLen Us t) hT_le).1
    have hSub : (st t).G.IsSubgraph (st t).H := by
      dsimp only [st]
      rw [hst_eq, hInv_t.G_eq]
      exact hInv_t.H_sub
    have hn_le : (G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n ≤ nMax := by
      obtain ⟨hBV_T, hds_T, _⟩ := batchIsValid_take Us.flatten G₀ (batchPrefixLen Us t) hBV hds
      have h1 := n_applyBatch_of_delOrSplit (Us.flatten.take (batchPrefixLen Us t)) G₀ hBV_T hds_T
      have h2 := batchSplitCount_take_le Us.flatten (batchPrefixLen Us t)
      omega
    have hsp_t := hSpars.2 (batchPrefixLen Us t) hT_le
    have hm_t : ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s := by
      dsimp only [st]
      rw [hst_eq]
      have hlog := log_mono_nm hn_le (le_rfl : G₀.m ≤ G₀.m) P.p_s
      have h1a : (1 : ℝ) ≤ ((G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n : ℝ) +
          (G₀.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ)
          (G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n, Nat.cast_nonneg (α := ℝ) G₀.m]
      have hΛnn : 0 ≤ (1 + Real.log (((G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n : ℝ) +
          (G₀.m : ℝ) + 2)) ^ P.p_s := pow_nonneg (by linarith [Real.log_nonneg h1a]) _
      have hLk : 0 ≤ (L + 1 : ℝ) * P.K_s := mul_nonneg (by linarith) P.hK_s
      have hkn : 0 ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ :=
        mul_nonneg (mul_nonneg hLk (Nat.cast_nonneg _)) hγl
      have hnr : ((G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n : ℝ) ≤ (nMax : ℝ) := by
        exact_mod_cast hn_le
      calc ((runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t)).H.m : ℝ)
          ≤ (L + 1 : ℝ) * P.K_s *
              ((G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n : ℝ) * P.γ_ℓ *
              (1 + Real.log (((G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n : ℝ) +
                (G₀.m : ℝ) + 2)) ^ P.p_s := hsp_t
        _ ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
              (1 + Real.log (((G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t))).n : ℝ) +
                (G₀.m : ℝ) + 2)) ^ P.p_s :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnr hLk) hγl) hΛnn
        _ ≤ M_H := mul_le_mul_of_nonneg_left hlog hkn
    refine ⟨hG, hSub, hm_t, hEmb, ?_, ?_⟩
    · simpa [lenBound] using hLen
    · simpa [vcongBound] using hVc
  · intro t ht
    set T := batchPrefixLen Us t
    have hT_le : T ≤ Us.flatten.length := batchPrefixLen_le Us t
    have hnMax_T : G₀.n + batchSplitCount (Us.flatten.take T) ≤ nMax := by
      have hsp := batchSplitCount_take_le Us.flatten T
      omega
    have hL59 := lemma_5_9 hVG₀ hL hq hGm₀ hSpec hBV hds hT_le hnMax_T hn_pow
    rcases hL59 with ⟨_, _, hUH59, hEnc59, hD59, hCost59⟩
    have hU_eq : ∀ t' < t, ∀ U, Us[t']? = some U →
        let k₀ := batchPrefixLen Us t'
        batchPrefixLen Us t' + U.length ≤ Us.flatten.length ∧
        (∀ (i : ℕ) (hi : i < U.length), Us.flatten[k₀ + i]? = some (U[i]'hi)) := by
      intro t' ht' U hU
      have hbp := batchPrefixLen_succ hU
      exact ⟨hbp ▸ batchPrefixLen_le Us (t' + 1), getElem?_flatten_of_take_succ hU⟩
    have hsum_UH : ∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) =
        ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify Us.flatten k).UH.length : ℝ) := by
      have h1 : ∀ t' < t, ((res t').UH.length : ℝ) =
          match Us[t']? with
          | some U => ∑ i ∈ Finset.range U.length,
              ((runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).UH.length : ℝ)
          | none => 0 := by
        intro t' ht'
        have ht'_lt : t' < Us.length := lt_of_lt_of_le ht' ht
        have ht'_some : Us[t']? = some (Us[t']'ht'_lt) := List.getElem?_eq_getElem ht'_lt
        obtain ⟨hlen_le, hmatch⟩ := hU_eq t' ht' (Us[t']'ht'_lt) ht'_some
        have hub := update_batch_spec hVG₀ hL hq1 hGm₀ hSpec hBV hds hlen_le hmatch
        have hres_eq := (hTrace.2 t' ht'_lt (Us[t']'ht'_lt) ht'_some).1
        rw [ht'_some]; dsimp only [res]
        rw [hres_eq, hub.2.2.2.2.1]
        push_cast; rfl
      rw [Finset.sum_congr rfl fun t' ht' => h1 t' (Finset.mem_range.mp ht')]
      exact sum_range_batch_eq Us
        (fun k => ((runStepOut (L := L) G₀ q sparsify Us.flatten k).UH.length : ℝ))
        (fun t' U => ∑ i ∈ Finset.range U.length,
          ((runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).UH.length : ℝ))
        (fun _ _ _ => rfl) t ht
    have hsum_cost : ∑ t' ∈ Finset.range t, ((res t').cost : ℝ) =
        ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify Us.flatten k).cost : ℝ) := by
      have h1 : ∀ t' < t, ((res t').cost : ℝ) =
          match Us[t']? with
          | some U => ∑ i ∈ Finset.range U.length,
              ((runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).cost : ℝ)
          | none => 0 := by
        intro t' ht'
        have ht'_lt : t' < Us.length := lt_of_lt_of_le ht' ht
        have ht'_some : Us[t']? = some (Us[t']'ht'_lt) := List.getElem?_eq_getElem ht'_lt
        obtain ⟨hlen_le, hmatch⟩ := hU_eq t' ht' (Us[t']'ht'_lt) ht'_some
        have hub := update_batch_spec hVG₀ hL hq1 hGm₀ hSpec hBV hds hlen_le hmatch
        have hres_eq := (hTrace.2 t' ht'_lt (Us[t']'ht'_lt) ht'_some).1
        rw [ht'_some]; dsimp only [res]
        rw [hres_eq, hub.2.2.2.2.2.2.2.2.2]
        push_cast; rfl
      rw [Finset.sum_congr rfl fun t' ht' => h1 t' (Finset.mem_range.mp ht')]
      exact sum_range_batch_eq Us
        (fun k => ((runStepOut (L := L) G₀ q sparsify Us.flatten k).cost : ℝ))
        (fun t' U => ∑ i ∈ Finset.range U.length,
          ((runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).cost : ℝ))
        (fun _ _ _ => rfl) t ht
    have hsum_D : ∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify Us.flatten k).D.card : ℝ) := by
      have h1 : ∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
          ∑ t' ∈ Finset.range t, match Us[t']? with
          | some U => ∑ i ∈ Finset.range U.length,
              ((runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).D.card : ℝ)
          | none => 0 := by
        refine Finset.sum_le_sum fun t' ht' => ?_
        have ht'_lt : t' < Us.length := lt_of_lt_of_le (Finset.mem_range.mp ht') ht
        have ht'_some : Us[t']? = some (Us[t']'ht'_lt) := List.getElem?_eq_getElem ht'_lt
        obtain ⟨hlen_le, hmatch⟩ := hU_eq t' (Finset.mem_range.mp ht') (Us[t']'ht'_lt) ht'_some
        have hub := update_batch_spec hVG₀ hL hq1 hGm₀ hSpec hBV hds hlen_le hmatch
        have hres_eq := (hTrace.2 t' ht'_lt (Us[t']'ht'_lt) ht'_some).1
        rw [ht'_some]; dsimp only [res]
        rw [hres_eq]
        exact_mod_cast hub.2.2.2.2.2.2.2.2.1
      refine le_trans h1 (le_of_eq (sum_range_batch_eq Us
        (fun k => ((runStepOut (L := L) G₀ q sparsify Us.flatten k).D.card : ℝ))
        (fun t' U => ∑ i ∈ Finset.range U.length,
          ((runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).D.card : ℝ))
        (fun _ _ _ => rfl) t ht))
    have hsum_enc_H : ∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) =
        ((runState (L := L) G₀ q sparsify Us.flatten 0).H.batchEnc
          ((List.range T).flatMap fun k => (runStepOut (L := L) G₀ q sparsify Us.flatten k).UH) : ℝ) := by
      have hflat_k :
          (runState (L := L) G₀ q sparsify Us.flatten 0).H.batchEnc
            ((List.range T).flatMap fun k => (runStepOut (L := L) G₀ q sparsify Us.flatten k).UH) =
          ∑ k ∈ Finset.range T,
            (runState (L := L) G₀ q sparsify Us.flatten k).H.batchEnc
              (runStepOut (L := L) G₀ q sparsify Us.flatten k).UH := by
        refine (applyBatch_and_batchEnc_flatMap
          (fun k => (runStepOut (L := L) G₀ q sparsify Us.flatten k).UH)
          (fun k => (runState (L := L) G₀ q sparsify Us.flatten k).H) T fun k hk => ?_).2
        have hk_lt : k < Us.flatten.length := lt_of_lt_of_le hk hT_le
        have hu : Us.flatten[k]? = some (Us.flatten[k]'hk_lt) := List.getElem?_eq_getElem hk_lt
        exact (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds (k + 1) (Nat.succ_le_of_lt hk_lt)).2
          k (Nat.lt_succ_self k) (Us.flatten[k]'hk_lt) hu |>.uh_apply
      have hbatch_k : ∀ t' < t, ((st t').H.batchEnc (res t').UH : ℝ) =
          match Us[t']? with
          | some U => ∑ i ∈ Finset.range U.length,
              ((runState (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).H.batchEnc
                (runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).UH : ℝ)
          | none => 0 := by
        intro t' ht'
        have ht'_lt : t' < Us.length := lt_of_lt_of_le ht' ht
        have ht'_some : Us[t']? = some (Us[t']'ht'_lt) := List.getElem?_eq_getElem ht'_lt
        obtain ⟨hlen_le, hmatch⟩ := hU_eq t' ht' (Us[t']'ht'_lt) ht'_some
        have hrun := updateGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ Us.flatten
          (Us[t']'ht'_lt) (batchPrefixLen Us t') [] ∅ 0 hlen_le hmatch
        have hst_eq : st t' = runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t') :=
          (hTrace.1 t' (Nat.le_of_lt ht'_lt)).1
        have hres_UH : (res t').UH = (List.range (Us[t']'ht'_lt).length).flatMap fun i =>
            (runStepOut (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t' + i)).UH := by
          have hres_eq := (hTrace.2 t' ht'_lt (Us[t']'ht'_lt) ht'_some).1
          dsimp only [res]
          rw [hres_eq]; simp [update, hrun]
        have hpart := (applyBatch_and_batchEnc_flatMap
          (fun i => (runStepOut (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t' + i)).UH)
          (fun i => (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t' + i)).H)
          (Us[t']'ht'_lt).length fun i hi => by
            have hk_lt : batchPrefixLen Us t' + i < Us.flatten.length := by omega
            have hu : Us.flatten[batchPrefixLen Us t' + i]? =
                some (Us.flatten[batchPrefixLen Us t' + i]'hk_lt) := List.getElem?_eq_getElem hk_lt
            have hr := (runInv_all hVG₀ hL hq1 hGm₀ hSpec hBV hds
              (batchPrefixLen Us t' + i + 1) hk_lt).2
              (batchPrefixLen Us t' + i) (Nat.lt_succ_self _)
              (Us.flatten[batchPrefixLen Us t' + i]'hk_lt) hu |>.uh_apply
            simpa [Nat.add_assoc] using hr).2
        rw [ht'_some]; dsimp only
        rw [hst_eq, hres_UH]
        have hpart' : (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t')).H.batchEnc
            ((List.range (Us[t']'ht'_lt).length).flatMap fun i =>
              (runStepOut (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t' + i)).UH) =
            ∑ i ∈ Finset.range (Us[t']'ht'_lt).length,
              (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t' + i)).H.batchEnc
                (runStepOut (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t' + i)).UH := by
          simpa using hpart
        rw [hpart']
        push_cast; rfl
      rw [hflat_k]
      rw [Finset.sum_congr rfl fun t' ht' => hbatch_k t' (Finset.mem_range.mp ht')]
      push_cast
      exact sum_range_batch_eq Us
        (fun k => ((runState (L := L) G₀ q sparsify Us.flatten k).H.batchEnc
          (runStepOut (L := L) G₀ q sparsify Us.flatten k).UH : ℝ))
        (fun t' U => ∑ i ∈ Finset.range U.length,
          ((runState (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).H.batchEnc
            (runStepOut (L := L) G₀ q sparsify Us.flatten ((Us.take t').flatten.length + i)).UH : ℝ))
        (fun _ _ _ => rfl) t ht
    have hencTotal_eq : encTotal t = (G₀.batchEnc (Us.flatten.take T) : ℝ) := by
      have h_ind : ∀ m ≤ Us.length,
          (∑ t' ∈ Finset.range m, match Us[t']? with
            | some U => ((st t').G.batchEnc U : ℝ)
            | none => 0) = (G₀.batchEnc ((Us.take m).flatten) : ℝ) := by
        intro m
        induction m with
        | zero => intro _; simp [MGraph.batchEnc]
        | succ m ih =>
          intro hm
          have hlt : m < Us.length := hm
          have hm_some : Us[m]? = some (Us[m]'hlt) := List.getElem?_eq_getElem hlt
          have hG_m := (hTrace.1 m (Nat.le_of_lt hlt)).2.1
          have htake_m : Us.flatten.take (batchPrefixLen Us m) = (Us.take m).flatten :=
            flatten_take_batchPrefixLen Us m
          have hfl : (Us.take (m + 1)).flatten = (Us.take m).flatten ++ Us[m]'hlt := by
            rw [take_succ_of_getElem? hm_some, List.flatten_append, List.flatten_singleton]
          rw [Finset.sum_range_succ, ih (Nat.le_of_lt hlt), hm_some]
          dsimp only [st]
          rw [hG_m, htake_m, hfl, batchEnc_append]
          push_cast; rfl
      change (∑ t' ∈ Finset.range t, match Us[t']? with
        | some U => ((st t').G.batchEnc U : ℝ)
        | none => 0) = _
      rw [h_ind t ht, flatten_take_batchPrefixLen Us t]
    have hD59' : ∑ k ∈ Finset.range T, ((runStepOut (L := L) G₀ q sparsify Us.flatten k).D.card : ℝ) ≤
        3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s * (T : ℝ) := by
      simpa [lenBound] using hD59
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsum_UH]; exact hUH59
    · rw [hsum_enc_H]; exact hEnc59
    · exact le_trans hsum_D hD59'
    · rw [hsum_cost, hencTotal_eq]; exact hCost59

/-- **Theorem 8.2 (page 39)**:
Dynamic spanner with branching factor `q = phaseBase (G₀.n + splitBound) L = max 2 ⌈(max nMax 1)^{1/L}⌉`
over valid update batches `Us` consisting only of edge deletions and at most `splitBound` (`Õ(n)`)
vertex splits. Achieves:
* Initialization sparsity `Õ(n γ_ℓ)` and initialization time `Õ(n + m γ_ℓ²)`.
* Stage-`t` spanner subgraph containment `H^{(t)} ⊆ G^{(t)}` and sparsity `Õ((L + 1) nMax γ_ℓ)`.
* Item 1: cumulative recourse `∑ |U_H| = Õ(L nMax^{1/L} γ_ℓ ∑ |U|)` (independent of `Δ_max(G)`) and
  cumulative spanner encoding `∑ Enc(U_H) = Õ(nMax γ_ℓ + L nMax^{1/L} γ_ℓ ∑ |U|)`.
* Item 2: path length `≤ 3^L γ_ℓ^{L+1}` and vertex congestion `≤ 3^{(L+1)(L+2)/2} γ_ℓ^{L(L+1)/2} γ_c^{L+1} Δ_max(G₀)`.
* Item 3: per-batch re-embedded edge set `D^{(t)} ⊆ E(H^{(t+1)})` with `eH ∉ D^{(t)}` preserved on
  all surviving walks, and cumulative bound `∑ |D| = Õ(L nMax^{1/L} γ_ℓ^{O(L)} ∑ |U|)` (independent of `Δ_max(G)`).
* Amortized update runtime `Õ(L nMax^{1/L} 3^{O(L²)} γ_c^{L+1} γ_ℓ^{O(L²)} Δ_max(G₀) ∑ Enc(U))`. -/
theorem theorem_8_2 {G₀ : MGraph} {L mMax splitBound : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    {Us : List (List Update)} (hBV : G₀.BatchIsValid Us.flatten)
    (hds : ∀ u ∈ Us.flatten, isDelOrSplit u)
    (hSplits : batchSplitCount Us.flatten ≤ splitBound) :
    let nMax := G₀.n + splitBound
    let q := phaseBase nMax L
    let initOut := init G₀ L q sparsify
    let st := fun t => runBatchState (L := L) G₀ q sparsify Us t
    let res := fun t => runBatchStepOut (L := L) G₀ q sparsify Us t
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let nRoot : ℝ := ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
    let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
      | some U => ((st t').G.batchEnc U : ℝ)
      | none => 0
    ((initOut.state.H.m : ℝ) ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
        (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) ∧
    ((initOut.cost : ℝ) ≤ P.K_t * (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
        (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) ∧
    (∀ t ≤ Us.length,
      (st t).G = G₀.applyBatch (Us.flatten.take (batchPrefixLen Us t)) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s ∧
      Embedding.IsEmbedding (piTotal (st t)) (st t).G (st t).H ∧
      (Embedding.length (piTotal (st t)) (st t).G : ℝ) ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P.γ_ℓ ^ (L * (L + 1) / 2) * P.γ_c ^ (L + 1) *
          (G₀.maxDeg : ℝ)) ∧
    (∀ t < Us.length, ∀ U, Us[t]? = some U →
      res t = update (runState (L := L) G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify ∧
      (res t).state = st (t + 1) ∧
      (st t).H.BatchIsValid (res t).UH ∧
      (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
      (res t).D ⊆ (st (t + 1)).H.E ∧
      (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
        eH ∈ walkEdges (piTotal (st (t + 1)) eG) → eH ∉ (res t).D →
        eH ∈ walkEdges (piTotal (st t) eG))) ∧
    (∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + 2 * (6 + 3 * degΛ) * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s *
          batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        90 * (L : ℝ) * nRoot * (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          encTotal t)) := by
  intro nMax q initOut st res Λ_s Λ M_H degΛ E_L nRoot batchTotal encTotal
  have hq : 2 ≤ q := two_le_phaseBase nMax L
  have hn_pow : max nMax 1 ≤ q ^ L := nCap_le_phaseBase_pow nMax L hL
  have hq_le : (q : ℝ) ≤ 2 * nRoot := phaseBase_le nMax L hL
  have hnMax_le : G₀.n + batchSplitCount Us.flatten ≤ nMax := by omega
  obtain ⟨hSp0, hCost0, hStage, hStep, hCum⟩ := theorem_8_2_general hVG₀ hL hq hGm₀ hSpec hBV hds
    hnMax_le hn_pow
  refine ⟨hSp0, hCost0, hStage, hStep, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hCum t ht
  have hγl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
  have hγc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
  have hL_nn : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have h1nm : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
  have hΛs_nn : 0 ≤ Λ_s := pow_nonneg (by linarith [Real.log_nonneg h1nm]) _
  have hΛ_nn : 0 ≤ Λ := pow_nonneg (by linarith [Real.log_nonneg h1nm]) _
  have hM_nn : 0 ≤ M_H := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) P.hK_s)
    (Nat.cast_nonneg _)) hγl) hΛs_nn
  have hdegΛ_nn : 0 ≤ 6 + 3 * degΛ := by
    have : (1 : ℝ) ≤ 6 * M_H + 10 := by linarith
    have : 0 ≤ degΛ := by dsimp only [degΛ]; linarith [Real.log_nonneg this]
    linarith
  have hEL_nn : 0 ≤ E_L := by positivity
  have hdeg1_nn : 0 ≤ (G₀.maxDeg : ℝ) + 1 := by positivity
  have hbt_nn : 0 ≤ batchTotal t := Nat.cast_nonneg _
  have het_nn : 0 ≤ encTotal t := Finset.sum_nonneg fun t' _ => by
    cases Us[t']? with | none => simp | some U => exact Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsub : 6 * (L : ℝ) * (q : ℝ) ≤ 6 * (L : ℝ) * (2 * nRoot) :=
      mul_le_mul_of_nonneg_left hq_le (by positivity)
    have hK_nn : 0 ≤ P.K_s * P.γ_ℓ * Λ_s := mul_nonneg (mul_nonneg P.hK_s hγl) hΛs_nn
    have hmul : 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s ≤
        12 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s :=
      le_trans (le_of_eq (by ring)) (le_trans (mul_le_mul_of_nonneg_right hsub hK_nn) (le_of_eq (by ring)))
    exact le_trans h1 (mul_le_mul_of_nonneg_right (by linarith only [hmul]) hbt_nn)
  · have hsub : (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) ≤ (6 + 3 * degΛ) * (L : ℝ) * (2 * nRoot) :=
      mul_le_mul_of_nonneg_left hq_le (mul_nonneg hdegΛ_nn hL_nn)
    have hK_nn : 0 ≤ P.K_s * P.γ_ℓ * Λ_s := mul_nonneg (mul_nonneg P.hK_s hγl) hΛs_nn
    have hmul : (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s ≤
        2 * (6 + 3 * degΛ) * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s :=
      le_trans (le_of_eq (by ring)) (le_trans (mul_le_mul_of_nonneg_right hsub hK_nn) (le_of_eq (by ring)))
    have hadd : (2 + (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t ≤
        (2 + 2 * (6 + 3 * degΛ) * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t :=
      mul_le_mul_of_nonneg_right (by linarith only [hmul]) hbt_nn
    exact le_trans h2 (add_le_add le_rfl hadd)
  · have hlen_nn : 0 ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) + 1 := by positivity
    have hsub : 3 * (L : ℝ) * (q : ℝ) ≤ 3 * (L : ℝ) * (2 * nRoot) :=
      mul_le_mul_of_nonneg_left hq_le (by linarith)
    have hK_nn : 0 ≤ P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s * batchTotal t :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg P.hK_s hγl) hlen_nn) hΛs_nn) hbt_nn
    have hmul := mul_le_mul_of_nonneg_right hsub hK_nn
    exact le_trans h3 (le_trans (le_of_eq (by ring)) (le_trans hmul (le_of_eq (by ring))))
  · have hK_nn : 0 ≤ (P.K_t + P.K_s + 1) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ * encTotal t :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith [P.hK_t, P.hK_s]) hEL_nn)
        hdeg1_nn) hΛ_nn) het_nn
    have hsub : 45 * (L : ℝ) * (q : ℝ) ≤ 45 * (L : ℝ) * (2 * nRoot) :=
      mul_le_mul_of_nonneg_left hq_le (by linarith)
    have hmul := mul_le_mul_of_nonneg_right hsub hK_nn
    exact le_trans h4 (le_trans (le_of_eq (by ring)) (le_trans hmul (le_of_eq (by ring))))

end

end Theorem8_2

section WithTime

private lemma mul_kt_absorb_le {pref K_t K_s γ_t b c d e : ℝ}
    (hpref : 0 ≤ pref) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hKs : 0 ≤ K_s) (hγt : 1 ≤ γ_t) :
    pref * (K_t * γ_t + K_s + 1) * b * c * d * e ≤
      pref * ((K_t + K_s + 1) * γ_t) * b * c * d * e := by
  have h1 : K_t * γ_t + K_s + 1 ≤ (K_t + K_s + 1) * γ_t := by nlinarith only [hKs, hγt]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hpref) hb) hc) hd) he

/-- Parametrized **Theorem 8.2** (general `q`) carrying an explicit runtime overhead `γ_t ≥ 1`
(`SparsifySpecWithTime`), reduced directly to `theorem_8_2_general` via `P.absorbTime`. -/
theorem theorem_8_2_general_with_time {G₀ : MGraph} {L q mMax nMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hG0_val : G₀.IsValid) (hL : 1 ≤ L) (hq : 2 ≤ q) (hmMax : G₀.m ≤ mMax)
    (hSp : SparsifySpecWithTime mMax P sparsify)
    {Us : List (List Update)}
    (hBat : G₀.BatchIsValid Us.flatten)
    (hSplit : ∀ u ∈ Us.flatten, isDelOrSplit u)
    (hnMax : G₀.n + batchSplitCount Us.flatten ≤ nMax)
    (hqL : max nMax 1 ≤ q ^ L) :
    let initOut := init G₀ L q sparsify
    let st := fun t => runBatchState (L := L) G₀ q sparsify Us t
    let res := fun t => runBatchStepOut (L := L) G₀ q sparsify Us t
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let batchTotal := fun t => ((List.take t Us).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t,
      match Us[t']? with | some U => ((st t').G.batchEnc U : ℝ) | none => 0
    ((initOut.state.H.m : ℝ) ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
      (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) ∧
    ((initOut.cost : ℝ) ≤ P.K_t * P.γ_t *
        (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
        (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) ∧
    (∀ t ≤ Us.length,
      (st t).G = G₀.applyBatch (List.take (batchPrefixLen Us t) Us.flatten) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s ∧
      (piTotal (st t)).IsEmbedding (st t).G (st t).H ∧
      (Embedding.length (piTotal (st t)) (st t).G : ℝ) ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P.γ_ℓ ^ (L * (L + 1) / 2) * P.γ_c ^ (L + 1) *
          (G₀.maxDeg : ℝ)) ∧
    (∀ t < Us.length, ∀ U, Us[t]? = some U →
      res t = update (runState G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify ∧
      (res t).state = st (t + 1) ∧
      (st t).H.BatchIsValid (res t).UH ∧
      (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
      (res t).D ⊆ (st (t + 1)).H.E ∧
      ∀ eG ∈ (st (t + 1)).G.E, ∀ eH ∈ walkEdges (piTotal (st (t + 1)) eG),
        eH ∉ (res t).D → eH ∈ walkEdges (piTotal (st t) eG)) ∧
    (∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤
        (2 + 6 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + (6 + 3 * degΛ) * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        3 * (L : ℝ) * (q : ℝ) * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        45 * (L : ℝ) * (q : ℝ) * ((P.K_t + P.K_s + 1) * P.γ_t) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          encTotal t)) := by
  have hSp' : SparsifySpec mMax P.absorbTime sparsify := sparsifySpecWithTime_iff_absorb.mp hSp
  have hbase := theorem_8_2_general hG0_val hL hq hmMax hSp' hBat hSplit hnMax hqL
  rcases hbase with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, ?_, h3, h4, fun t ht => ?_⟩
  · simpa [SparsifyParams.absorbTime, mul_assoc] using h2
  · obtain ⟨ha, hb, hc, hd⟩ := h5 t ht
    refine ⟨ha, hb, hc, ?_⟩
    have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hq_nn : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hEL_nn : 0 ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
        P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by
      have hgl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
      have hgc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
      positivity
    have hdeg_nn : (0 : ℝ) ≤ (G₀.maxDeg : ℝ) + 1 := by positivity
    have hΛ_nn : 0 ≤ (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) := by
      have hlog : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
      exact pow_nonneg (by linarith [Real.log_nonneg hlog]) _
    have het_nn : 0 ≤ ∑ t' ∈ Finset.range t,
        match Us[t']? with | some U => (((runBatchState (L := L) G₀ q sparsify Us t').G.batchEnc U : ℕ) : ℝ) | none => 0 :=
      Finset.sum_nonneg fun t' _ => by
        cases Us[t']? with | none => exact le_rfl | some U => exact Nat.cast_nonneg _
    have hpref_nn : 0 ≤ 45 * (L : ℝ) * (q : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hL_nn) hq_nn
    exact le_trans hd (mul_kt_absorb_le hpref_nn hEL_nn hdeg_nn hΛ_nn het_nn P.hK_s P.hγ_t)

/-- Parametrized **Theorem 8.2** (`phaseBase nMax L` specialization) carrying an explicit runtime
overhead `γ_t ≥ 1` (`SparsifySpecWithTime`), reduced directly to `theorem_8_2` via `P.absorbTime`. -/
theorem theorem_8_2_with_time {G₀ : MGraph} {L mMax splitBound : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hG0_val : G₀.IsValid) (hL : 1 ≤ L) (hmMax : G₀.m ≤ mMax)
    (hSp : SparsifySpecWithTime mMax P sparsify)
    {Us : List (List Update)}
    (hBat : G₀.BatchIsValid Us.flatten)
    (hSplit : ∀ u ∈ Us.flatten, isDelOrSplit u)
    (hBound : batchSplitCount Us.flatten ≤ splitBound) :
    let nMax := G₀.n + splitBound
    let q := phaseBase nMax L
    let initOut := init G₀ L q sparsify
    let st := fun t => runBatchState (L := L) G₀ q sparsify Us t
    let res := fun t => runBatchStepOut (L := L) G₀ q sparsify Us t
    let Λ_s := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s
    let Λ := (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t)
    let M_H := (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s
    let degΛ := 4 * Real.log (6 * M_H + 10) + 4
    let E_L := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
      P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
    let nRoot : ℝ := ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
    let batchTotal := fun t => ((List.take t Us).flatten.length : ℝ)
    let encTotal := fun t => ∑ t' ∈ Finset.range t,
      match Us[t']? with | some U => ((st t').G.batchEnc U : ℝ) | none => 0
    ((initOut.state.H.m : ℝ) ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
      (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s) ∧
    ((initOut.cost : ℝ) ≤ P.K_t * P.γ_t *
        (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
        (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + (L : ℝ) + 1) ∧
    (∀ t ≤ Us.length,
      (st t).G = G₀.applyBatch (List.take (batchPrefixLen Us t) Us.flatten) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ * Λ_s ∧
      (piTotal (st t)).IsEmbedding (st t).G (st t).H ∧
      (Embedding.length (piTotal (st t)) (st t).G : ℝ) ≤ 3 ^ L * P.γ_ℓ ^ (L + 1) ∧
      Embedding.vcong (piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        3 ^ ((L + 1) * (L + 2) / 2) * P.γ_ℓ ^ (L * (L + 1) / 2) * P.γ_c ^ (L + 1) *
          (G₀.maxDeg : ℝ)) ∧
    (∀ t < Us.length, ∀ U, Us[t]? = some U →
      res t = update (runState G₀ q sparsify Us.flatten (batchPrefixLen Us t)) U sparsify ∧
      (res t).state = st (t + 1) ∧
      (st t).H.BatchIsValid (res t).UH ∧
      (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
      (res t).D ⊆ (st (t + 1)).H.E ∧
      ∀ eG ∈ (st (t + 1)).G.E, ∀ eH ∈ walkEdges (piTotal (st (t + 1)) eG),
        eH ∉ (res t).D → eH ∈ walkEdges (piTotal (st t) eG)) ∧
    (∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + 2 * (6 + 3 * degΛ) * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * Λ_s) * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot * P.K_s * P.γ_ℓ * (3 ^ L * P.γ_ℓ ^ (L + 1) + 1) * Λ_s * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        90 * (L : ℝ) * nRoot * ((P.K_t + P.K_s + 1) * P.γ_t) * E_L * ((G₀.maxDeg : ℝ) + 1) * Λ *
          encTotal t)) := by
  have hSp' : SparsifySpec mMax P.absorbTime sparsify := sparsifySpecWithTime_iff_absorb.mp hSp
  have hbase := theorem_8_2 hG0_val hL hmMax hSp' hBat hSplit hBound
  rcases hbase with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, ?_, h3, h4, fun t ht => ?_⟩
  · simpa [SparsifyParams.absorbTime, mul_assoc] using h2
  · obtain ⟨ha, hb, hc, hd⟩ := h5 t ht
    refine ⟨ha, hb, hc, ?_⟩
    have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hn_nn : 0 ≤ (((max (G₀.n + splitBound) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) := by positivity
    have hEL_nn : 0 ≤ 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
        P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by
      have hgl : 0 ≤ P.γ_ℓ := by linarith [P.hγ_ℓ]
      have hgc : 0 ≤ P.γ_c := by linarith [P.hγ_c]
      positivity
    have hdeg_nn : (0 : ℝ) ≤ (G₀.maxDeg : ℝ) + 1 := by positivity
    have hΛ_nn : 0 ≤ (1 + Real.log (((G₀.n + splitBound : ℕ) : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) := by
      have hlog : (1 : ℝ) ≤ ((G₀.n + splitBound : ℕ) : ℝ) + (G₀.m : ℝ) + 2 := by
        linarith [Nat.cast_nonneg (α := ℝ) (G₀.n + splitBound), Nat.cast_nonneg (α := ℝ) G₀.m]
      exact pow_nonneg (by linarith [Real.log_nonneg hlog]) _
    have het_nn : 0 ≤ ∑ t' ∈ Finset.range t,
        match Us[t']? with | some U => (((runBatchState (L := L) G₀ (phaseBase (G₀.n + splitBound) L) sparsify Us t').G.batchEnc U : ℕ) : ℝ) | none => 0 :=
      Finset.sum_nonneg fun t' _ => by
        cases Us[t']? with | none => exact le_rfl | some U => exact Nat.cast_nonneg _
    have hpref_nn : 0 ≤ 90 * (L : ℝ) * (((max (G₀.n + splitBound) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) :=
      mul_nonneg (mul_nonneg (by norm_num) hL_nn) hn_nn
    exact le_trans hd (mul_kt_absorb_le hpref_nn hEL_nn hdeg_nn hΛ_nn het_nn P.hK_s P.hγ_t)

end WithTime

end MinCostFlow.DynSpanner
