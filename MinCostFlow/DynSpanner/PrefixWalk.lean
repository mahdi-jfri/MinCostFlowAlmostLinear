module

public import MinCostFlow.DynSpanner.Defs

import Mathlib.Tactic.Linarith

/-!
# Phase-period, embedding-lookup, and prefix-walk lemmas (Definitions 5.2 and 5.4)

This file establishes the combinatorial properties needed to prove correctness, length bounds,
vertex-congestion bounds, and re-embedding recourse for Algorithm 6:
* `chooseLevel` and `lastRebuild`: divisibility chain `q^{L - i} ∣ t` and interval characterization
  of the last stage `≤ t` where a level `≤ i` was rebuilt.
* `findEmbLevel` and `piLtFrom`: lookup characterization of `Π_{<j}` and `Π_{≤ j}`.
* `prefixWalk_spec` and `prefixWalk_append_of_not_mem`: survival of walks disjoint from `S` and
  existence/prefix/ancestor properties of the projected prefix and suffix walks under arbitrary
  sequences of edge deletions and vertex splits.
-/

namespace MinCostFlow.DynSpanner

section PhaseLemmas

@[expose] public section

/-- Most recent stage `≤ t` at which a level `≤ i` was rebuilt (`(t / B_i) * B_i`). -/
def lastRebuild (q L i t : ℕ) : ℕ :=
  (t / phasePeriod q L i) * phasePeriod q L i

theorem phasePeriod_pos {q : ℕ} (hq : 1 ≤ q) (L i : ℕ) : 0 < phasePeriod q L i := by
  unfold phasePeriod
  exact Nat.pow_pos hq

theorem phasePeriod_dvd_of_le {q L i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) :
    phasePeriod q L j ∣ phasePeriod q L i := by
  unfold phasePeriod
  exact Nat.pow_dvd_pow q (by omega)

theorem chooseLevel_le_iff_dvd {L q t i : ℕ} (_hq : 1 ≤ q) (hi : i ≤ L) :
    chooseLevel L q t ≤ i ↔ phasePeriod q L i ∣ t := by
  constructor
  · intro hle
    exact dvd_trans (phasePeriod_dvd_of_le hle hi) (chooseLevel_dvd L q t)
  · intro hdvd
    by_contra hlt
    exact not_dvd_of_lt_chooseLevel (Nat.lt_of_not_le hlt) hdvd

theorem lastRebuild_le (q L i t : ℕ) : lastRebuild q L i t ≤ t := by
  unfold lastRebuild
  rw [mul_comm]
  exact Nat.mul_div_le t (phasePeriod q L i)

theorem lastRebuild_dvd (q L i t : ℕ) : phasePeriod q L i ∣ lastRebuild q L i t :=
  dvd_mul_left _ _

theorem lastRebuild_chooseLevel_le {q L i t : ℕ} (hq : 1 ≤ q) (hi : i ≤ L) :
    chooseLevel L q (lastRebuild q L i t) ≤ i :=
  (chooseLevel_le_iff_dvd hq hi).mpr (lastRebuild_dvd q L i t)

theorem lt_chooseLevel_between_lastRebuild {q L i t s : ℕ} (hq : 1 ≤ q) (hi : i ≤ L)
    (hgt : lastRebuild q L i t < s) (hle : s ≤ t) :
    i < chooseLevel L q s := by
  by_contra hle_i
  have hdvd : phasePeriod q L i ∣ s :=
    (chooseLevel_le_iff_dvd hq hi).mp (Nat.le_of_not_lt hle_i)
  obtain ⟨k, hk⟩ := hdvd
  have hBpos : 0 < phasePeriod q L i := phasePeriod_pos hq L i
  have hk_le : k ≤ t / phasePeriod q L i := by
    rw [Nat.le_div_iff_mul_le hBpos]
    linarith [hk]
  have hs_le : s ≤ lastRebuild q L i t := by
    unfold lastRebuild
    calc s = phasePeriod q L i * k := hk
      _ = k * phasePeriod q L i := mul_comm _ _
      _ ≤ (t / phasePeriod q L i) * phasePeriod q L i := Nat.mul_le_mul_right _ hk_le
  omega

theorem lastRebuild_lt_of_lt_chooseLevel {q L i t : ℕ} (hq : 1 ≤ q) (hi : i ≤ L)
    (hlt : i < chooseLevel L q t) : lastRebuild q L i t < t := by
  refine lt_of_le_of_ne (lastRebuild_le q L i t) ?_
  intro heq
  have hdvd : phasePeriod q L i ∣ t := heq ▸ lastRebuild_dvd q L i t
  have hle := (chooseLevel_le_iff_dvd hq hi).mpr hdvd
  omega

theorem card_multiples_le (B T : ℕ) (hB : 0 < B) :
    ((Finset.Icc 1 T).filter fun s => B ∣ s).card ≤ T / B := by
  have hsub : ((Finset.Icc 1 T).filter fun s => B ∣ s) ⊆
      (Finset.Icc 1 (T / B)).image (fun k => B * k) := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_Icc] at hs
    rcases hs with ⟨⟨hs1, hsT⟩, ⟨k, rfl⟩⟩
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · by_contra hk0
      have hk : k = 0 := by omega
      subst hk; simp at hs1
    · rw [Nat.le_div_iff_mul_le hB]
      linarith
  calc ((Finset.Icc 1 T).filter fun s => B ∣ s).card
      ≤ ((Finset.Icc 1 (T / B)).image (fun k => B * k)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (T / B)).card := Finset.card_image_le
    _ = T / B := by simp

end

end PhaseLemmas

section EmbLookup

@[expose] public section

private theorem find?_range_rev_spec {n : ℕ} (p : ℕ → Bool) (h0 : 0 < n) (hp0 : p 0 = true) :
    ∃ i, (List.range n).reverse.find? p = some i ∧ i < n ∧ p i = true ∧
      ∀ k, i < k → k < n → p k = false := by
  have hne : ∃ a ∈ (List.range n).reverse, p a = true :=
    ⟨0, List.mem_reverse.mpr (List.mem_range.mpr h0), hp0⟩
  cases hfind : (List.range n).reverse.find? p with
  | none =>
    exfalso
    obtain ⟨a, ha, hpa⟩ := hne
    have hnone := List.find?_eq_none.mp hfind a ha
    simp [hpa] at hnone
  | some i =>
    obtain ⟨hpi, idx, hidx, hget, hprev⟩ := List.find?_eq_some_iff_getElem.mp hfind
    have himem : i ∈ (List.range n).reverse := List.mem_of_find?_eq_some hfind
    have hin : i < n := List.mem_range.mp (List.mem_reverse.mp himem)
    refine ⟨i, rfl, hin, hpi, fun k hik hkn => ?_⟩
    have hlen : (List.range n).reverse.length = n := by simp
    have hi_rev : idx = n - 1 - i := by
      have h1 : (List.range n).reverse[idx] = n - 1 - idx := by simp
      rw [hget] at h1
      rw [hlen] at hidx
      omega
    have hlt_idx : n - 1 - k < idx := by omega
    have hprevk := hprev (n - 1 - k) hlt_idx
    have hval : (List.range n).reverse[n - 1 - k] = k := by
      simp
      omega
    rw [hval] at hprevk
    simpa using hprevk

theorem findEmbLevel_spec {L : ℕ} (inDom : Fin (L + 1) → Finset ℕ) {j e : ℕ}
    (hj : 0 < j) (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩) :
    let i := findEmbLevel inDom j e
    ∃ hi : i < L + 1,
      i < j ∧ e ∈ inDom ⟨i, hi⟩ ∧
      (∀ k (hk : k < L + 1), i < k → k < j → e ∉ inDom ⟨k, hk⟩) := by
  have hn : 0 < min j (L + 1) := lt_min hj (Nat.zero_lt_succ L)
  let p : ℕ → Bool := fun i => if h : i < L + 1 then decide (e ∈ inDom ⟨i, h⟩) else false
  have hp0 : p 0 = true := by
    simp only [p, Nat.zero_lt_succ, ↓reduceDIte, decide_eq_true_eq]
    exact h0
  obtain ⟨i, hfind, himin, hpi, hprev⟩ := find?_range_rev_spec p hn hp0
  have hiL : i < L + 1 := lt_of_lt_of_le himin (min_le_right _ _)
  have hij : i < j := lt_of_lt_of_le himin (min_le_left _ _)
  have hie : e ∈ inDom ⟨i, hiL⟩ := by
    simp only [p, hiL, ↓reduceDIte, decide_eq_true_eq] at hpi
    exact hpi
  have hfind_eq : findEmbLevel inDom j e = i := by
    unfold findEmbLevel
    change ((List.range (min j (L + 1))).reverse.find? p).getD 0 = i
    rw [hfind]
    rfl
  rw [hfind_eq]
  refine ⟨hiL, hij, hie, fun k hk hik hkj => ?_⟩
  have hkmin : k < min j (L + 1) := lt_min hkj hk
  have hpk := hprev k hik hkmin
  simp only [p, hk, ↓reduceDIte, decide_eq_false_iff_not] at hpk
  exact hpk

theorem piLtFrom_eq {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) {j e : ℕ}
    (hj : 0 < j) (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩) :
    ∃ (i : Fin (L + 1)), i.1 < j ∧ e ∈ inDom i ∧
      (∀ k : Fin (L + 1), i.1 < k.1 → k.1 < j → e ∉ inDom k) ∧
      piLtFrom Pi_level inDom j e = Pi_level i e := by
  obtain ⟨hiL, hij, hie, hnone⟩ := findEmbLevel_spec inDom hj h0
  refine ⟨⟨findEmbLevel inDom j e, hiL⟩, hij, hie, fun k hik hkj => hnone k.1 k.2 hik hkj, ?_⟩
  unfold piLtFrom
  simp only [hiL, ↓reduceDIte]

private theorem find?_congr_list :
    ∀ (l : List ℕ) (p₁ p₂ : ℕ → Bool), (∀ x ∈ l, p₁ x = p₂ x) → l.find? p₁ = l.find? p₂
  | [], _, _, _ => rfl
  | a :: l, p₁, p₂, h => by
    simp only [List.find?_cons, h a List.mem_cons_self]
    cases p₂ a
    · exact find?_congr_list l p₁ p₂ fun x hx => h x (List.mem_cons_of_mem _ hx)
    · rfl

theorem piLtFrom_congr_inDom {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    {inDom₁ inDom₂ : Fin (L + 1) → Finset ℕ} {j e : ℕ}
    (h : ∀ i : Fin (L + 1), i.1 < j → (e ∈ inDom₁ i ↔ e ∈ inDom₂ i)) :
    piLtFrom Pi_level inDom₁ j e = piLtFrom Pi_level inDom₂ j e := by
  have hfind : findEmbLevel inDom₁ j e = findEmbLevel inDom₂ j e := by
    unfold findEmbLevel
    congr 1
    refine find?_congr_list _ _ _ fun x hx => ?_
    have hlt : x < j := lt_of_lt_of_le (List.mem_range.mp (List.mem_reverse.mp hx)) (min_le_left _ _)
    split_ifs with hxL
    · simp only [decide_eq_decide]
      exact h ⟨x, hxL⟩ hlt
    · rfl
  unfold piLtFrom
  rw [hfind]

theorem piLtFrom_eq_of_lt {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) {j₁ j₂ e : ℕ}
    (hj₁ : 0 < j₁) (hle : j₁ ≤ j₂) (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩)
    (hempty : ∀ k : Fin (L + 1), j₁ ≤ k.1 → k.1 < j₂ → e ∉ inDom k) :
    piLtFrom Pi_level inDom j₂ e = piLtFrom Pi_level inDom j₁ e := by
  obtain ⟨i₁, hi₁j, hi₁dom, hi₁none, heq₁⟩ := piLtFrom_eq Pi_level inDom hj₁ h0
  obtain ⟨i₂, hi₂j, hi₂dom, hi₂none, heq₂⟩ := piLtFrom_eq Pi_level inDom (lt_of_lt_of_le hj₁ hle) h0
  rw [heq₁, heq₂]
  have hi₂_lt : i₂.1 < j₁ := by
    by_contra hge
    exact hempty i₂ (Nat.le_of_not_lt hge) hi₂j hi₂dom
  have hi_eq : i₁ = i₂ := by
    ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h12 | h21
    · exact hi₁none i₂ h12 hi₂_lt hi₂dom
    · exact hi₂none i₁ h21 (lt_of_lt_of_le hi₁j hle) hi₁dom
  rw [hi_eq]

theorem piLtFrom_eq_self_of_mem {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) {j : Fin (L + 1)} {e : ℕ}
    (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩) (hj : e ∈ inDom j) :
    piLtFrom Pi_level inDom (j.1 + 1) e = Pi_level j e := by
  obtain ⟨i, hij, hidom, hnone, heq⟩ :=
    piLtFrom_eq Pi_level inDom (Nat.succ_pos j.1) h0
  rw [heq]
  have hi_eq : i = j := by
    ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hnone j hlt (Nat.lt_succ_self _) hj
    · exact absurd (Nat.lt_succ_iff.mp hij) (not_le_of_gt hgt)
  rw [hi_eq]

theorem piLtFrom_eq_prev_of_not_mem {L : ℕ} (Pi_level : Fin (L + 1) → Embedding)
    (inDom : Fin (L + 1) → Finset ℕ) {j : Fin (L + 1)} {e : ℕ}
    (hjpos : 0 < j.1) (h0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩) (hnj : e ∉ inDom j) :
    piLtFrom Pi_level inDom (j.1 + 1) e = piLtFrom Pi_level inDom j.1 e := by
  refine piLtFrom_eq_of_lt Pi_level inDom hjpos (Nat.le_succ j.1) h0 ?_
  intro k hjk hkj
  have hk_eq : k = j := Fin.ext (by omega)
  rwa [hk_eq]

end

end EmbLookup

section PrefixWalkLemmas

@[expose] public section

/-- A sequence of valid deletion/split updates preserves `G.IsValid`, decreases `E`, increases `V`,
and tracks vertex ancestors via `batchAnc`. -/
theorem batch_delOrSplit_invariants :
    ∀ (us : List Update) (G₀ : MGraph),
      G₀.IsValid → G₀.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      let Gk := G₀.applyBatch us
      Gk.IsValid ∧
      Gk.E ⊆ G₀.E ∧
      G₀.V ⊆ Gk.V ∧
      Gk.maxDeg ≤ G₀.maxDeg ∧
      (∀ z ∈ Gk.V, batchAnc us z ∈ G₀.V) ∧
      (∀ z ∈ G₀.V, batchAnc us z = z) ∧
      (∀ e ∈ G₀.E, batchAnc us (Gk.tail e) = G₀.tail e ∧ batchAnc us (Gk.head e) = G₀.head e)
  | [], G₀, hV, _, _ => by
    simp only [MGraph.applyBatch, List.foldl_nil]
    exact ⟨hV, Finset.Subset.rfl, Finset.Subset.rfl, le_rfl, fun _ h => h, fun _ _ => rfl,
      fun _ _ => ⟨rfl, rfl⟩⟩
  | u :: us, G₀, hV, hBV, hds => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hds_u : isDelOrSplit u := hds u List.mem_cons_self
    have hds' : ∀ u' ∈ us, isDelOrSplit u' := fun u' hu' => hds u' (List.mem_cons_of_mem _ hu')
    have hV1 : (G₀.applyUpdate u).IsValid := isValid_applyUpdate_of_delOrSplit hV hu hds_u
    have ih := batch_delOrSplit_invariants us (G₀.applyUpdate u) hV1 hBV' hds'
    rcases ih with ⟨hVk, hEk, hVsubk, hDegk, hAncMem, hAncEq, hAncEnds⟩
    simp only [MGraph.applyBatch, List.foldl_cons, batchAnc_cons]
    refine ⟨hVk, Finset.Subset.trans hEk (E_applyUpdate_subset hds_u),
      Finset.Subset.trans (V_subset_applyUpdate hds_u) hVsubk,
      le_trans hDegk (maxDeg_applyUpdate_le hV hu hds_u), ?_, ?_, ?_⟩
    · intro z hz
      exact stepAnc_mem hV hu hds_u _ (hAncMem z hz)
    · intro z hz
      rw [hAncEq z (V_subset_applyUpdate hds_u hz), stepAnc_eq_of_mem hu hds_u z hz]
    · intro e he
      by_cases he1 : e ∈ (G₀.applyUpdate u).E
      · obtain ⟨ht1, hh1⟩ := hAncEnds e he1
        simp only [MGraph.applyBatch] at ht1 hh1 ⊢
        rw [ht1, hh1]
        exact stepAnc_tail_head hV hu hds_u e he
      · -- `e` was deleted by `u`, so `u = .delete e`, `G₁ = {G₀ with E := G₀.E.erase e}`
        cases u with
        | insert _ _ _ => exact hds_u.elim
        | split _ _ _ _ =>
          exact absurd he (by simpa [MGraph.applyUpdate] using he1)
        | delete d =>
          -- `e` is not in `G₁.E`, so no split in `us` moves `e`, and `tail e` and `head e` at `G_k`
          -- still equal `G₀.tail e` and `G₀.head e`.
          have hstay : ∀ (us' : List Update) (G' : MGraph),
              G'.BatchIsValid us' → (∀ u' ∈ us', isDelOrSplit u') → e ∉ G'.E →
              (G'.applyBatch us').tail e = G'.tail e ∧
              (G'.applyBatch us').head e = G'.head e := by
            intro us' G' hBV'' hds'' he'
            induction us' generalizing G' with
            | nil => simp [MGraph.applyBatch]
            | cons u' rest ih' =>
              obtain ⟨hu', hrest⟩ := hBV''
              have hdu' := hds'' u' List.mem_cons_self
              have he'' : e ∉ (G'.applyUpdate u').E := fun h => he' (E_applyUpdate_subset hdu' h)
              obtain ⟨ht_r, hh_r⟩ := ih' (G'.applyUpdate u') hrest
                (fun x hx => hds'' x (List.mem_cons_of_mem _ hx)) he''
              simp only [MGraph.applyBatch, List.foldl_cons] at ht_r hh_r ⊢
              rw [ht_r, hh_r]
              cases u' with
              | insert _ _ _ => exact hdu'.elim
              | delete _ => simp [MGraph.applyUpdate]
              | split _ _ St' Sh' =>
                have heSt' : e ∉ St' := fun h => he' (hu'.2.2.1 (Finset.mem_union_left _ h))
                have heSh' : e ∉ Sh' := fun h => he' (hu'.2.2.1 (Finset.mem_union_right _ h))
                simp [MGraph.applyUpdate, heSt', heSh']
          obtain ⟨htk, hhk⟩ := hstay us (G₀.applyUpdate (.delete d)) hBV' hds' he1
          simp only [MGraph.applyBatch] at htk hhk
          rw [htk, hhk]
          simp only [MGraph.applyUpdate]
          have htd : G₀.tail e ∈ (G₀.applyUpdate (.delete d)).V := (hV e he).1
          have hhd : G₀.head e ∈ (G₀.applyUpdate (.delete d)).V := (hV e he).2
          rw [hAncEq _ htd, hAncEq _ hhd]
          exact ⟨rfl, rfl⟩

/-- `walkVertices` of `w` in `H_k` maps via `batchAnc us` to `walkVertices` of `w` in `H₀`. -/
theorem walkVertices_batchAnc {us : List Update} {G₀ H₀ Hk : MGraph}
    (hV : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hSub₀ : G₀.IsSubgraph H₀)
    (hEnds : ∀ e ∈ H₀.E, Hk.tail e = (G₀.applyBatch us).tail e ∧
      Hk.head e = (G₀.applyBatch us).head e)
    {w : List (ℕ × Bool)} (hw : ∀ x ∈ w, x.1 ∈ H₀.E)
    {a a₀ : ℕ} (ha : batchAnc us a = a₀) :
    (Hk.walkVertices a w).map (batchAnc us) = H₀.walkVertices a₀ w := by
  have hAnc := (batch_delOrSplit_invariants us G₀ hV hBV hds).2.2.2.2.2.2
  simp only [MGraph.walkVertices, List.map_cons, List.map_map, ha, List.cons.injEq, true_and]
  refine List.map_congr_left fun x hx => ?_
  have hxH : x.1 ∈ H₀.E := hw x hx
  have hxG : x.1 ∈ G₀.E := hSub₀.2.1 hxH
  obtain ⟨htHk, hhHk⟩ := hEnds x.1 hxH
  obtain ⟨htH0, hhH0⟩ := hSub₀.2.2 x.1 hxH
  obtain ⟨htAnc, hhAnc⟩ := hAnc x.1 hxG
  cases xb : x.2
  · simp [MGraph.dst, xb, htHk, htAnc, htH0]
  · simp [MGraph.dst, xb, hhHk, hhAnc, hhH0]

/-- Track touched vertices along a sequence of updates `us` starting at `G₀`. -/
def allTouched (G₀ : MGraph) : List Update → Finset ℕ
  | [] => ∅
  | u :: us => touchedVertices G₀ u ∪ allTouched (G₀.applyUpdate u) us

theorem allTouched_subset_V :
    ∀ (us : List Update) (G₀ : MGraph),
      G₀.IsValid → G₀.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      allTouched G₀ us ⊆ (G₀.applyBatch us).V
  | [], G₀, _, _, _ => by simp [allTouched]
  | u :: us, G₀, hV, hBV, hds => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hV1 := isValid_applyUpdate_of_delOrSplit hV hu hdu
    have hSubV := (batch_delOrSplit_invariants us (G₀.applyUpdate u) hV1 hBV'
      (fun x hx => hds x (List.mem_cons_of_mem _ hx))).2.2.1
    rw [MGraph.applyBatch, List.foldl_cons, allTouched]
    refine Finset.union_subset ?_ (allTouched_subset_V us (G₀.applyUpdate u) hV1 hBV'
      (fun x hx => hds x (List.mem_cons_of_mem _ hx)))
    refine Finset.Subset.trans ?_ hSubV
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete e =>
      intro v hv
      simp only [touchedVertices, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (hV e hu).1
      · exact (hV e hu).2
    | split v v' _ _ =>
      intro z hz
      simp only [touchedVertices, Finset.mem_insert, Finset.mem_singleton,
        MGraph.applyUpdate] at hz ⊢
      rcases hz with rfl | rfl
      · right; exact hu.1
      · left; rfl

theorem card_allTouched_le :
    ∀ (us : List Update) (G₀ : MGraph), (allTouched G₀ us).card ≤ 2 * us.length
  | [], _ => by simp [allTouched]
  | u :: us, G₀ => by
    simp only [allTouched, List.length_cons]
    have h1 := Finset.card_union_le (touchedVertices G₀ u) (allTouched (G₀.applyUpdate u) us)
    have h2 := card_touchedVertices_le_two G₀ u
    have h3 := card_allTouched_le us (G₀.applyUpdate u)
    omega

/-- Any vertex outside `allTouched G₀ us` that is in `G_k.V` was already in `G₀.V`, has
`batchAnc us z = z`, and keeps every incident edge-end in `G_k.E` at `z`. -/
theorem not_mem_allTouched_invariants :
    ∀ (us : List Update) (G₀ : MGraph),
      G₀.IsValid → G₀.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      ∀ z ∉ allTouched G₀ us,
        (z ∈ (G₀.applyBatch us).V → z ∈ G₀.V) ∧
        (z ∈ G₀.V → batchAnc us z = z) ∧
        (∀ e ∈ G₀.E,
          (G₀.tail e = z → e ∈ (G₀.applyBatch us).E ∧ (G₀.applyBatch us).tail e = z) ∧
          (G₀.head e = z → e ∈ (G₀.applyBatch us).E ∧ (G₀.applyBatch us).head e = z))
  | [], G₀, _, _, _, z, _ => by
    simp only [MGraph.applyBatch, List.foldl_nil, batchAnc]
    exact ⟨fun h => h, fun _ => rfl, fun _ he => ⟨fun h => ⟨he, h⟩, fun h => ⟨he, h⟩⟩⟩
  | u :: us, G₀, hV, hBV, hds, z, hz => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ us, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have hV1 := isValid_applyUpdate_of_delOrSplit hV hu hdu
    simp only [allTouched, Finset.mem_union, not_or] at hz
    obtain ⟨hz_u, hz_rest⟩ := hz
    obtain ⟨hmem_ih, hanc_ih, hedge_ih⟩ :=
      not_mem_allTouched_invariants us (G₀.applyUpdate u) hV1 hBV' hds' z hz_rest
    simp only [MGraph.applyBatch, List.foldl_cons]
    have hz_in_V1 : z ∈ (G₀.applyUpdate u).V → z ∈ G₀.V := by
      intro hz1
      cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact hz1
      | split v v' _ _ =>
        simp only [MGraph.applyUpdate, Finset.mem_insert] at hz1
        rcases hz1 with hzv' | hz0
        · rw [hzv'] at hz_u
          exact absurd (by simp [touchedVertices]) hz_u
        · exact hz0
    refine ⟨fun hzk => hz_in_V1 (hmem_ih hzk), fun hz0 => ?_, fun e he0 => ?_⟩
    · rw [batchAnc_cons, hanc_ih (V_subset_applyUpdate hdu hz0), stepAnc_eq_of_mem hu hdu z hz0]
    · constructor
      · intro htz
        have hstep_u : e ∈ (G₀.applyUpdate u).E ∧ (G₀.applyUpdate u).tail e = z := by
          cases u with
          | insert _ _ _ => exact hdu.elim
          | delete d =>
            have hne : e ≠ d := by
              intro heq; subst heq
              exact hz_u (by simp [touchedVertices, htz])
            simp [MGraph.applyUpdate, he0, hne, htz]
          | split v v' _ _ =>
            have hzv : z ≠ v := by
              intro hzv
              exact hz_u (by simp [touchedVertices, hzv])
            simp [MGraph.applyUpdate, he0, hzv, htz]
        exact hedge_ih e hstep_u.1 |>.1 hstep_u.2
      · intro hhz
        have hstep_u : e ∈ (G₀.applyUpdate u).E ∧ (G₀.applyUpdate u).head e = z := by
          cases u with
          | insert _ _ _ => exact hdu.elim
          | delete d =>
            have hne : e ≠ d := by
              intro heq; subst heq
              exact hz_u (by simp [touchedVertices, hhz])
            simp [MGraph.applyUpdate, he0, hne, hhz]
          | split v v' _ _ =>
            have hzv : z ≠ v := by
              intro hzv
              exact hz_u (by simp [touchedVertices, hzv])
            simp [MGraph.applyUpdate, he0, hzv, hhz]
        exact hedge_ih e hstep_u.1 |>.2 hstep_u.2

theorem prefixWalk_append_of_not_mem (H : MGraph) (S : Finset ℕ) :
    ∀ (p₁ W : List (ℕ × Bool)) (a : ℕ),
      (∀ z ∈ (H.walkVertices a p₁).dropLast, z ∉ S) →
      p₁ <+: (prefixWalk H a (p₁ ++ W) S).2
  | [], _, _, _ => List.nil_prefix
  | x :: p₁, W, a, h => by
    have ha : a ∉ S := h a (by simp [MGraph.walkVertices])
    have ih := prefixWalk_append_of_not_mem H S p₁ W (H.dst x) fun z hz => by
      apply h z
      simp only [MGraph.walkVertices, List.map_cons, List.dropLast_cons_of_ne_nil
        (List.cons_ne_nil _ _), List.mem_cons]
      right
      exact hz
    unfold prefixWalk
    simp only [ha, ↓reduceIte, List.cons_append]
    exact List.cons_prefix_cons.mpr ⟨rfl, ih⟩

/-- Key invariant of `prefixWalk` under valid deletions and vertex splits:
* If no vertex of `H_k.walkVertices a w` lies in `S`, then `w` survives as a walk in `H_k` from `a`
  to `b₀`, with `a = a₀` and `H_k.walkVertices a w = H₀.walkVertices a₀ w`.
* If some vertex of `H_k.walkVertices a w` lies in `S`, then `prefixWalk H_k a w S` returns
  `(â, p₁)` where `â ∈ S ∩ G_k.V`, `H_k.IsWalk a â p₁`, `p₁ <+: w`, every vertex of
  `H_k.walkVertices a p₁` maps via `batchAnc us` into `H₀.walkVertices a₀ w`, and every vertex in
  `(H_k.walkVertices a p₁).dropLast` is not in `S` (and fixed by `batchAnc us`). -/
theorem prefixWalk_spec {us : List Update} {G₀ H₀ Hk : MGraph} {S : Finset ℕ}
    (hV : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hSub₀ : G₀.IsSubgraph H₀) (hSub_k : (G₀.applyBatch us).IsSubgraph Hk)
    (hHkV : Hk.V = (G₀.applyBatch us).V) (hHkE : Hk.E = H₀.E ∩ (G₀.applyBatch us).E)
    (hEnds : ∀ e ∈ H₀.E, Hk.tail e = (G₀.applyBatch us).tail e ∧
      Hk.head e = (G₀.applyBatch us).head e)
    (hTouch : allTouched G₀ us ⊆ S) :
    ∀ (w : List (ℕ × Bool)) (a₀ b₀ a : ℕ),
      a₀ ∈ G₀.V → b₀ ∈ G₀.V → H₀.IsWalk a₀ b₀ w →
      a ∈ (G₀.applyBatch us).V → batchAnc us a = a₀ →
      (Disjoint (Hk.walkVertices a w).toFinset S →
        a = a₀ ∧ Hk.IsWalk a b₀ w ∧ Hk.walkVertices a w = H₀.walkVertices a₀ w) ∧
      ((∃ z ∈ Hk.walkVertices a w, z ∈ S) →
        let res := prefixWalk Hk a w S
        res.1 ∈ S ∧ res.1 ∈ (G₀.applyBatch us).V ∧
        Hk.IsWalk a res.1 res.2 ∧ res.2 <+: w ∧
        (∀ z ∈ Hk.walkVertices a res.2, batchAnc us z ∈ H₀.walkVertices a₀ w) ∧
        (∀ z ∈ (Hk.walkVertices a res.2).dropLast,
          z ∉ S ∧ z ∈ G₀.V ∧ batchAnc us z = z))
  | [], a₀, b₀, a, ha₀, _hb₀, hw, ha, hanca => by
    obtain ⟨rfl⟩ : a₀ = b₀ := by cases hw; rfl
    have ha_eq : a ∉ S → a = a₀ := fun haS => by
      have haNT : a ∉ allTouched G₀ us := fun h => haS (hTouch h)
      have hinv := not_mem_allTouched_invariants us G₀ hV hBV hds a haNT
      rw [← hanca, hinv.2.1 (hinv.1 ha)]
    constructor
    · intro hdisj
      have haS : a ∉ S := fun h =>
        (Finset.disjoint_left.mp hdisj) (by simp [MGraph.walkVertices]) h
      have hxeq := ha_eq haS
      subst hxeq
      exact ⟨rfl, .nil a, rfl⟩
    · rintro ⟨z, hz, hzS⟩
      simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hz
      have haS : a ∈ S := hz ▸ hzS
      simp only [prefixWalk, haS, ↓reduceIte, List.nil_prefix, true_and]
      refine ⟨ha, .nil a, fun z' hz' => ?_, fun z' hz' => ?_⟩
      · simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hz'
        subst hz'
        simp [MGraph.walkVertices, hanca]
      · simp [MGraph.walkVertices] at hz'
  | x :: w', a₀, b₀, a, ha₀, hb₀, hw, ha, hanca => by
    cases hw with
    | cons hxE₀ hsrc₀ hrest =>
      have hxG₀ : x.1 ∈ G₀.E := hSub₀.2.1 hxE₀
      have hVk : (G₀.applyBatch us).IsValid :=
        (batch_delOrSplit_invariants us G₀ hV hBV hds).1
      have hAncEnds := (batch_delOrSplit_invariants us G₀ hV hBV hds).2.2.2.2.2.2 x.1 hxG₀
      have hAncMem := (batch_delOrSplit_invariants us G₀ hV hBV hds).2.2.2.2.1
      have hd₀_mem : H₀.dst x ∈ G₀.V := by
        obtain ⟨ht₀, hh₀⟩ := hSub₀.2.2 x.1 hxE₀
        cases xb : x.2
        · simp [MGraph.dst, xb, ht₀]; exact (hV x.1 hxG₀).1
        · simp [MGraph.dst, xb, hh₀]; exact (hV x.1 hxG₀).2
      have hstep_if_not : a ∉ S →
          a = a₀ ∧ x.1 ∈ Hk.E ∧ Hk.src x = a ∧
          Hk.dst x ∈ (G₀.applyBatch us).V ∧ batchAnc us (Hk.dst x) = H₀.dst x := by
        intro haS
        have haNT : a ∉ allTouched G₀ us := fun h => haS (hTouch h)
        have hinv := not_mem_allTouched_invariants us G₀ hV hBV hds a haNT
        have ha_eq : a = a₀ := by rw [← hanca, hinv.2.1 (hinv.1 ha)]
        obtain ⟨htH0, hhH0⟩ := hSub₀.2.2 x.1 hxE₀
        obtain ⟨htHk, hhHk⟩ := hEnds x.1 hxE₀
        have hx_surv : x.1 ∈ (G₀.applyBatch us).E := by
          cases xb : x.2
          · have hh0 : G₀.head x.1 = a := by
              have hs : H₀.src x = H₀.head x.1 := by simp [MGraph.src, xb]
              rw [← hhH0, ← hs, hsrc₀, ha_eq]
            exact (hinv.2.2 x.1 hxG₀).2 hh0 |>.1
          · have ht0 : G₀.tail x.1 = a := by
              have hs : H₀.src x = H₀.tail x.1 := by simp [MGraph.src, xb]
              rw [← htH0, ← hs, hsrc₀, ha_eq]
            exact (hinv.2.2 x.1 hxG₀).1 ht0 |>.1
        have hxHkE : x.1 ∈ Hk.E := by rw [hHkE]; exact Finset.mem_inter.mpr ⟨hxE₀, hx_surv⟩
        have hsrc_k : Hk.src x = a := by
          cases xb : x.2
          · have hh0 : G₀.head x.1 = a := by
              have hs : H₀.src x = H₀.head x.1 := by simp [MGraph.src, xb]
              rw [← hhH0, ← hs, hsrc₀, ha_eq]
            have hh_k := ((hinv.2.2 x.1 hxG₀).2 hh0).2
            simp [MGraph.src, xb, hhHk, hh_k]
          · have ht0 : G₀.tail x.1 = a := by
              have hs : H₀.src x = H₀.tail x.1 := by simp [MGraph.src, xb]
              rw [← htH0, ← hs, hsrc₀, ha_eq]
            have ht_k := ((hinv.2.2 x.1 hxG₀).1 ht0).2
            simp [MGraph.src, xb, htHk, ht_k]
        have hdst_V : Hk.dst x ∈ (G₀.applyBatch us).V := by
          cases xb : x.2
          · simp only [MGraph.dst, xb, Bool.false_eq_true, ↓reduceIte, htHk]
            exact (hVk x.1 hx_surv).1
          · simp only [MGraph.dst, xb, ↓reduceIte, hhHk]
            exact (hVk x.1 hx_surv).2
        have hdst_anc : batchAnc us (Hk.dst x) = H₀.dst x := by
          cases xb : x.2
          · simp [MGraph.dst, xb, htHk, hAncEnds.1, htH0]
          · simp [MGraph.dst, xb, hhHk, hAncEnds.2, hhH0]
        exact ⟨ha_eq, hxHkE, hsrc_k, hdst_V, hdst_anc⟩
      constructor
      · intro hdisj
        have haS : a ∉ S := fun h =>
          (Finset.disjoint_left.mp hdisj) (by simp [MGraph.walkVertices]) h
        obtain ⟨ha_eq, hxHkE, hsrc_k, hdst_V, hdst_anc⟩ := hstep_if_not haS
        have hdisj' : Disjoint (Hk.walkVertices (Hk.dst x) w').toFinset S := by
          rw [Finset.disjoint_left]
          intro z hz
          apply Finset.disjoint_left.mp hdisj
          simp only [List.mem_toFinset, MGraph.walkVertices, List.map_cons, List.mem_cons] at hz ⊢
          right
          exact hz
        obtain ⟨hd_eq, hwalk_rest, hverts_rest⟩ :=
          (prefixWalk_spec hV hBV hds hSub₀ hSub_k hHkV hHkE hEnds hTouch
            w' (H₀.dst x) b₀ (Hk.dst x) hd₀_mem hb₀ hrest hdst_V hdst_anc).1 hdisj'
        refine ⟨ha_eq, .cons hxHkE hsrc_k hwalk_rest, ?_⟩
        simp only [MGraph.walkVertices, List.map_cons] at hverts_rest ⊢
        rw [ha_eq, hverts_rest]
      · rintro ⟨z, hz, hzS⟩
        by_cases haS : a ∈ S
        · simp only [prefixWalk, haS, ↓reduceIte, List.nil_prefix, true_and]
          refine ⟨ha, .nil a, fun z' hz' => ?_, fun z' hz' => ?_⟩
          · simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hz'
            subst hz'
            rw [hanca]
            exact mem_walkVertices_start _ _ _
          · simp [MGraph.walkVertices] at hz'
        · obtain ⟨ha_eq, hxHkE, hsrc_k, hdst_V, hdst_anc⟩ := hstep_if_not haS
          have hz_rest : ∃ z ∈ Hk.walkVertices (Hk.dst x) w', z ∈ S := by
            simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz
            rcases hz with rfl | rfl | hz'
            · exact absurd hzS haS
            · exact ⟨Hk.dst x, mem_walkVertices_start _ _ _, hzS⟩
            · exact ⟨z, by simp [MGraph.walkVertices, hz'], hzS⟩
          have ih := (prefixWalk_spec hV hBV hds hSub₀ hSub_k hHkV hHkE hEnds hTouch
            w' (H₀.dst x) b₀ (Hk.dst x) hd₀_mem hb₀ hrest hdst_V hdst_anc).2 hz_rest
          dsimp only at ih
          rcases ih with ⟨hres1S, hres1V, hwalk_rest, hpref_rest, hanc_rest, hdrop_rest⟩
          simp only [prefixWalk, eq_false haS, ↓reduceIte]
          refine ⟨hres1S, hres1V, .cons hxHkE hsrc_k hwalk_rest,
            List.cons_prefix_cons.mpr ⟨rfl, hpref_rest⟩, fun z' hz' => ?_, fun z' hz' => ?_⟩
          · simp only [MGraph.walkVertices, List.map_cons, List.mem_cons] at hz'
            rcases hz' with rfl | hz''
            · rw [hanca]; exact mem_walkVertices_start _ _ _
            · simp only [MGraph.walkVertices, List.map_cons, List.mem_cons]
              right
              simpa [MGraph.walkVertices] using
                hanc_rest z' (by simpa [MGraph.walkVertices] using hz'')
          · simp only [MGraph.walkVertices, List.map_cons,
              List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.mem_cons] at hz'
            rcases hz' with hzeq | hz''
            · rw [hzeq]
              have haNT : a ∉ allTouched G₀ us := fun h => haS (hTouch h)
              have hinv := not_mem_allTouched_invariants us G₀ hV hBV hds a haNT
              exact ⟨haS, hinv.1 ha, hinv.2.1 (hinv.1 ha)⟩
            · exact hdrop_rest z' hz''

theorem batchAnc_mem_allTouched_of_ne :
    ∀ (us : List Update) (G₀ : MGraph),
      G₀.IsValid → G₀.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      ∀ z ∈ (G₀.applyBatch us).V, batchAnc us z ≠ z → batchAnc us z ∈ allTouched G₀ us
  | [], G₀, _, _, _, z, _, hne => absurd rfl hne
  | u :: us, G₀, hV, hBV, hds, z, hz, hne => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ us, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have hV1 := isValid_applyUpdate_of_delOrSplit hV hu hdu
    simp only [MGraph.applyBatch, List.foldl_cons] at hz
    have hyV1 : batchAnc us z ∈ (G₀.applyUpdate u).V :=
      (batch_delOrSplit_invariants us (G₀.applyUpdate u) hV1 hBV' hds').2.2.2.2.1 z hz
    simp only [batchAnc_cons, allTouched, Finset.mem_union]
    by_cases hy0 : batchAnc us z ∈ G₀.V
    · rw [batchAnc_cons] at hne
      rw [stepAnc_eq_of_mem hu hdu _ hy0] at hne ⊢
      right
      exact batchAnc_mem_allTouched_of_ne us (G₀.applyUpdate u) hV1 hBV' hds' z hz hne
    · cases u with
      | insert _ _ _ => exact hdu.elim
      | delete _ => exact absurd hy0 (fun h => h hyV1)
      | split v v' _ _ =>
        simp only [MGraph.applyUpdate, Finset.mem_insert] at hyV1
        have heq : batchAnc us z = v' := hyV1.resolve_right hy0
        left
        simp [stepAnc, heq, touchedVertices]

theorem mem_S_of_anc_mem_S {us : List Update} {G₀ : MGraph} {S : Finset ℕ}
    (hV : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hTouch : allTouched G₀ us ⊆ S) {z : ℕ} (hz : z ∈ (G₀.applyBatch us).V) (hzS : z ∈ S) :
    batchAnc us z ∈ S := by
  by_cases hne : batchAnc us z = z
  · rwa [hne]
  · exact hTouch (batchAnc_mem_allTouched_of_ne us G₀ hV hBV hds z hz hne)

theorem exists_mem_walkVertices_iff_anc {us : List Update} {G₀ H₀ Hk : MGraph} {S : Finset ℕ}
    (hV : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hSub₀ : G₀.IsSubgraph H₀)
    (hEnds : ∀ e ∈ H₀.E, Hk.tail e = (G₀.applyBatch us).tail e ∧
      Hk.head e = (G₀.applyBatch us).head e)
    (hTouch : allTouched G₀ us ⊆ S)
    {w : List (ℕ × Bool)} (hw : ∀ x ∈ w, x.1 ∈ H₀.E)
    {a a₀ : ℕ} (_ha : a ∈ (G₀.applyBatch us).V) (hanca : batchAnc us a = a₀)
    (hV_walk : ∀ z ∈ Hk.walkVertices a w, z ∈ (G₀.applyBatch us).V) :
    (∃ z ∈ Hk.walkVertices a w, z ∈ S) ↔ (∃ z₀ ∈ H₀.walkVertices a₀ w, z₀ ∈ S) := by
  have hmap := walkVertices_batchAnc hV hBV hds hSub₀ hEnds hw hanca
  constructor
  · rintro ⟨z, hz, hzS⟩
    refine ⟨batchAnc us z, ?_, mem_S_of_anc_mem_S hV hBV hds hTouch (hV_walk z hz) hzS⟩
    rw [← hmap]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
  · rintro ⟨z₀, hz₀, hz₀S⟩
    rw [← hmap, List.mem_map] at hz₀
    obtain ⟨z, hz, rfl⟩ := hz₀
    by_cases hzS : z ∈ S
    · exact ⟨z, hz, hzS⟩
    · have hzNT : z ∉ allTouched G₀ us := fun h => hzS (hTouch h)
      have hinv := not_mem_allTouched_invariants us G₀ hV hBV hds z hzNT
      have hzeq := hinv.2.1 (hinv.1 (hV_walk z hz))
      exact ⟨z, hz, hzeq ▸ hz₀S⟩

private theorem getLast_walkVertices_eq {H : MGraph} :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, H.IsWalk u v P →
      (H.walkVertices u P)[P.length]'(by simp [MGraph.walkVertices]) = v
  | u, _, [], .nil _ => rfl
  | _, v, x :: P, .cons _ _ hrest => by
    simpa [MGraph.walkVertices] using getLast_walkVertices_eq hrest

/-- Combined prefix + suffix length from `prefixWalk` on `w` and `walkRev w` is at most `w.length`. -/
theorem prefixWalk_length_add_le {us : List Update} {G₀ H₀ Hk : MGraph} {S : Finset ℕ}
    (hV : G₀.IsValid) (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u)
    (hSub₀ : G₀.IsSubgraph H₀) (hSub_k : (G₀.applyBatch us).IsSubgraph Hk)
    (hHkV : Hk.V = (G₀.applyBatch us).V) (hHkE : Hk.E = H₀.E ∩ (G₀.applyBatch us).E)
    (hEnds : ∀ e ∈ H₀.E, Hk.tail e = (G₀.applyBatch us).tail e ∧
      Hk.head e = (G₀.applyBatch us).head e)
    (hTouch : allTouched G₀ us ⊆ S)
    {w : List (ℕ × Bool)} {a₀ b₀ a b : ℕ}
    (ha₀ : a₀ ∈ G₀.V) (hb₀ : b₀ ∈ G₀.V) (hw : H₀.IsWalk a₀ b₀ w)
    (ha : a ∈ (G₀.applyBatch us).V) (hb : b ∈ (G₀.applyBatch us).V)
    (hanca : batchAnc us a = a₀) (hancb : batchAnc us b = b₀)
    (hHit : ∃ z ∈ Hk.walkVertices a w, z ∈ S)
    (hHitRev : ∃ z ∈ Hk.walkVertices b (walkRev w), z ∈ S) :
    (prefixWalk Hk a w S).2.length + (prefixWalk Hk b (walkRev w) S).2.length ≤ w.length := by
  have hp := (prefixWalk_spec hV hBV hds hSub₀ hSub_k hHkV hHkE hEnds hTouch
    w a₀ b₀ a ha₀ hb₀ hw ha hanca).2 hHit
  have hwRev := isWalk_walkRev hw
  have hq := (prefixWalk_spec hV hBV hds hSub₀ hSub_k hHkV hHkE hEnds hTouch
    (walkRev w) b₀ a₀ b hb₀ ha₀ hwRev hb hancb).2 hHitRev
  dsimp only at hp hq
  rcases hp with ⟨hp1S, hp1V, hpWalk, hpPref, _, _⟩
  rcases hq with ⟨hq1S, hq1V, hqWalk, hqPref, _, hqDrop⟩
  set p₁ := (prefixWalk Hk a w S).2
  set q := (prefixWalk Hk b (walkRev w) S).2
  have hpLen : p₁.length ≤ w.length := hpPref.length_le
  have hqLen : q.length ≤ w.length := by simpa [length_walkRev] using hqPref.length_le
  -- Locate `batchAnc us (prefixWalk Hk a w S).1` at index `p₁.length` of `H₀.walkVertices a₀ w`
  have hpBatch : batchAnc us (prefixWalk Hk a w S).1 ∈ S :=
    mem_S_of_anc_mem_S hV hBV hds hTouch hp1V hp1S
  have hpEdges : ∀ x ∈ p₁, x.1 ∈ H₀.E := fun x hx =>
    IsWalk.mem_edge hw x (hpPref.mem hx)
  have hpMap := walkVertices_batchAnc hV hBV hds hSub₀ hEnds hpEdges hanca
  have hpEnd : (Hk.walkVertices a p₁)[p₁.length]'(by simp [MGraph.walkVertices]) =
      (prefixWalk Hk a w S).1 := getLast_walkVertices_eq hpWalk
  have hpAt_opt : (H₀.walkVertices a₀ w)[p₁.length]? =
      some (batchAnc us (prefixWalk Hk a w S).1) := by
    have hprefV : H₀.walkVertices a₀ p₁ <+: H₀.walkVertices a₀ w := by
      obtain ⟨rest, hrest⟩ := hpPref
      simp only [MGraph.walkVertices, ← hrest, List.map_append]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append _ _⟩
    obtain ⟨rest, hrest⟩ := hprefV
    have hlt_len : p₁.length < (H₀.walkVertices a₀ p₁).length := by simp [MGraph.walkVertices]
    rw [← hrest, List.getElem?_append_left hlt_len, ← hpMap, List.getElem?_map,
      List.getElem?_eq_getElem (by simp [MGraph.walkVertices] : p₁.length < (Hk.walkVertices a p₁).length),
      Option.map_some, hpEnd]
  -- If `w.length < p₁.length + q.length`, then `w.length - p₁.length < q.length`,
  -- so `(H₀.walkVertices b₀ (walkRev w))[w.length - p₁.length]` would be `∉ S`, contradicting `hpBatch`
  by_contra hlt
  have hk_lt : w.length - p₁.length < q.length := by omega
  have hqEdges : ∀ x ∈ q, x.1 ∈ H₀.E := fun x hx =>
    IsWalk.mem_edge hwRev x (hqPref.mem hx)
  have hqMap := walkVertices_batchAnc hV hBV hds hSub₀ hEnds hqEdges hancb
  have hqPrefV : H₀.walkVertices b₀ q <+: H₀.walkVertices b₀ (walkRev w) := by
    obtain ⟨rest, hrest⟩ := hqPref
    simp only [MGraph.walkVertices, ← hrest, List.map_append]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append _ _⟩
  have hidx_q : w.length - p₁.length < (Hk.walkVertices b q).length := by
    simp [MGraph.walkVertices]; omega
  have hmemDrop : (Hk.walkVertices b q)[w.length - p₁.length]'hidx_q ∈
      (Hk.walkVertices b q).dropLast := by
    have hlt_len : w.length - p₁.length < (Hk.walkVertices b q).dropLast.length := by
      simp [MGraph.walkVertices]; omega
    have heq := List.getElem_dropLast (xs := Hk.walkVertices b q) hlt_len
    rw [← heq]
    exact List.getElem_mem _
  have hdrop := hqDrop _ hmemDrop
  have hnotS := hdrop.1
  have hanc_z := hdrop.2.2
  have hz_opt : (H₀.walkVertices b₀ (walkRev w))[w.length - p₁.length]? =
      some ((Hk.walkVertices b q)[w.length - p₁.length]'hidx_q) := by
    obtain ⟨rest, hrest⟩ := hqPrefV
    have hlt_len : w.length - p₁.length < (H₀.walkVertices b₀ q).length := by
      simp [MGraph.walkVertices]; omega
    rw [← hrest, List.getElem?_append_left hlt_len, ← hqMap, List.getElem?_map,
      List.getElem?_eq_getElem hidx_q, Option.map_some, hanc_z]
  have hrev := walkVertices_walkRev hw
  have hrev_len : (H₀.walkVertices a₀ w).length = w.length + 1 := by simp [MGraph.walkVertices]
  have hrev_opt : (H₀.walkVertices b₀ (walkRev w))[w.length - p₁.length]? =
      (H₀.walkVertices a₀ w)[p₁.length]? := by
    rw [hrev]
    have hlt_rev : w.length - p₁.length < (H₀.walkVertices a₀ w).length := by omega
    rw [List.getElem?_reverse hlt_rev]
    congr 1
    omega
  rw [hrev_opt, hpAt_opt] at hz_opt
  exact hnotS ((Option.some.inj hz_opt) ▸ hpBatch)

end

end PrefixWalkLemmas

end MinCostFlow.DynSpanner


