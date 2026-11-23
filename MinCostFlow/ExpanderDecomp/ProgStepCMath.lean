module

public import MinCostFlow.ExpanderDecomp.ProgStepCSpec
public import MinCostFlow.ExpanderDecomp.ProgPortGraphBase
import MinCostFlow.Expander.WordRAMHelpers

import Mathlib.Tactic.Linarith

/-!
# Pure Matching-Completion and Size Lemmas for Step C and Step B (`ProgStepCMath`)

Proves the pure mathematical lemmas shared by the Step C (`ProgStepC*.lean`) and Step B
(`ProgStepB*.lean`) Word-RAM procedures:

- `matchedVerts` and `mem_matchedVerts_iff`: flat endpoint set of `matchings.flatten`.
- `pairwise_lt_blockList`, `pairwise_lt_fullPrefix`, `pairwise_lt_leftoverList`, and
  `filter_eq_sort_sdiff`: filtering any strictly increasing list `l` by `u ∉ S` equals
  `(l.toFinset \ S).sort (· ≤ ·)`.
- `completeMatchingFake_eq_of_flat`: for any valid disjoint terminal-pair batch `pairs` and
  per-pair partial matchings `matchings`, filtering sorted lists for `pairs[j].1` and `pairs[j].2`
  by `matchedVerts matchings.flatten` and zipping equals `completeMatchingFake` identically.
- `matched_flatten_bounds`, `completeBatchFake_length_le_card`, `edgeColor17_length_le_five_mul`,
  and `colorClass_length_le`: exact size bounds ensuring all output and heap buffers fit.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- The finite set of all endpoints appearing in a flat edge list `ms`. -/
def matchedVerts (ms : List (ℕ × ℕ)) : Finset ℕ :=
  (ms.flatMap fun e => [e.1, e.2]).toFinset

lemma mem_matchedVerts_iff {ms : List (ℕ × ℕ)} {x : ℕ} :
    x ∈ matchedVerts ms ↔ ∃ e ∈ ms, x = e.1 ∨ x = e.2 := by
  simp [matchedVerts]

lemma pairwise_lt_take {l : List ℕ} (h : l.Pairwise (· < ·)) (n : ℕ) :
    (l.take n).Pairwise (· < ·) :=
  h.sublist (List.take_sublist n l)

lemma pairwise_lt_drop {l : List ℕ} (h : l.Pairwise (· < ·)) (n : ℕ) :
    (l.drop n).Pairwise (· < ·) :=
  h.sublist (List.drop_sublist n l)

lemma pairwise_lt_blockList {vs : List ℕ} (h : vs.Pairwise (· < ·)) (b i : ℕ) :
    (blockList vs b i).Pairwise (· < ·) :=
  pairwise_lt_take (pairwise_lt_drop h (i * b)) b

lemma pairwise_lt_fullPrefix {vs : List ℕ} (h : vs.Pairwise (· < ·)) (b : ℕ) :
    (fullPrefix vs b).Pairwise (· < ·) :=
  pairwise_lt_take h _

lemma pairwise_lt_leftoverList {vs : List ℕ} (h : vs.Pairwise (· < ·)) (b : ℕ) :
    (leftoverList vs b).Pairwise (· < ·) :=
  pairwise_lt_drop h _

lemma filter_eq_sort_sdiff {l : List ℕ} (h : l.Pairwise (· < ·)) (S : Finset ℕ) :
    l.filter (fun x => decide (x ∉ S)) = (l.toFinset \ S).sort (· ≤ ·) := by
  have hpf : (l.filter (fun x => decide (x ∉ S))).Pairwise (· < ·) :=
    h.filter (fun x => decide (x ∉ S))
  have hfin : (l.filter (fun x => decide (x ∉ S))).toFinset = l.toFinset \ S := by
    ext x
    simp [Finset.mem_sdiff]
  rw [← hfin]
  exact pairwise_lt_eq_sort _ hpf

private lemma pairwise_disjoint_pairs_sides {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hvtp : ValidTerminalPairs X pairs) {j j' : ℕ}
    (hj : j < pairs.length) (hj' : j' < pairs.length) :
    Disjoint (pairs[j]'hj).1 (pairs[j']'hj').2 ∧
    (j ≠ j' → Disjoint (pairs[j]'hj).1 (pairs[j']'hj').1 ∧
              Disjoint (pairs[j]'hj).2 (pairs[j']'hj').2) := by
  have hpw := hvtp.2
  have hlen : (pairs.flatMap fun p => [p.1, p.2]).length = 2 * pairs.length := by
    clear hpw hj hj' hvtp
    induction pairs with
    | nil => simp
    | cons p rest ih => simp [List.flatMap_cons, ih]; omega
  have hget : ∀ i (hi : i < pairs.length),
      (pairs.flatMap fun p => [p.1, p.2])[2 * i]'(by rw [hlen]; omega) = (pairs[i]'hi).1 ∧
      (pairs.flatMap fun p => [p.1, p.2])[2 * i + 1]'(by rw [hlen]; omega) = (pairs[i]'hi).2 := by
    clear hpw hj hj' hvtp
    intro i hi
    induction pairs generalizing i with
    | nil => simp at hi
    | cons p rest ih =>
      cases i with
      | zero => simp [List.flatMap_cons]
      | succ i' =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
        have hlen_r : (rest.flatMap fun q => [q.1, q.2]).length = 2 * rest.length := by
          simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at hlen
          omega
        have hsub := ih hlen_r i' hi
        simp only [List.flatMap_cons, List.cons_append, List.nil_append,
          show 2 * (i' + 1) = 2 * i' + 2 by omega, List.getElem_cons_succ]
        exact hsub
  have hdisj_idx : ∀ a b (ha : a < 2 * pairs.length) (hb : b < 2 * pairs.length), a ≠ b →
      Disjoint ((pairs.flatMap fun p => [p.1, p.2])[a]'(by rw [hlen]; exact ha))
        ((pairs.flatMap fun p => [p.1, p.2])[b]'(by rw [hlen]; exact hb)) := by
    intro a b ha hb hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact List.pairwise_iff_getElem.mp hpw a b (by rw [hlen]; exact ha) (by rw [hlen]; exact hb) hlt
    · exact (List.pairwise_iff_getElem.mp hpw b a (by rw [hlen]; exact hb) (by rw [hlen]; exact ha) hgt).symm
  constructor
  · have h := hdisj_idx (2 * j) (2 * j' + 1) (by omega) (by omega) (by omega)
    rw [(hget j hj).1, (hget j' hj').2] at h
    exact h
  · intro hne
    constructor
    · have h := hdisj_idx (2 * j) (2 * j') (by omega) (by omega) (by omega)
      rw [(hget j hj).1, (hget j' hj').1] at h
      exact h
    · have h := hdisj_idx (2 * j + 1) (2 * j' + 1) (by omega) (by omega) (by omega)
      rw [(hget j hj).2, (hget j' hj').2] at h
      exact h

/-- For a valid disjoint terminal-pair batch `pairs` and per-pair partial matchings `matchings`,
the unmatched vertices of pair `j` depend only on `matchedVerts matchings.flatten`, and filtering
sorted lists for `pairs[j].1` and `pairs[j].2` reproduces `completeMatchingFake` identically. -/
theorem completeMatchingFake_eq_of_flat {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {matchings : List (List (ℕ × ℕ))}
    (hvtp : ValidTerminalPairs X pairs)
    (hmlen : matchings.length = pairs.length)
    (hm : ∀ j (hj : j < pairs.length),
      IsPartialMatching (pairs[j]'hj).1 (pairs[j]'hj).2 (matchings.getD j []))
    {j : ℕ} (hj : j < pairs.length)
    {A_l B_l : List ℕ}
    (hAs : A_l.Pairwise (· < ·)) (hBs : B_l.Pairwise (· < ·))
    (hAf : A_l.toFinset = (pairs[j]'hj).1) (hBf : B_l.toFinset = (pairs[j]'hj).2) :
    completeMatchingFake (pairs[j]'hj).1 (pairs[j]'hj).2 (matchings[j]'(by omega)) =
      (A_l.filter (fun u => decide (u ∉ matchedVerts matchings.flatten))).zip
        (B_l.filter (fun v => decide (v ∉ matchedVerts matchings.flatten))) := by
  have hm_get : ∀ i (hi : i < pairs.length), matchings.getD i [] = matchings[i]'(by omega) :=
    fun i hi => List.getD_eq_getElem _ _ (by omega)
  have h1 : A_l.toFinset \ matchedVerts matchings.flatten =
      (pairs[j]'hj).1 \ ((matchings[j]'(by omega)).map Prod.fst).toFinset := by
    rw [hAf]
    ext u
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_map, mem_matchedVerts_iff]
    constructor
    · rintro ⟨huA, hnot⟩
      refine ⟨huA, ?_⟩
      rintro ⟨ed, hed, rfl⟩
      apply hnot
      exact ⟨ed, List.mem_flatten.mpr ⟨matchings[j]'(by omega), List.getElem_mem _, hed⟩, Or.inl rfl⟩
    · rintro ⟨huA, hnot⟩
      refine ⟨huA, ?_⟩
      rintro ⟨ed, hed, hu_eq⟩
      obtain ⟨M', hM'_mem, hedM'⟩ := List.mem_flatten.mp hed
      obtain ⟨j', hj', rfl⟩ := List.mem_iff_getElem.mp hM'_mem
      have hj'_p : j' < pairs.length := by omega
      have hpm' := hm j' hj'_p
      rw [hm_get j' hj'_p] at hpm'
      have hed_in := hpm'.1 ed hedM'
      have hsides := pairwise_disjoint_pairs_sides hvtp hj hj'_p
      rcases hu_eq with rfl | rfl
      · by_cases hjj' : j = j'
        · subst hjj'
          exact hnot ⟨ed, hedM', rfl⟩
        · exact Finset.disjoint_left.mp (hsides.2 hjj').1 huA hed_in.1
      · exact Finset.disjoint_left.mp hsides.1 huA hed_in.2
  have h2 : B_l.toFinset \ matchedVerts matchings.flatten =
      (pairs[j]'hj).2 \ ((matchings[j]'(by omega)).map Prod.snd).toFinset := by
    rw [hBf]
    ext v
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_map, mem_matchedVerts_iff]
    constructor
    · rintro ⟨hvB, hnot⟩
      refine ⟨hvB, ?_⟩
      rintro ⟨ed, hed, rfl⟩
      apply hnot
      exact ⟨ed, List.mem_flatten.mpr ⟨matchings[j]'(by omega), List.getElem_mem _, hed⟩, Or.inr rfl⟩
    · rintro ⟨hvB, hnot⟩
      refine ⟨hvB, ?_⟩
      rintro ⟨ed, hed, hv_eq⟩
      obtain ⟨M', hM'_mem, hedM'⟩ := List.mem_flatten.mp hed
      obtain ⟨j', hj', rfl⟩ := List.mem_iff_getElem.mp hM'_mem
      have hj'_p : j' < pairs.length := by omega
      have hpm' := hm j' hj'_p
      rw [hm_get j' hj'_p] at hpm'
      have hed_in := hpm'.1 ed hedM'
      have hsides := pairwise_disjoint_pairs_sides hvtp hj'_p hj
      rcases hv_eq with rfl | rfl
      · exact Finset.disjoint_right.mp hsides.1 hvB hed_in.1
      · by_cases hjj' : j' = j
        · subst hjj'
          exact hnot ⟨ed, hedM', rfl⟩
        · exact Finset.disjoint_right.mp (hsides.2 hjj').2 hvB hed_in.2
  unfold completeMatchingFake unmatchedFst unmatchedSnd
  rw [filter_eq_sort_sdiff hAs, filter_eq_sort_sdiff hBs, h1, h2]

/-- Every edge of `matchings.flatten` lies in `X × X` and `matchings.flatten.length ≤ X.card`. -/
lemma matched_flatten_bounds {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {matchings : List (List (ℕ × ℕ))}
    (hvtp : ValidTerminalPairs X pairs)
    (hmlen : matchings.length = pairs.length)
    (hm : ∀ j (hj : j < pairs.length),
      IsPartialMatching (pairs[j]'hj).1 (pairs[j]'hj).2 (matchings.getD j [])) :
    (∀ e ∈ matchings.flatten, e.1 ∈ X ∧ e.2 ∈ X) ∧
    matchings.flatten.length ≤ X.card := by
  have h1 : ∀ e ∈ matchings.flatten, e.1 ∈ X ∧ e.2 ∈ X := by
    intro e he
    obtain ⟨M', hM', heM'⟩ := List.mem_flatten.mp he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hM'
    have hjp : j < pairs.length := by omega
    have hpm := hm j hjp
    rw [List.getD_eq_getElem _ _ hj] at hpm
    have hin := hpm.1 e heM'
    have hpX := hvtp.1 (pairs[j]'hjp) (List.getElem_mem hjp)
    exact ⟨hpX.1 hin.1, hpX.2.1 hin.2⟩
  have h2 : matchings.flatten.length ≤ X.card := by
    have hsum_le : matchings.flatten.length ≤ totalDemand pairs := by
      rw [List.length_flatten]
      have hle : ∀ j (hj : j < pairs.length),
          (matchings[j]'(by omega)).length ≤ (pairs[j]'hj).1.card := by
        intro j hj
        have hpm := hm j hj
        rw [List.getD_eq_getElem _ _ (by omega)] at hpm
        have hsub : ((matchings[j]'(by omega)).map Prod.fst).toFinset ⊆ (pairs[j]'hj).1 := by
          intro x hx
          rw [List.mem_toFinset, List.mem_map] at hx
          obtain ⟨e, he, rfl⟩ := hx
          exact (hpm.1 e he).1
        calc (matchings[j]'(by omega)).length
            = ((matchings[j]'(by omega)).map Prod.fst).length := (List.length_map _).symm
          _ = ((matchings[j]'(by omega)).map Prod.fst).toFinset.card :=
              (List.toFinset_card_of_nodup hpm.2.1).symm
          _ ≤ (pairs[j]'hj).1.card := Finset.card_le_card hsub
      clear h1 hm hvtp
      induction pairs generalizing matchings with
      | nil => cases matchings <;> simp at hmlen ⊢
      | cons p rest ih =>
        cases matchings with
        | nil => simp at hmlen
        | cons m mrest =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hmlen
          simp only [List.map_cons, List.sum_cons]
          have hhead := hle 0 (by simp)
          have htail := ih hmlen (fun j hj => hle (j + 1) (by simp; omega))
          simp only [List.getElem_cons_zero] at hhead
          unfold totalDemand at htail ⊢
          simp only [List.map_cons, List.sum_cons]
          omega
    have hdem : totalDemand pairs ≤ X.card := by
      have h2d := two_mul_totalDemand_le (routeTerminalPairs_of_validTerminalPairs hvtp)
      omega
    omega
  exact ⟨h1, h2⟩

/-- Total fake edges of `completeBatchFake pairs matchings` is at most `X.card`. -/
lemma completeBatchFake_length_le_card {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {matchings : List (List (ℕ × ℕ))} (hvtp : ValidTerminalPairs X pairs) :
    (completeBatchFake pairs matchings).length ≤ X.card := by
  have h1 : (completeBatchFake pairs matchings).length ≤ totalDemand pairs := by
    clear hvtp
    unfold completeBatchFake totalDemand
    induction pairs generalizing matchings with
    | nil => simp
    | cons p rest ih =>
      cases matchings with
      | nil => simp
      | cons m mrest =>
        simp only [List.zipWith_cons_cons, List.flatten_cons, List.length_append,
          List.map_cons, List.sum_cons]
        have hhead : (completeMatchingFake p.1 p.2 m).length ≤ p.1.card := by
          unfold completeMatchingFake unmatchedFst
          rw [List.length_zip]
          refine le_trans (Nat.min_le_left _ _) ?_
          rw [Finset.length_sort]
          exact Finset.card_le_card Finset.sdiff_subset
        have htail : (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) rest mrest).flatten.length ≤
            (rest.map fun p => p.1.card).sum := ih (matchings := mrest)
        omega
  have h2 := two_mul_totalDemand_le (routeTerminalPairs_of_validTerminalPairs hvtp)
  omega

/-- A graph of max degree `≤ 9` on `k` vertices has `|edgeColor17 H| ≤ 5 * k`. -/
lemma edgeColor17_length_le_five_mul {H : Graph} {k : ℕ}
    (hn : H.n = k) (hval : H.IsValid) (hdeg : ∀ v < k, H.deg v ≤ 9) :
    (edgeColor17 H).length ≤ 5 * k := by
  have hspec := edgeColor17_spec hval (fun v hv => hdeg v (hn ▸ hv))
  have hlen_col : (edgeColor17 H).length = (removeLoops H).edges.length := by
    have := congrArg List.length hspec.1
    simpa using this
  have hrem_le : (removeLoops H).edges.length ≤ H.edges.length := by
    unfold removeLoops; exact List.length_filter_le _ _
  have h2m : ∑ v ∈ Finset.range H.n, H.deg v = 2 * H.m := sum_deg_eq_two_mul_m hval
  have hsum_le : ∑ v ∈ Finset.range H.n, H.deg v ≤ 9 * k := by
    rw [hn]
    calc ∑ v ∈ Finset.range k, H.deg v
        ≤ ∑ _v ∈ Finset.range k, 9 := Finset.sum_le_sum fun v hv => hdeg v (Finset.mem_range.mp hv)
      _ = 9 * k := by simp [Nat.mul_comm]
  have hm_eq : H.m = H.edges.length := rfl
  omega

/-- Every colour class of `edgeColor17 H` (on `k` vertices, max degree `≤ 9`) has length `≤ k`. -/
lemma colorClass_length_le {H : Graph} {k : ℕ}
    (hn : H.n = k) (hval : H.IsValid) (hdeg : ∀ v < k, H.deg v ≤ 9) (c : ℕ) :
    (colorClass (edgeColor17 H) c).length ≤ k := by
  have hspec := edgeColor17_spec hval (fun v hv => hdeg v (hn ▸ hv))
  have hnd := hspec.2.2.1 c
  have hsub : (colorClass (edgeColor17 H) c |>.flatMap fun e => [e.1, e.2]).toFinset ⊆ Finset.range k := by
    intro x hx
    rw [List.mem_toFinset, List.mem_flatMap] at hx
    obtain ⟨e, he, hxe⟩ := hx
    unfold colorClass at he
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.mp he
    have hin : ec.1 ∈ (removeLoops H).edges := by
      rw [← hspec.1]
      exact List.mem_map.mpr ⟨ec, (List.mem_filter.mp hec).1, rfl⟩
    have hv := removeLoops_isValid hval ec.1 hin
    rw [removeLoops_n, hn] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxe
    rcases hxe with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hlen : (colorClass (edgeColor17 H) c |>.flatMap fun e => [e.1, e.2]).length =
      2 * (colorClass (edgeColor17 H) c).length := by
    generalize colorClass (edgeColor17 H) c = l
    induction l with
    | nil => simp
    | cons e rest ih => simp [List.flatMap_cons, ih]; omega
  have hcard : (colorClass (edgeColor17 H) c |>.flatMap fun e => [e.1, e.2]).length ≤ k := by
    rw [← List.toFinset_card_of_nodup hnd]
    exact le_trans (Finset.card_le_card hsub) (by simp)
  omega

end MinCostFlow.ExpanderDecomp
