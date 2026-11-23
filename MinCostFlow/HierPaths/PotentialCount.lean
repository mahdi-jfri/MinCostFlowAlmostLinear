module

public import MinCostFlow.HierPaths.Potential

import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting the invalid entries behind the cursors

The amortized bound (`events_le`) bounds the event count by the number of lost terminals. This file
proves the three counting facts that it needs, for a state with the invariant `DelInv`:

* `card_inelig_le`: every ineligible connector has a lost endpoint, so there are at most
  `κ · |lost|` of them, where `κ` bounds the connectors of a terminal;
* `sum_pairCur_le`: the pair cursors together have passed at most `|ineligible|` entries, since
  the entries behind a cursor are ineligible and each connector lies in one pair array;
* `sum_supCur_le`: the support cursors together have passed at most
  `|lost| + Σ_{c ineligible} |verts(walk c)|` entries, since the entries behind a cursor are dead
  and each entry belongs to one support array.
-/

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.Spanner

/-- The first `c` entries of a list without repetition form a set of size `c`. -/
private theorem card_take_toFinset {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {c : ℕ} (hc : c ≤ l.length) : (l.take c).toFinset.card = c := by
  rw [List.toFinset_card_of_nodup (hl.sublist (List.take_sublist c l)), List.length_take]
  omega

/-- A sum of the sizes of pairwise disjoint subsets of `Ω` is at most `|Ω|`. -/
private theorem sum_card_le {ι α : Type*} [DecidableEq α] {W : Finset ι} {D : ι → Finset α}
    {Ω : Finset α} (hdisj : (W : Set ι).PairwiseDisjoint D) (hsub : ∀ w ∈ W, D w ⊆ Ω) :
    ∑ w ∈ W, (D w).card ≤ Ω.card := by
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

namespace ConnectorSystem

variable (C : ConnectorSystem)

/-- A support array has no repeated entry. -/
theorem supportArray_nodup (w : ℕ) : (C.supportArray w).Nodup := by
  unfold supportArray
  refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
  · exact (List.nodup_range.filter _).map fun a b h => by cases h; rfl
  · refine List.nodup_flatMap.mpr ⟨fun c _ => ?_, ?_⟩
    · exact (List.nodup_range.filter _).map fun a b h => by cases h; rfl
    · refine List.nodup_range.pairwise_of_forall_ne fun c _ c' _ hne => ?_
      rw [Function.onFun]
      intro y hy hy'
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
      obtain ⟨_, _, h⟩ := List.mem_map.mp hy'
      cases h
      exact hne rfl
  · intro y hy y' hy' he
    subst he
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
    obtain ⟨c, _, hy'⟩ := List.mem_flatMap.mp hy'
    obtain ⟨_, _, h⟩ := List.mem_map.mp hy'
    cases h

/-- An entry of the support array of `w` determines `w`. -/
theorem eq_of_mem_supportArray {w w' : ℕ} {y : SupportEntry} (hy : y ∈ C.supportArray w)
    (hy' : y ∈ C.supportArray w') : w = w' := by
  rcases (C.mem_supportArray).mp hy with ⟨t, _, ho, rfl⟩ | ⟨c, _, pos, hpos, rfl⟩
  · rcases (C.mem_supportArray).mp hy' with ⟨t', _, ho', he⟩ | ⟨_, _, _, _, he⟩
    · cases he; exact ho.symm.trans ho'
    · cases he
  · rcases (C.mem_supportArray).mp hy' with ⟨_, _, _, he⟩ | ⟨c', _, pos', hpos', he⟩
    · cases he
    · cases he
      exact ((C.mem_positionsOn).mp hpos).2.symm.trans ((C.mem_positionsOn).mp hpos').2

end ConnectorSystem

namespace StaticArrays

variable (A : StaticArrays) {G : Graph} {ξ κ : ℕ}

public section

/-- Every ineligible connector has a lost endpoint, so there are at most `κ` per lost terminal. -/
theorem card_inelig_le {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) :
    st.inelig.card ≤ κ * st.loss.glob.card := by
  have hsub : st.inelig ⊆ st.loss.glob.biUnion fun t => (A.termConns t).toFinset := by
    intro c hc
    rw [hinv.inelig_eq, Finset.mem_filter, Finset.mem_range] at hc
    obtain ⟨hcN, hne⟩ := hc
    obtain ⟨ha, hb, _⟩ := hA.fits.2 c hcN
    rw [Finset.mem_biUnion]
    by_cases hsa : A.C.endA c ∈ A.surv st
    · have hsb : A.C.endB c ∉ A.surv st := fun hsb => hne ⟨hcN, hsa, hsb⟩
      refine ⟨A.C.endB c, ?_, List.mem_toFinset.mpr ((hA.mem_termConns _ hb c).mpr
        ⟨hcN, Or.inr rfl⟩)⟩
      by_contra h; exact hsb ((A.mem_surv).mpr ⟨hb, h⟩)
    · refine ⟨A.C.endA c, ?_, List.mem_toFinset.mpr ((hA.mem_termConns _ ha c).mpr
        ⟨hcN, Or.inl rfl⟩)⟩
      by_contra h; exact hsa ((A.mem_surv).mpr ⟨ha, h⟩)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [mul_comm]
  exact Finset.sum_le_card_nsmul _ _ _ fun t _ =>
    (List.toFinset_card_le _).trans (hA.termConns_length t)

/-- The pair cursors together have passed at most as many entries as there are ineligible
connectors. -/
theorem sum_pairCur_le {st : DelState} (hA : A.Spec G ξ κ) (hinv : A.DelInv G st) :
    ∑ p ∈ Finset.range A.numPairs, st.pairCur p ≤ st.inelig.card := by
  have hcard : ∀ p ∈ Finset.range A.numPairs,
      st.pairCur p = ((A.pairConns p).take (st.pairCur p)).toFinset.card := fun p hp =>
    (card_take_toFinset (hA.pairConns_nodup p)
      (hinv.pairCur p (Finset.mem_range.mp hp)).1).symm
  rw [Finset.sum_congr rfl hcard]
  refine sum_card_le ?_ ?_
  · intro p _ p' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro c hc hc'
    have h1 := (hA.mem_pairConns p c
      ((List.take_sublist _ _).subset (List.mem_toFinset.mp hc))).2
    have h2 := (hA.mem_pairConns p' c
      ((List.take_sublist _ _).subset (List.mem_toFinset.mp hc'))).2
    exact hne (h1.symm.trans h2)
  · intro p hp c hc
    have hinvp := hinv.pairCur p (Finset.mem_range.mp hp)
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hc)
    have hjl : j < (A.pairConns p).length := lt_of_lt_of_le hj (min_le_right _ _)
    have hv := hinvp.2.1 j (lt_of_lt_of_le hj (min_le_left _ _))
    rw [pairValid, List.getD_eq_getElem _ _ hjl] at hv
    rw [hinv.inelig_eq, Finset.mem_filter, Finset.mem_range]
    exact ⟨(hA.mem_pairConns p _ (List.getElem_mem hjl)).1, by simpa using hv⟩

/-- The support cursors together have passed at most `|lost| + Σ_{c ineligible} |verts c|`
entries. -/
theorem sum_supCur_le {st : DelState} (hinv : A.DelInv G st) :
    ∑ w ∈ Finset.range G.n, st.supCur w ≤
      st.loss.glob.card + ∑ c ∈ st.inelig, (A.C.walk c).verts.length := by
  have hcard : ∀ w ∈ Finset.range G.n,
      st.supCur w = ((A.C.supportArray w).take (st.supCur w)).toFinset.card := fun w hw =>
    (card_take_toFinset (A.C.supportArray_nodup w)
      (hinv.supCur w (Finset.mem_range.mp hw)).1).symm
  rw [Finset.sum_congr rfl hcard]
  set Ω : Finset SupportEntry := st.loss.glob.image SupportEntry.term ∪
    st.inelig.biUnion fun c =>
      (Finset.range (A.C.walk c).verts.length).image (SupportEntry.onWalk c)
  have hΩ : Ω.card ≤ st.loss.glob.card + ∑ c ∈ st.inelig, (A.C.walk c).verts.length := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
    refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun c _ => ?_)
    exact Finset.card_image_le.trans (Finset.card_range _).le
  refine le_trans (sum_card_le ?_ ?_) hΩ
  · intro w _ w' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    exact hne (A.C.eq_of_mem_supportArray
      ((List.take_sublist _ _).subset (List.mem_toFinset.mp hy))
      ((List.take_sublist _ _).subset (List.mem_toFinset.mp hy')))
  · intro w hw y hy
    have hinvw := hinv.supCur w (Finset.mem_range.mp hw)
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hy)
    have hjl : j < (A.C.supportArray w).length := lt_of_lt_of_le hj (min_le_right _ _)
    have hv := hinvw.2.1 j (lt_of_lt_of_le hj (min_le_left _ _))
    rw [supValid, List.getD_eq_getElem _ _ hjl] at hv
    have hmem := List.getElem_mem hjl
    rcases (A.C.mem_supportArray).mp hmem with ⟨t, ht, _, he⟩ | ⟨c, hc, pos, hpos, he⟩
    · rw [he] at hv ⊢
      simp only [ConnectorSystem.entryLive, decide_eq_false_iff_not] at hv
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ?_, rfl⟩)
      by_contra h; exact hv ((A.mem_surv).mpr ⟨ht, h⟩)
    · rw [he] at hv ⊢
      simp only [ConnectorSystem.entryLive, decide_eq_false_iff_not] at hv
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, ?_, ?_⟩)
      · rw [hinv.inelig_eq, Finset.mem_filter, Finset.mem_range]; exact ⟨hc, hv⟩
      · exact Finset.mem_image.mpr ⟨pos, Finset.mem_range.mpr ((A.C.mem_positionsOn).mp hpos).1,
          rfl⟩

end

end StaticArrays

end MinCostFlow.HierPaths
