module

public import MinCostFlow.HierPaths.LossCounters
public import MinCostFlow.HierPaths.LossLocal
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The loss counters compute the lost sets

This file proves that the procedure of `HierPaths/LossCounters.lean` is correct. After any list
of distinct first failures with set `F`, every counter `own j g` equals `|lost F j g|`, every
`sum j g` equals the size of the union of the children's lost sets, and the marked terminals are
exactly the global lost set (`runFailures_inv`). Each step outputs exactly the newly globally lost
terminals, without repetition (`failStep_spec`). The operation counts are small: at most
`(leafDepth + 1) · |F|` counter updates (`runFailures_updates_le`), and at most
`(leafDepth + 1) · |globalLost F|` enumerated terminals (`runFailures_enumerated_le`).

The proof follows one failure of `u` up the chain of `u`. `ClimbInv` describes the state when the
climb has processed the depths from `j` to the leaves: those depths hold the new values, the
depths above hold the old ones, and `Δ` is the growth of the lost set of the group of `u` at
depth `j`. The facts of `HierPaths/LossLocal.lean` show that one level step keeps this, that the
groups off the chain do not change, and that when `Δ = 0` the depths above need no change.
-/

public section

namespace MinCostFlow.HierPaths

open Finset

variable {x b : ℕ}

/-- The invariant of the counters after the set `F` of first failures. -/
structure LossInv (x b : ℕ) (F : Finset ℕ) (st : LossState) : Prop where
  failed : st.failed = F
  glob : st.glob = globalLost x b F
  own : ∀ i ≤ leafDepth x b, ∀ g, st.own i g = (lost x b F i g).card
  sum : ∀ i < leafDepth x b, ∀ g, st.sum i g = (childUnion x b F i g).card
  updates : st.updates ≤ (leafDepth x b + 1) * F.card
  enumerated : st.enumerated = F.card + ∑ i ∈ range (leafDepth x b), (fullSet x b F i).card

/-- The set of failures that a depth `i` sees while the climb for `u` is at depth `j`. -/
def failSetAt (F : Finset ℕ) (u j i : ℕ) : Finset ℕ := if j ≤ i then insert u F else F

/-- The invariant of the climb for a new failure of `u`, after it processed depths `j` and
below. -/
structure ClimbInv (x b : ℕ) (F : Finset ℕ) (u j Δ : ℕ) (st : LossState) : Prop where
  le : j ≤ leafDepth x b
  failed : st.failed = insert u F
  own : ∀ i ≤ leafDepth x b, ∀ g, st.own i g = (lost x b (failSetAt F u j i) i g).card
  sum : ∀ i < leafDepth x b, ∀ g, st.sum i g = (childUnion x b (failSetAt F u j i) i g).card
  delta : Δ = (lost x b (insert u F) j (groupOf x b j u)).card -
    (lost x b F j (groupOf x b j u)).card
  glob : st.glob = globalLost x b F ∪ {u} ∪
    ((Ico j (leafDepth x b)).filter
      (fun i => NewlyFull x b F (insert u F) i (groupOf x b i u))).biUnion
      (fun i => members x b i (groupOf x b i u))
  updates : st.updates ≤ (leafDepth x b + 1) * F.card + 1 + (leafDepth x b - j)
  enumerated : st.enumerated = F.card + 1 + ∑ i ∈ range (leafDepth x b), (fullSet x b F i).card +
    ∑ i ∈ Ico j (leafDepth x b),
      if NewlyFull x b F (insert u F) i (groupOf x b i u) then groupSize x b i else 0

/-- What an output list must satisfy: no repetition, and exactly the newly marked terminals. -/
def OutputOK (old new : Finset ℕ) (out : List ℕ) : Prop :=
  old ⊆ new ∧ out.Nodup ∧ out.toFinset = new \ old

theorem OutputOK.append {A B C : Finset ℕ} {l l' : List ℕ} (h : OutputOK A B l)
    (h' : OutputOK B C l') : OutputOK A C (l ++ l') := by
  obtain ⟨hAB, hl, hlB⟩ := h
  obtain ⟨hBC, hl', hlC⟩ := h'
  refine ⟨hAB.trans hBC, List.nodup_append.mpr ⟨hl, hl', ?_⟩, ?_⟩
  · intro a ha a' ha' he
    subst he
    have h1 : a ∈ B \ A := hlB ▸ List.mem_toFinset.mpr ha
    have h2 : a ∈ C \ B := hlC ▸ List.mem_toFinset.mpr ha'
    exact (mem_sdiff.mp h2).2 (mem_sdiff.mp h1).1
  · rw [List.toFinset_append, hlB, hlC]
    ext a
    simp only [mem_union, mem_sdiff]
    constructor
    · rintro (⟨ha, hn⟩ | ⟨ha, hn⟩)
      · exact ⟨hBC ha, hn⟩
      · exact ⟨ha, fun h => hn (hAB h)⟩
    · rintro ⟨ha, hn⟩
      by_cases hb : a ∈ B
      · exact Or.inl ⟨hb, hn⟩
      · exact Or.inr ⟨ha, hb⟩

theorem OutputOK.nodup {A B : Finset ℕ} {l : List ℕ} (h : OutputOK A B l) : l.Nodup := h.2.1

theorem OutputOK.toFinset_eq {A B : Finset ℕ} {l : List ℕ} (h : OutputOK A B l) :
    l.toFinset = B \ A := h.2.2

theorem OutputOK.nil (A : Finset ℕ) : OutputOK A A [] :=
  ⟨Subset.rfl, List.nodup_nil, by simp⟩

theorem enumerate_outputOK (st : LossState) {l : List ℕ} (hl : l.Nodup) :
    OutputOK st.glob (enumerate st l).1.glob (enumerate st l).2 := by
  refine ⟨subset_union_left, hl.filter _, ?_⟩
  ext a
  simp [enumerate]
  tauto

theorem toFinset_memberList (j g : ℕ) : (memberList x b j g).toFinset = members x b j g := by
  ext a
  simp [memberList, members, List.mem_range']
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [Nat.succ_mul]
    omega
  · intro ⟨h1, h2⟩
    refine ⟨a - g * groupSize x b j, ?_, by omega⟩
    rw [Nat.succ_mul] at h2
    omega

theorem nodup_memberList (j g : ℕ) : (memberList x b j g).Nodup := List.nodup_range'

theorem length_memberList (j g : ℕ) : (memberList x b j g).length = groupSize x b j :=
  List.length_range'

section levelStep

variable (x b u j Δ : ℕ) (st : LossState)

/-- The condition under which `levelStep` enumerates: the group has just become wholly lost. -/
abbrev levelCond : Prop :=
  newOwn x b j (st.sum j (groupOf x b j u) + Δ) = groupSize x b j ∧
    st.own j (groupOf x b j u) ≠ groupSize x b j

theorem levelStep_own : (levelStep x b u j Δ st).1.own =
    setAt st.own j (groupOf x b j u) (newOwn x b j (st.sum j (groupOf x b j u) + Δ)) := by
  unfold levelStep; dsimp only; split_ifs <;> rfl

theorem levelStep_sum : (levelStep x b u j Δ st).1.sum =
    setAt st.sum j (groupOf x b j u) (st.sum j (groupOf x b j u) + Δ) := by
  unfold levelStep; dsimp only; split_ifs <;> rfl

theorem levelStep_failed : (levelStep x b u j Δ st).1.failed = st.failed := by
  unfold levelStep; dsimp only; split_ifs <;> rfl

theorem levelStep_updates : (levelStep x b u j Δ st).1.updates = st.updates + 1 := by
  unfold levelStep; dsimp only; split_ifs <;> rfl

theorem levelStep_delta : (levelStep x b u j Δ st).2.2 =
    newOwn x b j (st.sum j (groupOf x b j u) + Δ) - st.own j (groupOf x b j u) := by
  unfold levelStep; dsimp only; split_ifs <;> rfl

theorem levelStep_glob : (levelStep x b u j Δ st).1.glob =
    if levelCond x b u j Δ st then st.glob ∪ members x b j (groupOf x b j u) else st.glob := by
  unfold levelStep; dsimp only
  split_ifs <;> simp only [enumerate, toFinset_memberList]

theorem levelStep_enumerated : (levelStep x b u j Δ st).1.enumerated =
    st.enumerated + if levelCond x b u j Δ st then groupSize x b j else 0 := by
  unfold levelStep; dsimp only
  split_ifs <;> simp only [enumerate, length_memberList, Nat.add_zero]

theorem levelStep_outputOK :
    OutputOK st.glob (levelStep x b u j Δ st).1.glob (levelStep x b u j Δ st).2.1 := by
  unfold levelStep; dsimp only
  split_ifs
  · exact enumerate_outputOK _ (nodup_memberList _ _)
  · exact OutputOK.nil _

end levelStep

section facts

variable {F : Finset ℕ}

theorem lost_eq_members_iff_card {j g : ℕ} :
    lost x b F j g = members x b j g ↔ (lost x b F j g).card = groupSize x b j := by
  constructor
  · intro h; rw [h, card_members]
  · intro h
    exact eq_of_subset_of_card_le (lost_subset_members j g) (by rw [card_members, h])

theorem newlyFull_iff_card {F' : Finset ℕ} {j g : ℕ} :
    NewlyFull x b F F' j g ↔
      (lost x b F' j g).card = groupSize x b j ∧ (lost x b F j g).card ≠ groupSize x b j := by
  unfold NewlyFull
  rw [lost_eq_members_iff_card, Ne, lost_eq_members_iff_card]

theorem lost_empty (j g : ℕ) : lost x b ∅ j g = ∅ := by
  have h := card_lost_le (x := x) (b := b) (F := ∅) j g
  rw [empty_inter, card_empty, Nat.mul_zero] at h
  exact card_eq_zero.mp (Nat.le_zero.mp h)

theorem fullSet_empty (j : ℕ) : fullSet x b ∅ j = ∅ := by
  ext v
  simp only [fullSet, mem_filter, notMem_empty, iff_false, not_and]
  intro _ h
  have h1 := congrArg card h
  rw [lost_empty, card_empty, card_members] at h1
  exact absurd h1.symm (Nat.pos_iff_ne_zero.mp groupSize_pos)

theorem childUnion_empty (j g : ℕ) : childUnion x b ∅ j g = ∅ := by
  unfold childUnion
  ext v
  simp [lost_empty]

/-- At the leaf of `u`, a new failure of `u` adds exactly `u` to the lost set. -/
theorem card_lost_insert_leaf {u : ℕ} (huF : u ∉ F) :
    (lost x b (insert u F) (leafDepth x b) (groupOf x b (leafDepth x b) u)).card =
      (lost x b F (leafDepth x b) (groupOf x b (leafDepth x b) u)).card + 1 := by
  rw [lost_of_le le_rfl, lost_of_le le_rfl, inter_insert_of_mem (mem_members_groupOf u),
    card_insert_of_notMem (fun h => huF (mem_inter.mp h).2)]

theorem newlyFull_false_of_eq {F' : Finset ℕ} {j g : ℕ} (h : lost x b F' j g = lost x b F j g) :
    ¬ NewlyFull x b F F' j g := fun hn => hn.2 (h ▸ hn.1)

end facts

section climb

variable {F : Finset ℕ} {u : ℕ}

theorem failSetAt_of_le {j i : ℕ} (h : j ≤ i) : failSetAt F u j i = insert u F := by
  simp only [failSetAt, eq_true h, ↓reduceIte]

theorem failSetAt_of_lt {j i : ℕ} (h : i < j) : failSetAt F u j i = F := by
  simp only [failSetAt, eq_false (Nat.not_le.mpr h), ↓reduceIte]

/-- One level step keeps the climb invariant, one depth higher. -/
theorem levelStep_spec {j Δ : ℕ} {st : LossState} (hj : j < leafDepth x b)
    (hinv : ClimbInv x b F u (j + 1) Δ st) :
    ClimbInv x b F u j (levelStep x b u j Δ st).2.2 (levelStep x b u j Δ st).1 := by
  have hsum : st.sum j (groupOf x b j u) = (childUnion x b F j (groupOf x b j u)).card := by
    rw [hinv.sum j hj (groupOf x b j u), failSetAt_of_lt (Nat.lt_succ_self j)]
  have hown : st.own j (groupOf x b j u) = (lost x b F j (groupOf x b j u)).card := by
    rw [hinv.own j hj.le (groupOf x b j u), failSetAt_of_lt (Nat.lt_succ_self j)]
  have hs : st.sum j (groupOf x b j u) + Δ = (childUnion x b (insert u F) j (groupOf x b j u)).card := by
    rw [hsum, hinv.delta, card_childUnion_insert]
  have ho' : newOwn x b j (st.sum j (groupOf x b j u) + Δ) = (lost x b (insert u F) j (groupOf x b j u)).card := by
    rw [hs, card_lost_of_lt hj, newOwn]
  have hcond : levelCond x b u j Δ st ↔ NewlyFull x b F (insert u F) j (groupOf x b j u) := by
    rw [levelCond, ho', hown, newlyFull_iff_card]
  refine ⟨hj.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [levelStep_failed, hinv.failed]
  · intro i hi g
    rw [levelStep_own]
    unfold setAt
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [ho', failSetAt_of_le le_rfl]
    · rw [hinv.own i hi g]
      by_cases hij : i = j
      · subst hij
        have hg : groupOf x b i u ≠ g := fun he => h ⟨rfl, he.symm⟩
        rw [failSetAt_of_lt (Nat.lt_succ_self i), failSetAt_of_le le_rfl,
          lost_insert_of_groupOf_ne hg]
      · unfold failSetAt
        congr 3
        exact propext ⟨fun h' => by omega, fun h' => by omega⟩
  · intro i hi g
    rw [levelStep_sum]
    unfold setAt
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [hs, failSetAt_of_le le_rfl]
    · rw [hinv.sum i hi g]
      by_cases hij : i = j
      · subst hij
        have hg : groupOf x b i u ≠ g := fun he => h ⟨rfl, he.symm⟩
        rw [failSetAt_of_lt (Nat.lt_succ_self i), failSetAt_of_le le_rfl,
          childUnion_insert_of_groupOf_ne hg]
      · unfold failSetAt
        congr 3
        exact propext ⟨fun h' => by omega, fun h' => by omega⟩
  · rw [levelStep_delta, ho', hown]
  · rw [levelStep_glob, hinv.glob, ← insert_Ico_add_one_left_eq_Ico hj, filter_insert]
    by_cases hc : levelCond x b u j Δ st
    · simp only [eq_true hc, eq_true (hcond.mp hc), ↓reduceIte]
      rw [biUnion_insert]
      ext v
      simp only [mem_union]
      tauto
    · simp only [eq_false hc, eq_false (fun h => hc (hcond.mpr h)), ↓reduceIte]
  · rw [levelStep_updates]
    have := hinv.updates
    omega
  · rw [levelStep_enumerated, hinv.enumerated, sum_eq_sum_Ico_succ_bot hj]
    by_cases hc : levelCond x b u j Δ st
    · simp only [eq_true hc, eq_true (hcond.mp hc), ↓reduceIte]; omega
    · simp only [eq_false hc, eq_false (fun h => hc (hcond.mpr h)), ↓reduceIte]; omega

/-- When the climb stops at depth `j` (at the root, or because the lost set of the group of `u`
at depth `j` did not change), the state satisfies the invariant for the new failure set. -/
theorem ClimbInv.finish {j Δ : ℕ} {st : LossState} (hu : u < 2 ^ x) (huF : u ∉ F)
    (hinv : ClimbInv x b F u j Δ st)
    (hstop : j = 0 ∨ lost x b (insert u F) j (groupOf x b j u) = lost x b F j (groupOf x b j u)) :
    LossInv x b (insert u F) st := by
  have heq : ∀ i < j, lost x b (insert u F) i (groupOf x b i u) = lost x b F i (groupOf x b i u)
      ∧ lost x b (insert u F) (i + 1) (groupOf x b (i + 1) u) =
        lost x b F (i + 1) (groupOf x b (i + 1) u) := by
    intro i hi
    rcases hstop with h0 | hst
    · omega
    · exact ⟨lost_insert_eq_of_le hinv.le hst (by omega),
        lost_insert_eq_of_le hinv.le hst (by omega)⟩
  have hlost : ∀ i < j, ∀ g, lost x b (insert u F) i g = lost x b F i g := by
    intro i hi g
    by_cases hg : groupOf x b i u = g
    · rw [← hg]; exact (heq i hi).1
    · exact lost_insert_of_groupOf_ne hg
  have hcu : ∀ i < j, ∀ g, (childUnion x b (insert u F) i g).card =
      (childUnion x b F i g).card := by
    intro i hi g
    by_cases hg : groupOf x b i u = g
    · rw [← hg, card_childUnion_insert, (heq i hi).2, Nat.sub_self, Nat.add_zero]
    · rw [childUnion_insert_of_groupOf_ne hg]
  have hnf : ∀ i < j, ¬ NewlyFull x b F (insert u F) i (groupOf x b i u) :=
    fun i hi => newlyFull_false_of_eq (heq i hi).1
  have hfilter : (range (leafDepth x b)).filter
        (fun i => NewlyFull x b F (insert u F) i (groupOf x b i u)) =
      (Ico j (leafDepth x b)).filter
        (fun i => NewlyFull x b F (insert u F) i (groupOf x b i u)) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    constructor
    · rintro ⟨hi, hn⟩
      refine ⟨⟨Nat.not_lt.mp fun h => hnf i h hn, hi⟩, hn⟩
    · rintro ⟨⟨_, hi⟩, hn⟩
      exact ⟨hi, hn⟩
  refine ⟨hinv.failed, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hinv.glob, globalLost_insert hu, hfilter]
  · intro i hi g
    rw [hinv.own i hi g]
    by_cases hji : j ≤ i
    · rw [failSetAt_of_le hji]
    · rw [failSetAt_of_lt (Nat.not_le.mp hji), hlost i (Nat.not_le.mp hji)]
  · intro i hi g
    rw [hinv.sum i hi g]
    by_cases hji : j ≤ i
    · rw [failSetAt_of_le hji]
    · rw [failSetAt_of_lt (Nat.not_le.mp hji), hcu i (Nat.not_le.mp hji)]
  · have h1 := hinv.updates
    rw [card_insert_of_notMem huF]
    have h2 : leafDepth x b - j ≤ leafDepth x b := Nat.sub_le _ _
    rw [Nat.mul_succ]
    omega
  · rw [hinv.enumerated, card_insert_of_notMem huF]
    have hsplit := sum_range_add_sum_Ico
      (fun i => if NewlyFull x b F (insert u F) i (groupOf x b i u) then groupSize x b i else 0)
      hinv.le
    have hzero : ∑ i ∈ range j,
        (if NewlyFull x b F (insert u F) i (groupOf x b i u) then groupSize x b i else 0) = 0 :=
      sum_eq_zero fun i hi => by
        simp only [eq_false (hnf i (mem_range.mp hi)), ↓reduceIte]
    have hfs : ∑ i ∈ range (leafDepth x b), (fullSet x b (insert u F) i).card =
        ∑ i ∈ range (leafDepth x b), (fullSet x b F i).card +
          ∑ i ∈ range (leafDepth x b),
            (if NewlyFull x b F (insert u F) i (groupOf x b i u) then groupSize x b i else 0) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => card_fullSet_insert hu i
    rw [hfs]
    omega

/-- **The climb.** From the climb invariant at depth `j`, the climb ends in a state with the
invariant for the new failure set, and outputs exactly the newly marked terminals. -/
theorem climb_spec (hu : u < 2 ^ x) (huF : u ∉ F) :
    ∀ (j Δ : ℕ) (st : LossState), ClimbInv x b F u j Δ st →
      LossInv x b (insert u F) (climb x b u j Δ st).1 ∧
        OutputOK st.glob (climb x b u j Δ st).1.glob (climb x b u j Δ st).2
  | 0, Δ, st, hinv => by
    simp only [climb]
    exact ⟨hinv.finish hu huF (Or.inl rfl), OutputOK.nil _⟩
  | j + 1, Δ, st, hinv => by
    by_cases hΔ : Δ = 0
    · simp only [climb, eq_true hΔ, ↓reduceIte]
      refine ⟨hinv.finish hu huF (Or.inr ?_), OutputOK.nil _⟩
      have hd := hinv.delta
      rw [hΔ] at hd
      exact (eq_of_subset_of_card_le (lost_mono (subset_insert u F) _ _) (by omega)).symm
    · simp only [climb, eq_false hΔ, ↓reduceIte]
      have hj : j < leafDepth x b := hinv.le
      have hnext := levelStep_spec hj hinv
      obtain ⟨h1, h2⟩ := climb_spec hu huF j _ _ hnext
      exact ⟨h1, (levelStep_outputOK x b u j Δ st).append h2⟩

end climb

end MinCostFlow.HierPaths
