module

public import MinCostFlow.HierPaths.LossCountersSpec
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The loss counters over a list of failures

This file finishes the proof that the loss counters are correct. `failStep_spec`: one first failure
of a terminal `u < 2 ^ x` keeps the invariant `LossInv` of `HierPaths/LossCountersSpec.lean`, and
the step outputs, without repetition, exactly the terminals that became globally lost. Then
`runFailures_inv` follows by induction over the list, and the main results read off the
invariant:

* `runFailures_own`, `runFailures_sum`, `runFailures_glob`: after the distinct failures of a
  list `l` with set `F`, every count equals the size of its lost set and the marked terminals are
  the global lost set;
* `runFailures_updates_le`: at most `(leafDepth + 1) · |F|` counter updates;
* `runFailures_enumerated_le`: at most `(leafDepth + 1) · |globalLost F|` enumerated terminals.
  Here each failure enumerates its own leaf once, and each group is enumerated once, when it
  becomes wholly lost; the groups wholly lost at one depth are disjoint and lie in the global
  lost set.
-/

public section

namespace MinCostFlow.HierPaths

open Finset

variable {x b : ℕ} {F : Finset ℕ}

theorem lossInv_init : LossInv x b ∅ LossState.init := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [globalLost_eq, lost_empty]; rfl
  · intro i _ g; rw [lost_empty]; rfl
  · intro i _ g; rw [childUnion_empty]; rfl
  · exact Nat.zero_le _
  · simp only [fullSet_empty, card_empty, sum_const_zero]; rfl

/-- The state after the leaf step of a first direct failure of `u` (the failed set, the leaf
counter, and the enumeration of `u`) meets the climb invariant at the leaf depth with change `1`.
-/
theorem failStart_climbInv {u : ℕ} {st : LossState} (hinv : LossInv x b F st) (huF : u ∉ F) :
    ClimbInv x b F u (leafDepth x b) 1 (enumerate
      ⟨setAt st.own (leafDepth x b) (groupOf x b (leafDepth x b) u)
        (st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) + 1), st.sum,
        insert u st.failed, st.glob, st.updates + 1, st.enumerated⟩ [u]).1 := by
  set st1 : LossState :=
    ⟨setAt st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) (st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) + 1), st.sum,
      insert u st.failed, st.glob, st.updates + 1, st.enumerated⟩
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [enumerate, st1, hinv.failed]
  · intro i hi g
    simp only [enumerate, st1, setAt]
    split_ifs with hig
    · obtain ⟨rfl, rfl⟩ := hig
      rw [hinv.own _ le_rfl, failSetAt_of_le le_rfl, card_lost_insert_leaf huF]
    · rw [hinv.own i hi g]
      by_cases hih : i = (leafDepth x b)
      · have hg : groupOf x b (leafDepth x b) u ≠ g := fun he => hig ⟨hih, he.symm⟩
        rw [hih, failSetAt_of_le le_rfl, lost_insert_of_groupOf_ne hg]
      · rw [failSetAt_of_lt (by omega)]
  · intro i hi g
    simp only [enumerate, st1]
    rw [hinv.sum i hi g, failSetAt_of_lt hi]
  · rw [card_lost_insert_leaf huF]; omega
  · simp only [enumerate, st1, hinv.glob, Ico_self, filter_empty, biUnion_empty, union_empty,
      List.toFinset_cons, List.toFinset_nil, insert_empty]
  · simp only [enumerate, st1, Nat.sub_self, Nat.add_zero]
    exact Nat.add_le_add_right hinv.updates 1
  · simp only [enumerate, st1, Ico_self, sum_empty, Nat.add_zero, hinv.enumerated,
      List.length_singleton]
    omega

/-- **One failure step.** A first direct failure of `u < 2 ^ x` keeps the invariant, and the
step outputs, without repetition, exactly the terminals that became globally lost. -/
theorem failStep_spec {u : ℕ} {st : LossState} (hinv : LossInv x b F st) (hu : u < 2 ^ x)
    (huF : u ∉ F) :
    LossInv x b (insert u F) (failStep x b u st).1 ∧ (failStep x b u st).2.Nodup ∧
      (failStep x b u st).2.toFinset = globalLost x b (insert u F) \ globalLost x b F := by
  set st1 : LossState :=
    ⟨setAt st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) (st.own (leafDepth x b) (groupOf x b (leafDepth x b) u) + 1), st.sum,
      insert u st.failed, st.glob, st.updates + 1, st.enumerated⟩
  have hc : ClimbInv x b F u (leafDepth x b) 1 (enumerate st1 [u]).1 :=
    failStart_climbInv hinv huF
  obtain ⟨h1, h2⟩ := climb_spec hu huF (leafDepth x b) 1 _ hc
  have h0 : OutputOK st.glob (enumerate st1 [u]).1.glob (enumerate st1 [u]).2 :=
    enumerate_outputOK st1 (List.nodup_singleton u)
  have h3 := h0.append h2
  refine ⟨h1, h3.nodup, ?_⟩
  change ((enumerate st1 [u]).2 ++ (climb x b u (leafDepth x b) 1 (enumerate st1 [u]).1).2).toFinset
    = _
  rw [h3.toFinset_eq, h1.glob, hinv.glob]

/-- The invariant after a list of distinct first failures, started from any state. -/
theorem foldl_failStep_inv :
    ∀ (l : List ℕ) (F : Finset ℕ) (st : LossState), LossInv x b F st → l.Nodup →
      (∀ u ∈ l, u < 2 ^ x ∧ u ∉ F) →
      LossInv x b (F ∪ l.toFinset) (l.foldl (fun st u => (failStep x b u st).1) st)
  | [], F, st, hinv, _, _ => by simpa using hinv
  | u :: l, F, st, hinv, hnd, hl => by
    rw [List.foldl_cons]
    have hu := hl u List.mem_cons_self
    have hstep := (failStep_spec hinv hu.1 hu.2).1
    have hrest := foldl_failStep_inv l (insert u F) _ hstep (List.nodup_cons.mp hnd).2
      (fun v hv => ⟨(hl v (List.mem_cons_of_mem u hv)).1, fun hvF => by
        rcases mem_insert.mp hvF with rfl | hvF
        · exact (List.nodup_cons.mp hnd).1 hv
        · exact (hl v (List.mem_cons_of_mem u hv)).2 hvF⟩)
    have he : insert u F ∪ l.toFinset = F ∪ (u :: l).toFinset := by
      ext v; simp only [mem_union, mem_insert, List.toFinset_cons]; tauto
    rwa [he] at hrest

/-- **Loss counters**, the invariant: after the distinct first failures of `l`, all below `2 ^ x`, the
state satisfies `LossInv` for the set of `l`. -/
theorem runFailures_inv {l : List ℕ} (hnd : l.Nodup) (hl : ∀ u ∈ l, u < 2 ^ x) :
    LossInv x b l.toFinset (runFailures x b l) := by
  have h := foldl_failStep_inv (b := b) l ∅ _ lossInv_init hnd
    (fun u hu => ⟨hl u hu, notMem_empty u⟩)
  rwa [empty_union] at h

/-- **Loss counters**: every count equals the size of its lost set. -/
theorem runFailures_own {l : List ℕ} (hnd : l.Nodup) (hl : ∀ u ∈ l, u < 2 ^ x) {j : ℕ}
    (hj : j ≤ leafDepth x b) (g : ℕ) :
    (runFailures x b l).own j g = (lost x b l.toFinset j g).card :=
  (runFailures_inv hnd hl).own j hj g

/-- **Loss counters**: every children's sum equals the size of the union of the children's lost
sets. -/
theorem runFailures_sum {l : List ℕ} (hnd : l.Nodup) (hl : ∀ u ∈ l, u < 2 ^ x) {j : ℕ}
    (hj : j < leafDepth x b) (g : ℕ) :
    (runFailures x b l).sum j g = (childUnion x b l.toFinset j g).card :=
  (runFailures_inv hnd hl).sum j hj g

/-- **Loss counters**: the marked terminals are exactly the global lost set. -/
theorem runFailures_glob {l : List ℕ} (hnd : l.Nodup) (hl : ∀ u ∈ l, u < 2 ^ x) :
    (runFailures x b l).glob = globalLost x b l.toFinset :=
  (runFailures_inv hnd hl).glob

/-- **Loss counters**, number of count updates: at most `(leafDepth + 1) · |F|`. -/
theorem runFailures_updates_le {l : List ℕ} (hnd : l.Nodup) (hl : ∀ u ∈ l, u < 2 ^ x) :
    (runFailures x b l).updates ≤ (leafDepth x b + 1) * l.toFinset.card :=
  (runFailures_inv hnd hl).updates

/-- The invariant bounds the enumerated terminals by `(leafDepth + 1)` times the globally lost
ones, when all failures are below `2 ^ x`. -/
theorem LossInv.enumerated_le {st : LossState} (hinv : LossInv x b F st)
    (hF : ∀ u ∈ F, u < 2 ^ x) :
    st.enumerated ≤ (leafDepth x b + 1) * (globalLost x b F).card := by
  rw [hinv.enumerated, Nat.succ_mul, Nat.add_comm]
  have h1 : F.card ≤ (globalLost x b F).card :=
    card_le_card fun u hu => mem_globalLost_of_mem (hF u hu) hu
  have h2 : ∑ i ∈ range (leafDepth x b), (fullSet x b F i).card ≤
      leafDepth x b * (globalLost x b F).card := by
    calc ∑ i ∈ range (leafDepth x b), (fullSet x b F i).card
        ≤ ∑ _i ∈ range (leafDepth x b), (globalLost x b F).card :=
          sum_le_sum fun i hi => card_le_card (fullSet_subset_globalLost (mem_range.mp hi))
      _ = leafDepth x b * (globalLost x b F).card := by
            rw [sum_const, card_range]; rfl
  omega

/-- **Loss counters**, number of enumerations: at most `(leafDepth + 1) · |globalLost F|` enumerated
terminals, repeats included. -/
theorem runFailures_enumerated_le {l : List ℕ} (hnd : l.Nodup) (hl : ∀ u ∈ l, u < 2 ^ x) :
    (runFailures x b l).enumerated ≤ (leafDepth x b + 1) * (globalLost x b l.toFinset).card :=
  (runFailures_inv hnd hl).enumerated_le fun u hu => hl u (List.mem_toFinset.mp hu)

end MinCostFlow.HierPaths
