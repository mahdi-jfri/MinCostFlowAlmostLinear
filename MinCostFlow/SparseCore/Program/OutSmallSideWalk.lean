module

public import MinCostFlow.SparseCore.Program.OutTourInterface

/-!
# The walk of the helper `outSmallSide`

The helper walks the marked ends of a tour list, starting from the first one and asking each
time for the next marked end (`OutTourAbs.nextMarked`). This file shows what the walk sees. When
the list has no repeated end, the next marked end after the `i`-th marked end is the
`(i + 1)`-th, counted cyclically (`nextMarked_markedList`). So the walk comes back to the first
marked end after exactly as many steps as there are marked ends. It also bounds the number of
marked ends by `2 eCap` (`markedList_length_le`), which gives the space bound of the helper in
fixed sizes.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

/-- In `A ++ x :: B`, the first entry of `B ++ A ++ [x]` is the entry after `x`, counted
cyclically. -/
theorem head?_rotate_eq_getElem? (A B : List End) (x : End) :
    (B ++ A ++ [x]).head? = (A ++ x :: B)[(A.length + 1) % (A ++ x :: B).length]? := by
  cases B with
  | cons b B =>
    have hlen : (A ++ x :: b :: B).length = A.length + 2 + B.length := by simp; omega
    rw [hlen, Nat.mod_eq_of_lt (by omega)]
    simp
  | nil =>
    cases A with
    | cons a A =>
      have hlen : ((a :: A) ++ [x]).length = (a :: A).length + 1 := by simp
      rw [hlen, Nat.mod_self]
      simp
    | nil => simp

private theorem afterEnd_of_append' (x : End) (before rest : List End) (h : x ∉ before) :
    afterEnd x (before ++ x :: rest) = rest ++ before := by
  have hp : ∀ y ∈ before, y != x := by
    intro y hy
    exact bne_iff_ne.mpr (fun he => h (he ▸ hy))
  simp [afterEnd, List.takeWhile_append_of_pos hp, List.drop_append]

/-- **The next marked end of a marked end.** If the list `cord r` has no repeated end, the next
marked end after the `i`-th marked end is the `(i + 1)`-th marked end, counted cyclically. -/
theorem nextMarked_markedList (s : OutTourAbs) (r : ℕ) (hnd : (s.cord r).Nodup) {i : ℕ}
    (hi : i < (s.markedList r).length) :
    s.nextMarked r ((s.markedList r)[i]) =
      (s.markedList r)[(i + 1) % (s.markedList r).length]? := by
  classical
  set M := s.markedList r with hM
  set x := M[i] with hx
  have hxM : x ∈ M := List.getElem_mem hi
  have hxt : x ∈ s.cord r := (List.mem_filter.mp hxM).1
  have hxm : x ∈ s.marked := by simpa using (List.mem_filter.mp hxM).2
  obtain ⟨A, B, hAB⟩ := List.mem_iff_append.mp hxt
  have hxA : x ∉ A := by
    intro hm
    rw [hAB] at hnd
    exact (List.nodup_append.mp hnd).2.2 x hm x (by simp) rfl
  set P : End → Bool := fun z => decide (z ∈ s.marked) with hP
  have hMeq : M = A.filter P ++ x :: B.filter P := by
    rw [hM, OutTourAbs.markedList, hAB, List.filter_append, List.filter_cons_of_pos (by simpa)]
  have hMnd : M.Nodup := hnd.filter _
  -- the index of `x` is the number of marked ends before it
  have hidx : i = (A.filter P).length := by
    have hlt : (A.filter P).length < M.length := by rw [hMeq]; simp
    have hget : M[(A.filter P).length]'hlt = x := by
      simp only [hMeq, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
    exact (List.Nodup.getElem_inj_iff hMnd).mp (hx.symm.trans hget.symm)
  unfold OutTourAbs.nextMarked
  rw [← hM, hAB, afterEnd_of_append' x A B hxA, ← List.head?_filter]
  have hf : (B ++ A ++ [x]).filter (fun z => decide (z ∈ s.marked)) =
      B.filter P ++ A.filter P ++ [x] := by
    rw [List.filter_append, List.filter_append, List.filter_singleton]
    simp [hxm, hP]
  rw [hf, head?_rotate_eq_getElem?, ← hMeq, hidx]

/-- A list of ends without repeats, all of edges below `eCap`, has at most `2 eCap` entries. -/
theorem length_le_of_nodup_lt {l : List End} {eCap : ℕ} (hnd : l.Nodup)
    (hl : ∀ x ∈ l, x.1 < eCap) : l.length ≤ 2 * eCap := by
  classical
  have hsub : l.toFinset ⊆ (Finset.range eCap) ×ˢ (Finset.univ : Finset Bool) := by
    intro x hx
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    exact hl x (List.mem_toFinset.mp hx)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_product, Finset.card_range,
    Finset.card_univ, Fintype.card_bool] at this
  omega

/-- The marked ends of a list without repeats, of edges below `eCap`, are at most `2 eCap`. -/
theorem markedList_length_le (s : OutTourAbs) (r : ℕ) {eCap : ℕ} (hnd : (s.cord r).Nodup)
    (hl : ∀ x ∈ s.markedList r, x.1 < eCap) : (s.markedList r).length ≤ 2 * eCap :=
  length_le_of_nodup_lt (hnd.filter _) hl

end MinCostFlow.SparseCore.Program
