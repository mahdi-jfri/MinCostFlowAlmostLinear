module

public import MinCostFlow.SparseCore.Program.OutTourInterface
import MinCostFlow.Bundle.Cyclic

/-!
# Order edits on one cyclic list

The output step returns edits of the output order (`OrdEdit`). A list of ends stands for a
cyclic order, so a program first gets the lists right up to rotation and then rotates each list
to its start. This file proves the two list facts behind this.

* `insertBefore_cycNext_isRotated`: let `t` be a list without repeats, `P` the ends present so
  far, and `x ∈ t` an end not present. If `xs` is a rotation of `t` restricted to `P`, then
  inserting `x` before the next present end after `x` in `t` (`cycNextWith`), or at the back when
  there is none, gives a rotation of `t` restricted to `P` and `x`.
* `rotateToList_eq_of_isRotated`: a list without repeats that is a rotation of `y :: r`, rotated
  to start at `y`, is `y :: r`.

Both come from one fact: a rotation of `y :: r` without repeats is cut at the position of `y`
(`drop_idxOf_append_take`).
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

/-- A list without repeats that is a rotation of `y :: r`, cut at the position of `y` and put
back together the other way, is `y :: r`. -/
theorem drop_idxOf_append_take {xs r : List End} {y : End} (hn : xs.Nodup)
    (h : xs.IsRotated (y :: r)) :
    xs.drop (xs.idxOf y) ++ xs.take (xs.idxOf y) = y :: r := by
  obtain ⟨n, hrot⟩ := h
  have hlen : 0 < xs.length := by
    have := congrArg List.length hrot
    simp only [List.length_rotate, List.length_cons] at this
    omega
  have hi : n % xs.length < xs.length := Nat.mod_lt _ hlen
  have hrot' : xs.rotate (n % xs.length) = y :: r := by rw [List.rotate_mod]; exact hrot
  rw [List.rotate_eq_drop_append_take hi.le, List.drop_eq_getElem_cons hi] at hrot'
  have hy : xs[n % xs.length] = y := (List.cons.inj hrot').1
  have hidx : xs.idxOf y = n % xs.length := hy ▸ hn.idxOf_getElem _ hi
  rw [hidx, List.drop_eq_getElem_cons hi]
  exact hrot'

/-- Rotating a list without repeats that is a rotation of `y :: r` to start at `y` gives
`y :: r`. -/
theorem rotateToList_eq_of_isRotated {xs r : List End} {y : End} (hn : xs.Nodup)
    (h : xs.IsRotated (y :: r)) : rotateToList y xs = y :: r := by
  have hy : y ∈ xs := h.mem_iff.mpr List.mem_cons_self
  rw [rotateToList, ite_eq_left hy]
  exact drop_idxOf_append_take hn h

/-- Inserting `x` before `y` in a list without repeats that is a rotation of `y :: r` gives a
rotation of `x :: y :: r`. -/
theorem insertBeforeList_isRotated {xs r : List End} {x y : End} (hn : xs.Nodup)
    (h : xs.IsRotated (y :: r)) :
    (insertBeforeList x (some y) xs).IsRotated (x :: y :: r) := by
  rw [insertBeforeList]
  have hcut := drop_idxOf_append_take hn h
  have : x :: y :: r = (x :: xs.drop (xs.idxOf y)) ++ xs.take (xs.idxOf y) := by
    rw [List.cons_append, hcut]
  rw [this]
  exact List.isRotated_append

private theorem afterEnd_of_append (x : End) (before rest : List End) (h : x ∉ before) :
    afterEnd x (before ++ x :: rest) = rest ++ before := by
  have hp : ∀ y ∈ before, y != x := by
    intro y hy
    exact bne_iff_ne.mpr (fun he => h (he ▸ hy))
  simp [afterEnd, List.takeWhile_append_of_pos hp, List.drop_append]

/-- A list without repeats that holds `x` is a rotation of `x` followed by the ends after it. -/
theorem isRotated_cons_afterEnd {x : End} {xs : List End} (h : x ∈ xs) (hn : xs.Nodup) :
    xs.IsRotated (x :: afterEnd x xs) := by
  obtain ⟨pre, rest, rfl⟩ := List.mem_iff_append.mp h
  have hnot : x ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 x hm x (by simp) rfl
  rw [afterEnd_of_append x pre rest hnot]
  have : x :: (rest ++ pre) = (x :: rest) ++ pre := rfl
  rw [this]
  exact List.isRotated_append

/-- **Insertion at the next present end.** Let `t` be a list without repeats, `P` the present
ends, and `x ∈ t` not present. If `xs` is a rotation of `t` restricted to `P`, then inserting
`x` before the next present end after `x` (or at the back when there is none) gives a rotation of
`t` restricted to `P` and `x`. -/
theorem insertBefore_cycNext_isRotated {t xs : List End} {P : End → Bool} {x : End}
    (ht : t.Nodup) (hx : x ∈ t) (hPx : P x = false) (h : xs.IsRotated (t.filter P)) :
    (insertBeforeList x (cycNextWith t P x) xs).IsRotated
      (t.filter fun z => P z || z == x) := by
  set a := afterEnd x t with ha
  have hrot := isRotated_cons_afterEnd hx ht
  have hna : (x :: a).Nodup := hrot.nodup_iff.mp ht
  have hxa : x ∉ a := (List.nodup_cons.mp hna).1
  -- the present ends of `t` are those after `x`
  have hP : (t.filter P).IsRotated (a.filter P) := by
    have := isRotated_filter P hrot
    rwa [List.filter_cons_of_neg (by simp [hPx])] at this
  have hQ : (t.filter fun z => P z || z == x).IsRotated (x :: a.filter P) := by
    have := isRotated_filter (fun z => P z || z == x) hrot
    rw [List.filter_cons_of_pos (by simp)] at this
    have hcongr : (a.filter fun z => P z || z == x) = a.filter P := by
      apply List.filter_congr
      intro z hz
      have hzx : (z == x) = false := by
        simp only [beq_eq_false_iff_ne]; rintro rfl; exact hxa hz
      simp [hzx]
    rwa [hcongr] at this
  have hxs : xs.IsRotated (a.filter P) := h.trans hP
  have hnext : cycNextWith t P x = (a.filter P).head? := by
    rw [cycNextWith, ← ha, List.head?_filter]
  rw [hnext]
  cases hf : a.filter P with
  | nil =>
    rw [hf] at hxs hQ
    rw [List.isRotated_nil_iff.mp hxs]
    exact hQ.symm
  | cons y r =>
    rw [hf] at hxs hQ
    have hnr : (y :: r).Nodup := hf ▸ (List.nodup_cons.mp hna).2.filter P
    exact (insertBeforeList_isRotated (hxs.nodup_iff.mpr hnr) hxs).trans hQ.symm

end MinCostFlow.SparseCore.Program
