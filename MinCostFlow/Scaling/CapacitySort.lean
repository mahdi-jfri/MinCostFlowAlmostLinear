module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Sorting the bottleneck candidates with counted work

Lemma C.10 of Chen et al., arXiv:2203.00671v2, searches the at most `m` edge
capacity values. This file supplies a deterministic merge sort for those integer
candidates and an explicit operation counter. The recursion depth is a ceiling
binary logarithm. Its output is a sorted permutation of the input, including
when capacities repeat.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Merge two sorted capacity lists, with counted comparisons and writes.
Five operations are reserved per comparison and the final suffix is copied. -/
def mergeCapacities : List ℕ → List ℕ → List ℕ × ℕ
  | [], ys => (ys, ys.length)
  | xs, [] => (xs, xs.length)
  | x :: xs, y :: ys =>
    if x ≤ y then
      let r := mergeCapacities xs (y :: ys)
      (x :: r.1, 5 + r.2)
    else
      let r := mergeCapacities (x :: xs) ys
      (y :: r.1, 5 + r.2)
termination_by xs ys => xs.length + ys.length

/-- The counted merge computes the usual stable merge. -/
theorem mergeCapacities_value (xs ys : List ℕ) :
    (mergeCapacities xs ys).1 = xs.merge ys (fun x y => decide (x ≤ y)) := by
  induction xs, ys using mergeCapacities.induct with
  | case1 ys => simp [mergeCapacities]
  | case2 xs => simp [mergeCapacities]
  | case3 x xs y ys h ih =>
    rw [mergeCapacities, ite_eq_left h, List.cons_merge_cons]
    simp only [h, decide_true, ↓reduceIte, ih]
  | case4 x xs y ys h ih =>
    rw [mergeCapacities, ite_eq_right h, List.cons_merge_cons]
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, ih]

/-- Merging uses at most six operations per input entry, plus one. -/
theorem mergeCapacities_work (xs ys : List ℕ) :
    (mergeCapacities xs ys).2 ≤ 6 * (xs.length + ys.length) + 1 := by
  induction xs, ys using mergeCapacities.induct with
  | case1 ys => simp only [mergeCapacities]; omega
  | case2 xs => simp only [mergeCapacities]; omega
  | case3 x xs y ys h ih =>
    rw [mergeCapacities, ite_eq_left h]
    dsimp only
    simp only [List.length_cons] at ih ⊢
    omega
  | case4 x xs y ys h ih =>
    rw [mergeCapacities, ite_eq_right h]
    dsimp only
    simp only [List.length_cons] at ih ⊢
    omega

/-- Split capacity candidates into balanced contiguous halves and sort them
with an explicit depth budget. A zero budget leaves its input unchanged. -/
def sortCapacitiesFuel : ℕ → List ℕ → List ℕ × ℕ
  | 0, xs => (xs, xs.length)
  | fuel + 1, xs =>
    if xs.length ≤ 1 then (xs, xs.length + 1)
    else
      let cut := (xs.length + 1) / 2
      let a := sortCapacitiesFuel fuel (xs.take cut)
      let b := sortCapacitiesFuel fuel (xs.drop cut)
      let r := mergeCapacities a.1 b.1
      (r.1, a.2 + b.2 + r.2 + 2 * xs.length + 3)

/-- Every depth budget preserves the multiset of capacity values. -/
theorem sortCapacitiesFuel_perm (fuel : ℕ) (xs : List ℕ) :
    (sortCapacitiesFuel fuel xs).1.Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    rw [sortCapacitiesFuel]
    split
    · exact List.Perm.refl _
    · dsimp only
      rw [mergeCapacities_value]
      apply (List.merge_perm_append _).trans
      have h := (ih (xs.take ((xs.length + 1) / 2))).append
        (ih (xs.drop ((xs.length + 1) / 2)))
      simpa only [List.take_append_drop] using h

/-- The sorted output has exactly the original number of capacity candidates. -/
theorem sortCapacitiesFuel_length (fuel : ℕ) (xs : List ℕ) :
    (sortCapacitiesFuel fuel xs).1.length = xs.length :=
  (sortCapacitiesFuel_perm fuel xs).length_eq

/-- A depth sufficient for the input size produces a sorted list. -/
theorem sortCapacitiesFuel_sorted (fuel : ℕ) (xs : List ℕ)
    (hsize : xs.length ≤ 2 ^ fuel) : (sortCapacitiesFuel fuel xs).1.Pairwise (· ≤ ·) := by
  induction fuel generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [sortCapacitiesFuel]
    | cons x xs =>
      cases xs with
      | nil => simp [sortCapacitiesFuel]
      | cons y ys => simp only [List.length_cons, Nat.pow_zero] at hsize; omega
  | succ fuel ih =>
    rw [sortCapacitiesFuel]
    split
    · rename_i h
      cases xs with
      | nil => simp
      | cons x xs =>
        cases xs with
        | nil => simp
        | cons y ys => simp only [List.length_cons] at h; omega
    · dsimp only
      rw [mergeCapacities_value]
      apply List.Pairwise.merge
      · apply ih
        simp only [List.length_take]
        rw [Nat.pow_succ] at hsize
        omega
      · apply ih
        simp only [List.length_drop]
        rw [Nat.pow_succ] at hsize
        omega

private theorem sort_work_step (fuel n a b u v w : ℕ) (hn : 2 ≤ n) (hab : a + b = n)
    (hu : u ≤ 12 * (fuel + 1) * a + 1) (hv : v ≤ 12 * (fuel + 1) * b + 1)
    (hw : w ≤ 6 * n + 1) : u + v + w + 2 * n + 3 ≤ 12 * (fuel + 2) * n + 1 := by
  subst n
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at *
  omega

/-- Sorting has a linear work budget at each of its explicit depth levels. -/
theorem sortCapacitiesFuel_work (fuel : ℕ) (xs : List ℕ) :
    (sortCapacitiesFuel fuel xs).2 ≤ 12 * (fuel + 1) * xs.length + 1 := by
  induction fuel generalizing xs with
  | zero => simp only [sortCapacitiesFuel]; omega
  | succ fuel ih =>
    rw [sortCapacitiesFuel]
    split
    · dsimp only
      apply Nat.add_le_add_right
      exact Nat.le_mul_of_pos_left _ (by omega)
    · rename_i hn
      dsimp only
      have ha := ih (xs.take ((xs.length + 1) / 2))
      have hb := ih (xs.drop ((xs.length + 1) / 2))
      have hm := mergeCapacities_work
        (sortCapacitiesFuel fuel (xs.take ((xs.length + 1) / 2))).1
        (sortCapacitiesFuel fuel (xs.drop ((xs.length + 1) / 2))).1
      rw [sortCapacitiesFuel_length, sortCapacitiesFuel_length] at hm
      have hl : (xs.take ((xs.length + 1) / 2)).length +
          (xs.drop ((xs.length + 1) / 2)).length = xs.length := by
        rw [← List.length_append, List.take_append_drop]
      rw [hl] at hm
      exact sort_work_step fuel xs.length _ _ _ _ _ (by omega) hl ha hb hm

/-- The complete deterministic sort of the edge capacity candidates. -/
def sortCapacities (xs : List ℕ) : List ℕ × ℕ :=
  sortCapacitiesFuel (Nat.clog 2 (xs.length + 1)) xs

/-- The sorted list is a permutation of the original capacity list. -/
theorem sortCapacities_perm (xs : List ℕ) : (sortCapacities xs).1.Perm xs :=
  sortCapacitiesFuel_perm _ _

/-- The capacity candidates are returned in nondecreasing order. -/
theorem sortCapacities_sorted (xs : List ℕ) : (sortCapacities xs).1.Pairwise (· ≤ ·) :=
  sortCapacitiesFuel_sorted _ _ (le_trans (Nat.le_succ _)
    (Nat.le_pow_clog (by decide) _))

/-- The sorting counter is at most `12*(clog_2(m+1)+1)*m+1`. -/
theorem sortCapacities_work (xs : List ℕ) :
    (sortCapacities xs).2 ≤ 12 * (Nat.clog 2 (xs.length + 1) + 1) * xs.length + 1 :=
  sortCapacitiesFuel_work _ _

end MinCostFlow.Scaling
