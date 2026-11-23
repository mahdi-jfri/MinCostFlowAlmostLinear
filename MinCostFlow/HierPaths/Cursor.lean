module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Monotone cursors

The path data structure keeps several fixed arrays (the connectors of a pair of children, the
support entries of a vertex), each with a cursor to its first valid entry.
Entries only turn from valid to invalid. When an entry becomes invalid, the cursor moves forward
past invalid entries until it finds a valid one or reaches the end. So a query reads a valid
entry in one step, and the total cost of all cursor moves is paid by the invalidations.

This file proves this once, for an array of `N` entries and a validity `valid t i` of entry `i` at
time `t` that can only turn off (`Antitone`-style hypothesis `hmono`). The cursor after time `t`
is `cursorAt valid N t`: at time `0` it moves from `0`, and at each later time it moves from where
it was (`advance`). The main results:

* `cursorAt_invalid`: every entry before the cursor is invalid;
* `cursorAt_valid`: if the cursor is before the end, its entry is valid;
* `cursorAt_eq_iff`: the cursor is at the end exactly when all entries are invalid;
* `sum_moves_eq` and `cursorAt_le_card_invalid`: over the whole history the number of moves is the
  final cursor position, and it is at most the number of entries that are invalid at the end;
  when all entries start valid, this is the number of entries made invalid
  (`cursorAt_le_card_madeInvalid`).

Calling `advance` on a cursor whose entry is still valid does not move it (`advance_of_valid`), so
it does not matter whether a cursor is refreshed at every time or only when its entry turns off.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- Move the cursor `c` forward to the first valid entry at or after `c`, or to `N` if there is
none. -/
def advance (valid : ℕ → Bool) (N c : ℕ) : ℕ :=
  if c < N then (if valid c then c else advance valid N (c + 1)) else c
termination_by N - c

/-- The cursor after time `t`: at time `0` it moves forward from `0`, and at time `t + 1` from its
position after time `t`, for the validity at that time. -/
def cursorAt (valid : ℕ → ℕ → Bool) (N : ℕ) : ℕ → ℕ
  | 0 => advance (valid 0) N 0
  | t + 1 => advance (valid (t + 1)) N (cursorAt valid N t)

/-- The cursor before time `t`: `0` before time `0`, and the cursor after time `t - 1` otherwise. -/
def cursorBefore (valid : ℕ → ℕ → Bool) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => cursorAt valid N t

end MinCostFlow.HierPaths

end

namespace MinCostFlow.HierPaths

public section

/-- `advance` never moves backward. -/
theorem le_advance (valid : ℕ → Bool) (N c : ℕ) : c ≤ advance valid N c := by
  induction h : N - c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    rw [advance]
    split_ifs with h1 h2
    · exact le_rfl
    · exact (ih (N - (c + 1)) (by omega) (c + 1) rfl).trans' (Nat.le_succ c)
    · exact le_rfl

/-- `advance` stays within the array when it starts there. -/
theorem advance_le (valid : ℕ → Bool) {N c : ℕ} (hc : c ≤ N) : advance valid N c ≤ N := by
  induction h : N - c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    rw [advance]
    split_ifs with h1 h2
    · exact hc
    · exact ih (N - (c + 1)) (by omega) (by omega) rfl
    · exact hc

/-- The entries that `advance` passes over are invalid. -/
theorem advance_invalid (valid : ℕ → Bool) (N c : ℕ) :
    ∀ i, c ≤ i → i < advance valid N c → valid i = false := by
  induction h : N - c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro i hci hi
    rw [advance] at hi
    split_ifs at hi with h1 h2
    · omega
    · rcases Nat.eq_or_lt_of_le hci with rfl | hlt
      · simpa using h2
      · exact ih (N - (c + 1)) (by omega) (c + 1) rfl i hlt hi
    · omega

/-- If `advance` stops before the end, it stops at a valid entry. -/
theorem advance_valid (valid : ℕ → Bool) (N c : ℕ) (h : advance valid N c < N) :
    valid (advance valid N c) = true := by
  induction hk : N - c using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    rw [advance] at h ⊢
    split_ifs at h ⊢ with h1 h2
    · exact h2
    · exact ih (N - (c + 1)) (by omega) (c + 1) h rfl
    · omega

/-- `advance` does not move a cursor whose entry is valid. -/
theorem advance_of_valid (valid : ℕ → Bool) {N c : ℕ} (hc : c < N) (hv : valid c = true) :
    advance valid N c = c := by
  rw [advance]
  simp [hc, hv]

variable {valid : ℕ → ℕ → Bool} {N : ℕ}

/-- The cursor never leaves the array. -/
theorem cursorAt_le (t : ℕ) : cursorAt valid N t ≤ N := by
  induction t with
  | zero => exact advance_le _ (Nat.zero_le N)
  | succ t ih => exact advance_le _ ih

/-- The cursor only moves forward. -/
theorem cursorBefore_le_cursorAt (t : ℕ) : cursorBefore valid N t ≤ cursorAt valid N t := by
  cases t with
  | zero => exact Nat.zero_le _
  | succ t => exact le_advance _ _ _

/-- The cursor invariant: every entry before the cursor is invalid at that time. -/
theorem cursorAt_invalid (hmono : ∀ t i, valid (t + 1) i = true → valid t i = true) (t : ℕ) :
    ∀ i < cursorAt valid N t, valid t i = false := by
  induction t with
  | zero => exact fun i hi => advance_invalid _ _ _ i (Nat.zero_le i) hi
  | succ t ih =>
    intro i hi
    by_cases hit : i < cursorAt valid N t
    · have h := ih i hit
      cases hv : valid (t + 1) i
      · rfl
      · rw [hmono t i hv] at h
        exact absurd h (by decide)
    · exact advance_invalid _ _ _ i (Nat.le_of_not_lt hit) hi

/-- A cursor before the end points to a valid entry. -/
theorem cursorAt_valid (t : ℕ) (h : cursorAt valid N t < N) :
    valid t (cursorAt valid N t) = true := by
  cases t with
  | zero => exact advance_valid _ _ _ h
  | succ t => exact advance_valid _ _ _ h

/-- The cursor is at the end exactly when all entries are invalid. -/
theorem cursorAt_eq_iff (hmono : ∀ t i, valid (t + 1) i = true → valid t i = true) (t : ℕ) :
    cursorAt valid N t = N ↔ ∀ i < N, valid t i = false := by
  constructor
  · intro h i hi
    exact cursorAt_invalid hmono t i (h ▸ hi)
  · intro hall
    rcases Nat.lt_or_ge (cursorAt valid N t) N with hlt | hge
    · have := cursorAt_valid t hlt
      rw [hall _ hlt] at this
      exact absurd this (by decide)
    · exact le_antisymm (cursorAt_le t) hge

/-- The moves of the cursor over times `0, …, t` add up to its final position. -/
theorem sum_moves_eq (t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), (cursorAt valid N k - cursorBefore valid N k) =
      cursorAt valid N t := by
  induction t with
  | zero => simp [cursorBefore]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    have := cursorBefore_le_cursorAt (valid := valid) (N := N) (t + 1)
    simp only [cursorBefore] at this ⊢
    omega

/-- Over any history the cursor moves at most once for each entry that is invalid at the end. -/
theorem cursorAt_le_card_invalid (hmono : ∀ t i, valid (t + 1) i = true → valid t i = true)
    (t : ℕ) : cursorAt valid N t ≤ ((Finset.range N).filter fun i => valid t i = false).card := by
  have hsub : Finset.range (cursorAt valid N t) ⊆
      (Finset.range N).filter fun i => valid t i = false := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_lt_of_le hi (cursorAt_le t), cursorAt_invalid hmono t i hi⟩
  simpa using Finset.card_le_card hsub

/-- When all entries start valid, the cursor moves at most once for each entry made invalid. -/
theorem cursorAt_le_card_madeInvalid
    (hmono : ∀ t i, valid (t + 1) i = true → valid t i = true)
    (h0 : ∀ i < N, valid 0 i = true) (t : ℕ) :
    cursorAt valid N t ≤
      ((Finset.range N).filter fun i => valid 0 i = true ∧ valid t i = false).card := by
  refine (cursorAt_le_card_invalid hmono t).trans (Finset.card_le_card ?_)
  intro i hi
  rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨hi.1, h0 i hi.1, hi.2⟩

end

end MinCostFlow.HierPaths
