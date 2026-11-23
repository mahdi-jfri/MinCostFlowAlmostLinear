module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.FinCases

/-!
# The five sums of region growing, entry by entry

The petal search keeps five sums over the active entries `j < n` (each one a pair with the ends
`ea j` and `eb j`, super-vertices, and the scaled weight `wt j`), for the list `ℓ` of settled
super-vertices in the order they were settled (`ESum`):
* `0`: the entries with both ends settled;
* `1`: the weights of the entries with an end settled and both ends allowed;
* `2`: the weights of the entries with both ends settled;
* `3`, `4`: as `1` and `2`, each weight times the cost `δ` of the end settled first.

When a super-vertex `u` is settled, each entry at `u` adds what `psum` adds for the arc of `u`
along it (`EAdd`, `esum_snoc`). Here the arcs of `u` are counted by the items `o < 2n` with tail
`u` (`esum_snoc_items`): item `2j` goes from `ea j` to `eb j`, item `2j + 1` back.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Classical

variable (ea eb wt : ℕ → ℕ) (ok : ℕ → Prop) (δ : ℕ → ℕ)

/-- The end of entry `j` that comes first in `ℓ` (the first end if neither is in `ℓ`). -/
noncomputable def efst (ℓ : List ℕ) (j : ℕ) : ℕ :=
  if ℓ.idxOf (ea j) ≤ ℓ.idxOf (eb j) then ea j else eb j

/-- Entry `j` has an end in `ℓ` and both ends allowed. -/
def EOne (ℓ : List ℕ) (j : ℕ) : Prop := (ea j ∈ ℓ ∨ eb j ∈ ℓ) ∧ ok (ea j) ∧ ok (eb j)

/-- Both ends of entry `j` are in `ℓ`. -/
def EBoth (ℓ : List ℕ) (j : ℕ) : Prop := ea j ∈ ℓ ∧ eb j ∈ ℓ

/-- What entry `j` adds to each of the five sums. -/
noncomputable def eTerm (ℓ : List ℕ) (j : ℕ) : Fin 5 → ℕ
  | 0 => if EBoth ea eb ℓ j then 1 else 0
  | 1 => if EOne ea eb ok ℓ j then wt j else 0
  | 2 => if EBoth ea eb ℓ j then wt j else 0
  | 3 => if EOne ea eb ok ℓ j then wt j * δ (efst ea eb ℓ j) else 0
  | 4 => if EBoth ea eb ℓ j then wt j * δ (efst ea eb ℓ j) else 0

/-- The five sums. -/
noncomputable def ESum (n : ℕ) (ℓ : List ℕ) (t : Fin 5) : ℕ :=
  ∑ j ∈ Finset.range n, eTerm ea eb wt ok δ ℓ j t

/-- What the arc of a newly settled `u` along an entry of weight `x` to `y` adds, as in `psum`.
`ℓ'` is the settled list with `u` at its end. -/
noncomputable def EAdd (ℓ' : List ℕ) (u y x : ℕ) : Fin 5 → ℕ
  | 0 => if ok y ∧ y ∈ ℓ' then 1 else 0
  | 1 => if ok y ∧ y ∉ ℓ' then x else 0
  | 2 => if ok y ∧ y ∈ ℓ' then x else 0
  | 3 => if ok y ∧ y ∉ ℓ' then x * δ u else 0
  | 4 => if ok y ∧ y ∈ ℓ' then x * δ y else 0

variable {ea eb wt ok δ}

theorem idxOf_snoc_of_mem {ℓ : List ℕ} {x u : ℕ} (hx : x ∈ ℓ) :
    (ℓ ++ [u]).idxOf x = ℓ.idxOf x := by
  rw [List.idxOf_append, if_pos hx]

theorem idxOf_snoc_of_not_mem {ℓ : List ℕ} {x u : ℕ} (hx : x ∉ ℓ) (hxu : x ≠ u) :
    (ℓ ++ [u]).idxOf x = ℓ.length + 1 := by
  rw [List.idxOf_append, if_neg hx]
  simp [hxu.symm]
  omega

theorem idxOf_snoc_self {ℓ : List ℕ} {u : ℕ} (hu : u ∉ ℓ) :
    (ℓ ++ [u]).idxOf u = ℓ.length := by
  rw [List.idxOf_append, if_neg hu]
  simp

theorem idxOf_of_not_mem {ℓ : List ℕ} {x : ℕ} (hx : x ∉ ℓ) : ℓ.idxOf x = ℓ.length :=
  List.idxOf_eq_length_iff.mpr hx

theorem idxOf_lt_of_mem {ℓ : List ℕ} {x : ℕ} (hx : x ∈ ℓ) : ℓ.idxOf x < ℓ.length :=
  List.idxOf_lt_length_iff.mpr hx

/-- The first end does not change for an entry away from the new `u`. -/
theorem efst_snoc {ℓ : List ℕ} {u j : ℕ} (ha : ea j ≠ u) (hb : eb j ≠ u) :
    efst ea eb (ℓ ++ [u]) j = efst ea eb ℓ j := by
  unfold efst
  congr 1
  apply propext
  by_cases h1 : ea j ∈ ℓ <;> by_cases h2 : eb j ∈ ℓ
  · rw [idxOf_snoc_of_mem h1, idxOf_snoc_of_mem h2]
  · rw [idxOf_snoc_of_mem h1, idxOf_snoc_of_not_mem h2 hb, idxOf_of_not_mem h2]
    have := idxOf_lt_of_mem h1; constructor <;> intro <;> omega
  · rw [idxOf_snoc_of_not_mem h1 ha, idxOf_snoc_of_mem h2, idxOf_of_not_mem h1]
    have := idxOf_lt_of_mem h2; constructor <;> intro <;> omega
  · rw [idxOf_snoc_of_not_mem h1 ha, idxOf_snoc_of_not_mem h2 hb, idxOf_of_not_mem h1,
      idxOf_of_not_mem h2]
    omega

/-- An entry at the new `u` whose other end `y` was settled before: its first end is `y`. -/
theorem efst_snoc_a {ℓ : List ℕ} {u j : ℕ} (hu : u ∉ ℓ) (ha : ea j = u) (hb : eb j ∈ ℓ) :
    efst ea eb (ℓ ++ [u]) j = eb j ∧ efst ea eb ℓ j = eb j := by
  have hbu : eb j ≠ u := fun e => hu (e ▸ hb)
  have h1 := idxOf_lt_of_mem hb
  unfold efst
  rw [ha, idxOf_snoc_self hu, idxOf_snoc_of_mem hb, idxOf_of_not_mem hu]
  constructor
  · rw [if_neg (by omega)]
  · rw [if_neg (by omega)]

theorem efst_snoc_b {ℓ : List ℕ} {u j : ℕ} (hu : u ∉ ℓ) (hb : eb j = u) (ha : ea j ∈ ℓ) :
    efst ea eb (ℓ ++ [u]) j = ea j ∧ efst ea eb ℓ j = ea j := by
  have h1 := idxOf_lt_of_mem ha
  unfold efst
  rw [hb, idxOf_snoc_self hu, idxOf_snoc_of_mem ha, idxOf_of_not_mem hu]
  constructor
  · rw [if_pos (by omega)]
  · rw [if_pos (by omega)]

/-- An entry at the new `u` whose other end was not settled: its first end is now `u`. -/
theorem efst_snoc_a' {ℓ : List ℕ} {u j : ℕ} (hu : u ∉ ℓ) (ha : ea j = u) (hb : eb j ∉ ℓ)
    (hbu : eb j ≠ u) : efst ea eb (ℓ ++ [u]) j = u := by
  unfold efst
  rw [ha, idxOf_snoc_self hu, idxOf_snoc_of_not_mem hb hbu, if_pos (by omega)]

theorem efst_snoc_b' {ℓ : List ℕ} {u j : ℕ} (hu : u ∉ ℓ) (hb : eb j = u) (ha : ea j ∉ ℓ)
    (hau : ea j ≠ u) : efst ea eb (ℓ ++ [u]) j = u := by
  unfold efst
  rw [hb, idxOf_snoc_self hu, idxOf_snoc_of_not_mem ha hau, if_neg (by omega)]

/-- **One entry.** Settling `u` changes the terms of entry `j` by what its arcs at `u` add. -/
theorem eTerm_snoc {ℓ : List ℕ} {u j : ℕ} (hu : u ∉ ℓ) (hok : ok u) (hℓ : ∀ v ∈ ℓ, ok v)
    (hab : ea j ≠ eb j) (t : Fin 5) :
    eTerm ea eb wt ok δ (ℓ ++ [u]) j t = eTerm ea eb wt ok δ ℓ j t +
      ((if ea j = u then EAdd ok δ (ℓ ++ [u]) u (eb j) (wt j) t else 0) +
       (if eb j = u then EAdd ok δ (ℓ ++ [u]) u (ea j) (wt j) t else 0)) := by
  have hm : ∀ x, x ∈ ℓ ++ [u] ↔ x ∈ ℓ ∨ x = u := fun x => by simp
  by_cases ha : ea j = u
  · have hb : eb j ≠ u := fun e => hab (ha.trans e.symm)
    rw [if_pos ha, if_neg hb, Nat.add_zero]
    have hau : ea j ∉ ℓ := ha ▸ hu
    by_cases hbl : eb j ∈ ℓ
    · obtain ⟨e1, e2⟩ := efst_snoc_a (ea := ea) hu ha hbl
      have hokb := hℓ _ hbl
      fin_cases t <;>
        simp [eTerm, EAdd, EOne, EBoth, hm, ha, hbl, hau, hu, hok, hokb, e1, e2]
    · have e1 := efst_snoc_a' (ea := ea) hu ha hbl hb
      fin_cases t <;> by_cases hokb : ok (eb j) <;>
        simp [eTerm, EAdd, EOne, EBoth, hm, ha, hbl, hb, hau, hu, hok, hokb, e1]
  · rw [if_neg ha]
    by_cases hb : eb j = u
    · rw [if_pos hb, Nat.zero_add]
      have hbl : eb j ∉ ℓ := hb ▸ hu
      by_cases hal : ea j ∈ ℓ
      · obtain ⟨e1, e2⟩ := efst_snoc_b (ea := ea) hu hb hal
        have hoka := hℓ _ hal
        fin_cases t <;>
          simp [eTerm, EAdd, EOne, EBoth, hm, hb, hal, hbl, hu, hok, hoka, e1, e2]
      · have e1 := efst_snoc_b' (ea := ea) hu hb hal ha
        fin_cases t <;> by_cases hoka : ok (ea j) <;>
          simp [eTerm, EAdd, EOne, EBoth, hm, hb, hal, hbl, ha, hu, hok, hoka, e1]
    · rw [if_neg hb, Nat.add_zero]
      have e1 := efst_snoc (ea := ea) (ℓ := ℓ) ha hb
      by_cases h1 : ea j ∈ ℓ <;> by_cases h2 : eb j ∈ ℓ <;> fin_cases t <;>
        simp [eTerm, EOne, EBoth, hm, ha, hb, e1, h1, h2]

/-- **Settling `u`.** The sums grow by what the entries at `u` add. -/
theorem esum_snoc {n : ℕ} {ℓ : List ℕ} {u : ℕ} (hu : u ∉ ℓ) (hok : ok u) (hℓ : ∀ v ∈ ℓ, ok v)
    (hab : ∀ j < n, ea j ≠ eb j) (t : Fin 5) :
    ESum ea eb wt ok δ n (ℓ ++ [u]) t = ESum ea eb wt ok δ n ℓ t +
      (∑ j ∈ (Finset.range n).filter (ea · = u), EAdd ok δ (ℓ ++ [u]) u (eb j) (wt j) t +
       ∑ j ∈ (Finset.range n).filter (eb · = u), EAdd ok δ (ℓ ++ [u]) u (ea j) (wt j) t) := by
  unfold ESum
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact eTerm_snoc hu hok hℓ (hab j (Finset.mem_range.mp hj)) t

variable (ea eb) in
/-- The tail of item `o`: item `2j` goes from `ea j` to `eb j`, item `2j + 1` back. -/
def itl (o : ℕ) : ℕ := if o % 2 = 0 then ea (o / 2) else eb (o / 2)
variable (ea eb) in
/-- The head of item `o`. -/
def ihd (o : ℕ) : ℕ := if o % 2 = 0 then eb (o / 2) else ea (o / 2)

theorem sum_range_two_mul (n : ℕ) (h : ℕ → ℕ) :
    ∑ o ∈ Finset.range (2 * n), h o = ∑ j ∈ Finset.range n, (h (2 * j) + h (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    omega

variable (ea eb) in
/-- The items with tail `u` add the same as the entries at `u`. -/
theorem sum_items (n : ℕ) (u : ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ o ∈ (Finset.range (2 * n)).filter (itl ea eb · = u), f (ihd ea eb o) (o / 2) =
      ∑ j ∈ (Finset.range n).filter (ea · = u), f (eb j) j +
      ∑ j ∈ (Finset.range n).filter (eb · = u), f (ea j) j := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, sum_range_two_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j) % 2 = 0 := by omega
  have q1 : (2 * j + 1) / 2 = j := by omega
  have q2 : (2 * j) / 2 = j := by omega
  simp only [itl, ihd, h1, h2, q1, q2, if_true, one_ne_zero, if_false]

end MinCostFlow.LowStretch
