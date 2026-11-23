module

public import MinCostFlow.MinRatio.SelectLevelBlocks
public import MinCostFlow.MinRatio.WireSelectSplitPot
public import MinCostFlow.MinRatio.WireSelectHeapRebal

/-!
# The frozen potentials at a vertex split (`SelectBlocksSplit`)

At an `Update`, a split `v ↦ v'` that enters a level `j` that is not rebuilt gives `G_j` a new
vertex `v'` (`WireSelectSplitPot.lean`). The frozen potentials keep every key if the new vertex
gets the potential of the vertex it split from: `φ'_j v' = φ_j v`. In memory this is one copy of
the `Lk` limbs of entry `v` to entry `v'` of the table `φ_j` (`copyLimbsToContract`, cost
`18 Lk + 16`). This file proves that the copy gives the table of `φ'`.

* `EdgeValuesAt.write_entry`: writing a valid entry `v'` with value `x`, and nothing else, gives
  the table of `Function.update φ v' x` on `insert v' V`.
* `EdgeValuesAt.copy_entry`: the copy of entry `v` to entry `v'`.
* `edgeValuesAt_of_copyLimbsTo_post`: the post of `copyLimbsToContract` at the two entries gives
  the table of `φ'`.
* `splitPot`: the potentials after the splits of one level, and `splitPot_old`, `splitPot_new`:
  `φ'` agrees with `φ` on the old vertices and copies `φ v` to `v'` (the hypotheses of
  `endPotAgree_of_split`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

private theorem entry_disj {e v' L i : ℕ} (hne : e ≠ v') (hi : i < L) :
    e * L + i < v' * L ∨ v' * L + L ≤ e * L + i := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  · right
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at this
    omega

/-- Writing the entry `v'` of a table of values, and no other word, gives the table of
`Function.update φ v' x` on `insert v' V`, if the new entry is valid with value `x`. -/
theorem EdgeValuesAt.write_entry {mem mem' : ℕ → ℕ} {a h L P : ℕ} {V : Finset ℕ}
    {φ : ℕ → ℝ} {v' : ℕ} {x : ℝ}
    (hv : EdgeValuesAt mem a h L P V φ)
    (hfr : ∀ y, (y < a + v' * L ∨ a + v' * L + L ≤ y) → mem' y = mem y)
    (hnew : Num.Valid mem' (a + v' * L) h L ∧ Num.fixVal mem' (a + v' * L) h L P = x) :
    EdgeValuesAt mem' a h L P (insert v' V) (Function.update φ v' x) := by
  intro e he
  by_cases hev : e = v'
  · subst hev
    rw [Function.update_self]
    exact hnew
  · have heV : e ∈ V := (Finset.mem_insert.mp he).resolve_left hev
    rw [Function.update_of_ne hev]
    -- The words of entry `e` lie outside entry `v'`, so the copy keeps them.
    have hkeep : ∀ i < L, mem' (a + e * L + i) = mem (a + e * L + i) := fun i hi => by
      apply hfr
      rcases entry_disj hev hi with h1 | h1
      · left; omega
      · right; omega
    refine ⟨fun i hi => (hkeep i hi) ▸ (hv e heV).1 i hi, ?_⟩
    unfold Num.fixVal
    rw [Num.intVal_congr hkeep]
    exact (hv e heV).2

/-- Copying the `L` words of entry `v` to entry `v'`, and writing no other word, gives the table
of `Function.update φ v' (φ v)` on `insert v' V`. -/
theorem EdgeValuesAt.copy_entry {mem mem' : ℕ → ℕ} {a h L P : ℕ} {V : Finset ℕ}
    {φ : ℕ → ℝ} {v v' : ℕ}
    (hv : EdgeValuesAt mem a h L P V φ) (hvV : v ∈ V)
    (hcp : ∀ i < L, mem' (a + v' * L + i) = mem (a + v * L + i))
    (hfr : ∀ y, (y < a + v' * L ∨ a + v' * L + L ≤ y) → mem' y = mem y) :
    EdgeValuesAt mem' a h L P (insert v' V) (Function.update φ v' (φ v)) := by
  refine hv.write_entry hfr ⟨fun i hi => (hcp i hi) ▸ (hv v hvV).1 i hi, ?_⟩
  unfold Num.fixVal
  rw [Num.intVal_congr hcp]
  exact (hv v hvV).2

/-- **The copy at a split, as a call.** The post of `copyLimbsToContract` with source the entry `v`
and destination the entry `v'` of the table `φ_j` gives the table of `φ'_j`. -/
theorem edgeValuesAt_of_copyLimbsTo_post {w : ℕ} {mem mem' : ℕ → ℕ} {a h L P ret : ℕ}
    {V : Finset ℕ} {φ : ℕ → ℝ} {v v' : ℕ}
    (hv : EdgeValuesAt mem a h L P V φ) (hvV : v ∈ V)
    (hpost : (copyLimbsToContract w).post [a + v * L, a + v' * L, L] mem ret mem') :
    EdgeValuesAt mem' a h L P (insert v' V) (Function.update φ v' (φ v)) := by
  obtain ⟨_, hcp, hfr⟩ := hpost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hcp hfr
  exact hv.copy_entry hvV hcp hfr

/-- The potentials of level `j` after the splits `splits` (pairs `(v, v')`, in order): each new
vertex `v'` gets the potential that `v` has at that point. -/
def splitPot (φj : ℕ → ℝ) : List (ℕ × ℕ) → ℕ → ℝ
  | [] => φj
  | (v, v') :: rest => splitPot (Function.update φj v' (φj v)) rest

/-- On a vertex that is not the new vertex of any split, `splitPot` keeps the potential. -/
theorem splitPot_old (φj : ℕ → ℝ) (splits : List (ℕ × ℕ)) (u : ℕ)
    (hu : ∀ s ∈ splits, s.2 ≠ u) : splitPot φj splits u = φj u := by
  induction splits generalizing φj with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨v, v'⟩ := s
    simp only [splitPot]
    rw [ih _ fun s hs => hu s (List.mem_cons_of_mem _ hs)]
    exact Function.update_of_ne (fun h => hu (v, v') List.mem_cons_self h.symm) _ _

/-- If no split creates `v` or creates `v'` twice, and `v` is not a new vertex, the new vertex
`v'` of a split `(v, v')` gets the old potential of `v`. -/
theorem splitPot_new (φj : ℕ → ℝ) (splits : List (ℕ × ℕ)) {v v' : ℕ}
    (hmem : (v, v') ∈ splits) (hold : ∀ s ∈ splits, s.2 ≠ v)
    (huniq : ∀ s ∈ splits, s.2 = v' → s = (v, v')) (hnodup : splits.Nodup) :
    splitPot φj splits v' = φj v := by
  induction splits generalizing φj with
  | nil => cases hmem
  | cons s rest ih =>
    obtain ⟨u, u'⟩ := s
    simp only [splitPot]
    have hnd := List.nodup_cons.mp hnodup
    rcases List.mem_cons.mp hmem with h | h
    · -- The split `(v, v')` comes first: later splits do not create `v'` again.
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rw [splitPot_old _ rest _ fun s hs hs2 => by
        have := huniq s (List.mem_cons_of_mem _ hs) hs2
        exact hnd.1 (this ▸ hs)]
      rw [Function.update_self]
    · rw [ih _ h (fun s hs => hold s (List.mem_cons_of_mem _ hs))
        (fun s hs => huniq s (List.mem_cons_of_mem _ hs)) hnd.2]
      have hu' : u' ≠ v := hold (u, u') List.mem_cons_self
      exact Function.update_of_ne hu'.symm _ _

end MinCostFlow.MinRatio
