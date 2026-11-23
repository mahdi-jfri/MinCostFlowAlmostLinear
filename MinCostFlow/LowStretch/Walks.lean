module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Walks and distances in a pair graph

The construction of the low-stretch tree works on a *pair graph*: vertices `0, …, n - 1` and a
list of pairs `(u, v, ω)`, one for each unordered pair of vertices joined by an edge of the input.
This file gives walks that stay in a vertex set and use allowed pairs, their lengths under a length
function on pair numbers, and the distance (the least length of a walk).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- A pair graph: `n` vertices and pairs `(u, v, ω)`. -/
structure PG where
  /-- The number of vertices. -/
  n : ℕ
  /-- The pairs: two ends and a weight. -/
  pairs : List (ℕ × ℕ × ℕ)

namespace PG

variable (G : PG)

/-- The number of pairs. -/
def m : ℕ := G.pairs.length

/-- The first end of pair `p`. -/
def pu (p : ℕ) : ℕ := (G.pairs.getD p (0, 0, 0)).1

/-- The second end of pair `p`. -/
def pv (p : ℕ) : ℕ := (G.pairs.getD p (0, 0, 0)).2.1

/-- The weight of pair `p`. -/
def pω (p : ℕ) : ℕ := (G.pairs.getD p (0, 0, 0)).2.2

/-- Pair `p` exists and joins `a` and `b`, in either order. -/
def Joins (p a b : ℕ) : Prop :=
  p < G.m ∧ (G.pu p = a ∧ G.pv p = b ∨ G.pu p = b ∧ G.pv p = a)

theorem Joins.symm {G : PG} {p a b : ℕ} (h : G.Joins p a b) : G.Joins p b a :=
  ⟨h.1, h.2.symm⟩

/-- `ps` is a walk from `a` to `b` whose vertices lie in `V` and whose pairs lie in `P`. -/
inductive IsWalk (V P : Set ℕ) : ℕ → ℕ → List ℕ → Prop
  | nil {a : ℕ} (ha : a ∈ V) : IsWalk V P a a []
  | cons {a b c p : ℕ} {ps : List ℕ} (ha : a ∈ V) (hp : p ∈ P) (hj : G.Joins p a b)
      (rest : IsWalk V P b c ps) : IsWalk V P a c (p :: ps)

/-- The length of a list of pairs under the length function `len`. -/
def wlen (len : ℕ → ℕ) (ps : List ℕ) : ℕ := (ps.map len).sum

/-- The distance from `a` to `b` in `V` under `len`: the least length of a walk in `V`. -/
noncomputable def dist (V : Set ℕ) (len : ℕ → ℕ) (a b : ℕ) : ℕ :=
  sInf {l | ∃ ps, G.IsWalk V Set.univ a b ps ∧ wlen len ps = l}

/-- `a` and `b` are joined by a walk in `V`. -/
def Reach (V : Set ℕ) (a b : ℕ) : Prop := ∃ ps, G.IsWalk V Set.univ a b ps

variable {G}

@[simp] theorem wlen_nil (len : ℕ → ℕ) : wlen len [] = 0 := rfl

@[simp] theorem wlen_cons (len : ℕ → ℕ) (p : ℕ) (ps : List ℕ) :
    wlen len (p :: ps) = len p + wlen len ps := by simp [wlen]

@[simp] theorem wlen_append (len : ℕ → ℕ) (ps qs : List ℕ) :
    wlen len (ps ++ qs) = wlen len ps + wlen len qs := by simp [wlen]

theorem wlen_reverse (len : ℕ → ℕ) (ps : List ℕ) : wlen len ps.reverse = wlen len ps := by
  simp [wlen, List.sum_reverse]

theorem wlen_mono {len len' : ℕ → ℕ} (h : ∀ p, len p ≤ len' p) (ps : List ℕ) :
    wlen len ps ≤ wlen len' ps := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [wlen_cons]; exact Nat.add_le_add (h p) ih

namespace IsWalk

variable {V P : Set ℕ}

theorem start_mem {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) : a ∈ V := by
  cases h with
  | nil ha => exact ha
  | cons ha _ _ _ => exact ha

theorem end_mem {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) : b ∈ V := by
  induction h with
  | nil ha => exact ha
  | cons _ _ _ _ ih => exact ih

theorem append {a b c : ℕ} {ps qs : List ℕ} (h₁ : G.IsWalk V P a b ps)
    (h₂ : G.IsWalk V P b c qs) : G.IsWalk V P a c (ps ++ qs) := by
  induction h₁ with
  | nil _ => exact h₂
  | cons ha hp hj _ ih => exact .cons ha hp hj (ih h₂)

/-- A walk followed by one more pair. -/
theorem snoc {a b c p : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) (hp : p ∈ P)
    (hj : G.Joins p b c) (hc : c ∈ V) : G.IsWalk V P a c (ps ++ [p]) :=
  h.append (.cons h.end_mem hp hj (.nil hc))

theorem reverse {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) :
    G.IsWalk V P b a ps.reverse := by
  induction h with
  | nil ha => exact .nil ha
  | cons ha hp hj rest ih =>
    rw [List.reverse_cons]
    exact ih.snoc hp hj.symm ha

theorem mono {V' P' : Set ℕ} (hV : V ⊆ V') (hP : P ⊆ P') {a b : ℕ} {ps : List ℕ}
    (h : G.IsWalk V P a b ps) : G.IsWalk V' P' a b ps := by
  induction h with
  | nil ha => exact .nil (hV ha)
  | cons ha hp hj _ ih => exact .cons (hV ha) (hP hp) hj ih

theorem pair_mem {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) {p : ℕ} (hp : p ∈ ps) :
    p ∈ P := by
  induction h with
  | nil _ => simp at hp
  | cons _ hq _ _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hq
    · exact ih hp

theorem pair_lt {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps) {p : ℕ} (hp : p ∈ ps) :
    p < G.m := by
  induction h with
  | nil _ => simp at hp
  | cons _ _ hj _ ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hj.1
    · exact ih hp

/-- The same walk with a smaller set of allowed pairs, when every pair it uses is allowed. -/
theorem restrict_pairs {P' : Set ℕ} {a b : ℕ} {ps : List ℕ} (h : G.IsWalk V P a b ps)
    (hP : ∀ p ∈ ps, p ∈ P') : G.IsWalk V P' a b ps := by
  induction h with
  | nil ha => exact .nil ha
  | cons ha _ hj _ ih =>
    exact .cons ha (hP _ (List.mem_cons_self ..)) hj
      (ih fun q hq => hP q (List.mem_cons_of_mem _ hq))

end IsWalk

theorem Reach.symm {V : Set ℕ} {a b : ℕ} (h : G.Reach V a b) : G.Reach V b a :=
  let ⟨ps, hps⟩ := h; ⟨ps.reverse, hps.reverse⟩

theorem Reach.trans {V : Set ℕ} {a b c : ℕ} (h₁ : G.Reach V a b) (h₂ : G.Reach V b c) :
    G.Reach V a c :=
  let ⟨ps, hps⟩ := h₁; let ⟨qs, hqs⟩ := h₂; ⟨ps ++ qs, hps.append hqs⟩

theorem dist_le {V : Set ℕ} {len : ℕ → ℕ} {a b : ℕ} {ps : List ℕ}
    (h : G.IsWalk V Set.univ a b ps) : G.dist V len a b ≤ wlen len ps :=
  Nat.sInf_le ⟨ps, h, rfl⟩

/-- A distance is attained by a walk, when there is a walk at all. -/
theorem exists_walk_dist {V : Set ℕ} (len : ℕ → ℕ) {a b : ℕ} (h : G.Reach V a b) :
    ∃ ps, G.IsWalk V Set.univ a b ps ∧ wlen len ps = G.dist V len a b := by
  obtain ⟨ps, hps⟩ := h
  have hne : {l | ∃ ps, G.IsWalk V Set.univ a b ps ∧ wlen len ps = l}.Nonempty :=
    ⟨_, ps, hps, rfl⟩
  exact Nat.sInf_mem hne

theorem dist_self {V : Set ℕ} {len : ℕ → ℕ} {a : ℕ} (ha : a ∈ V) : G.dist V len a a = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using dist_le (G := G) (len := len) (IsWalk.nil (P := Set.univ) ha))

theorem dist_comm (V : Set ℕ) (len : ℕ → ℕ) (a b : ℕ) : G.dist V len a b = G.dist V len b a := by
  have key : ∀ x y, G.dist V len y x ≤ G.dist V len x y := by
    intro x y
    by_cases h : G.Reach V x y
    · obtain ⟨ps, hps, hl⟩ := exists_walk_dist len h
      exact (dist_le hps.reverse).trans_eq (by rw [wlen_reverse, hl])
    · have h' : ¬ G.Reach V y x := fun h' => h h'.symm
      have e1 : {l | ∃ ps, G.IsWalk V Set.univ x y ps ∧ wlen len ps = l} = ∅ := by
        ext l; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨ps, hps, -⟩; exact h ⟨ps, hps⟩
      have e2 : {l | ∃ ps, G.IsWalk V Set.univ y x ps ∧ wlen len ps = l} = ∅ := by
        ext l; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨ps, hps, -⟩; exact h' ⟨ps, hps⟩
      simp only [dist, e1, e2, le_refl]
  exact le_antisymm (key b a) (key a b)

theorem dist_triangle {V : Set ℕ} (len : ℕ → ℕ) {a b c : ℕ} (h₁ : G.Reach V a b)
    (h₂ : G.Reach V b c) : G.dist V len a c ≤ G.dist V len a b + G.dist V len b c := by
  obtain ⟨ps, hps, hl⟩ := exists_walk_dist len h₁
  obtain ⟨qs, hqs, hl'⟩ := exists_walk_dist len h₂
  exact (dist_le (hps.append hqs)).trans_eq (by rw [wlen_append, hl, hl'])

/-- Distances only shrink in a larger vertex set. -/
theorem dist_mono {V V' : Set ℕ} (hV : V ⊆ V') (len : ℕ → ℕ) {a b : ℕ} (h : G.Reach V a b) :
    G.dist V' len a b ≤ G.dist V len a b := by
  obtain ⟨ps, hps, hl⟩ := exists_walk_dist len h
  exact (dist_le (hps.mono hV le_rfl)).trans_eq hl

/-- Distances only grow with the lengths. -/
theorem dist_mono_len {V : Set ℕ} {len len' : ℕ → ℕ} (hl : ∀ p, len p ≤ len' p) {a b : ℕ}
    (h : G.Reach V a b) : G.dist V len a b ≤ G.dist V len' a b := by
  obtain ⟨ps, hps, he⟩ := exists_walk_dist len' h
  exact (dist_le hps).trans ((wlen_mono hl ps).trans_eq he)

/-- One pair gives a bound on the distance. -/
theorem dist_le_pair {V : Set ℕ} (len : ℕ → ℕ) {p a b : ℕ} (hj : G.Joins p a b) (ha : a ∈ V)
    (hb : b ∈ V) : G.dist V len a b ≤ len p := by
  simpa using dist_le (len := len) (IsWalk.cons ha (Set.mem_univ p) hj (.nil hb))

end PG

end MinCostFlow.LowStretch
