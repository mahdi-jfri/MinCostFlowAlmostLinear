module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.ExplicitExpander.Fourier
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The explicit expander on `n` vertices

This file defines the graph `explicitGraph n` and proves that its edges are well formed and that
it has no loops. `Expansion.lean` proves that it expands and `Degree.lean` bounds its degrees.

Let `m = ⌊√n⌋` and `N = m²`, so that `N ≤ n < (m + 1)²` and the other `r = n - N` vertices number
at most `2m ≤ 2N`.

* The first `N` vertices carry the Margulis graph on the torus `ℤ_m × ℤ_m`. Vertex `z < N` is the
  point `(z / m, z % m)` (`toTorus`), and it is joined to its four images under the shears
  `(x, y) ↦ (x + 2y, y)`, `(x + 2y + 1, y)`, `(x, y + 2x)`, `(x, y + 2x + 1)` (`tgt`). An image
  equal to `z` would be a loop; it is dropped (`emitE`). A loop never crosses a cut, so this
  changes no cut.
* Vertex `N + j`, for `j < r`, is joined to vertex `j % N`. When `m ≥ 2`, `r ≤ 2m ≤ N`, so each
  of the first `N` vertices gets at most one such edge.

The edges are listed in the order in which the program of `Program.lean` writes them.
-/

public section

namespace MinCostFlow.ExplicitExpander

open MinCostFlow.Cited Finset

/-- The four neighbours of vertex `z` in the Margulis graph on `ℤ_m × ℤ_m`, with `z` standing for
the point `(z / m, z % m)`. -/
@[expose] def tgt (m z : ℕ) : ℕ → ℕ
  | 0 => ((z / m + 2 * (z % m)) % m) * m + z % m
  | 1 => ((z / m + 2 * (z % m) + 1) % m) * m + z % m
  | 2 => (z / m) * m + (z % m + 2 * (z / m)) % m
  | _ => (z / m) * m + (z % m + 2 * (z / m) + 1) % m

/-- The edge from `z` to `t`, or nothing if `t = z`. -/
@[expose] def emitE (z t : ℕ) : List (ℕ × ℕ) := if t = z then [] else [(z, t)]

/-- The edges from vertex `z` of the Margulis graph to its four neighbours, without loops. -/
@[expose] def vertexEdges (m z : ℕ) : List (ℕ × ℕ) :=
  emitE z (tgt m z 0) ++ emitE z (tgt m z 1) ++ emitE z (tgt m z 2) ++ emitE z (tgt m z 3)

/-- The edges of the Margulis graph on the vertices `0, …, m² - 1`. -/
@[expose] def coreEdges (m : ℕ) : List (ℕ × ℕ) := (List.range (m * m)).flatMap (vertexEdges m)

/-- The edges `(N + j, j % N)` for `j < r`. -/
@[expose] def pendEdges (N r : ℕ) : List (ℕ × ℕ) := (List.range r).map fun j => (N + j, j % N)

/-- The explicit expander on `n` vertices. -/
@[expose] def explicitGraph (n : ℕ) : Graph where
  n := n
  edges := coreEdges (Nat.sqrt n) ++
    pendEdges (Nat.sqrt n * Nat.sqrt n) (n - Nat.sqrt n * Nat.sqrt n)

/-- Vertex `z` as a point of the torus. -/
@[expose] def toTorus (m z : ℕ) : Torus m := (((z / m : ℕ) : ZMod m), ((z % m : ℕ) : ZMod m))

/-- The vertex of a point of the torus. -/
@[expose] def ofTorus (m : ℕ) (u : Torus m) : ℕ := u.1.val * m + u.2.val

/-- The four shears, numbered as in `tgt`. -/
@[expose] def shearOf {m : ℕ} : ℕ → Torus m ≃ Torus m
  | 0 => shearA 0
  | 1 => shearA 1
  | 2 => shearB 0
  | _ => shearB 1

lemma tgt_lt {m z : ℕ} (i : ℕ) (hz : z < m * m) : tgt m z i < m * m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hz)
  have hy : z % m < m := Nat.mod_lt _ hm
  have hx : z / m < m := Nat.div_lt_of_lt_mul hz
  have key : ∀ a b, a < m → b < m → a * m + b < m * m := fun a b ha hb => by
    calc a * m + b < a * m + m := by omega
      _ = (a + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right _ ha
  match i with
  | 0 => exact key _ _ (Nat.mod_lt _ hm) hy
  | 1 => exact key _ _ (Nat.mod_lt _ hm) hy
  | 2 => exact key _ _ hx (Nat.mod_lt _ hm)
  | _ + 3 => exact key _ _ hx (Nat.mod_lt _ hm)

variable {m : ℕ} [NeZero m]

private lemma m_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)

private lemma div_mod_of_lt {a b : ℕ} (hb : b < m) : (a * m + b) / m = a ∧ (a * m + b) % m = b := by
  have hm := m_pos (m := m)
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- The neighbours `tgt m z i` are the images of `z` under the shears. -/
lemma toTorus_tgt (z i : ℕ) : toTorus m (tgt m z i) = shearOf i (toTorus m z) := by
  have hm := m_pos (m := m)
  have hy : z % m < m := Nat.mod_lt _ hm
  match i with
  | 0 =>
    obtain ⟨h1, h2⟩ := div_mod_of_lt (m := m) (a := (z / m + 2 * (z % m)) % m) hy
    simp only [tgt, toTorus, shearOf, shearA_apply, h1, h2, ZMod.natCast_mod]
    push_cast; simp only [ZMod.natCast_mod]; try ring_nf
  | 1 =>
    obtain ⟨h1, h2⟩ := div_mod_of_lt (m := m) (a := (z / m + 2 * (z % m) + 1) % m) hy
    simp only [tgt, toTorus, shearOf, shearA_apply, h1, h2, ZMod.natCast_mod]
    push_cast; simp only [ZMod.natCast_mod]; try ring_nf
  | 2 =>
    obtain ⟨h1, h2⟩ := div_mod_of_lt (m := m) (a := z / m)
      (Nat.mod_lt (z % m + 2 * (z / m)) hm)
    simp only [tgt, toTorus, shearOf, shearB_apply, h1, h2, ZMod.natCast_mod]
    push_cast; simp only [ZMod.natCast_mod]; try ring_nf
  | _ + 3 =>
    obtain ⟨h1, h2⟩ := div_mod_of_lt (m := m) (a := z / m)
      (Nat.mod_lt (z % m + 2 * (z / m) + 1) hm)
    simp only [tgt, toTorus, shearOf, shearB_apply, h1, h2, ZMod.natCast_mod]
    push_cast; simp only [ZMod.natCast_mod]; try ring_nf

lemma ofTorus_toTorus {z : ℕ} (hz : z < m * m) : ofTorus m (toTorus m z) = z := by
  have hm := m_pos (m := m)
  have hx : z / m < m := Nat.div_lt_of_lt_mul hz
  simp only [ofTorus, toTorus, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_mod]
  rw [Nat.mul_comm]
  exact Nat.div_add_mod z m

lemma toTorus_ofTorus (u : Torus m) : toTorus m (ofTorus m u) = u := by
  obtain ⟨h1, h2⟩ := div_mod_of_lt (m := m) (a := u.1.val) (ZMod.val_lt u.2)
  simp only [toTorus, ofTorus, h1, h2, ZMod.natCast_zmod_val]

lemma ofTorus_lt (u : Torus m) : ofTorus m u < m * m := by
  have h1 := ZMod.val_lt u.1
  have h2 := ZMod.val_lt u.2
  unfold ofTorus
  calc u.1.val * m + u.2.val < u.1.val * m + m := by omega
    _ = (u.1.val + 1) * m := by ring
    _ ≤ m * m := Nat.mul_le_mul_right _ h1

/-- A sum over the first `m²` vertices is a sum over the torus. -/
lemma sum_range_eq_sum_torus {M : Type*} [AddCommMonoid M] (g : Torus m → M) :
    ∑ z ∈ range (m * m), g (toTorus m z) = ∑ u : Torus m, g u :=
  Finset.sum_nbij' (toTorus m) (ofTorus m) (fun _ _ => Finset.mem_univ _)
    (fun u _ => Finset.mem_range.mpr (ofTorus_lt u))
    (fun _ hz => ofTorus_toTorus (Finset.mem_range.mp hz))
    (fun u _ => toTorus_ofTorus u) (fun _ _ => rfl)

/-- `m = ⌊√n⌋` satisfies `m² ≤ n < (m + 1)²`, so `n - m² ≤ 2m`. -/
lemma sub_sqrt_le (n : ℕ) : n - Nat.sqrt n * Nat.sqrt n ≤ 2 * Nat.sqrt n := by
  have h := Nat.lt_succ_sqrt n
  rw [Nat.succ_eq_add_one] at h
  have : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) = Nat.sqrt n * Nat.sqrt n + 2 * Nat.sqrt n + 1 := by
    ring
  omega

lemma explicitGraph_isValid (n : ℕ) (hn : 1 ≤ n) : (explicitGraph n).IsValid := by
  intro e he
  have hle := Nat.sqrt_le n
  have hpos : 0 < Nat.sqrt n * Nat.sqrt n := by
    have : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
    positivity
  simp only [explicitGraph, coreEdges, pendEdges, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_map] at he
  show e.1 < n ∧ e.2 < n
  rcases he with ⟨z, hz, he⟩ | ⟨j, hj, rfl⟩
  · simp only [vertexEdges, emitE, List.mem_append] at he
    have key : ∀ i, e ∈ (if tgt (Nat.sqrt n) z i = z then [] else [(z, tgt (Nat.sqrt n) z i)]) →
        e.1 < n ∧ e.2 < n := by
      intro i hi
      split_ifs at hi with h
      · simp at hi
      · simp only [List.mem_singleton] at hi
        subst hi
        exact ⟨by omega, by have := tgt_lt i hz; omega⟩
    rcases he with ((h | h) | h) | h
    · exact key 0 h
    · exact key 1 h
    · exact key 2 h
    · exact key 3 h
  · exact ⟨by omega, by have := Nat.mod_lt j hpos; omega⟩

lemma explicitGraph_isLoopless (n : ℕ) (hn : 1 ≤ n) : (explicitGraph n).IsLoopless := by
  intro e he
  have hpos : 0 < Nat.sqrt n * Nat.sqrt n := by
    have : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr hn
    positivity
  simp only [explicitGraph, coreEdges, pendEdges, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_map] at he
  rcases he with ⟨z, _, he⟩ | ⟨j, _, rfl⟩
  · simp only [vertexEdges, emitE, List.mem_append] at he
    have key : ∀ t, e ∈ (if t = z then [] else [(z, t)]) → e.1 ≠ e.2 := by
      intro t ht
      split_ifs at ht with h
      · simp at ht
      · simp only [List.mem_singleton] at ht
        subst ht
        exact fun h' => h h'.symm
    rcases he with ((h | h) | h) | h <;> exact key _ h
  · have := Nat.mod_lt j hpos
    show Nat.sqrt n * Nat.sqrt n + j ≠ j % (Nat.sqrt n * Nat.sqrt n)
    omega

/-- The list of edges with both ends among the vertices is the whole edge list. -/
lemma inside_verts_of_isValid {G : Graph} (hG : G.IsValid) : G.inside G.verts = G.edges := by
  unfold Graph.inside
  rw [List.filter_eq_self]
  intro e he
  obtain ⟨h1, h2⟩ := hG e he
  simp [Graph.verts, h1, h2]

/-- Counting along `List.range` is summing over `Finset.range`. -/
lemma countP_range (q : ℕ → Bool) (r : ℕ) :
    (List.range r).countP q = ∑ j ∈ range r, if q j then 1 else 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp [List.countP_cons]

/-- Counting along a `flatMap` over `List.range` is summing over `Finset.range`. -/
lemma countP_flatMap_range {α : Type*} (q : α → Bool) (f : ℕ → List α) (r : ℕ) :
    ((List.range r).flatMap f).countP q = ∑ j ∈ range r, (f j).countP q := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.flatMap_append, List.countP_append, ih, Finset.sum_range_succ]
    simp

end MinCostFlow.ExplicitExpander
