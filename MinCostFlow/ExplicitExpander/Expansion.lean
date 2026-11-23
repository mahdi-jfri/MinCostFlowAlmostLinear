module

public import MinCostFlow.ExplicitExpander.Graph
import MinCostFlow.ExplicitExpander.Margulis
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The explicit expander has expansion at least `1/12`

Let `S` be a set of vertices of `explicitGraph n`, with `m = ⌊√n⌋`, `N = m²` and `r = n - N`.
Write `a` for the number of vertices of `S` below `N`, `c` for the number of edges of the
Margulis part that cross `S`, and `d` for the number of the other edges `(N + j, j % N)` that
cross `S`.

* The Margulis part (`core_cross_ge`): `min(a, N - a) ≤ 4c`. This is `card_crossing_ge` of
  `Margulis.lean`, moved to the vertices by `toTorus`. A loop that the graph drops never crosses
  `S`, so dropping it changes nothing.
* The other vertices (`card_le_three_mul`): vertex `N + j` is in `S` only if `j % N` is in `S`
  or its edge crosses `S`, and each vertex below `N` is `j % N` for at most two `j < r`, since
  `r ≤ 2N`. So `|S| ≤ 3a + d`, and in the same way `|V \ S| ≤ 3(N - a) + d`.

Together, `min(|S|, |V \ S|) ≤ 3 min(a, N - a) + d ≤ 12c + d ≤ 12 (c + d)`, and `c + d` is the
cut of `S` (`explicitGraph_expansion`).
-/

public section

namespace MinCostFlow.ExplicitExpander

open MinCostFlow.Cited Finset

/-- `1` if exactly one of `z` and `t` is in `S`. -/
private def cr (S : Finset ℕ) (z t : ℕ) : ℕ := if (z ∈ S ↔ t ∈ S) then 0 else 1

private abbrev xorS (S : Finset ℕ) (e : ℕ × ℕ) : Bool := decide (e.1 ∈ S) != decide (e.2 ∈ S)

private lemma countP_emitE (S : Finset ℕ) (z t : ℕ) :
    (emitE z t).countP (xorS S) = cr S z t := by
  unfold emitE cr
  by_cases h : t = z
  · subst h; simp
  · by_cases hz : z ∈ S <;> by_cases ht : t ∈ S <;> simp [h, hz, ht]

private lemma countP_core (S : Finset ℕ) (m : ℕ) :
    (coreEdges m).countP (xorS S) =
      ∑ z ∈ range (m * m), (cr S z (tgt m z 0) + cr S z (tgt m z 1) + cr S z (tgt m z 2) +
        cr S z (tgt m z 3)) := by
  unfold coreEdges
  rw [countP_flatMap_range]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [vertexEdges, List.countP_append, countP_emitE]

private lemma countP_pend (S : Finset ℕ) (N r : ℕ) :
    (pendEdges N r).countP (xorS S) =
      ∑ j ∈ range r, if (N + j ∈ S ↔ j % N ∈ S) then 0 else 1 := by
  unfold pendEdges
  rw [List.countP_map, countP_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : N + j ∈ S <;> by_cases h2 : j % N ∈ S <;> simp [h1, h2]

/-- The Margulis part of the graph expands. -/
private lemma core_cross_ge (m : ℕ) [NeZero m] (S : Finset ℕ) :
    min ((∑ z ∈ range (m * m), if z ∈ S then 1 else 0 : ℕ) : ℝ)
        ((m * m : ℕ) - (∑ z ∈ range (m * m), if z ∈ S then 1 else 0 : ℕ) : ℝ) ≤
      4 * ((coreEdges m).countP (xorS S) : ℝ) := by
  set A : Finset (Torus m) := Finset.univ.filter fun u => ofTorus m u ∈ S with hA
  have hmemA : ∀ z, z < m * m → (z ∈ S ↔ toTorus m z ∈ A) := by
    intro z hz
    simp [hA, ofTorus_toTorus hz]
  have hcardA : A.card = ∑ z ∈ range (m * m), if z ∈ S then 1 else 0 := by
    rw [Finset.card_filter]
    rw [← sum_range_eq_sum_torus (m := m) (fun u => if ofTorus m u ∈ S then 1 else 0)]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [ofTorus_toTorus (Finset.mem_range.mp hz)]
  have hcr : ∀ z, z < m * m → ∀ i, (cr S z (tgt m z i) : ℝ) =
      crossInd A (toTorus m z) (shearOf i (toTorus m z)) := by
    intro z hz i
    have h1 := hmemA z hz
    have h2 := hmemA (tgt m z i) (tgt_lt i hz)
    rw [toTorus_tgt] at h2
    have e : (z ∈ S ↔ tgt m z i ∈ S) ↔ (toTorus m z ∈ A ↔ shearOf i (toTorus m z) ∈ A) := by
      rw [h1, h2]
    unfold cr crossInd
    by_cases hc : (z ∈ S ↔ tgt m z i ∈ S)
    · simp [hc, e.mp hc]
    · simp [hc, mt e.mpr hc]
  have hsum : ((coreEdges m).countP (xorS S) : ℝ) =
      ∑ u : Torus m, (crossInd A u (shearA 0 u) + crossInd A u (shearA 1 u) +
        crossInd A u (shearB 0 u) + crossInd A u (shearB 1 u)) := by
    rw [countP_core, ← sum_range_eq_sum_torus]
    push_cast
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_range.mp hz
    rw [hcr z hz' 0, hcr z hz' 1, hcr z hz' 2, hcr z hz' 3]
    rfl
  have h := card_crossing_ge A
  rw [hcardA, ← hsum] at h
  have hmm : ((m * m : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  rw [hmm]
  exact h

/-- Counting a property along `N + r` vertices, when every vertex `N + j` is compared with
`j % N` and `r ≤ 2N`. -/
private lemma card_le_three_mul (P : ℕ → Prop) [DecidablePred P] (N r : ℕ) (hr : r ≤ 2 * N) :
    (∑ v ∈ range (N + r), if P v then 1 else 0) ≤
      3 * (∑ v ∈ range N, if P v then 1 else 0) +
        ∑ j ∈ range r, if (P (N + j) ↔ P (j % N)) then 0 else 1 := by
  rw [Finset.sum_range_add]
  have h1 : (∑ j ∈ range r, if P (N + j) then 1 else 0) ≤
      (∑ j ∈ range r, if P (j % N) then 1 else 0) +
        ∑ j ∈ range r, if (P (N + j) ↔ P (j % N)) then 0 else 1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases ha : P (N + j) <;> by_cases hb : P (j % N) <;> simp [ha, hb]
  have h2 : (∑ j ∈ range r, if P (j % N) then 1 else 0) ≤
      ∑ j ∈ range (N + N), if P (j % N) then 1 else 0 :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  have h3 : (∑ j ∈ range (N + N), if P (j % N) then 1 else 0) =
      2 * ∑ v ∈ range N, if P v then 1 else 0 := by
    rw [Finset.sum_range_add, two_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
  omega

private lemma card_eq_sum {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    S.card = ∑ v ∈ range n, if v ∈ S then 1 else 0 := by
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]

private lemma card_sdiff_eq_sum (n : ℕ) (S : Finset ℕ) :
    (range n \ S).card = ∑ v ∈ range n, if v ∉ S then 1 else 0 := by
  rw [← Finset.card_filter]
  congr 1
  ext v
  simp

/-- **The explicit expander has expansion at least `1/12`.** -/
theorem explicitGraph_expansion (n : ℕ) (hn : 1 ≤ n) :
    (explicitGraph n).IsExpansionExpanderOn (explicitGraph n).verts (1 / 12) := by
  intro S hS _ _
  set m := Nat.sqrt n with hm
  set N := m * m with hN
  set r := n - N with hr
  have hmpos : 0 < m := Nat.sqrt_pos.mpr hn
  have : NeZero m := ⟨hmpos.ne'⟩
  have hNle : N ≤ n := Nat.sqrt_le n
  have hnN : n = N + r := by omega
  have hr2 : r ≤ 2 * N := by
    have h1 : r ≤ 2 * m := sub_sqrt_le n
    have h2 : m ≤ N := Nat.le_mul_self m
    omega
  have hverts : (explicitGraph n).verts = range n := rfl
  rw [hverts] at hS ⊢
  -- the cut is the core crossing plus the other crossing
  have hcut : (explicitGraph n).cutIn (range n) S =
      (coreEdges m).countP (xorS S) + (pendEdges N r).countP (xorS S) := by
    unfold Graph.cutIn
    rw [← hverts, inside_verts_of_isValid (explicitGraph_isValid n hn), ← List.countP_eq_length_filter]
    show (coreEdges m ++ pendEdges N r).countP (xorS S) = _
    rw [List.countP_append]
  set c := (coreEdges m).countP (xorS S) with hc
  set d := (pendEdges N r).countP (xorS S) with hd
  set a := ∑ v ∈ range N, if v ∈ S then 1 else 0 with ha
  set b := ∑ v ∈ range N, if v ∉ S then 1 else 0 with hb
  have hab : a + b = N := by
    rw [ha, hb, ← Finset.sum_add_distrib]
    have : ∀ v ∈ range N, ((if v ∈ S then 1 else 0) + if v ∉ S then 1 else 0) = 1 := by
      intro v _; by_cases h : v ∈ S <;> simp [h]
    rw [Finset.sum_congr rfl this]
    simp
  have hcore := core_cross_ge m S
  rw [← hN, ← ha] at hcore
  have hdS : d = ∑ j ∈ range r, if (N + j ∈ S ↔ j % N ∈ S) then 0 else 1 := countP_pend S N r
  have hS1 : S.card ≤ 3 * a + d := by
    rw [card_eq_sum hS, hnN, hdS]
    exact card_le_three_mul (· ∈ S) N r hr2
  have hS2 : (range n \ S).card ≤ 3 * b + d := by
    rw [card_sdiff_eq_sum, hnN, hdS]
    have h := card_le_three_mul (· ∉ S) N r hr2
    have hx : (∑ j ∈ range r, if (N + j ∉ S ↔ j % N ∉ S) then 0 else 1) =
        ∑ j ∈ range r, if (N + j ∈ S ↔ j % N ∈ S) then 0 else 1 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h1 : N + j ∈ S <;> by_cases h2 : j % N ∈ S <;> simp [h1, h2]
    rw [hx] at h
    exact h
  rw [hcut]
  have hbR : ((N : ℕ) : ℝ) - (a : ℝ) = (b : ℝ) := by
    rw [← hab]; push_cast; ring
  rw [hbR] at hcore
  have hS1' : (S.card : ℝ) ≤ 3 * a + d := by exact_mod_cast hS1
  have hS2' : ((range n \ S).card : ℝ) ≤ 3 * b + d := by exact_mod_cast hS2
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  push_cast
  rcases le_total (a : ℝ) b with h | h
  · rw [min_eq_left h] at hcore
    have := min_le_left (S.card : ℝ) ((range n \ S).card)
    nlinarith
  · rw [min_eq_right h] at hcore
    have := min_le_right (S.card : ℝ) ((range n \ S).card)
    nlinarith

end MinCostFlow.ExplicitExpander
