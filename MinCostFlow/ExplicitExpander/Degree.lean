module

public import MinCostFlow.ExplicitExpander.Graph
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The explicit expander has degrees at most `9`

Let `m = ⌊√n⌋`, `N = m²` and `r = n - N`. The degree of `v` in `explicitGraph n` counts four kinds
of edge ends.

* Margulis edges leaving `v`: at most `4`, since only vertex `v` has edges leaving it in its own
  block of `vertexEdges`.
* Margulis edges entering `v`: at most `4`, since for each of the four shears at most one `z < N`
  is sent to `v` (the shears are bijections of the torus, `toTorus_tgt`).
* Edges `(N + j, j % N)` leaving `v`: at most one, and none if `v < N`.
* Edges `(N + j, j % N)` entering `v`: none if `v ≥ N`, and at most one if `m ≥ 2`, since then
  `r ≤ 2m ≤ N`, so that `j % N = j`.

This gives `4 + 4 + 1 = 9` in both cases. When `m = 1`, the Margulis edges are all loops and are
dropped, and the degree is at most `1 + 2`.
-/

public section

namespace MinCostFlow.ExplicitExpander

open MinCostFlow.Cited Finset

/-- A sum of indicators of `f j = v` over `j < k` is at most `1` when `f` is injective there. -/
private lemma sum_ite_le_one (f : ℕ → ℕ) (k v : ℕ)
    (hf : ∀ a b, a < k → b < k → f a = f b → a = b) :
    (∑ j ∈ range k, if f j = v then 1 else 0) ≤ 1 := by
  rw [← Finset.card_filter]
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  exact hf a b ha.1 hb.1 (ha.2.trans hb.2.symm)

private lemma countP_fst_emitE (z t v : ℕ) :
    (emitE z t).countP (fun e => decide (e.1 = v)) ≤ if z = v then 1 else 0 := by
  unfold emitE
  split_ifs <;> simp_all

private lemma countP_snd_emitE (z t v : ℕ) :
    (emitE z t).countP (fun e => decide (e.2 = v)) ≤ if t = v then 1 else 0 := by
  unfold emitE
  split_ifs <;> simp_all

private lemma core_fst_le (m v : ℕ) :
    (coreEdges m).countP (fun e => decide (e.1 = v)) ≤ 4 := by
  unfold coreEdges
  rw [countP_flatMap_range]
  have h : ∀ z ∈ range (m * m), (vertexEdges m z).countP (fun e => decide (e.1 = v)) ≤
      4 * if z = v then 1 else 0 := by
    intro z _
    simp only [vertexEdges, List.countP_append]
    have := countP_fst_emitE z (tgt m z 0) v
    have := countP_fst_emitE z (tgt m z 1) v
    have := countP_fst_emitE z (tgt m z 2) v
    have := countP_fst_emitE z (tgt m z 3) v
    omega
  calc _ ≤ ∑ z ∈ range (m * m), 4 * if z = v then 1 else 0 := Finset.sum_le_sum h
    _ = 4 * ∑ z ∈ range (m * m), if z = v then 1 else 0 := by rw [Finset.mul_sum]
    _ ≤ 4 * 1 := Nat.mul_le_mul_left _ (sum_ite_le_one id _ v fun _ _ _ _ h => h)

private lemma tgt_inj (m : ℕ) [NeZero m] (i a b : ℕ) (ha : a < m * m) (hb : b < m * m)
    (h : tgt m a i = tgt m b i) : a = b := by
  have h1 := congrArg (toTorus m) h
  rw [toTorus_tgt, toTorus_tgt] at h1
  have h2 := congrArg (ofTorus m) ((shearOf i).injective h1)
  rwa [ofTorus_toTorus ha, ofTorus_toTorus hb] at h2

private lemma core_snd_le (m v : ℕ) [NeZero m] :
    (coreEdges m).countP (fun e => decide (e.2 = v)) ≤ 4 := by
  unfold coreEdges
  rw [countP_flatMap_range]
  have h : ∀ z ∈ range (m * m), (vertexEdges m z).countP (fun e => decide (e.2 = v)) ≤
      (if tgt m z 0 = v then 1 else 0) + (if tgt m z 1 = v then 1 else 0) +
        (if tgt m z 2 = v then 1 else 0) + (if tgt m z 3 = v then 1 else 0) := by
    intro z _
    simp only [vertexEdges, List.countP_append]
    have := countP_snd_emitE z (tgt m z 0) v
    have := countP_snd_emitE z (tgt m z 1) v
    have := countP_snd_emitE z (tgt m z 2) v
    have := countP_snd_emitE z (tgt m z 3) v
    omega
  have hi : ∀ i, (∑ z ∈ range (m * m), if tgt m z i = v then 1 else 0) ≤ 1 :=
    fun i => sum_ite_le_one (fun z => tgt m z i) _ v (tgt_inj m i)
  calc _ ≤ ∑ z ∈ range (m * m), ((if tgt m z 0 = v then 1 else 0) +
        (if tgt m z 1 = v then 1 else 0) + (if tgt m z 2 = v then 1 else 0) +
        (if tgt m z 3 = v then 1 else 0)) := Finset.sum_le_sum h
    _ ≤ 4 := by
        simp only [Finset.sum_add_distrib]
        have := hi 0; have := hi 1; have := hi 2; have := hi 3
        omega

private lemma core_fst_eq_zero (m v : ℕ) (hv : m * m ≤ v) :
    (coreEdges m).countP (fun e => decide (e.1 = v)) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  simp only [coreEdges, List.mem_flatMap, List.mem_range] at he
  obtain ⟨z, hz, he⟩ := he
  simp only [vertexEdges, emitE, List.mem_append] at he
  have key : ∀ t, e ∈ (if t = z then [] else [(z, t)]) → e.1 = z := by
    intro t ht
    split_ifs at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht; rw [ht]
  have : e.1 = z := by rcases he with ((h | h) | h) | h <;> exact key _ h
  simp only [decide_eq_true_eq]
  omega

private lemma core_snd_eq_zero (m v : ℕ) (hv : m * m ≤ v) :
    (coreEdges m).countP (fun e => decide (e.2 = v)) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  simp only [coreEdges, List.mem_flatMap, List.mem_range] at he
  obtain ⟨z, hz, he⟩ := he
  simp only [vertexEdges, emitE, List.mem_append] at he
  have key : ∀ i, e ∈ (if tgt m z i = z then [] else [(z, tgt m z i)]) → e.2 < m * m := by
    intro i ht
    split_ifs at ht
    · simp at ht
    · simp only [List.mem_singleton] at ht; rw [ht]; exact tgt_lt i hz
  have : e.2 < m * m := by
    rcases he with ((h | h) | h) | h
    · exact key 0 h
    · exact key 1 h
    · exact key 2 h
    · exact key 3 h
  simp only [decide_eq_true_eq]
  omega

private lemma pend_fst_le (N r v : ℕ) :
    (pendEdges N r).countP (fun e => decide (e.1 = v)) ≤ if v < N then 0 else 1 := by
  unfold pendEdges
  rw [List.countP_map, countP_range]
  split_ifs with hv
  · rw [Finset.sum_eq_zero]
    intro j _
    have : ¬ (N + j = v) := by omega
    simp [this]
  · simp only [Function.comp_apply, decide_eq_true_eq]
    exact sum_ite_le_one (fun j => N + j) r v fun a b _ _ h => by simpa using h

private lemma pend_snd_le (N r v : ℕ) (hr : r ≤ N) :
    (pendEdges N r).countP (fun e => decide (e.2 = v)) ≤ 1 := by
  unfold pendEdges
  rw [List.countP_map, countP_range]
  simp only [Function.comp_apply, decide_eq_true_eq]
  refine sum_ite_le_one (fun j => j % N) r v fun a b ha hb h => ?_
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

private lemma pend_snd_eq_zero (N r v : ℕ) (hv : N ≤ v) (hN : 0 < N) :
    (pendEdges N r).countP (fun e => decide (e.2 = v)) = 0 := by
  unfold pendEdges
  rw [List.countP_map, countP_range, Finset.sum_eq_zero]
  intro j _
  have := Nat.mod_lt j hN
  have : ¬ (j % N = v) := by omega
  simp [this]

private lemma pend_count_le (N r : ℕ) (p : ℕ × ℕ → Bool) :
    (pendEdges N r).countP p ≤ r := by
  unfold pendEdges
  exact (List.countP_le_length).trans (by simp)

private lemma coreEdges_one : coreEdges 1 = [] := by decide

/-- **The explicit expander has degrees at most `9`.** -/
theorem explicitGraph_deg_le (n : ℕ) (hn : 1 ≤ n) (v : ℕ) : (explicitGraph n).deg v ≤ 9 := by
  set m := Nat.sqrt n with hm
  have hmpos : 0 < m := Nat.sqrt_pos.mpr hn
  have : NeZero m := ⟨hmpos.ne'⟩
  have hr : n - m * m ≤ 2 * m := sub_sqrt_le n
  have hdeg : (explicitGraph n).deg v =
      (coreEdges m).countP (fun e => decide (e.1 = v)) +
        (pendEdges (m * m) (n - m * m)).countP (fun e => decide (e.1 = v)) +
      ((coreEdges m).countP (fun e => decide (e.2 = v)) +
        (pendEdges (m * m) (n - m * m)).countP (fun e => decide (e.2 = v))) := by
    unfold Graph.deg Graph.degIn
    rw [inside_verts_of_isValid (explicitGraph_isValid n hn), ← List.countP_eq_length_filter,
      ← List.countP_eq_length_filter]
    show (coreEdges m ++ pendEdges (m * m) (n - m * m)).countP _ +
      (coreEdges m ++ pendEdges (m * m) (n - m * m)).countP _ = _
    rw [List.countP_append, List.countP_append]
  rw [hdeg]
  have c1 := core_fst_le m v
  have c2 := core_snd_le m v
  have p1 := pend_fst_le (m * m) (n - m * m) v
  rcases (show m = 1 ∨ 2 ≤ m by omega) with h1 | h2
  · have hc : coreEdges m = [] := by rw [h1]; exact coreEdges_one
    have p2 := pend_count_le (m * m) (n - m * m) (fun e => decide (e.2 = v))
    rw [hc]
    simp only [List.countP_nil]
    split_ifs at p1 <;> omega
  · have hrN : n - m * m ≤ m * m := by
      have : 2 * m ≤ m * m := Nat.mul_le_mul_right m h2
      omega
    by_cases hv : v < m * m
    · have p2 := pend_snd_le (m * m) (n - m * m) v hrN
      simp only [hv, ↓reduceIte] at p1
      omega
    · simp only [hv, ↓reduceIte] at p1
      rw [pend_snd_eq_zero (m * m) (n - m * m) v (by omega) (by positivity)]
      omega

end MinCostFlow.ExplicitExpander
