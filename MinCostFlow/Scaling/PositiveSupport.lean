module

public import MinCostFlow.Scaling.DirectedWalk
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Directed paths in the positive support of a circulation

The cycle argument in the proof of Lemma C.3 of Chen et al.,
arXiv:2203.00671v2, Appendix C, discards arcs whose rounded costs are too
large. Each positive-flow arc lies on a cycle in the positive support.
We prove the needed reachability by a cut argument: a set with no positive
outgoing flow cannot have positive incoming flow, since its total balance
is zero.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The directed support of a real flow, represented by unit-capacity slots. -/
noncomputable abbrev positiveSupport (I : Circulation) (f : Fin I.m → ℝ) : Circulation :=
  { I with capacity := fun e => if 0 < f e then 1 else 0 }

/-- A vertex set closed under positive outgoing flow is also closed under
positive incoming flow when the flow is a circulation. -/
theorem mem_tail_of_closed_support (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) (S : Finset (Fin I.n))
    (hclosed : ∀ e, I.tail e ∈ S → 0 < f e → I.head e ∈ S)
    (e : Fin I.m) (he : 0 < f e) (hhead : I.head e ∈ S) : I.tail e ∈ S := by
  classical
  let y : Fin I.n → ℝ := fun v => if v ∈ S then 1 else 0
  have hs : (∑ a, I.potentialDifference y a * f a) = 0 := by
    rw [I.potential_pairing]
    apply Finset.sum_eq_zero
    intro v _
    rw [hf.1 v, mul_zero]
  have hnon (a : Fin I.m) : I.potentialDifference y a * f a ≤ 0 := by
    have hpos := (hf.2 a).1
    by_cases ht : I.tail a ∈ S <;> by_cases hh : I.head a ∈ S
    · simp only [potentialDifference, y, ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
    · have hzero : f a = 0 := by
        by_contra hn
        exact hh (hclosed a ht (lt_of_le_of_ne hpos (Ne.symm hn)))
      rw [hzero, mul_zero]
    · simp only [potentialDifference, y, ht, hh, ↓reduceIte, zero_sub, neg_mul, one_mul]
      exact neg_nonpos.mpr hpos
    · simp only [potentialDifference, y, ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun a (_ : a ∈ Finset.univ) => hnon a)).mp hs
  by_contra ht
  have heq := hz e (Finset.mem_univ e)
  simp only [potentialDifference, y, ht, hhead, ↓reduceIte, zero_sub, neg_mul, one_mul] at heq
  linarith only [he, heq]

/-- Each positive-flow edge has a return walk entirely within positive support. -/
theorem exists_support_return_walk (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) (e : Fin I.m) (he : 0 < f e) :
    Nonempty ((I.positiveSupport f).DirectedWalk (I.head e) (I.tail e)) := by
  classical
  let S : Finset (Fin I.n) := Finset.univ.filter
    (fun v => Nonempty ((I.positiveSupport f).DirectedWalk (I.head e) v))
  have hmem (v : Fin I.n) : v ∈ S ↔
      Nonempty ((I.positiveSupport f).DirectedWalk (I.head e) v) := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hclosed : ∀ a, I.tail a ∈ S → 0 < f a → I.head a ∈ S := by
    intro a ha hpos
    obtain ⟨p⟩ := (hmem _).mp ha
    apply (hmem _).mpr
    have hactive : 0 < (I.positiveSupport f).capacity a := by
      change 0 < if 0 < f a then 1 else 0
      rw [ite_eq_left hpos]
      decide
    exact ⟨p.append (DirectedWalk.cons (I := I.positiveSupport f) a hactive
      (DirectedWalk.nil (I := I.positiveSupport f) (I.head a)))⟩
  have hh : I.head e ∈ S := (hmem _).mpr ⟨DirectedWalk.nil (I := I.positiveSupport f) (I.head e)⟩
  exact (hmem _).mp (I.mem_tail_of_closed_support f hf S hclosed e he hh)

end MinCostFlow.Scaling.Circulation
