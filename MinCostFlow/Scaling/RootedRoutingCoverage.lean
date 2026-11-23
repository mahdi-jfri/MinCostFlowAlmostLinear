module

public import MinCostFlow.Scaling.LabelReachability
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A rooted unit-demand routing reaches every vertex

In Lemma C.8 of Chen et al., arXiv:2203.00671v2, Appendix C, the source
sends one unit to each other vertex. A proper vertex set containing the
source has strictly positive total balance. It therefore cannot be closed
under positive outgoing flow. Applying this cut argument to the traversal's
visited set proves that the finished traversal visits every vertex.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- A set closed under positive outgoing flow and containing the source
contains every vertex of a rooted unit-demand routing. -/
theorem all_mem_of_rooted_routing (I : Circulation) (root : Fin I.n)
    (f : Fin I.m → ℝ) (hnon : ∀ e, 0 ≤ f e)
    (hb : ∀ v, I.balance f v = (I.n : ℝ) * (if v = root then 1 else 0) - 1)
    (S : Finset (Fin I.n)) (hroot : root ∈ S)
    (hclosed : ∀ e, I.tail e ∈ S → 0 < f e → I.head e ∈ S) :
    ∀ v : Fin I.n, v ∈ S := by
  classical
  let y : Fin I.n → ℝ := fun v => if v ∈ S then 1 else 0
  have he (e : Fin I.m) : I.potentialDifference y e * f e ≤ 0 := by
    by_cases ht : I.tail e ∈ S <;> by_cases hh : I.head e ∈ S
    · simp only [potentialDifference, y, ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
    · have hz : f e = 0 := by
        by_contra hn
        exact hh (hclosed e ht (lt_of_le_of_ne (hnon e) (Ne.symm hn)))
      rw [hz, mul_zero]
    · simp only [potentialDifference, y, ht, hh, ↓reduceIte, zero_sub, neg_mul, one_mul]
      exact neg_nonpos.mpr (hnon e)
    · simp only [potentialDifference, y, ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
  have hs := Finset.sum_nonpos (s := Finset.univ) (fun e _ => he e)
  rw [I.potential_pairing] at hs
  have hv (v : Fin I.n) : y v * I.balance f v =
      (if v = root then (I.n : ℝ) else 0) - (if v ∈ S then 1 else 0) := by
    rw [hb]
    by_cases hvr : v = root
    · subst v
      simp only [y, hroot, ↓reduceIte, mul_one, one_mul]
    · simp only [y, hvr, ↓reduceIte, mul_zero, zero_sub]
      split <;> ring
  simp only [hv, Finset.sum_sub_distrib] at hs
  simp at hs
  intro v
  by_contra hv
  have hsub : S ⊆ Finset.univ.erase v := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨by intro heq; subst w; exact hv hw, Finset.mem_univ _⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at hc
  have hn : 0 < I.n := Nat.zero_lt_of_lt v.isLt
  have hlt : S.card < I.n := by omega
  omega

/-- The finished label traversal visits all vertices of a nonnegative
rooted unit-demand routing. -/
theorem propagateLabels_all_seen (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) (hnon : ∀ e, 0 ≤ (flow e : ℝ))
    (hb : ∀ v, I.balance (fun e => (flow e : ℝ)) v =
      (I.n : ℝ) * (if v = root then 1 else 0) - 1) :
    ∀ v, (I.propagateLabels flow root).1.seen v = true := by
  classical
  let S := Finset.univ.filter (fun v => (I.propagateLabels flow root).1.seen v = true)
  have hm (v : Fin I.n) : v ∈ S ↔ (I.propagateLabels flow root).1.seen v = true := by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hr : root ∈ S := (hm root).mpr (I.propagateLabels_root_seen flow root)
  have hh : ∀ e, I.tail e ∈ S → 0 < (flow e : ℝ) → I.head e ∈ S := by
    intro e he hp
    exact (hm _).mpr (I.propagateLabels_closed flow root e (Int.cast_pos.mp hp) ((hm _).mp he))
  intro v
  exact (hm v).mp (I.all_mem_of_rooted_routing root (fun e => (flow e : ℝ)) hnon hb S hr hh v)

end MinCostFlow.Scaling.Circulation
