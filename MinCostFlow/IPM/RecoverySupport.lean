module

public import MinCostFlow.IPM.Definitions
public import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Residual support for the recovery argument

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, excludes positive
auxiliary flow by comparing with a feasible original flow. Their
difference is a real circulation. To handle fractional auxiliary flow,
we use its directed support. Every supported arc of a circulation has
a return route: otherwise the reachable cut has strictly negative net
flow, contrary to conservation. This is the first step in the real-flow
repair of the source's one-unit argument.
-/

noncomputable section
@[expose] public section
namespace MinCostFlow.IPM

/-- The tail as a vertex of a valid instance. -/
def tailVertex (I : Instance) (hI : I.IsValid) (e : Fin I.m) : Fin I.n :=
  ⟨(I.edge e).tail, (hI.1 (I.edge e) (List.getElem_mem e.2)).1⟩

/-- The head as a vertex of a valid instance. -/
def headVertex (I : Instance) (hI : I.IsValid) (e : Fin I.m) : Fin I.n :=
  ⟨(I.edge e).head, (hI.1 (I.edge e) (List.getElem_mem e.2)).2⟩

/-- Directed support of a real circulation. Negative coordinates use the
reverse of the instance's edge orientation. -/
def residualSupport (I : Instance) (hI : I.IsValid) (d : Fin I.m → ℝ)
    (u v : Fin I.n) : Prop :=
  ∃ e, (0 < d e ∧ tailVertex I hI e = u ∧ headVertex I hI e = v) ∨
    (d e < 0 ∧ headVertex I hI e = u ∧ tailVertex I hI e = v)

/-- Sum of an edge's incidence over a finite vertex cut. -/
theorem sum_incidence_cut (I : Instance) (hI : I.IsValid) (S : Finset (Fin I.n)) (e : Fin I.m) :
    (∑ v ∈ S, (I.edge e).b v) =
      (if tailVertex I hI e ∈ S then (1 : ℝ) else 0) -
      (if headVertex I hI e ∈ S then (1 : ℝ) else 0) := by
  classical
  have ht : ∀ v : Fin I.n, ((v : ℕ) = (I.edge e).tail) ↔ v = tailVertex I hI e :=
    fun v => by
      change ((v : ℕ) = (tailVertex I hI e).val) ↔ v = tailVertex I hI e
      exact Fin.ext_iff.symm
  have hh : ∀ v : Fin I.n, ((v : ℕ) = (I.edge e).head) ↔ v = headVertex I hI e :=
    fun v => by
      change ((v : ℕ) = (headVertex I hI e).val) ↔ v = headVertex I hI e
      exact Fin.ext_iff.symm
  simp only [Edge.b, Finset.sum_sub_distrib, ht, hh, Finset.sum_ite_eq']

/-- Conservation implies that the signed flow across every cut is zero. -/
theorem circulation_cut_zero (I : Instance) (hI : I.IsValid) (d : Fin I.m → ℝ)
    (hd : IsCirculation I d) (S : Finset (Fin I.n)) :
    (∑ e, ((if tailVertex I hI e ∈ S then (1 : ℝ) else 0) -
      (if headVertex I hI e ∈ S then (1 : ℝ) else 0))*d e) = 0 := by
  classical
  have hsum : (∑ v ∈ S, ∑ e, (I.edge e).b v*d e) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    exact hd v
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.sum_mul, sum_incidence_cut I hI S] at hsum
  exact hsum

/-- A cut closed under the directed support has no positive outgoing term. -/
theorem closed_cut_term_nonpos (I : Instance) (hI : I.IsValid) (d : Fin I.m → ℝ)
    (S : Finset (Fin I.n))
    (hclosed : ∀ u v, u ∈ S → residualSupport I hI d u v → v ∈ S) (e : Fin I.m) :
    ((if tailVertex I hI e ∈ S then (1 : ℝ) else 0) -
      (if headVertex I hI e ∈ S then (1 : ℝ) else 0))*d e ≤ 0 := by
  classical
  by_cases ht : tailVertex I hI e ∈ S <;> by_cases hh : headVertex I hI e ∈ S
  · simp only [ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]
  · have hn : d e ≤ 0 := by
      by_contra hp
      exact hh (hclosed _ _ ht ⟨e, Or.inl ⟨lt_of_not_ge hp, rfl, rfl⟩⟩)
    simpa only [ht, hh, ↓reduceIte, sub_zero, one_mul] using hn
  · have hn : 0 ≤ d e := by
      by_contra hp
      exact ht (hclosed _ _ hh ⟨e, Or.inr ⟨lt_of_not_ge hp, rfl, rfl⟩⟩)
    simpa only [ht, hh, ↓reduceIte, zero_sub, neg_one_mul] using neg_nonpos.mpr hn
  · simp only [ht, hh, ↓reduceIte, sub_self, zero_mul, le_refl]

/-- Every directed support arc of a real circulation admits a return
route. This uses no rationality or lower bound on the nonzero flow. -/
theorem residualSupport_return (I : Instance) (hI : I.IsValid) (d : Fin I.m → ℝ)
    (hd : IsCirculation I d) (u v : Fin I.n) (huv : residualSupport I hI d u v) :
    Relation.ReflTransGen (residualSupport I hI d) v u := by
  classical
  by_contra hn
  let S : Finset (Fin I.n) := Finset.univ.filter fun w =>
    Relation.ReflTransGen (residualSupport I hI d) v w
  have hv : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ v, Relation.ReflTransGen.refl⟩
  have hu : u ∉ S := fun h => hn (Finset.mem_filter.mp h).2
  have hclosed : ∀ x y, x ∈ S → residualSupport I hI d x y → y ∈ S := by
    intro x y hx hxy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, (Finset.mem_filter.mp hx).2.tail hxy⟩
  have hzero := circulation_cut_zero I hI d hd S
  obtain ⟨e, he⟩ := huv
  have hneg : ((if tailVertex I hI e ∈ S then (1 : ℝ) else 0) -
      (if headVertex I hI e ∈ S then (1 : ℝ) else 0))*d e < 0 := by
    rcases he with ⟨hp, htail, hhead⟩ | ⟨hp, hhead, htail⟩
    · simpa only [htail, hhead, hu, hv, ↓reduceIte, zero_sub, neg_one_mul] using neg_neg_of_pos hp
    · simpa only [htail, hhead, hu, hv, ↓reduceIte, sub_zero, one_mul] using hp
  have hsumneg := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => closed_cut_term_nonpos I hI d S hclosed j)
    ⟨e, Finset.mem_univ e, hneg⟩
  simp only [Finset.sum_const_zero] at hsumneg
  rw [hzero] at hsumneg
  exact (lt_irrefl 0) hsumneg

end MinCostFlow.IPM
