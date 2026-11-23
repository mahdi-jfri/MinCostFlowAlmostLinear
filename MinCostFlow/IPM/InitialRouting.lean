module

public import MinCostFlow.IPM.InitialConstruction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Routing of the initial flow

Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2, corrects each old
vertex's midpoint demand using its auxiliary edge. The new vertex has
zero net demand because the original demands sum to zero. We prove the
balance check, the effect of deleting fixed edges, and these routing
identities for the constructed initial flow.
-/

public section
namespace MinCostFlow.IPM

private theorem sum_indicator_vertex (n : ℕ) (w : Fin n) :
    (∑ v : Fin n, if (v : ℕ) = w then (1 : ℝ) else 0) = 1 := by
  have hi : ∀ v : Fin n, ((v : ℕ) = w) ↔ v = w := fun _ => Fin.ext_iff.symm
  simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Each valid edge has zero total incidence. -/
theorem sum_incidence_zero (I : Instance) (hI : I.IsValid) (e : Fin I.m) :
    (∑ v : Fin I.n, (I.edge e).b v) = 0 := by
  have he := hI.1 (I.edge e) (List.getElem_mem e.2)
  have ht := sum_indicator_vertex I.n ⟨(I.edge e).tail, he.1⟩
  have hh := sum_indicator_vertex I.n ⟨(I.edge e).head, he.2⟩
  unfold Edge.b
  rw [Finset.sum_sub_distrib, ht, hh, sub_self]

/-- Every flow on a valid instance has zero total routed demand. -/
theorem sum_routed_zero (I : Instance) (hI : I.IsValid) (f : Fin I.m → ℝ) :
    (∑ v : Fin I.n, ∑ e, (I.edge e).b v*f e) = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _
  rw [← Finset.sum_mul, sum_incidence_zero I hI e, zero_mul]

/-- A nonzero sum of demands is a certificate of infeasibility, and must
be rejected before the auxiliary-vertex construction. -/
theorem infeasible_of_unbalanced (I : Instance) (hI : I.IsValid)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) ≠ 0) : ¬ ∃ f, I.IsFeasible f := by
  rintro ⟨f, hf⟩
  have h := sum_routed_zero I hI f
  have heq : (∑ v : Fin I.n, ∑ e, (I.edge e).b v*f e) = ∑ v : Fin I.n, (I.d v : ℝ) :=
    Finset.sum_congr rfl (fun v _ => hf.1 v)
  exact hbal (heq.symm.trans h)

/-- A removed fixed edge's midpoint is its forced capacity. Thus the
original midpoint is the expansion of the retained-edge midpoints. -/
theorem expand_free_midpoint (I : Instance)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper) :
    expandFreeFlow I
      (fun j => (((freeEdgeArray I j).lower : ℝ)+(freeEdgeArray I j).upper)/2) = midpointFlow I := by
  funext e
  by_cases he : e ∈ freeEdges I
  · simp only [expandFreeFlow, he, ↓reduceDIte, freeEdgeArray, Equiv.apply_symm_apply, midpointFlow]
  · have hn : ¬ (I.edge e).lower < (I.edge e).upper := by
      intro h
      exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩)
    have hi := le_antisymm (hordered e) (not_lt.mp hn)
    simp only [expandFreeFlow, he, ↓reduceDIte, midpointFlow, hi]
    ring

/-- The retained midpoint demand plus half of the twice-deficit equals
the adjusted demand at every original vertex. -/
theorem free_midpoint_deficit (I : Instance)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper) (v : Fin I.n) :
    (∑ j, (freeEdgeArray I j).b v*
      ((((freeEdgeArray I j).lower : ℝ)+(freeEdgeArray I j).upper)/2)) +
      (twiceDeficit I v : ℝ)/2 = (freeDemands I v : ℝ) := by
  have ht := sum_expandFreeFlow I (fun e => (I.edge e).b v)
    (fun j => (((freeEdgeArray I j).lower : ℝ)+(freeEdgeArray I j).upper)/2)
  rw [expand_free_midpoint I hordered] at ht
  rw [freeDemands_cast]
  have hd := twiceDeficit_cast I v
  dsimp only [freeEdgeArray] at ht ⊢
  linarith only [ht, hd]

/-- A sum over the auxiliary edge indices can be written as a sum over
all vertices when the summand vanishes at zero-deficit vertices. -/
theorem sum_deficitIndex (I : Instance) (f : Fin I.n → ℝ)
    (hf : ∀ v, twiceDeficit I v = 0 → f v = 0) :
    (∑ j, f (deficitIndex I j).1) = ∑ v, f v := by
  calc
    _ = ∑ v : {v // v ∈ deficitVertices I}, f v.1 := (deficitIndex I).sum_comp _
    _ = ∑ v ∈ deficitVertices I, f v := by
      rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
    _ = ∑ v, f v := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      have hz : twiceDeficit I v = 0 := by
        by_contra hn
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hn⟩)
      exact hf v hz

/-- Auxiliary midpoint flows contribute the missing deficit at each old vertex. -/
theorem sum_star_old_contribution (I : Instance) (K : ℤ) (v : Fin I.n) :
    (∑ j, (starEdge I.n (deficitIndex I j).1 (twiceDeficit I (deficitIndex I j).1) K).b v*
      (|(twiceDeficit I (deficitIndex I j).1 : ℝ)|/2)) = (twiceDeficit I v : ℝ)/2 := by
  simp_rw [starEdge_old_contribution]
  have hsum : (∑ j, if v = (deficitIndex I j).1 then
      (twiceDeficit I (deficitIndex I j).1 : ℝ)/2 else 0) =
      ∑ w : Fin I.n, if v = w then (twiceDeficit I w : ℝ)/2 else 0 := by
    exact sum_deficitIndex I (fun w => if v = w then (twiceDeficit I w : ℝ)/2 else 0)
      (fun w hw => by simp only [hw, Int.cast_zero, zero_div, ite_self])
  rw [hsum]
  simp

/-- All auxiliary midpoint contributions sum to zero at the new vertex. -/
theorem sum_star_new_contribution (I : Instance) (K : ℤ) (hI : I.IsValid)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) = 0) :
    (∑ j, (starEdge I.n (deficitIndex I j).1 (twiceDeficit I (deficitIndex I j).1) K).b I.n*
      (|(twiceDeficit I (deficitIndex I j).1 : ℝ)|/2)) = 0 := by
  simp_rw [starEdge_new_contribution]
  rw [sum_deficitIndex I (fun v => -(twiceDeficit I v : ℝ)/2)
    (fun v hv => by simp only [hv, Int.cast_zero, neg_zero, zero_div])]
  simp_rw [twiceDeficit_cast]
  have hz := sum_routed_zero I hI (midpointFlow I)
  have hring : ∀ x y : ℝ, -(2*(x-y))/2 = -x+y := by intro x y; ring
  simp_rw [hring]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hbal, hz]
  norm_num

/-- The initial flow of Appendix B.1 (page 92) routes the adjusted demands on the
augmented instance, after reversed capacities and unbalanced demands
have been rejected. -/
theorem initialFlow_routes (I : Instance) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hbal : (∑ v : Fin I.n, (I.d v : ℝ)) = 0) :
    (initialInstance I K).Routes (initialFlow I K) := by
  apply (routes_flowOfArray_iff (initialEdgeArray I K) (initialDemands I) (initialArrayFlow I)).mpr
  intro v
  refine Fin.lastCases ?_ (fun w => ?_) v
  · simp only [initialDemands, Fin.lastCases_last, Fin.val_last]
    rw [Fin.sum_univ_add]
    simp only [initialEdgeArray, initialArrayFlow, Fin.addCases_left, Fin.addCases_right]
    have hzero : ∀ j, (freeEdgeArray I j).b I.n = 0 := by
      intro j
      have ht := hI.1 (I.edge (freeIndex I j).1) (List.getElem_mem ((freeIndex I j).1).2)
      have htail : I.n ≠ (freeEdgeArray I j).tail := (Nat.ne_of_lt ht.1).symm
      have hhead : I.n ≠ (freeEdgeArray I j).head := (Nat.ne_of_lt ht.2).symm
      simp only [Edge.b, htail, hhead, ↓reduceIte, sub_self]
    simp only [hzero, zero_mul, Finset.sum_const_zero, zero_add, Int.cast_zero]
    exact sum_star_new_contribution I K hI hbal
  · simp only [initialDemands, Fin.lastCases_castSucc, Fin.val_castSucc]
    rw [Fin.sum_univ_add]
    simp only [initialEdgeArray, initialArrayFlow, Fin.addCases_left, Fin.addCases_right]
    rw [sum_star_old_contribution]
    exact free_midpoint_deficit I hordered w

end MinCostFlow.IPM
