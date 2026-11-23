module

public import MinCostFlow.IPM.RemoveFixed
public import MinCostFlow.IPM.CapacityPreprocessing
import Mathlib.Tactic.Linarith

/-!
# Bounds after fixed-edge deletion

The preprocessing before Appendix B.1 (page 92) of Chen et al., arXiv:2203.00671v2,
keeps the original vertex set and at most the original number of edges.
Its capacities are strictly ordered, so their midpoints have positive
slacks. The adjusted demands are integral and bounded by `2mU`, while
the retained costs and capacities retain their original bounds.
-/

public section
namespace MinCostFlow.IPM

/-- Fixed-edge deletion does not increase the number of edges. -/
theorem removeFixed_m_le (I : Instance) : (removeFixed I).m ≤ I.m := by
  rw [removeFixed, instanceOfArrays_m]
  have h := Finset.card_le_card (Finset.filter_subset (fun e : Fin I.m =>
    (I.edge e).lower < (I.edge e).upper) Finset.univ)
  simpa only [Finset.card_univ, Fintype.card_fin, freeEdges] using h

/-- The vertex set is preserved by fixed-edge deletion. -/
theorem removeFixed_n (I : Instance) : (removeFixed I).n = I.n := rfl

/-- Validity is preserved by fixed-edge deletion. -/
theorem removeFixed_valid (I : Instance) (hI : I.IsValid) : (removeFixed I).IsValid := by
  apply valid_instanceOfArrays
  intro j
  exact hI.1 (I.edge (freeIndex I j).1)
    (List.getElem_mem (n := ((freeIndex I j).1).1) ((freeIndex I j).1).2)

/-- All retained capacity intervals are strictly ordered. -/
theorem removeFixed_strict (I : Instance) (e : Fin (removeFixed I).m) :
    (((removeFixed I).edge e).lower : ℝ) < ((removeFixed I).edge e).upper := by
  have he : (removeFixed I).edge e =
      freeEdgeArray I (arrayIndex (freeEdgeArray I) (freeDemands I) e) :=
    instanceOfArrays_edge (freeEdgeArray I) (freeDemands I) e
  rw [he]
  exact_mod_cast freeEdgeArray_strict I (arrayIndex (freeEdgeArray I) (freeDemands I) e)

/-- Midpoints of the reduced instance are strictly inside every interval. -/
theorem midpoint_removeFixed_inside (I : Instance) :
    StrictlyInside (removeFixed I) (midpointFlow (removeFixed I)) :=
  (midpoint_inside_iff (removeFixed I)).mpr (removeFixed_strict I)

private theorem incidence_abs_le_one (e : Edge) (v : ℕ) : |e.b v| ≤ 1 := by
  unfold Edge.b
  split_ifs <;> norm_num

/-- The forced flow has the same absolute bound as the original capacities. -/
theorem abs_fixedFlow_le (I : Instance) (U : ℝ) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (e : Fin I.m) : |(fixedFlow I e : ℝ)| ≤ U := by
  by_cases he : e ∈ freeEdges I
  · simpa only [fixedFlow, he, ↓reduceIte, Int.cast_zero, abs_zero] using hU
  · simpa only [fixedFlow, he, ↓reduceIte] using (hnums.2 e).1

/-- Subtracting fixed routing contributions increases demand magnitudes
by at most `mU`, so the new demands are bounded by `2mU` when `m > 0`. -/
theorem abs_freeDemands_le (I : Instance) (U : ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (v : Fin I.n) :
    |(freeDemands I v : ℝ)| ≤ 2*I.m*U := by
  have hsum : |∑ e, (I.edge e).b v*(fixedFlow I e : ℝ)| ≤ I.m*U := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ e, |(I.edge e).b v*(fixedFlow I e : ℝ)|) ≤ ∑ _ : Fin I.m, U := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul]
        have h := mul_le_mul (incidence_abs_le_one (I.edge e) v)
          (abs_fixedFlow_le I U hU hnums e) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using h
      _ = I.m*U := by simp
  have ht := abs_sub_le (I.d v : ℝ) 0 (∑ e, (I.edge e).b v*(fixedFlow I e : ℝ))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  rw [freeDemands_cast]
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hmU := mul_le_mul_of_nonneg_right hm' hU
  have hd := hnums.1 v
  nlinarith only [ht, hsum, hmU, hd]

/-- All numbers of the reduced instance are bounded by `2mU`. -/
theorem removeFixed_numbers_bounded (I : Instance) (U : ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) : NumbersBounded (removeFixed I) (2*I.m*U) := by
  constructor
  · intro v
    have hd : (removeFixed I).d v = freeDemands I v :=
      instanceOfArrays_d (freeEdgeArray I) (freeDemands I) v
    rw [hd]
    exact abs_freeDemands_le I U hm hU hnums v
  · intro e
    have he : (removeFixed I).edge e =
        freeEdgeArray I (arrayIndex (freeEdgeArray I) (freeDemands I) e) :=
      instanceOfArrays_edge (freeEdgeArray I) (freeDemands I) e
    rw [he]
    have ht := hnums.2 (freeIndex I (arrayIndex (freeEdgeArray I) (freeDemands I) e)).1
    have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
    have hbound : U ≤ 2*I.m*U := by nlinarith only [hm', hU]
    exact ⟨ht.1.trans hbound, ht.2.1.trans hbound, ht.2.2.trans hbound⟩

end MinCostFlow.IPM
