module

public import MinCostFlow.Scaling.CostLoopFeasibility
public import MinCostFlow.Scaling.VertexCompression
import Mathlib.Tactic.Ring

/-!
# The complete counted cost-scaling model

Lemma C.3 of Chen et al., arXiv:2203.00671v2, reduces arbitrary costs to
polynomially bounded costs. First discard isolated vertices. If costs already
fit the polynomial bound, call the bounded solver directly. Otherwise run the
integer cost loop. This direct branch avoids the source's extra assumption
that the given cost bound is at least polynomial in the graph size.

This file gives the function and its call/instance/work bounds. Exact
optimality of the loop remains a separate mathematical result.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Handle empty graphs, use one direct call for small costs, and otherwise
execute the counted integer cost-scaling loop on compressed vertices. -/
def costScalingModel (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) : CallResult (Fin I.m → ℤ) :=
  if I.m = 0 then ⟨fun _ => 0, [], 1⟩
  else
    let J := I.compress
    let prep := I.n + 20 * I.m + 1
    if C ≤ I.m ^ 10 then
      ⟨Circulation.solveWithZeroCapacities solve J, [J.positiveInstance],
        prep + 10 * (I.m + 1)⟩
    else
      let r := costLoop solve J C
      ⟨r.value.flow, r.calls, prep + r.work⟩

private theorem one_le_costLog (C : ℕ) : 1 ≤ Nat.clog 2 (C + 2) := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (C + 2)
  by_contra hn
  have he : Nat.clog 2 (C + 2) = 0 := by omega
  rw [he, Nat.pow_zero] at h
  omega

private theorem largeCost_vertex_bound (I : Circulation) (C : ℕ)
    (hm : I.m ≠ 0) (hC : ¬ C ≤ I.m ^ 10) :
    0 < C ∧ I.compress.n ≤ 2 * C := by
  have hp : 0 < I.m := Nat.pos_of_ne_zero hm
  have hpow : I.m ≤ I.m ^ 10 := by
    simpa only [Nat.pow_one] using
      (Nat.pow_le_pow_right hp (show 1 ≤ 10 by decide))
  have hn := I.endpointLabels_count_le
  change I.compress.n ≤ 2 * I.m at hn
  omega

/-- At most eight padded binary logarithms of `C+2` many calls are made. -/
theorem costScalingModel_calls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    (costScalingModel solve I C).calls.length ≤ 8 * Nat.clog 2 (C + 2) := by
  unfold costScalingModel
  split
  · simp
  · rename_i hm
    dsimp only
    split
    · have h := one_le_costLog C
      simp only [List.length_singleton]
      omega
    · rename_i hC
      have hb := largeCost_vertex_bound I C hm hC
      have h := costLoop_calls_le_eight_log solve I.compress C hb.1 hb.2
      have hl : Nat.clog 2 (C + 1) ≤ Nat.clog 2 (C + 2) :=
      Nat.clog_mono_right (b := 2) (Nat.le_succ (C + 1))
      exact le_trans h (Nat.mul_le_mul_left 8 hl)

/-- Every solver input has at most `12*m` edge slots. The vertex compression
is performed once outside the cost loop. -/
theorem costScalingModel_edges (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    ∀ J ∈ (costScalingModel solve I C).calls, J.m ≤ 12 * I.m := by
  unfold costScalingModel
  split
  · simp
  · dsimp only
    split
    · intro J hJ
      have he : J = I.compress.positiveInstance := List.mem_singleton.mp hJ
      subst J
      change I.m ≤ 12 * I.m
      omega
    · exact costLoop_edges_le_twelve solve I.compress C I.endpointLabels_count_le

/-- The direct call and all calls made by the loop satisfy the exact
polynomial cost specification, at their own edge counts. -/
theorem costScalingModel_polynomialCosts
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C : ℕ)
    (hc : I.CostsBounded C) :
    ∀ J ∈ (costScalingModel solve I C).calls, J.CostsBounded (J.m ^ 10) := by
  unfold costScalingModel
  split
  · simp
  · dsimp only
    split
    · rename_i hC
      intro J hJ
      have he : J = I.compress.positiveInstance := List.mem_singleton.mp hJ
      subst J
      apply Circulation.positiveInstance_costsBounded
      intro e
      exact le_trans (hc e) hC
    · exact costLoop_polynomialCosts solve I.compress C

/-- The work counter is at most `12000*m*clog_2(C+2)+n`. The additive vertex
scan occurs once, so isolated vertices do not multiply the logarithmic factor. -/
theorem costScalingModel_work (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) (hm : 0 < I.m) :
    (costScalingModel solve I C).work ≤ 12000 * I.m * Nat.clog 2 (C + 2) + I.n := by
  have hlog := one_le_costLog C
  unfold costScalingModel
  rw [ite_eq_right (Nat.ne_of_gt hm)]
  dsimp only
  split
  · dsimp only
    have hmul := Nat.mul_le_mul_left (12000 * I.m) hlog
    omega
  · rename_i hC
    have hb := largeCost_vertex_bound I C (Nat.ne_of_gt hm) hC
    have hw := costLoop_work_le_ten_thousand solve I.compress C hm
      I.endpointLabels_count_le hb.1 hb.2
    have hl : Nat.clog 2 (C + 1) ≤ Nat.clog 2 (C + 2) :=
      Nat.clog_mono_right (b := 2) (Nat.le_succ (C + 1))
    have hm1 := Nat.mul_le_mul_left (10000 * I.m) hl
    have hpad := Nat.mul_le_mul_left I.m hlog
    change (costLoop solve I.compress C).work ≤
      10000 * I.m * Nat.clog 2 (C + 1) at hw
    dsimp only
    have hw' := le_trans hw hm1
    simp only [Nat.mul_assoc, Nat.mul_one] at hw' hpad ⊢
    omega

/-- Every solver input has capacities in `1,...,max U (2*m+1)`, using only
that bounded solver specification. The increased bound records the shortest
routing used for dual extraction. -/
theorem costScalingModel_capacities
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C U : ℕ) (hU : 1 ≤ U)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (2 * I.m + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hu : ∀ e, I.capacity e ≤ U) :
    ∀ J ∈ (costScalingModel solve I C).calls, ∀ e,
      1 ≤ J.capacity e ∧ J.capacity e ≤ max U (2 * I.m + 1) := by
  unfold costScalingModel
  split
  · simp
  · dsimp only
    split
    · intro J hJ
      have he : J = I.compress.positiveInstance := List.mem_singleton.mp hJ
      subst J
      apply Circulation.positiveInstance_capacitiesBounded
      · exact le_trans hU (le_max_left _ _)
      · intro e
        exact le_trans (hu e) (le_max_left _ _)
    · have hbudget : max U (I.compress.n + 1) ≤ max U (2 * I.m + 1) :=
        max_le_max le_rfl (Nat.add_le_add_right I.endpointLabels_count_le 1)
      have hs : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
          (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.compress.n + 1)) →
          J.Optimal (fun e => (solve J e : ℝ)) := by
        intro J hc hcap
        exact hsolve J hc (fun e => ⟨(hcap e).1, le_trans (hcap e).2 hbudget⟩)
      intro J hJ e
      have h := costLoop_capacities solve I.compress C U hU hs hu J hJ e
      exact ⟨h.1, le_trans h.2 hbudget⟩

end MinCostFlow.Scaling
