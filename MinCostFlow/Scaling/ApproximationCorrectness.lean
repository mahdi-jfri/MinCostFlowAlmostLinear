module

public import MinCostFlow.Scaling.ApproximationModel
public import MinCostFlow.Scaling.BottleneckCycleApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correctness of the bottleneck approximation routine

Lemma C.10 used by Lemma C.9 of Chen et al., arXiv:2203.00671v2,
Appendix C, binary-searches a negative-cycle bottleneck and scatters that
amount along an extracted cycle. The actual integer function is proved
feasible and `m^12` approximate. Its reported magnitude is exactly minus its
objective. A zero magnitude certifies an optimum. The proof uses only the
source's bounded primal solver and the proved search and extraction loops.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Lemma C.10 (Appendix C): the counted integer approximation routine
returns a feasible flow of value `-B`, with `-m^12*B` a lower bound for every
real feasible objective. If `B=0`, its returned flow is an exact optimum. -/
theorem lemma_C_10 (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) :
    let r := (polyApproxModel solve I).value
    I.Feasible (fun e => (r.flow e : ℝ)) ∧
      I.objective (fun e => (r.flow e : ℝ)) = -(r.magnitude : ℝ) ∧
      (∀ g : Fin I.m → ℝ, I.Feasible g →
        -((I.m ^ 12 : ℕ) : ℝ) * r.magnitude ≤ I.objective g) ∧
      (r.magnitude = 0 → I.Optimal (fun e => (r.flow e : ℝ))) := by
  cases hbest : (bottleneckSearch solve I).value.best with
  | none =>
    have hzero := bottleneckSearch_none_optimal solve hsolve I hc hbest
    simp only [polyApproxModel, hbest, Int.cast_zero, Nat.cast_zero, neg_zero, mul_zero]
    have hcost : I.objective (fun _ => 0) = 0 := by simp only [Circulation.objective, mul_zero, Finset.sum_const_zero]
    refine ⟨hzero.1, hcost, ?_, fun _ => hzero⟩
    intro g hg
    have hh := hzero.2 g hg
    rw [hcost] at hh
    exact hh
  | some pair =>
    obtain ⟨u, f⟩ := pair
    have hs := bottleneckSearch_selection solve hsolve I hc
    have hb := hs.2.2.2
    rw [hbest] at hb
    have htest : (I.bottleneckGraph u).Optimal (fun e => (f e : ℝ)) := by
      rw [hb.2.2.1]
      exact I.bottleneckTest_optimal solve hsolve hc u
    have hunit := I.bottleneckGraph_unit u f htest.1
    have hfeas := I.bottleneckGraph_feasible u (fun e => (f e : ℝ)) htest.1
    have hnegative : I.integerObjective f < 0 := hb.2.2.2
    have hextract := I.extractCycleModel_closed_or_nonnegative f hunit hfeas
    rcases hextract with hn | ⟨es, v, p, hes, hedges, hp⟩
    · have hh := hn.2
      omega
    · let F := (Scatter.withWork (fun _ : Fin I.m => (0 : ℤ)) (es.map (fun e => (e, (u : ℤ))))).1
      have hdata := selected_cycle_flow_approximation solve hsolve I hc u f hbest es hes v p hedges hp
      change I.Feasible (fun e => (F e : ℝ)) ∧ I.objective (fun e => (F e : ℝ)) < 0 ∧ _ at hdata
      have hcostint : I.integerObjective F < 0 := by
        have hh := hdata.2.1
        rw [← I.integerObjective_cast] at hh
        exact_mod_cast hh
      let B := (-I.integerObjective F).toNat
      have hB : 0 < B := Int.lt_toNat.mpr (neg_pos.mpr hcostint)
      have hBint : (B : ℤ) = -I.integerObjective F := Int.toNat_of_nonneg (neg_nonneg.mpr hcostint.le)
      have hBreal : (B : ℝ) = -I.objective (fun e => (F e : ℝ)) := by
        have hh := congrArg (fun z : ℤ => (z : ℝ)) hBint
        simpa only [Int.cast_natCast, Int.cast_neg, I.integerObjective_cast] using hh
      simp only [polyApproxModel, hbest, hes]
      change I.Feasible (fun e => (F e : ℝ)) ∧
        I.objective (fun e => (F e : ℝ)) = -(B : ℝ) ∧
        (∀ g : Fin I.m → ℝ, I.Feasible g → -((I.m ^ 12 : ℕ) : ℝ) * B ≤ I.objective g) ∧
        (B = 0 → I.Optimal (fun e => (F e : ℝ)))
      have hcost : I.objective (fun e => (F e : ℝ)) = -(B : ℝ) := by linarith only [hBreal]
      refine ⟨hdata.1, hcost, ?_, ?_⟩
      · intro g hg
        have hh := hdata.2.2 g hg
        rw [hcost] at hh
        simpa only [mul_neg, neg_mul] using hh
      · intro hz
        omega

end MinCostFlow.Scaling
