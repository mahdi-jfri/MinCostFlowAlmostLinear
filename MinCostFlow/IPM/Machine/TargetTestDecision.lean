module

public import MinCostFlow.IPM.Machine.TargetTestInvariant
public import MinCostFlow.IPM.Machine.PrecisionInitialPotential
public import MinCostFlow.IPM.GuessInitial
import Mathlib.Tactic.Linarith

/-!
# Integer target decisions from the machine test

The initialized half-slacks give the promised potential bound whenever
the exact initial residual exceeds the stopping tolerance. Acceptance
also gives a feasible flow, so the quarter tolerance distinguishes
consecutive integral optimum values.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Any actual machine target-test record on the half-slack starting
flow decides the side of the integer optimum. An accepted flow is
within a quarter of the tested target. -/
theorem targetTest_integer_decision {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U E src heap out : ℕ) (target z : ℤ) (mem final : ℕ → ℕ)
    (hresult : TargetTestResult F I U E src heap out (target:ℝ) mem final)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hF : -(I.m*(U:ℝ)^2)≤(target:ℝ))
    (hfeas : I.IsFeasible (epochVector F I mem src))
    (hslack : ∀ e, (1/2:ℝ)≤epochVector F I mem src e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem src e)
    (fstar : Fin I.m → ℝ) (hstar : I.IsMinCostFlow fstar) (hz : I.cost fstar=(z:ℝ)) :
    (final (out-1)=1 ↔ z≤target) := by
  obtain ⟨_,_,_,_,hbit,hfail,hok⟩ := hresult
  constructor
  · intro hOK
    obtain ⟨hf,hr⟩ := hok hOK
    have hOpt := hstar.2 _ hf.2.1
    have hCost : (z:ℝ)≤I.cost (epochVector F I final (final (out-2))) := hz ▸ hOpt
    by_contra hbad
    have hh : (target:ℝ)+1≤z := by exact_mod_cast (show target+1≤z by omega)
    unfold residual at hr
    linarith only [hCost,hh,hr]
  · intro hzle
    by_contra hbad
    have hzero : final (out-1)=0 := by omega
    obtain ⟨hr,hnot⟩ := hfail hzero
    have hpos : 0<residual I (target:ℝ) (epochVector F I mem src) := by linarith only [hr]
    have hpot := guess_initial_potential_alphaPrime I U (target:ℝ) _ hm hU hsize hnums hfeas hslack hF hpos
    have hCost : I.cost fstar≤(target:ℝ) := by rw [hz]; exact_mod_cast hzle
    exact hnot ⟨⟨fstar,hstar.1,hCost⟩,hpot⟩

end MinCostFlow.IPM.Machine
