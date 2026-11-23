module

public import MinCostFlow.IPM.Machine.EpochHistoryRun
import MinCostFlow.IPM.Machine.EpochGuardRanges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Potential drop of a complete actual epoch

Each accepted rounded step reduces the potential by at least the
factor-four analysis's drop. Within an epoch the held residual gives
strictly positive residuals, so the same estimate applies through the
last materialized flow.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A certified loop prefix decreases the potential by its exact
number of rounded steps times `q²/2000`. -/
theorem epoch_dyadic_progress (I : Instance) (U i : ℕ) (target q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (hm : 0<I.m) (hi : i≤ I.m) (hsize : 2≤ I.m*U)
    (hnums : NumbersBounded I U) (hq : 0<q) (hq' : q≤1/2)
    (hf : StrictlyInside I base) (hroute : I.Routes base) (hr : 0<residual I target base)
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ)))
    (hsteps : EpochDyadicPrefix I U target q A D eta op base i) :
    potential I (Num.IPM.alphaPrime I.m U) target (epochHistoryFlow I A D eta op (2*i) base)≤
      potential I (Num.IPM.alphaPrime I.m U) target base-(i:ℝ)*q^2/2000 := by
  let a := Num.IPM.alphaPrime I.m U
  let f := fun j => epochHistoryFlow I A D eta op (2*j) base
  have hw := epochDyadicPrefix_state I U i target q A D eta op base hm hi hsize hnums hq hq'
    hf hroute hr hpot hsteps
  have hdrop : ∀ j< i,potential I a target (f (j+1))≤potential I a target (f j)-q^2/2000 := by
    intro j hj
    obtain ⟨hroute',hf',_,hres⟩ := hw j hj.le
    exact ((hsteps j hj).spec I U target q _ _ hm hsize hnums hf' hroute' hres.2.1 hq hq').2.2.2
  have hbound : ∀ j≤ i,potential I a target (f j)≤potential I a target base-(j:ℝ)*q^2/2000 := by
    intro j
    induction j with
    | zero =>
      intro _
      change potential I a target (epochHistoryFlow I A D eta op 0 base)≤_
      rw [epochHistoryFlow_zero]
      norm_num
    | succ j ih =>
      intro hj
      have hh := ih (by omega)
      have hd := hdrop j (by omega)
      push_cast
      linarith only [hh,hd]
  exact hbound i le_rfl

end MinCostFlow.IPM.Machine
