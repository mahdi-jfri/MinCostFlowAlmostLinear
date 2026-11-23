module

public import MinCostFlow.IPM.Machine.EpochHistoryAccuracy
public import MinCostFlow.IPM.Machine.EpochHistoryCachePrefix
import Mathlib.Tactic.Linarith

/-!
# Hidden stability from the accuracy of every actual input

Use the computed coefficients at every stage of the shared history.
The valid-history condition holds the lengths until reinsertion, and
the exact report list holds the cached coordinates for that same
interval. Lemma 9.2 then supplies the negative-ratio witness.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Certified inputs of a promised epoch have Definition 4.4's hidden
stability with quality `a/8` and the selected logarithmic range. -/
theorem epoch_hidden_of_inputs_at_range (I : Instance) (U R : ℕ) (target κ a r : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ)
    (op : ℕ → Bool) (T : ℕ) (base fstar : Fin I.m → ℝ)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤(I.m:ℝ)*U)
    (hnums : NumbersBounded I U) (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (hκ : 0≤κ) (hκ' : κ≤1) (ha : 0<a) (ha' : a≤alpha I U) (hx : κ*a≤1)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hcache : EpochHistoryCacheStable I A D eta op T base)
    (hinputs : ∀ t≤T,EpochInputAccuracyAt I R target a r (κ*a/32) A D eta op base t)
    (hstates : ∀ t≤T,
      let f := epochInputFlow I A D eta op t base
      StrictlyInside I f ∧ I.Routes f ∧
      -10*Real.log (I.m*U)≤Real.log (residual I target f) ∧
      potential I a target f≤200*I.m*Real.log (I.m*U)) :
    D.HiddenStable T (a/8) ((R+slackRangeExponent I.m U+6 : ℕ) : ℝ) := by
  let f := fun t => epochInputFlow I A D eta op t base
  let stored := fun t => epochHistoryCache I A D eta op t base
  let q := κ*a/32
  have hx0 : 0≤κ*a := mul_nonneg hκ ha.le
  have he : 0≤q/4 := by unfold q; linarith only [hx0]
  have he' : q/4≤1 := by unfold q; linarith only [hx]
  apply epoch_hidden_at_range I U R target a (q/4) D T fstar f stored
    (fun t e => D.g t e) (fun t e => D.ℓ t e) r hm hU hsize hnums hstar hF ha ha' he he' hG
  · exact fun t ht => (hinputs t ht).1
  · exact fun t ht => (hinputs t ht).2.1
  · exact fun t ht => (hstates t ht).1
  · exact fun t ht => (hstates t ht).2.1
  · exact fun t ht => (hinputs t ht).2.2.1.2.1
  · exact fun t ht => (hstates t ht).2.2.1
  · exact fun t ht => (hstates t ht).2.2.2
  · exact fun t ht => (hinputs t ht).2.2.1
  · intro t ht e
    have hgrad := (hinputs t ht).2.2.2.2.1 e
    have hsmall := mul_le_mul_of_nonneg_right hκ' ha.le
    have htol : q/16≤a/2 := by unfold q; linarith only [hsmall,ha]
    exact hgrad.trans htol
  · exact fun t ht => (hinputs t ht).2.2.2.1
  · exact fun t ht => (hinputs t ht).2.2.2.2.2.1
  · intro t ht u hu e hn
    exact epoch_length_constant I D op T hv hG hu ht e hn
  · exact hcache
  · exact fun t ht => (hinputs t ht).2.2.2.2.2.2

/-- The original range gives the original hidden-stability parameter. -/
theorem epoch_hidden_of_inputs (I : Instance) (U : ℕ) (target κ a r : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ)
    (op : ℕ → Bool) (T : ℕ) (base fstar : Fin I.m → ℝ)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤(I.m:ℝ)*U)
    (hnums : NumbersBounded I U) (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target)
    (hκ : 0≤κ) (hκ' : κ≤1) (ha : 0<a) (ha' : a≤alpha I U) (hx : κ*a≤1)
    (hv : MinRatioHistoryValid D op T) (hG : ∀ t≤T,D.G t=namedInstance I)
    (hcache : EpochHistoryCacheStable I A D eta op T base)
    (hinputs : ∀ t≤T,EpochInputAccuracy I U target a r (κ*a/32) A D eta op base t)
    (hstates : ∀ t≤T,
      let f := epochInputFlow I A D eta op t base
      StrictlyInside I f ∧ I.Routes f ∧
      -10*Real.log (I.m*U)≤Real.log (residual I target f) ∧
      potential I a target f≤200*I.m*Real.log (I.m*U)) :
    D.HiddenStable T (a/8) (precisionHiddenPsi I.m U) :=
  epoch_hidden_of_inputs_at_range I U _ target κ a r A D eta op T base fstar
    hm hU hsize hnums hstar hF hκ hκ' ha ha' hx hv hG hcache hinputs hstates

end MinCostFlow.IPM.Machine
