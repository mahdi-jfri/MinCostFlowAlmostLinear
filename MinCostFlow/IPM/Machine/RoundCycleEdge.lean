module

public import MinCostFlow.IPM.Machine.RoundPrecision
import Mathlib.Tactic

/-!
# Bounds on the new edge during a cycle correction

The original floor and ceiling are the two limits for the new
coordinate. If the new coordinate remains fractional, its own floor
and ceiling give those same limits for a later Link.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- The two directional updates stay in the original unit interval.
Reaching the available amount reaches an integer endpoint. -/
theorem roundCycleEdge_bounds (q δ : ℚ) (backward : Bool)
    (hδ : 0≤δ)
    (hBound : δ ≤ (if backward then q-(⌊q⌋:ℚ) else (⌈q⌉:ℚ)-q)) :
    let value := if backward then q-δ else q+δ
    (⌊q⌋:ℚ)≤value ∧ value≤(⌈q⌉:ℚ) ∧ |value|≤|q|+1 ∧
      (isIntRat value=false → δ < (if backward then q-(⌊q⌋:ℚ) else (⌈q⌉:ℚ)-q)) := by
  have hlo := Int.floor_le q
  have hhi := Int.le_ceil q
  have hlo' := Int.sub_one_lt_floor q
  have hhi' := Int.ceil_lt_add_one q
  have hb : ∀ x : ℚ,(⌊q⌋:ℚ)≤x → x≤(⌈q⌉:ℚ) → |x|≤|q|+1 := by
    intro x hx hy
    have hq := le_abs_self q
    have hq' := neg_abs_le q
    exact abs_le.mpr ⟨by linarith only [hlo',hx,hq'],by linarith only [hhi',hy,hq]⟩
  cases backward with
  | false =>
    simp only [Bool.false_eq_true,ite_false] at hBound ⊢
    have h₁ : (⌊q⌋:ℚ)≤q+δ := by linarith only [hlo,hδ]
    have h₂ : q+δ≤(⌈q⌉:ℚ) := by linarith only [hBound]
    refine ⟨h₁,h₂,hb _ h₁ h₂,fun hfrac => lt_of_le_of_ne hBound ?_⟩
    intro hEq
    have hInt : isIntRat (q+δ)=true := isIntRat_iff.mpr ⟨⌈q⌉,by linarith only [hEq]⟩
    rw [hfrac] at hInt
    cases hInt
  | true =>
    simp only [eq_self,ite_true] at hBound ⊢
    have h₁ : (⌊q⌋:ℚ)≤q-δ := by linarith only [hBound]
    have h₂ : q-δ≤(⌈q⌉:ℚ) := by linarith only [hhi,hδ]
    refine ⟨h₁,h₂,hb _ h₁ h₂,fun hfrac => lt_of_le_of_ne hBound ?_⟩
    intro hEq
    have hInt : isIntRat (q-δ)=true := isIntRat_iff.mpr ⟨⌊q⌋,by linarith only [hEq]⟩
    rw [hfrac] at hInt
    cases hInt

/-- Compute relink availabilities by using the new fractional
coordinate. The resulting floor and ceiling are exactly the model's
original endpoints. -/
theorem roundRelink_endpoints {q value : ℚ}
    (hq : isIntRat q=false) (hv : isIntRat value=false)
    (hlo : (⌊q⌋:ℚ)≤value) (hhi : value≤(⌈q⌉:ℚ)) :
    ⌊value⌋=⌊q⌋ ∧ ⌈value⌉=⌈q⌉ := by
  have hNonint : ∀ x : ℚ,isIntRat x=false → x∉Set.range (Int.cast : ℤ → ℚ) := by
    intro x hx
    rintro ⟨z,hz⟩
    have hInt := isIntRat_iff.mpr ⟨z,hz.symm⟩
    rw [hx] at hInt
    cases hInt
  have ha : value<(⌈q⌉:ℚ) := lt_of_le_of_ne hhi (fun he => hNonint value hv ⟨⌈q⌉,he.symm⟩)
  have hc := (Int.ceil_eq_floor_add_one_iff_notMem q).mpr (hNonint q hq)
  have hc' := (Int.ceil_eq_floor_add_one_iff_notMem value).mpr (hNonint value hv)
  have hfloor : ⌊value⌋=⌊q⌋ := by
    apply Int.floor_eq_iff.mpr
    rw [hc,Int.cast_add,Int.cast_one] at ha
    exact ⟨hlo,ha⟩
  exact ⟨hfloor,by rw [hc,hc',hfloor]⟩

end MinCostFlow.IPM.Machine
