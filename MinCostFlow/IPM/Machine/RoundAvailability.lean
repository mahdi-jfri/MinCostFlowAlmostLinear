module

public import MinCostFlow.IPM.Machine.RoundingInput
public import MinCostFlow.Num.Floor
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.ShiftLeft
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Fixed-point availabilities for a fractional edge

Kang and Payor, arXiv:1507.08139v1, Section 4, stores both
directional amounts before a flow becomes integral. The backward
amount is the fractional part of the current flow. For a fractional
coordinate the other amount is one minus that part.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Rounding WordRAM

/-- The two availability calculations stay on the same rational
grid and have magnitude at most one. -/
theorem round_availability_bounds (P : ℕ) (f : ℚ) (hf : IsFixedPoint P f)
    (hfrac : isIntRat f=false) :
    let back := f-(⌊f⌋:ℚ)
    let forward := (⌈f⌉:ℚ)-f
    IsFixedPoint P back ∧ IsFixedPoint P forward ∧ 0<back ∧ back<1 ∧
      0<forward ∧ forward<1 ∧ forward=1-back := by
  dsimp only
  have hnonint : f∉Set.range (Int.cast : ℤ → ℚ) := by
    rintro ⟨z,hz⟩
    have ho := isIntRat_iff.mpr ⟨z,hz.symm⟩
    rw [hfrac] at ho
    cases ho
  have hback0 : 0<f-(⌊f⌋:ℚ) := by
    apply sub_pos.mpr
    apply lt_of_le_of_ne (Int.floor_le f)
    exact fun he => hnonint ⟨⌊f⌋,he⟩
  have hback1 : f-(⌊f⌋:ℚ)<1 := by
    have hh := Int.lt_floor_add_one f
    linarith only [hh]
  have hceil := (Int.ceil_eq_floor_add_one_iff_notMem f).mpr hnonint
  have he : (⌈f⌉:ℚ)-f=1-(f-(⌊f⌋:ℚ)) := by rw [hceil,Int.cast_add,Int.cast_one]; ring
  exact ⟨isFixedPoint_sub hf (isFixedPoint_int P _),isFixedPoint_sub (isFixedPoint_int P _) hf,
    hback0,hback1,by rw [he]; linarith only [hback1],by rw [he]; linarith only [hback0],he⟩

/-- The integer part, backward amount and forward amount are all
representable at the selected scale. The floor differs from its
input by less than one. -/
theorem round_availability_fits (m U : ℕ) (f : ℚ)
    (hm : 0<m) (hU : 1≤U) (hf : IsFixedPoint (ipmPrecision m U) f)
    (hmag : |(f:ℝ)|≤U) (hfrac : isIntRat f=false) :
    RatFits 4 (ipmLimbs m U) (ipmPrecision m U) (⌊f⌋:ℚ) ∧
    RatFits 4 (ipmLimbs m U) (ipmPrecision m U) (f-(⌊f⌋:ℚ)) ∧
    RatFits 4 (ipmLimbs m U) (ipmPrecision m U) ((⌈f⌉:ℚ)-f) := by
  obtain ⟨hfixB,hfixF,hB,hB',hF,hF',_⟩ := round_availability_bounds _ f hf hfrac
  have hCap := twice_capacity_le_dyadic m U hm hU
  have hE : (2:ℝ)^(slackRangeExponent m U)≤(2:ℝ)^(ipmRangeExponent m U) :=
    pow_le_pow_right₀ (by norm_num) (by unfold ipmRangeExponent; omega)
  have hBound := hCap.trans hE
  have hu : (1:ℝ)≤U := by exact_mod_cast hU
  have hBreal : (0:ℝ)<(f:ℝ)-(⌊f⌋:ℤ) := by exact_mod_cast hB
  have hBreal' : (f:ℝ)-(⌊f⌋:ℤ)<1 := by exact_mod_cast hB'
  have hFloor : |((⌊f⌋:ℤ):ℝ)|≤2*(U:ℝ) := by
    apply abs_le.mpr
    obtain ⟨h1,h2⟩ := abs_le.mp hmag
    exact ⟨by linarith only [h1,hBreal',hu],by linarith only [h2,hBreal,hu]⟩
  have h1 : (1:ℝ)≤(2:ℝ)^(ipmRangeExponent m U) := one_le_pow₀ (by norm_num)
  have hfB : |((f-(⌊f⌋:ℚ):ℚ):ℝ)|≤1 := by
    have h : |f-(⌊f⌋:ℚ)|≤1 := (abs_of_pos hB).symm ▸ hB'.le
    exact_mod_cast h
  have hfF : |(((⌈f⌉:ℚ)-f:ℚ):ℝ)|≤1 := by
    have h : |(⌈f⌉:ℚ)-f|≤1 := (abs_of_pos hF).symm ▸ hF'.le
    exact_mod_cast h
  exact ⟨ratFits_chosen_precision m U _ (isFixedPoint_int _ _) (by simpa using hFloor.trans hBound),
    ratFits_chosen_precision m U _ hfixB (hfB.trans h1),
    ratFits_chosen_precision m U _ hfixF (hfF.trans h1)⟩

/-- The integer part, backward amount and forward amount are all
representable at the selected scale. The floor differs from its
input by less than one. -/
theorem round_availability_fits_widened (m U k : ℕ) (f : ℚ)
    (hm : 0<m) (hU : 1≤U) (hf : IsFixedPoint (ipmQualityPrecision m U k) f)
    (hmag : |(f:ℝ)|≤U) (hfrac : isIntRat f=false) :
    RatFits 4 (ipmQualityLimbs m U k) (ipmQualityPrecision m U k) (⌊f⌋:ℚ) ∧
    RatFits 4 (ipmQualityLimbs m U k) (ipmQualityPrecision m U k) (f-(⌊f⌋:ℚ)) ∧
    RatFits 4 (ipmQualityLimbs m U k) (ipmQualityPrecision m U k) ((⌈f⌉:ℚ)-f) := by
  obtain ⟨hfixB,hfixF,hB,hB',hF,hF',_⟩ := round_availability_bounds _ f hf hfrac
  have hCap := twice_capacity_le_dyadic m U hm hU
  have hE : (2:ℝ)^(slackRangeExponent m U)≤(2:ℝ)^(ipmQualityRangeExponent m U k) :=
    pow_le_pow_right₀ (by norm_num) (by have hs := slackRangeExponent_le_qualitySlackExponent m U k; unfold ipmQualityRangeExponent; omega)
  have hBound := hCap.trans hE
  have hu : (1:ℝ)≤U := by exact_mod_cast hU
  have hBreal : (0:ℝ)<(f:ℝ)-(⌊f⌋:ℤ) := by exact_mod_cast hB
  have hBreal' : (f:ℝ)-(⌊f⌋:ℤ)<1 := by exact_mod_cast hB'
  have hFloor : |((⌊f⌋:ℤ):ℝ)|≤2*(U:ℝ) := by
    apply abs_le.mpr
    obtain ⟨h1,h2⟩ := abs_le.mp hmag
    exact ⟨by linarith only [h1,hBreal',hu],by linarith only [h2,hBreal,hu]⟩
  have h1 : (1:ℝ)≤(2:ℝ)^(ipmQualityRangeExponent m U k) := one_le_pow₀ (by norm_num)
  have hfB : |((f-(⌊f⌋:ℚ):ℚ):ℝ)|≤1 := by
    have h : |f-(⌊f⌋:ℚ)|≤1 := (abs_of_pos hB).symm ▸ hB'.le
    exact_mod_cast h
  have hfF : |(((⌈f⌉:ℚ)-f:ℚ):ℝ)|≤1 := by
    have h : |(⌈f⌉:ℚ)-f|≤1 := (abs_of_pos hF).symm ▸ hF'.le
    exact_mod_cast h
  exact ⟨ratFits_widened_precision m U k _ (isFixedPoint_int _ _) (by simpa using hFloor.trans hBound),
    ratFits_widened_precision m U k _ hfixB (hfB.trans h1),
    ratFits_widened_precision m U k _ hfixF (hfF.trans h1)⟩

end MinCostFlow.IPM.Machine
