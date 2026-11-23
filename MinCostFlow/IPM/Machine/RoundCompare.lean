module

public import MinCostFlow.IPM.Machine.RoundRatFacts
public import MinCostFlow.Num.IsInteger
public import MinCostFlow.Num.Less
public import MinCostFlow.Rounding.Algorithm
import Mathlib.Tactic

/-!
# Exact comparisons on rounding values

Both signed operands have the same scale. The integer test checks
divisibility by that scale, as required by Kang and Payor's exact
rounding algorithm.
-/

public section
namespace MinCostFlow.IPM.Machine
open Rounding

/-- The comparison on signed numerators agrees with rational order. -/
theorem RatAt.lt_iff {mem : ℕ → ℕ} {a b h L P : ℕ} {x y : ℚ}
    (hx : RatAt mem a h L P x) (hy : RatAt mem b h L P y) :
    Num.intVal mem a h L<Num.intVal mem b h L ↔ x<y := by
  rw [← hx.2,← hy.2,readRat,readRat,div_lt_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

/-- The numerator is divisible by the scale exactly for integral
flow, which is the predicate in the rounding model. -/
theorem RatAt.isInt_iff {mem : ℕ → ℕ} {a h L P : ℕ} {q : ℚ}
    (hq : RatAt mem a h L P q) :
    (2:ℤ)^P∣Num.intVal mem a h L ↔ isIntRat q=true := by
  rw [isIntRat_iff]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    rw [← hq.2,readRat,hz]
    push_cast
    field_simp
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    have hh : (Num.intVal mem a h L:ℚ)/(2:ℚ)^P=(z:ℚ) := hq.2.trans hz
    have hab : (Num.intVal mem a h L:ℚ)=(2:ℚ)^P*(z:ℚ) :=
      (div_eq_iff (by positivity)).mp hh |>.trans (mul_comm _ _)
    exact_mod_cast hab

end MinCostFlow.IPM.Machine
