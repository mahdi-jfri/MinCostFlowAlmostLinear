module

public import MinCostFlow.Num.Floor
import MinCostFlow.Num.ShiftFacts
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Values used in fixed-point rounding

An extra limb makes signed negation exact, even for the smallest input. Smaller-width
wrapping discards any wrap at a larger width. Finally, ceiling is the negative floor
of the negative value.
-/

public section
namespace MinCostFlow.Num

/-- One extra limb can hold the negative of every source integer. -/
theorem fits_neg_extra {h L : ℕ} {x : ℤ} (hh : 0<h) (hx : Fits h L x) : Fits h (L+1) (-x) := by
  have hb : 2≤base h := Nat.succ_le_of_lt (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide))
  have hc : (0:ℤ)<capacity h L := by exact_mod_cast capacity_pos h L
  have hm : 2*(capacity h L : ℤ)≤capacity h (L+1) := by
    rw [capacity_succ]
    exact_mod_cast Nat.mul_le_mul_right (capacity h L) hb
  obtain ⟨hl,hu⟩ := hx
  constructor <;> omega

/-- Wrapping at a larger limb count does not affect the final smaller wrapped value. -/
theorem wrap_prefix_wrap {h L K : ℕ} (hLK : L≤K) (x : ℤ) :
    wrap h L (wrap h K x)=wrap h L x := by
  have hd : (capacity h L : ℤ)∣(capacity h K : ℤ) := by
    have hn : capacity h L∣capacity h K := by
      unfold capacity
      exact pow_dvd_pow (base h) hLK
    exact_mod_cast hn
  exact wrap_congr (Int.ModEq.of_dvd hd (wrap_emod h K x))

/-- The negative quotient of the negative numerator is the real ceiling. -/
theorem ceil_fixVal (mem : ℕ→ℕ) (a h L P : ℕ) :
    ⌈fixVal mem a h L P⌉= -((-intVal mem a h L)/(2:ℤ)^P) := by
  have he := floorDiv_eq_floor (-intVal mem a h L) ((2:ℤ)^P)
  have hn : ¬ (2:ℤ)^P<0 := not_lt.mpr (le_of_lt (pow_pos (by decide) _))
  simp only [floorDiv,ite_eq_right hn,Int.cast_neg,Int.cast_pow,Int.cast_ofNat,neg_div,Int.floor_neg] at he
  change ⌈(intVal mem a h L : ℝ)/(2:ℝ)^P⌉= _
  omega

end MinCostFlow.Num
