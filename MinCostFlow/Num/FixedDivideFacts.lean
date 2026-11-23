module

public import MinCostFlow.Num.DivisionSigns
import MinCostFlow.Num.ShiftFacts
import Mathlib.Tactic

/-!
# Workspace width for fixed-point division

If the divisor is a stored integer and the quotient fits the output, the scaled
numerator fits three times the output width. Thus division needs only a constant
multiple of the limb count even when the precision parameter is large.
-/

public section
namespace MinCostFlow.Num

/-- Increasing the limb count preserves the signed range. -/
theorem fits_of_length_le {h L K : ℕ} {x : ℤ} (hLK : L≤K) (hx : Fits h L x) : Fits h K x := by
  have he : capacity h L≤capacity h K := by
    unfold capacity
    exact Nat.pow_le_pow_right (base_pos h) hLK
  have hei : (capacity h L : ℤ)≤capacity h K := by exact_mod_cast he
  obtain ⟨hlo,hhi⟩ := hx
  constructor <;> omega

/-- A quotient fitting `L` limbs bounds its numerator by three limb blocks. -/
theorem fits_numerator_of_floorDiv_fits {h L : ℕ} {x d : ℤ}
    (hh : 0<h) (hd : d≠0) (hD : d.natAbs<capacity h L)
    (hq : Fits h L (floorDiv x d)) : Fits h (3*L) x := by
  have hL : 0<L := by
    by_contra he
    have he0 : L=0 := by omega
    rw [he0,capacity_zero] at hD
    have hp := Int.natAbs_pos.mpr hd
    omega
  have hC : 2≤capacity h L := by
    have hb : 2≤base h := Nat.succ_le_of_lt (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide))
    have he := Nat.pow_le_pow_right (base_pos h) (show 1≤L by omega)
    exact le_trans hb (by simpa only [pow_one,capacity] using he)
  have hDp : (0:ℤ)<d.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hd
  have hDC : (d.natAbs:ℤ)<capacity h L := by exact_mod_cast hD
  have hCi : (2:ℤ)≤capacity h L := by exact_mod_cast hC
  have he : floorDiv x d=(if d<0 then -x else x)/(d.natAbs:ℤ) := by
    unfold floorDiv
    by_cases hn : d<0
    · simp only [hn,ite_eq_left,Int.natCast_natAbs,abs_of_neg hn]
    · simp only [hn,ite_false,Int.natCast_natAbs,abs_of_nonneg (show 0≤d by omega)]
  have hb := (Int.ediv_eq_iff_of_pos hDp).mp he.symm
  obtain ⟨hql,hqu⟩ := hq
  have hqlo : -(capacity h L : ℤ)+1≤floorDiv x d := by omega
  have hqhi : floorDiv x d+1≤(capacity h L : ℤ) := by omega
  have hlo := mul_le_mul_of_nonneg_right hqlo (le_of_lt hDp)
  have hhi := mul_le_mul_of_nonneg_right hqhi (le_of_lt hDp)
  have hlowprod := mul_le_mul_of_nonpos_left (le_of_lt hDC)
    (show -(capacity h L : ℤ)+1≤0 by omega)
  have hhighprod := mul_le_mul_of_nonneg_left (le_of_lt hDC)
    (show (0:ℤ)≤capacity h L by omega)
  have hAlo : -(capacity h L : ℤ)^2 < (if d<0 then -x else x) := by
    nlinarith only [hb.1,hlo,hlowprod,hCi]
  have hAhi : (if d<0 then -x else x) < (capacity h L : ℤ)^2 := by
    nlinarith only [hb.2,hhi,hhighprod]
  have hxlo : -(capacity h L : ℤ)^2<x := by split_ifs at hAlo hAhi <;> omega
  have hxhi : x<(capacity h L : ℤ)^2 := by split_ifs at hAlo hAhi <;> omega
  have hcube : 2*(capacity h L : ℤ)^2≤(capacity h L : ℤ)^3 := by
    have hm := mul_nonneg (show (0:ℤ)≤(capacity h L : ℤ)-2 by omega) (sq_nonneg (capacity h L : ℤ))
    nlinarith only [hm]
  have heC : capacity h (3*L)=capacity h L*capacity h L*capacity h L := by
    rw [show 3*L=(L+L)+L by omega,capacity_add,capacity_add]
  change -(capacity h (3*L) : ℤ)≤2*x ∧ 2*x<(capacity h (3*L) : ℤ)
  rw [heC]
  push_cast
  constructor <;> nlinarith only [hxlo,hxhi,hcube]

end MinCostFlow.Num
