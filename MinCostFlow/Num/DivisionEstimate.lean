module

public import MinCostFlow.Num.Representation
import Mathlib.Tactic

/-!
# A quotient-digit estimate for long division

Use the leading two divisor limbs and the leading three numerator limbs. The leading
divisor pair is at least the limb base, even without normalization. The estimate is
therefore the quotient digit or one larger. One comparison and decrement correct it.
The three-limb numerator fits in a word when `3*h+2 ≤ w`.
-/

public section
namespace MinCostFlow.Num

/-- Truncating after two leading divisor limbs overestimates a quotient digit by at most one. -/
theorem quotient_digit_estimate {B C D V T X vl xl : ℕ}
    (hB : 1 < B) (hC : 0 < C) (hD : B ≤ D)
    (hV : V = D * C + vl) (hvl : vl < C)
    (hX : X = T * C + xl) (hxl : xl < C) (hbound : X < V * B) :
    X / V ≤ min (B - 1) (T / D) ∧ min (B - 1) (T / D) ≤ X / V + 1 := by
  have hVp : 0 < V := by nlinarith only [hV, hD, hC, hB]
  have hDp : 0 < D := by omega
  have hqnonneg : 0 ≤ X / V := Nat.zero_le _
  have hqB : X / V < B := (Nat.div_lt_iff_lt_mul hVp).mpr (by simpa only [Nat.mul_comm] using hbound)
  have hqV : (X / V) * V ≤ X := Nat.div_mul_le_self _ _
  have hDC : D * C ≤ V := by omega
  have hm := Nat.mul_le_mul_left (X / V) hDC
  have hlowprod : ((X / V) * D) * C < (T + 1) * C := by
    nlinarith only [hm, hqV, hX, hxl]
  have hlow : (X / V) * D ≤ T := by
    by_contra hn
    have hmono := Nat.mul_le_mul_right C (show T + 1 ≤ (X / V) * D by omega)
    omega
  have hqT : X / V ≤ T / D := (Nat.le_div_iff_mul_le hDp).mpr hlow
  have hupperV : X < (X / V + 1) * V := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ X hVp
  have hVle : V ≤ D * C + C := by omega
  have hupper := Nat.mul_le_mul_left (X / V + 1) hVle
  have hTprod : T * C < ((X / V + 1) * D + (X / V + 1)) * C := by
    nlinarith only [hupperV, hupper, hX]
  have hT : T ≤ (X / V + 1) * D + X / V := by
    by_contra hn
    have hmono := Nat.mul_le_mul_right C
      (show (X / V + 1) * D + (X / V + 1) ≤ T by omega)
    omega
  have hqD : X / V < D := lt_of_lt_of_le hqB hD
  have hTlt : T < (X / V + 2) * D := by nlinarith only [hT, hqD]
  have hTdiv : T / D ≤ X / V + 1 := by
    have he := (Nat.div_lt_iff_lt_mul hDp).mpr hTlt
    omega
  exact ⟨le_min (by omega) hqT, le_trans (min_le_right _ _) hTdiv⟩

/-- Comparing an estimated multiple and decrementing at most once gives the exact digit. -/
theorem correct_quotient_digit {X V estimate : ℕ} (hV : 0 < V)
    (hlo : X / V ≤ estimate) (hhi : estimate ≤ X / V + 1) :
    (if X < estimate * V then estimate - 1 else estimate) = X / V := by
  have hqnonneg : 0 ≤ X / V := Nat.zero_le _
  split_ifs with hover
  · have hnot : ¬ estimate ≤ X / V := by
      intro he
      have hm := Nat.mul_le_mul_right V he
      have hq := Nat.div_mul_le_self X V
      omega
    omega
  · have he : estimate ≤ X / V := (Nat.le_div_iff_mul_le hV).mpr (by omega)
    omega

private theorem join_mul_add_lt {B C x y : ℕ} (hx : x < C) (hy : y < B) :
    x * B + y < C * B := by
  have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hx)
  nlinarith only [hm, hy]

/-- Three limbs, combined into one natural number, fit in a word with the stated slack. -/
theorem three_limbs_lt_word {h w x y z : ℕ} (hw : 3 * h + 2 ≤ w)
    (hx : x < base h) (hy : y < base h) (hz : z < base h) :
    (x * base h + y) * base h + z < 2 ^ w := by
  have h2 := join_mul_add_lt hx hy
  have h3 := join_mul_add_lt h2 hz
  have he : (base h * base h) * base h = 2 ^ (3 * h) := by
    calc
      _ = base h ^ 3 := by ring
      _ = _ := by rw [base, ← pow_mul, Nat.mul_comm h 3]
  calc
    _ < (base h * base h) * base h := h3
    _ = 2 ^ (3 * h) := he
    _ < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)

end MinCostFlow.Num
