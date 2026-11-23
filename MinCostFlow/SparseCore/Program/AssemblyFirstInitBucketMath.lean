module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSide
public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.DivisionStepFacts
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# The bucket word of an edge: the arithmetic (`AssemblyFirstInitBucketMath`)

At the init of a branch, each edge `e` of the graph gets the word `bucketCode (bucketOf (wstr e ·
ℓ₀ e))` (`AsmSdMapsAt`, `AssemblyBranchSide.lean`). Here `wstr e = num / den` is a quotient of two
integers from P4's export, and `ℓ₀ e = len / 2 ^ P` is a fixed-point number. So the bucket is the
floor of `log₂ (num · len / (den · 2 ^ P))`. This file reduces it to integer steps that a machine
can do on numbers of many limbs (`AssemblyFirstInitBucket.lean`):

* the sign does not matter, since `log |x| = log x`. Let `X = |num| · len` and `Y = den`;
* if `X = 0`, the bucket is `0`;
* otherwise, with `a = ⌊log₂ X⌋` and `c = ⌊log₂ Y⌋`, the bucket is `a - (c + P + lt)`, where `lt`
  is `1` when `X · 2 ^ c < Y · 2 ^ a`, and `0` otherwise (`bucketOf_ratio`). The test compares the
  leading bits of `X` and `Y`, once their tops are aligned;
* the floor of `log₂` of a block of limbs of four bits is `4 (t - 1) + ⌊log₂ x⌋`, for the number `t`
  of limbs up to the top nonzero limb `x`, and `⌊log₂ x⌋` is a sum of three tests
  (`limbLog`, `natLog_unsignedVal_top`);
* `bucketCode` of `a - v` is `2 (a - v) + 2 (v - a) - [a < v]` in truncated subtraction
  (`bucketCode_natSub`).

The main result is `bucketCode_bucketOf_eq`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.SparseCore

/-- The floor of `log₂` of a nonzero limb of four bits, as three tests. -/
def limbLog (x : ℕ) : ℕ :=
  (if 1 < x then 1 else 0) + (if 3 < x then 1 else 0) + (if 7 < x then 1 else 0)

theorem limbLog_le_three (x : ℕ) : limbLog x ≤ 3 := by
  unfold limbLog
  split_ifs <;> omega

/-- `limbLog x` is the floor of `log₂ x` for `0 < x < 16`. -/
theorem limbLog_bounds {x : ℕ} (h0 : 0 < x) (h16 : x < 16) :
    2 ^ limbLog x ≤ x ∧ x < 2 ^ (limbLog x + 1) := by
  interval_cases x <;> decide

/-- A block of `t + 1` limbs of four bits whose top limb is not zero: the floor of `log₂` of its
value is `4 t` plus `limbLog` of the top limb. -/
theorem natLog_unsignedVal_top {mem : ℕ → ℕ} {p t : ℕ} (hv : Num.Valid mem p 4 (t + 1))
    (htop : 0 < mem (p + t)) :
    Nat.log 2 (Num.unsignedVal mem p 4 (t + 1)) = 4 * t + limbLog (mem (p + t)) := by
  have hx16 : mem (p + t) < 16 := by
    have := hv t (by omega)
    simpa [Num.base] using this
  obtain ⟨hlo, hhi⟩ := limbLog_bounds htop hx16
  have hsplit := Num.unsignedVal_split mem p 4 t 1
  have h1 : Num.unsignedVal mem (p + t) 4 1 = mem (p + t) := by simp [Num.unsignedVal]
  have hlow : Num.unsignedVal mem p 4 t < Num.capacity 4 t :=
    Num.unsignedVal_lt (fun i hi => hv i (by omega))
  have hcap : Num.capacity 4 t = 2 ^ (4 * t) := by
    simp only [Num.capacity, Num.base, ← pow_mul]
  rw [hsplit, h1, hcap]
  rw [hcap] at hlow
  set u := Num.unsignedVal mem p 4 t
  set x := mem (p + t)
  set g := limbLog x
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · calc 2 ^ (4 * t + g) = 2 ^ (4 * t) * 2 ^ g := pow_add _ _ _
      _ ≤ 2 ^ (4 * t) * x := Nat.mul_le_mul_left _ hlo
      _ ≤ u + 2 ^ (4 * t) * x := Nat.le_add_left _ _
  · have hx1 : x + 1 ≤ 2 ^ (g + 1) := hhi
    calc u + 2 ^ (4 * t) * x < 2 ^ (4 * t) + 2 ^ (4 * t) * x := by omega
      _ = 2 ^ (4 * t) * (x + 1) := by ring
      _ ≤ 2 ^ (4 * t) * 2 ^ (g + 1) := Nat.mul_le_mul_left _ hx1
      _ = 2 ^ (4 * t + g + 1) := by rw [← pow_add]; ring_nf

/-- A bucket from bounds by powers of two. -/
theorem bucketOf_eq_of_zpow {r : ℝ} {k : ℤ} (hr : 0 < r) (h1 : (2 : ℝ) ^ k ≤ r)
    (h2 : r < (2 : ℝ) ^ (k + 1)) : bucketOf r = k := by
  unfold bucketOf
  rw [Real.log_div_log]
  have hfl := Real.floor_logb_natCast (b := 2) hr.le
  simp only [Nat.cast_ofNat] at hfl
  rw [hfl]
  have hb : 1 < (2 : ℕ) := by norm_num
  apply le_antisymm
  · have h2' : r < ((2 : ℕ) : ℝ) ^ (k + 1) := by simpa using h2
    have := (Int.lt_zpow_iff_log_lt hb hr).mp h2'
    omega
  · have h1' : ((2 : ℕ) : ℝ) ^ k ≤ r := by simpa using h1
    exact (Int.zpow_le_iff_le_log hb hr).mp h1'

/-- The sign does not change the bucket. -/
theorem bucketOf_abs (x : ℝ) : bucketOf |x| = bucketOf x := by
  unfold bucketOf
  rw [Real.log_abs]

theorem bucketOf_zero : bucketOf 0 = 0 := by
  simp [bucketOf]

/-- **The bucket of a quotient of naturals**, from the floors of their `log₂` and one test. -/
theorem bucketOf_ratio {X Y : ℕ} (P : ℕ) (hX : 0 < X) (hY : 0 < Y) :
    bucketOf ((X : ℝ) / ((Y : ℝ) * 2 ^ P)) =
      (Nat.log 2 X : ℤ) - ((Nat.log 2 Y + P +
        (if X * 2 ^ Nat.log 2 Y < Y * 2 ^ Nat.log 2 X then 1 else 0) : ℕ) : ℤ) := by
  set a := Nat.log 2 X with ha
  set c := Nat.log 2 Y with hc
  set lt : ℕ := if X * 2 ^ c < Y * 2 ^ a then 1 else 0 with hlt
  set v := c + P + lt with hv
  have haX : 2 ^ a ≤ X := Nat.pow_log_le_self 2 (by omega)
  have hXa : X < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
  have hcY : 2 ^ c ≤ Y := Nat.pow_log_le_self 2 (by omega)
  have hYc : Y < 2 ^ (c + 1) := Nat.lt_pow_succ_log_self (by norm_num) Y
  have hpa : 0 < 2 ^ a := by positivity
  have hpc : 0 < 2 ^ c := by positivity
  -- the two bounds, in `ℕ`, before the factor `2 ^ P`
  have hlow : 2 ^ a * Y ≤ X * 2 ^ c * 2 ^ lt := by
    by_cases h : X * 2 ^ c < Y * 2 ^ a
    · have hl : lt = 1 := by simp [hlt, h]
      rw [hl, pow_one]
      have hY2 : Y ≤ 2 ^ c * 2 := by rw [pow_succ] at hYc; omega
      calc 2 ^ a * Y ≤ 2 ^ a * (2 ^ c * 2) := Nat.mul_le_mul_left _ hY2
        _ ≤ X * (2 ^ c * 2) := Nat.mul_le_mul_right _ haX
        _ = X * 2 ^ c * 2 := by ring
    · have hl : lt = 0 := by simp [hlt, h]
      rw [hl, pow_zero, mul_one, mul_comm]
      omega
  have hhigh : X * 2 ^ c * 2 ^ lt < 2 ^ (a + 1) * Y := by
    by_cases h : X * 2 ^ c < Y * 2 ^ a
    · have hl : lt = 1 := by simp [hlt, h]
      rw [hl, pow_one, pow_succ]
      nlinarith
    · have hl : lt = 0 := by simp [hlt, h]
      rw [hl, pow_zero, mul_one]
      calc X * 2 ^ c < 2 ^ (a + 1) * 2 ^ c := Nat.mul_lt_mul_of_pos_right hXa hpc
        _ ≤ 2 ^ (a + 1) * Y := Nat.mul_le_mul_left _ hcY
  have hlowN : 2 ^ a * (Y * 2 ^ P) ≤ X * 2 ^ v := by
    calc 2 ^ a * (Y * 2 ^ P) = (2 ^ a * Y) * 2 ^ P := by ring
      _ ≤ (X * 2 ^ c * 2 ^ lt) * 2 ^ P := Nat.mul_le_mul_right _ hlow
      _ = X * 2 ^ v := by rw [hv, pow_add, pow_add]; ring
  have hhighN : X * 2 ^ v < 2 ^ (a + 1) * (Y * 2 ^ P) := by
    calc X * 2 ^ v = (X * 2 ^ c * 2 ^ lt) * 2 ^ P := by rw [hv, pow_add, pow_add]; ring
      _ < (2 ^ (a + 1) * Y) * 2 ^ P := Nat.mul_lt_mul_of_pos_right hhigh (by positivity)
      _ = 2 ^ (a + 1) * (Y * 2 ^ P) := by ring
  have hpow : ∀ n : ℕ, (2 : ℝ) ^ ((n : ℤ) - (v : ℤ)) = (2 : ℝ) ^ n / (2 : ℝ) ^ v := by
    intro n
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
  have hYP : (0 : ℝ) < (Y : ℝ) * 2 ^ P := by positivity
  have hv0 : (0 : ℝ) < (2 : ℝ) ^ v := by positivity
  apply bucketOf_eq_of_zpow (by positivity)
  · rw [hpow a, div_le_div_iff₀ hv0 hYP]
    exact_mod_cast hlowN
  · have hk : (a : ℤ) - (v : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) - (v : ℤ) := by push_cast; ring
    rw [hk, hpow (a + 1), div_lt_div_iff₀ hYP hv0]
    exact_mod_cast hhighN

/-- `bucketCode` of a difference of naturals, in truncated subtraction. -/
theorem bucketCode_natSub (a v : ℕ) :
    bucketCode ((a : ℤ) - (v : ℤ)) =
      2 * (a - v) + 2 * (v - a) - (if a < v then 1 else 0) := by
  unfold bucketCode
  by_cases h : a < v
  · have h1 : ¬ (0 ≤ (a : ℤ) - (v : ℤ)) := by omega
    have h2 : (-((a : ℤ) - (v : ℤ))).toNat = v - a := by omega
    simp only [h1, h2, h, ↓reduceIte]
    omega
  · have h1 : 0 ≤ (a : ℤ) - (v : ℤ) := by omega
    have h2 : ((a : ℤ) - (v : ℤ)).toNat = a - v := by omega
    simp only [h1, h2, h, ↓reduceIte]
    omega

/-- **The bucket word of an edge.** For integers `num`, `den > 0` and `len > 0`, let
`X = |num| · len`. If the machine finds `t` with `0 < t` exactly when `0 < X`, the floor `a` of
`log₂ X` when `0 < t`, the floor `c` of `log₂ den`, and the test `lt`, then the code of the bucket
of `num / den · len / 2 ^ P` is the expression it computes. -/
theorem bucketCode_bucketOf_eq {num den len : ℤ} {P t a c lt : ℕ} (hden : 0 < den)
    (hlen : 0 < len) (ht : 0 < t ↔ 0 < num.natAbs * len.toNat)
    (ha : 0 < t → a = Nat.log 2 (num.natAbs * len.toNat))
    (hc : c = Nat.log 2 den.toNat)
    (hlt : lt = if num.natAbs * len.toNat * 2 ^ c < den.toNat * 2 ^ a then 1 else 0) :
    bucketCode (bucketOf ((num : ℝ) / (den : ℝ) * ((len : ℝ) / 2 ^ P))) =
      (if 0 < t then 1 else 0) *
        (2 * (a - (c + P + lt)) + 2 * ((c + P + lt) - a) -
          (if a < c + P + lt then 1 else 0)) := by
  set X := num.natAbs * len.toNat with hX
  have hdenR : ((den.toNat : ℕ) : ℝ) = (den : ℝ) := by
    have : ((den.toNat : ℕ) : ℤ) = den := Int.toNat_of_nonneg hden.le
    exact_mod_cast this
  have hlenR : ((len.toNat : ℕ) : ℝ) = (len : ℝ) := by
    have : ((len.toNat : ℕ) : ℤ) = len := Int.toNat_of_nonneg hlen.le
    exact_mod_cast this
  have habs : |(num : ℝ) / (den : ℝ) * ((len : ℝ) / 2 ^ P)| =
      (X : ℝ) / ((den.toNat : ℝ) * 2 ^ P) := by
    have hd : (0 : ℝ) < den := by exact_mod_cast hden
    have hl : (0 : ℝ) < len := by exact_mod_cast hlen
    rw [abs_mul, abs_div, abs_div, abs_of_pos hd, abs_of_pos hl,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ P), hX, hdenR]
    push_cast
    rw [hlenR, Nat.cast_natAbs, Int.cast_abs]
    field_simp
  by_cases h0 : 0 < t
  · have hXpos : 0 < X := ht.mp h0
    have hYpos : 0 < den.toNat := by omega
    simp only [h0, ↓reduceIte, one_mul]
    rw [← bucketOf_abs, habs, bucketOf_ratio P hXpos hYpos, ← ha h0, ← hc,
      ← hlt, show c + P + lt = c + P + lt from rfl]
    exact bucketCode_natSub a (c + P + lt)
  · have hX0 : X = 0 := by
      by_contra hne
      exact h0 (ht.mpr (Nat.pos_of_ne_zero hne))
    have hzero : (num : ℝ) / (den : ℝ) * ((len : ℝ) / 2 ^ P) = 0 := by
      rw [← abs_eq_zero, habs, hX0]
      simp
    simp only [h0, ↓reduceIte, zero_mul]
    rw [hzero, bucketOf_zero]
    rfl

end MinCostFlow.SparseCore.Program
