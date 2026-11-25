module

public import MinCostFlow.Narrow.CostDefs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Reduced costs from cost bits and word-size bounds (Lemma 5)

This file proves the integer bit-splitting identities for signed edge costs,
establishes Lemma 5 (that the half-unit reduced cost `X = ⌊2 ĉ / δ⌋` updates
from round `j` to `j + 1` via `2 * X + bit - 4 * (Δy tail - Δy head)` without
storing potentials), and proves the explicit word-size bounds on `halfCost`,
rounded slot costs, and dual potentials.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

private lemma int_ediv_mul_two (c : ℤ) (d : ℤ) (hd : 0 < d) :
    c / (d * 2) = (c / d) / 2 := by
  have h1 : c = d * (c / d) + c % d := (Int.mul_ediv_add_emod c d).symm
  have h2 : c / d = 2 * ((c / d) / 2) + (c / d) % 2 := (Int.mul_ediv_add_emod (c / d) 2).symm
  have hr1_lo : 0 ≤ c % d := Int.emod_nonneg c (ne_of_gt hd)
  have hr1_hi : c % d < d := Int.emod_lt_of_pos c hd
  have hr2_lo : 0 ≤ (c / d) % 2 := Int.emod_nonneg _ (by decide)
  have hr2_hi : (c / d) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
  have hrem_lo : 0 ≤ d * ((c / d) % 2) + c % d := by
    have : 0 ≤ d * ((c / d) % 2) := mul_nonneg hd.le hr2_lo
    linarith only [this, hr1_lo]
  have hrem_hi : d * ((c / d) % 2) + c % d < d * 2 := by
    have hle1 : (c / d) % 2 ≤ 1 := by omega
    have : d * ((c / d) % 2) ≤ d * 1 := mul_le_mul_of_nonneg_left hle1 hd.le
    linarith only [this, hr1_hi]
  have hdecomp : c = (d * ((c / d) % 2) + c % d) + (d * 2) * ((c / d) / 2) := by
    calc
      c = d * (2 * ((c / d) / 2) + (c / d) % 2) + c % d := by rw [← h2, ← h1]
      _ = (d * ((c / d) % 2) + c % d) + (d * 2) * ((c / d) / 2) := by ring
  have hd2 : (d * 2) ≠ 0 := ne_of_gt (by linarith only [hd])
  conv_lhs => rw [hdecomp]
  rw [Int.add_mul_ediv_left _ _ hd2,
    Int.ediv_eq_zero_of_lt hrem_lo hrem_hi, zero_add]

/-- Signed floor-division bit identity: dropping one low bit doubles the
shifted quotient and adds `(c / 2 ^ (k - 1)) % 2`. Holds for negative `c` as
well because Lean's `Int` division rounds down for positive divisors. -/
theorem int_ediv_two_pow_sub_one (c : ℤ) (k : ℕ) (hk : 1 ≤ k) :
    c / (2 ^ (k - 1) : ℤ) = 2 * (c / (2 ^ k : ℤ)) + (c / (2 ^ (k - 1) : ℤ)) % 2 := by
  rcases k with _ | s
  · omega
  · simp only [Nat.add_sub_cancel]
    have hd : (0 : ℤ) < (2 ^ s : ℤ) := pow_pos (by decide) s
    rw [pow_succ, int_ediv_mul_two c (2 ^ s : ℤ) hd, Int.mul_ediv_add_emod]

/-- Unified bit-scaling recurrence for `costScaled` across all signed shifts
`k : ℤ` (positive, zero, or negative). -/
theorem costScaled_sub_one (c k : ℤ) :
    costScaled c (k - 1) = 2 * costScaled c k + costBit c (k - 1) := by
  by_cases h1 : 1 ≤ k
  · have hk0 : 0 ≤ k := by omega
    have hk1 : 0 ≤ k - 1 := by omega
    have hto : (k - 1).toNat = k.toNat - 1 := by omega
    have hpos : 1 ≤ k.toNat := by omega
    simp only [costScaled, costBit, hk0, hk1, ↓reduceIte, hto]
    exact int_ediv_two_pow_sub_one c k.toNat hpos
  · by_cases h0 : k = 0
    · subst h0
      simp only [costScaled, costBit, le_refl, ↓reduceIte, Int.toNat_zero, pow_zero, Int.ediv_one,
        show ¬ (0 : ℤ) ≤ 0 - 1 by omega, show (-(0 - 1 : ℤ)).toNat = 1 by decide, pow_one, add_zero]
      ring
    · have hkneg : ¬ (0 ≤ k) := by omega
      have hk1neg : ¬ (0 ≤ k - 1) := by omega
      have hto : (-(k - 1)).toNat = (-k).toNat + 1 := by omega
      simp only [costScaled, costBit, hkneg, hk1neg, ↓reduceIte, hto, pow_succ, add_zero]
      ring

/-- Every cost bit lies in `{0, 1}`. -/
theorem costBit_bounds (c k : ℤ) : 0 ≤ costBit c k ∧ costBit c k ≤ 1 := by
  unfold costBit
  split
  · have h1 : 0 ≤ (c / (2 ^ k.toNat : ℤ)) % 2 := Int.emod_nonneg _ (by decide)
    have h2 : (c / (2 ^ k.toNat : ℤ)) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
    omega
  · omega

/-- Exact real floor characterization of `costScaled`. -/
theorem floor_div_two_zpow (c k : ℤ) :
    Int.floor ((c : ℝ) / (2 : ℝ) ^ k) = costScaled c k := by
  by_cases hk : 0 ≤ k
  · have hkeq : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk).symm
    simp only [costScaled, hk, ↓reduceIte]
    rw [Int.floor_eq_iff]
    let d : ℤ := 2 ^ k.toNat
    have hd_int : (0 : ℤ) < d := pow_pos (by decide) k.toNat
    have hd_real : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_int
    have hpow : (2 : ℝ) ^ k = (d : ℝ) := by
      conv_lhs => rw [hkeq]
      rw [zpow_natCast]
      simp [d]
    rw [hpow, le_div_iff₀ hd_real, div_lt_iff₀ hd_real]
    have hdiv := Int.mul_ediv_add_emod c d
    have hr0 : 0 ≤ c % d := Int.emod_nonneg c (ne_of_gt hd_int)
    have hr1 : c % d < d := Int.emod_lt_of_pos c hd_int
    have hlo : (c / d) * d ≤ c := by linarith only [hdiv, hr0]
    have hhi : c < (c / d + 1) * d := by linarith only [hdiv, hr1]
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  · have hkeq : k = -((-k).toNat : ℤ) := by omega
    simp only [costScaled, hk, ↓reduceIte]
    have hpow : (c : ℝ) / (2 : ℝ) ^ k = ((c * (2 ^ (-k).toNat : ℤ) : ℤ) : ℝ) := by
      conv_lhs => rw [hkeq]
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul]
      push_cast
      rfl
    rw [hpow, Int.floor_intCast]

/-- Initialization identity: when `|c| < 2 ^ L`, `costScaled c L` is `-1` for
negative `c` and `0` for nonnegative `c`. -/
theorem costScaled_init (c : ℤ) (L : ℕ) (hc : c.natAbs < 2 ^ L) :
    costScaled c (L : ℤ) = if c < 0 then -1 else 0 := by
  have hk : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
  simp only [costScaled, hk, ↓reduceIte, Int.toNat_natCast]
  have hd : (0 : ℤ) < (2 ^ L : ℤ) := pow_pos (by decide) L
  have hbound : -(2 ^ L : ℤ) < c ∧ c < (2 ^ L : ℤ) := by
    have hc' : (c.natAbs : ℤ) < (2 ^ L : ℤ) := by exact_mod_cast hc
    omega
  split
  · rename_i hneg
    have hdecomp : c = (c + 2 ^ L) + (2 ^ L : ℤ) * (-1) := by ring
    have hlo : 0 ≤ c + 2 ^ L := by omega
    have hhi : c + 2 ^ L < (2 ^ L : ℤ) := by omega
    rw [hdecomp, Int.add_mul_ediv_left _ _ (ne_of_gt hd),
      Int.ediv_eq_zero_of_lt hlo hhi, zero_add]
  · rename_i hnonneg
    exact Int.ediv_eq_zero_of_lt (by omega) hbound.2

/-- Exact relation between the real floor `⌊2 ĉ / δ_j⌋` and `costScaled` minus
twice the integer potential difference. -/
theorem halfCost_eq_floor (I : Circulation) (L j : ℕ) (Y : Fin I.n → ℤ)
    (e : Fin I.m) :
    Int.floor (2 * I.reducedCost (fun v => stageDelta L j * (Y v : ℝ)) e / stageDelta L j) =
      costScaled (I.cost e) ((L : ℤ) - (j : ℤ)) - 2 * (Y (I.tail e) - Y (I.head e)) := by
  have hδ : (0 : ℝ) < stageDelta L j := zpow_pos (by norm_num) _
  have hδ_ne : stageDelta L j ≠ 0 := ne_of_gt hδ
  have hhalf : stageDelta L j / 2 = (2 : ℝ) ^ ((L : ℤ) - (j : ℤ)) := by
    unfold stageDelta
    have hexp : (((L + 1 : ℕ) : ℤ) - (j : ℤ)) = ((L : ℤ) - (j : ℤ)) + 1 := by omega
    rw [hexp, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have harg : 2 * I.reducedCost (fun v => stageDelta L j * (Y v : ℝ)) e / stageDelta L j =
      (I.cost e : ℝ) / (2 : ℝ) ^ ((L : ℤ) - (j : ℤ)) -
        ((2 * (Y (I.tail e) - Y (I.head e)) : ℤ) : ℝ) := by
    simp only [Circulation.reducedCost, Circulation.potentialDifference, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sub]
    rw [← hhalf]
    field_simp [hδ_ne]
  rw [harg, Int.floor_sub_intCast, floor_div_two_zpow]

/-- Lemma 5 (reduced costs from bits): advancing from round `j` to `j + 1` with
dual update `Y' = 2 * (Y + dy)` updates the half-unit reduced cost by
`2 * X + costBit (I.cost e) (L - (j + 1)) - 4 * (dy tail - dy head)`. -/
theorem halfCost_step_identity (I : Circulation) (L j : ℕ)
    (Y dy : Fin I.n → ℤ) (e : Fin I.m) :
    costScaled (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
        2 * (2 * (Y (I.tail e) + dy (I.tail e)) - 2 * (Y (I.head e) + dy (I.head e))) =
      2 * (costScaled (I.cost e) ((L : ℤ) - (j : ℤ)) - 2 * (Y (I.tail e) - Y (I.head e))) +
        costBit (I.cost e) ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) -
        4 * (dy (I.tail e) - dy (I.head e)) := by
  have hexp : ((L : ℤ) - ((j + 1 : ℕ) : ℤ)) = ((L : ℤ) - (j : ℤ)) - 1 := by omega
  rw [hexp, costScaled_sub_one]
  ring

/-- `stepHalfCost` always stores a value of magnitude strictly below `Θ`
(when `0 < Θ`). -/
theorem stepHalfCost_snd_abs_lt (Θ : ℕ) (hΘ : 0 < Θ) (fr : FreezeState)
    (x bit dyDiff : ℤ) :
    (stepHalfCost Θ fr x bit dyDiff).2.natAbs < Θ := by
  cases fr with
  | pos => simpa [stepHalfCost] using hΘ
  | neg => simpa [stepHalfCost] using hΘ
  | none =>
    dsimp only [stepHalfCost]
    split
    · simpa using hΘ
    · split
      · simpa using hΘ
      · omega

/-- Intermediate word bound on `2 * x + bit - 4 * dyDiff` before the freeze
comparison. -/
theorem halfCost_next_raw_abs_le (m : ℕ) (x bit dyDiff : ℤ)
    (hx : x.natAbs < freezeThreshold m) (hbit : 0 ≤ bit ∧ bit ≤ 1)
    (hdy : dyDiff.natAbs ≤ upperClip m) :
    (2 * x + bit - 4 * dyDiff).natAbs ≤ 20 * upperClip m + 1 := by
  unfold freezeThreshold at hx
  omega

/-- `lowerClip m ≤ upperClip m` for all `m`. -/
theorem lowerClip_le_upperClip (m : ℕ) : lowerClip m ≤ upperClip m := by
  unfold lowerClip upperClip
  exact Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)

/-- Word bound on rounded forward slot costs: `≤ upperClip m`. -/
theorem roundedForwardCost_natAbs_le (m : ℕ) (fr : FreezeState) (x : ℤ) :
    (roundedForwardCost m fr x).natAbs ≤ upperClip m := by
  have hle : lowerClip m ≤ upperClip m := lowerClip_le_upperClip m
  cases fr with
  | pos => simp [roundedForwardCost]
  | neg => simpa [roundedForwardCost] using hle
  | none =>
    dsimp only [roundedForwardCost, clampInt]
    have : -(lowerClip m : ℤ) ≤ max (-(lowerClip m : ℤ)) (min ((x + 1) / 2) (upperClip m : ℤ)) ∧
        max (-(lowerClip m : ℤ)) (min ((x + 1) / 2) (upperClip m : ℤ)) ≤ (upperClip m : ℤ) := by
      refine ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
      omega
    omega

/-- Word bound on rounded reverse slot costs: `≤ upperClip m`. -/
theorem roundedReverseCost_natAbs_le (m : ℕ) (fr : FreezeState) (x : ℤ) :
    (roundedReverseCost m fr x).natAbs ≤ upperClip m := by
  have hle : lowerClip m ≤ upperClip m := lowerClip_le_upperClip m
  cases fr with
  | pos => simpa [roundedReverseCost] using hle
  | neg => simp [roundedReverseCost]
  | none =>
    dsimp only [roundedReverseCost, clampInt]
    have : -(lowerClip m : ℤ) ≤ max (-(lowerClip m : ℤ)) (min (-((x + 1) / 2)) (upperClip m : ℤ)) ∧
        max (-(lowerClip m : ℤ)) (min (-((x + 1) / 2)) (upperClip m : ℤ)) ≤ (upperClip m : ℤ) := by
      refine ⟨le_max_left _ _, max_le ?_ (min_le_right _ _)⟩
      omega
    omega

/-- Every rounded slot cost has magnitude at most `upperClip I.m`. -/
theorem narrowRoundedCosts_natAbs_le (I : Circulation)
    (fr : Fin I.m → FreezeState) (x : Fin I.m → ℤ) (a : Fin (I.m + I.m)) :
    (narrowRoundedCosts I fr x a).natAbs ≤ upperClip I.m := by
  refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
  · simpa only [narrowRoundedCosts, Fin.addCases_left] using
      roundedForwardCost_natAbs_le I.m (fr e) (x e)
  · simpa only [narrowRoundedCosts, Fin.addCases_right] using
      roundedReverseCost_natAbs_le I.m (fr e) (x e)

/-- Word bound on the round's dual potential and its edge differences when
`0 ≤ dy v ≤ (n - 1) * lowerClip m` on a compressed graph `n ≤ 2 * m`. -/
theorem dual_natAbs_le (n m : ℕ) (hn : n ≤ 2 * m) (dy : Fin n → ℤ)
    (hdy : ∀ v, 0 ≤ dy v ∧ dy v ≤ ((n - 1 : ℕ) : ℤ) * (lowerClip m : ℤ)) :
    (∀ v, (dy v).natAbs ≤ upperClip m) ∧
    ∀ u v, (dy u - dy v).natAbs ≤ upperClip m := by
  have hq : 2 * m ≤ 2 ^ costClipExp m := Nat.le_pow_clog (by decide) (2 * m)
  have hmul : (n - 1) * lowerClip m ≤ upperClip m := by
    unfold lowerClip upperClip
    rw [pow_add]
    calc
      (n - 1) * 2 ^ costPrecisionExp m ≤ (2 * m) * 2 ^ costPrecisionExp m :=
        Nat.mul_le_mul_right _ (by omega)
      _ ≤ 2 ^ costClipExp m * 2 ^ costPrecisionExp m := Nat.mul_le_mul_right _ hq
      _ = 2 ^ costPrecisionExp m * 2 ^ costClipExp m := Nat.mul_comm _ _
  have hbound : ∀ v, 0 ≤ dy v ∧ dy v ≤ (upperClip m : ℤ) := fun v =>
    ⟨(hdy v).1, le_trans (hdy v).2 (by exact_mod_cast hmul)⟩
  refine ⟨fun v => ?_, fun u v => ?_⟩
  · have hv := hbound v
    omega
  · have hu := hbound u
    have hv := hbound v
    omega

end MinCostFlow.Narrow
