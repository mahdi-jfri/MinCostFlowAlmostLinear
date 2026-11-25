module

public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Scaling.EpsilonOptimal
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import MinCostFlow.Narrow.CostBits
import MinCostFlow.Scaling.EpsilonExactness
import MinCostFlow.Scaling.ExpensiveArcs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Power-of-two units, half-unit rounding, and clipping (Items 1 and 2)

This file establishes the arithmetic properties of the power-of-two scales
`stageEps` and `stageDelta`, the clipping bounds `lowerClip`, `upperClip`, and
`freezeThreshold`, the half-unit rounding error `≤ δ_j / 2`, and the
rounding-error certificate required by Lemma C.7
(`epsilonOptimalWith_augment_of_rounded_signs`).
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- `stageEps L p j` is strictly positive. -/
theorem stageEps_pos (L p j : ℕ) : 0 < stageEps L p j :=
  zpow_pos (by norm_num) _

/-- `stageDelta L j` is strictly positive. -/
theorem stageDelta_pos (L j : ℕ) : 0 < stageDelta L j :=
  zpow_pos (by norm_num) _

/-- `stageEps` halves in each round. -/
theorem stageEps_succ (L p j : ℕ) :
    stageEps L p (j + 1) = stageEps L p j / 2 := by
  unfold stageEps
  have h : (((L + p + 1 : ℕ) : ℤ) - (j : ℤ)) =
      (((L + p + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) + 1 := by omega
  rw [h, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- `stageDelta` halves in each round. -/
theorem stageDelta_succ (L j : ℕ) :
    stageDelta L (j + 1) = stageDelta L j / 2 := by
  unfold stageDelta
  have h : (((L + 1 : ℕ) : ℤ) - (j : ℤ)) =
      (((L + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) + 1 := by omega
  rw [h, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- `ε_j = lowerClip m * δ_j`. -/
theorem stageEps_eq_lowerClip_mul_delta (L m j : ℕ) :
    stageEps L (costPrecisionExp m) j = (lowerClip m : ℝ) * stageDelta L j := by
  unfold stageEps stageDelta lowerClip
  have h : (((L + costPrecisionExp m + 1 : ℕ) : ℤ) - (j : ℤ)) =
      (costPrecisionExp m : ℤ) + (((L + 1 : ℕ) : ℤ) - (j : ℤ)) := by omega
  rw [h, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
  simp

/-- `lowerClip m ≥ (2 * m) ^ 8`. -/
theorem lowerClip_ge_pow8 (m : ℕ) : (2 * m) ^ 8 ≤ lowerClip m :=
  Nat.le_pow_clog (by decide) ((2 * m) ^ 8)

/-- `lowerClip m > 0`. -/
theorem lowerClip_pos (m : ℕ) : 0 < lowerClip m :=
  Nat.pow_pos (by decide)

/-- `lowerClip m < 2 * (2 * m) ^ 8` for `0 < m`. -/
theorem lowerClip_lt_two_mul_pow8 (m : ℕ) (hm : 0 < m) :
    lowerClip m < 2 * (2 * m) ^ 8 := by
  unfold lowerClip costPrecisionExp
  have hgt1 : 1 < (2 * m) ^ 8 := by
    have h2 : 2 ≤ 2 * m := by omega
    calc
      1 < 2 ^ 8 := by decide
      _ ≤ (2 * m) ^ 8 := Nat.pow_le_pow_left h2 8
  have hpos : 0 < Nat.clog 2 ((2 * m) ^ 8) := Nat.clog_pos (by decide) hgt1
  have hlt : 2 ^ (Nat.clog 2 ((2 * m) ^ 8) - 1) < (2 * m) ^ 8 :=
    Nat.pow_pred_clog_lt_self (by decide) hgt1
  have hpow : 2 ^ Nat.clog 2 ((2 * m) ^ 8) = 2 * 2 ^ (Nat.clog 2 ((2 * m) ^ 8) - 1) := by
    have h1 : Nat.clog 2 ((2 * m) ^ 8) = (Nat.clog 2 ((2 * m) ^ 8) - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ]
    ring
  omega

/-- `2 * m ≤ 2 ^ costClipExp m`. -/
theorem two_mul_le_two_pow_clipExp (m : ℕ) : 2 * m ≤ 2 ^ costClipExp m :=
  Nat.le_pow_clog (by decide) (2 * m)

/-- `2 ^ costClipExp m < 4 * m` for `0 < m`. -/
theorem two_pow_clipExp_lt_four_mul (m : ℕ) (hm : 0 < m) :
    2 ^ costClipExp m < 4 * m := by
  unfold costClipExp
  have hgt1 : 1 < 2 * m := by omega
  have hpos : 0 < Nat.clog 2 (2 * m) := Nat.clog_pos (by decide) hgt1
  have hlt : 2 ^ (Nat.clog 2 (2 * m) - 1) < 2 * m :=
    Nat.pow_pred_clog_lt_self (by decide) hgt1
  have hpow : 2 ^ Nat.clog 2 (2 * m) = 2 * 2 ^ (Nat.clog 2 (2 * m) - 1) := by
    have h1 : Nat.clog 2 (2 * m) = (Nat.clog 2 (2 * m) - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ]
    ring
  omega

/-- `n * lowerClip m ≤ upperClip m` on compressed instances `n ≤ 2 * m`. -/
theorem upperClip_ge_n_mul_lowerClip (n m : ℕ) (hn : n ≤ 2 * m) :
    n * lowerClip m ≤ upperClip m := by
  unfold upperClip lowerClip
  rw [pow_add, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (le_trans hn (two_mul_le_two_pow_clipExp m))

/-- `upperClip m ≤ (2 * m) ^ 10` for every `0 < m`, without padding arcs. -/
theorem upperClip_le_pow10 (m : ℕ) (hm : 0 < m) : upperClip m ≤ (2 * m) ^ 10 := by
  by_cases hm1 : m = 1
  · subst hm1
    decide
  · have hm2 : 2 ≤ m := by omega
    have hlo : lowerClip m ≤ 2 * (2 * m) ^ 8 := (lowerClip_lt_two_mul_pow8 m hm).le
    have hq : 2 ^ costClipExp m ≤ 2 * (2 * m) := by
      have := two_pow_clipExp_lt_four_mul m hm
      omega
    have h4 : 4 ≤ 2 * m := by omega
    calc
      upperClip m = lowerClip m * 2 ^ costClipExp m := by
        unfold upperClip lowerClip
        rw [pow_add]
      _ ≤ (2 * (2 * m) ^ 8) * (2 * (2 * m)) := Nat.mul_le_mul hlo hq
      _ = 4 * (2 * m) ^ 9 := by ring
      _ ≤ (2 * m) * (2 * m) ^ 9 := Nat.mul_le_mul_right _ h4
      _ = (2 * m) ^ 10 := by ring

/-- `freezeThreshold m > 0`. -/
theorem freezeThreshold_pos (m : ℕ) : 0 < freezeThreshold m := by
  unfold freezeThreshold upperClip
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

/-- `δ_j / 2 < ε_j / 2` for every `0 < m`. -/
theorem stageDelta_div_two_lt_half_eps (L m j : ℕ) (hm : 0 < m) :
    stageDelta L j / 2 < stageEps L (costPrecisionExp m) j / 2 := by
  rw [stageEps_eq_lowerClip_mul_delta]
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hlo : (2 : ℝ) ≤ (lowerClip m : ℝ) := by
    have h2 : 2 ≤ lowerClip m := le_trans (by decide : 2 ≤ 2 ^ 8)
      (le_trans (Nat.pow_le_pow_left (show 2 ≤ 2 * m by omega) 8) (lowerClip_ge_pow8 m))
    exact_mod_cast h2
  nlinarith only [hδ, hlo]

/-- Half-unit rounding error: for `X = ⌊2 c / δ⌋` and `r = (X + 1) / 2`,
`|c - r * δ| ≤ δ / 2`. -/
theorem half_unit_rounding_error (c δ : ℝ) (hδ : 0 < δ) :
    -(δ / 2) ≤ c - (((Int.floor (2 * c / δ) + 1) / 2 : ℤ) : ℝ) * δ ∧
    c - (((Int.floor (2 * c / δ) + 1) / 2 : ℤ) : ℝ) * δ ≤ δ / 2 := by
  set X : ℤ := Int.floor (2 * c / δ)
  set r : ℤ := (X + 1) / 2
  have hfl : (X : ℝ) ≤ 2 * c / δ := Int.floor_le (2 * c / δ)
  have hlt : 2 * c / δ < (X : ℝ) + 1 := Int.lt_floor_add_one (2 * c / δ)
  have hlo_c : (X : ℝ) * δ ≤ 2 * c := (le_div_iff₀ hδ).mp hfl
  have hhi_c : 2 * c < ((X : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp hlt
  have hdiv : 2 * r + (X + 1) % 2 = X + 1 := Int.mul_ediv_add_emod (X + 1) 2
  have hmod0 : 0 ≤ (X + 1) % 2 := Int.emod_nonneg _ (by decide)
  have hmod1 : (X + 1) % 2 < 2 := Int.emod_lt_of_pos _ (by decide)
  have hX_lo : 2 * r - 1 ≤ X := by omega
  have hX_hi : X ≤ 2 * r := by omega
  have hX_lo_r : 2 * (r : ℝ) - 1 ≤ (X : ℝ) := by exact_mod_cast hX_lo
  have hX_hi_r : (X : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hX_hi
  constructor <;> nlinarith only [hδ, hlo_c, hhi_c, hX_lo_r, hX_hi_r]

/-- For an active forward arc in an `ε_j`-optimal state (`-ε_j < c`), the
unclipped half-unit rounded cost is at least `-lowerClip m`. -/
theorem unfrozen_active_lower_ge_fwd (L m j : ℕ) (c : ℝ)
    (hc : -(stageEps L (costPrecisionExp m) j) < c) :
    -(lowerClip m : ℤ) ≤ (Int.floor (2 * c / stageDelta L j) + 1) / 2 := by
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have heps : stageEps L (costPrecisionExp m) j = (lowerClip m : ℝ) * stageDelta L j :=
    stageEps_eq_lowerClip_mul_delta L m j
  rw [heps] at hc
  have hgt : ((-(2 * (lowerClip m : ℤ)) : ℤ) : ℝ) < 2 * c / stageDelta L j := by
    rw [lt_div_iff₀ hδ]
    push_cast
    nlinarith only [hc]
  have hfloor : -(2 * (lowerClip m : ℤ)) ≤ Int.floor (2 * c / stageDelta L j) :=
    Int.le_floor.mpr hgt.le
  omega

/-- For an active reverse arc in an `ε_j`-optimal state (`-ε_j < -c`), the
negated half-unit rounded cost is at least `-lowerClip m`. -/
theorem unfrozen_active_lower_ge_rev (L m j : ℕ) (c : ℝ)
    (hc : -(stageEps L (costPrecisionExp m) j) < -c) :
    -(lowerClip m : ℤ) ≤ -((Int.floor (2 * c / stageDelta L j) + 1) / 2) := by
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have heps : stageEps L (costPrecisionExp m) j = (lowerClip m : ℝ) * stageDelta L j :=
    stageEps_eq_lowerClip_mul_delta L m j
  rw [heps] at hc
  have hlt : 2 * c / stageDelta L j < ((2 * (lowerClip m : ℤ) : ℤ) : ℝ) := by
    rw [div_lt_iff₀ hδ]
    push_cast
    nlinarith only [hc]
  have hfloor : Int.floor (2 * c / stageDelta L j) < 2 * (lowerClip m : ℤ) :=
    Int.floor_lt.mpr hlt
  omega

/-- Every rounded slot cost is at least `-lowerClip I.m`. -/
theorem narrowRoundedCosts_lower_bound (I : Circulation)
    (fr : Fin I.m → FreezeState) (x : Fin I.m → ℤ) (a : Fin (I.m + I.m)) :
    -(lowerClip I.m : ℤ) ≤ narrowRoundedCosts I fr x a := by
  have hle : lowerClip I.m ≤ upperClip I.m := lowerClip_le_upperClip I.m
  refine Fin.addCases (m := I.m) (n := I.m) (fun e => ?_) (fun e => ?_) a
  · simp only [narrowRoundedCosts, Fin.addCases_left]
    cases fr e with
    | none => exact le_max_left _ _
    | pos => dsimp only [roundedForwardCost]; omega
    | neg => exact le_rfl
  · simp only [narrowRoundedCosts, Fin.addCases_right]
    cases fr e with
    | none => exact le_max_left _ _
    | pos => exact le_rfl
    | neg => dsimp only [roundedReverseCost]; omega

/-- Any slot whose cost in `narrowRoundInstance I s` equals `upperClip I.m`
receives zero flow in every optimal integral circulation of that instance. -/
theorem narrowRoundedCosts_optimal_zero_of_eq_upperClip (I : Circulation)
    (_hm : 0 < I.m) (hn : I.n ≤ 2 * I.m) (s : NarrowCostState I)
    (g : Fin (I.m + I.m) → ℤ)
    (hg : (narrowRoundInstance I s).Optimal (fun a => (g a : ℝ)))
    (a : Fin (I.m + I.m))
    (hcost : (narrowRoundInstance I s).cost a = (upperClip I.m : ℤ)) :
    g a = 0 := by
  have hCpos : (0 : ℤ) < (lowerClip I.m : ℤ) := Int.natCast_pos.mpr (lowerClip_pos I.m)
  have hge : (I.n : ℤ) * (lowerClip I.m : ℤ) ≤ (upperClip I.m : ℤ) := by
    exact_mod_cast upperClip_ge_n_mul_lowerClip I.n I.m hn
  exact (narrowRoundInstance I s).optimal_zero_on_expensive_arc g hg
    (lowerClip I.m : ℤ) hCpos
    (narrowRoundedCosts_lower_bound I s.frozen s.halfCost) a
    (by rw [hcost]; exact hge)

/-- Rounding-error certificate for Lemma C.7: under `ε_j`-optimality and the
unfrozen/frozen state invariants, every active slot satisfies the lower error
bound `-δ_j / 2` and every positive-flow slot of an optimum `g` satisfies the
upper error bound `+δ_j / 2`. -/
theorem narrowRoundedCosts_error_for_progress (I : Circulation)
    (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m) (L j : ℕ) (s : NarrowCostState I)
    (y : Fin I.n → ℝ)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ))
      (stageEps L (costPrecisionExp I.m) j) y)
    (hunf : ∀ e, s.frozen e = .none →
      s.halfCost e = Int.floor (2 * I.reducedCost y e / stageDelta L j))
    (hpos : ∀ e, s.frozen e = .pos →
      s.flow e = 0 ∧ (upperClip I.m : ℝ) * stageDelta L j ≤ I.reducedCost y e)
    (hneg : ∀ e, s.frozen e = .neg →
      s.flow e = (I.capacity e : ℤ) ∧
        (upperClip I.m : ℝ) * stageDelta L j ≤ -I.reducedCost y e)
    (g : Fin (I.m + I.m) → ℤ)
    (hg : (narrowRoundInstance I s).Optimal (fun a => (g a : ℝ))) :
    ∀ a, 0 < (I.residual s.flow).capacity a →
      -(stageDelta L j / 2) ≤
        (I.residual s.flow).reducedCost y a -
          stageDelta L j * ((narrowRoundInstance I s).cost a : ℝ) ∧
      (0 < (g a : ℝ) →
        (I.residual s.flow).reducedCost y a -
          stageDelta L j * ((narrowRoundInstance I s).cost a : ℝ) ≤
          stageDelta L j / 2) := by
  have hδ : 0 < stageDelta L j := stageDelta_pos L j
  have hres_eps := I.epsilonOptimalWith_residual s.flow _ y hopt
  intro a ha
  revert ha
  refine Fin.addCases (m := I.m) (n := I.m) (fun e ha => ?_) (fun e ha => ?_) a
  · -- Forward slot `Fin.castAdd I.m e`
    have hred : (I.residual s.flow).reducedCost y (Fin.castAdd I.m e) = I.reducedCost y e := by
      simp [Circulation.reducedCost, Circulation.potentialDifference]
    have hceps : -(stageEps L (costPrecisionExp I.m) j) < I.reducedCost y e := by
      rw [← hred]; exact hres_eps _ ha
    rw [hred]
    cases hfr : s.frozen e with
    | none =>
      have hx : s.halfCost e = Int.floor (2 * I.reducedCost y e / stageDelta L j) := hunf e hfr
      have herr := half_unit_rounding_error (I.reducedCost y e) (stageDelta L j) hδ
      set r : ℤ := (s.halfCost e + 1) / 2
      have herr' : -(stageDelta L j / 2) ≤ I.reducedCost y e - (r : ℝ) * stageDelta L j ∧
          I.reducedCost y e - (r : ℝ) * stageDelta L j ≤ stageDelta L j / 2 := by
        simpa only [r, hx] using herr
      have hr_lo : -(lowerClip I.m : ℤ) ≤ r := by
        simpa only [r, hx] using unfrozen_active_lower_ge_fwd L I.m j (I.reducedCost y e) hceps
      have hcost_min : (narrowRoundInstance I s).cost (Fin.castAdd I.m e) =
          min r (upperClip I.m : ℤ) := by
        simp only [narrowRoundedCosts, Fin.addCases_left, hfr, roundedForwardCost, clampInt]
        apply max_eq_right
        exact le_min hr_lo (by have := lowerClip_le_upperClip I.m; omega)
      rw [hcost_min]
      refine ⟨?_, ?_⟩
      · have hle : ((min r (upperClip I.m : ℤ) : ℤ) : ℝ) ≤ (r : ℝ) := by
          exact_mod_cast min_le_left r (upperClip I.m : ℤ)
        nlinarith only [hδ, hle, herr'.1]
      · intro hgpos
        have hlt : r < (upperClip I.m : ℤ) := by
          by_contra hge
          have hge' : (upperClip I.m : ℤ) ≤ r := le_of_not_gt hge
          have hceq : (narrowRoundInstance I s).cost (Fin.castAdd I.m e) = (upperClip I.m : ℤ) := by
            rw [hcost_min, min_eq_right hge']
          have hz := narrowRoundedCosts_optimal_zero_of_eq_upperClip I hm hn s g hg
            (Fin.castAdd I.m e) hceq
          rw [hz, Int.cast_zero] at hgpos
          exact lt_irrefl 0 hgpos
        rw [min_eq_left hlt.le]
        nlinarith only [herr'.2]
    | pos =>
      have hceq : (narrowRoundInstance I s).cost (Fin.castAdd I.m e) = (upperClip I.m : ℤ) := by
        simp only [narrowRoundedCosts, Fin.addCases_left, hfr, roundedForwardCost]
      rw [hceq]
      refine ⟨?_, ?_⟩
      · have hhi := (hpos e hfr).2
        push_cast
        linarith only [hδ, hhi]
      · intro hgpos
        have hz := narrowRoundedCosts_optimal_zero_of_eq_upperClip I hm hn s g hg
          (Fin.castAdd I.m e) hceq
        rw [hz, Int.cast_zero] at hgpos
        exact False.elim (lt_irrefl 0 hgpos)
    | neg =>
      have hfe := (hneg e hfr).1
      have hcap0 : (I.residual s.flow).capacity (Fin.castAdd I.m e) = 0 := by
        simp only [Fin.addCases_left, hfe, sub_self, Int.toNat_zero]
      omega
  · -- Reverse slot `Fin.natAdd I.m e`
    have hred : (I.residual s.flow).reducedCost y (Fin.natAdd I.m e) = -I.reducedCost y e := by
      simp only [Circulation.reducedCost, Circulation.potentialDifference, Fin.addCases_right,
        Int.cast_neg]
      ring
    have hceps : -(stageEps L (costPrecisionExp I.m) j) < -I.reducedCost y e := by
      rw [← hred]; exact hres_eps _ ha
    rw [hred]
    cases hfr : s.frozen e with
    | none =>
      have hx : s.halfCost e = Int.floor (2 * I.reducedCost y e / stageDelta L j) := hunf e hfr
      have herr := half_unit_rounding_error (I.reducedCost y e) (stageDelta L j) hδ
      set r : ℤ := (s.halfCost e + 1) / 2
      have herr' : -(stageDelta L j / 2) ≤ -I.reducedCost y e - ((-r : ℤ) : ℝ) * stageDelta L j ∧
          -I.reducedCost y e - ((-r : ℤ) : ℝ) * stageDelta L j ≤ stageDelta L j / 2 := by
        have h1 : -(stageDelta L j / 2) ≤ I.reducedCost y e - (r : ℝ) * stageDelta L j ∧
            I.reducedCost y e - (r : ℝ) * stageDelta L j ≤ stageDelta L j / 2 := by
          simpa only [r, hx] using herr
        push_cast
        constructor <;> linarith only [h1.1, h1.2]
      have hr_lo : -(lowerClip I.m : ℤ) ≤ -r := by
        simpa only [r, hx] using unfrozen_active_lower_ge_rev L I.m j (I.reducedCost y e) hceps
      have hcost_min : (narrowRoundInstance I s).cost (Fin.natAdd I.m e) =
          min (-r) (upperClip I.m : ℤ) := by
        simp only [narrowRoundedCosts, Fin.addCases_right, hfr, roundedReverseCost, clampInt]
        apply max_eq_right
        exact le_min hr_lo (by have := lowerClip_le_upperClip I.m; omega)
      rw [hcost_min]
      refine ⟨?_, ?_⟩
      · have hle : ((min (-r) (upperClip I.m : ℤ) : ℤ) : ℝ) ≤ ((-r : ℤ) : ℝ) := by
          exact_mod_cast min_le_left (-r) (upperClip I.m : ℤ)
        nlinarith only [hδ, hle, herr'.1]
      · intro hgpos
        have hlt : -r < (upperClip I.m : ℤ) := by
          by_contra hge
          have hge' : (upperClip I.m : ℤ) ≤ -r := le_of_not_gt hge
          have hceq : (narrowRoundInstance I s).cost (Fin.natAdd I.m e) = (upperClip I.m : ℤ) := by
            rw [hcost_min, min_eq_right hge']
          have hz := narrowRoundedCosts_optimal_zero_of_eq_upperClip I hm hn s g hg
            (Fin.natAdd I.m e) hceq
          rw [hz, Int.cast_zero] at hgpos
          exact lt_irrefl 0 hgpos
        rw [min_eq_left hlt.le]
        nlinarith only [herr'.2]
    | pos =>
      have hfe := (hpos e hfr).1
      have hcap0 : (I.residual s.flow).capacity (Fin.natAdd I.m e) = 0 := by
        simp only [Fin.addCases_right, hfe, Int.toNat_zero]
      omega
    | neg =>
      have hceq : (narrowRoundInstance I s).cost (Fin.natAdd I.m e) = (upperClip I.m : ℤ) := by
        simp only [narrowRoundedCosts, Fin.addCases_right, hfr, roundedReverseCost]
      rw [hceq]
      refine ⟨?_, ?_⟩
      · have hhi := (hneg e hfr).2
        push_cast
        linarith only [hδ, hhi]
      · intro hgpos
        have hz := narrowRoundedCosts_optimal_zero_of_eq_upperClip I hm hn s g hg
          (Fin.natAdd I.m e) hceq
        rw [hz, Int.cast_zero] at hgpos
        exact False.elim (lt_irrefl 0 hgpos)

end MinCostFlow.Narrow
