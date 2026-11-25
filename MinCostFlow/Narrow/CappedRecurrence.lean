module

public import MinCostFlow.Narrow.Defs

/-!
# Capped residual and flow recurrences for bit scaling

This file proves the bit-splitting identities and the capped-value recurrences
used by Stage 2 (Gabow bit scaling). When each phase augments twice the
previous flow by a residual flow bounded in magnitude by `M`, any residual or
flow value at or above `M` stays at or above `M` after the phase. Thus both the
next phase's capacities and the post-update capped values depend only on the
previous capped values, the incoming capacity bit, and the phase's residual
flow.
-/

public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- Dropping one low bit doubles the shifted quotient and adds the next bit. -/
theorem div_two_pow_sub_one (u k : ℕ) (hk : 1 ≤ k) :
    u / 2 ^ (k - 1) = 2 * (u / 2 ^ k) + (u / 2 ^ (k - 1)) % 2 := by
  rcases k with _ | j
  · omega
  · simp only [Nat.add_sub_cancel]
    rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_add_mod]

/-- Dividing by `2 ^ 0` leaves a natural number unchanged. -/
theorem div_two_pow_zero (u : ℕ) : u / 2 ^ 0 = u := by
  simp

/-- Integer capping identity for the updated forward residual capacity. -/
theorem min_two_mul_add_sub_eq (ρ b x M : ℤ) (_hρ : 0 ≤ ρ) (hx : x ≤ M) (hb : 0 ≤ b) :
    min (2 * ρ + b - x) M = min (2 * min ρ M + b - x) M := by
  rcases le_total ρ M with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge, min_eq_right (by omega), min_eq_right (by omega)]

/-- Integer capping identity for the updated flow (reverse residual capacity). -/
theorem min_two_mul_add_eq (g x M : ℤ) (_hg : 0 ≤ g) (hx : -M ≤ x) :
    min (2 * g + x) M = min (2 * min g M + x) M := by
  rcases le_total g M with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge, min_eq_right (by omega), min_eq_right (by omega)]

/-- Natural-number capping identity for doubled forward residual capacities. -/
theorem min_two_mul_add_nat (ρ b M : ℕ) :
    min (2 * ρ + b) M = min (2 * min ρ M + b) M := by
  rcases le_total ρ M with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge, min_eq_right (by omega), min_eq_right (by omega)]

/-- Natural-number capping identity for doubled reverse residual capacities. -/
theorem min_two_mul_nat (g M : ℕ) :
    min (2 * g) M = min (2 * min g M) M := by
  rcases le_total g M with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge, min_eq_right (by omega), min_eq_right (by omega)]

/-- Underflow-free natural-number capping identity for the post-update residual. -/
theorem min_two_mul_add_add_sub_nat (ρ b df dr M : ℕ) (hdf : df ≤ M) :
    min (2 * ρ + b + dr - df) M = min (2 * min ρ M + b + dr - df) M := by
  rcases le_total ρ M with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge, min_eq_right (by omega), min_eq_right (by omega)]

/-- Underflow-free natural-number capping identity for the post-update flow. -/
theorem min_two_mul_add_sub_nat (g df dr M : ℕ) (hdr : dr ≤ M) :
    min (2 * g + df - dr) M = min (2 * min g M + df - dr) M := by
  rcases le_total g M with hle | hge
  · rw [min_eq_left hle]
  · rw [min_eq_right hge, min_eq_right (by omega), min_eq_right (by omega)]

/-- Nonnegativity and natural-number capacity bounds for a feasible integer
residual flow in the capped phase instance. -/
theorem phaseInstance_delta_bounds (I : Circulation) (b : Fin I.m → ℕ)
    (g : Fin I.m → ℤ) (M : ℕ) (d : Fin (I.m + I.m) → ℤ)
    (hd : (phaseInstance I b g M).Feasible (fun a => (d a : ℝ)))
    (a : Fin (I.m + I.m)) :
    0 ≤ d a ∧ (d a).toNat ≤ (phaseInstance I b g M).capacity a := by
  have h1 : 0 ≤ d a := (Int.cast_nonneg_iff (R := ℝ)).mp (hd.2 a).1
  have h2 : d a ≤ ((phaseInstance I b g M).capacity a : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using (hd.2 a).2
  exact ⟨h1, by omega⟩

/-- The forward slot capacity of `phaseInstance` is a function of the capped
residual and incoming bit `b e`. -/
theorem phaseInstance_capacity_forward (I : Circulation) (b : Fin I.m → ℕ)
    (g : Fin I.m → ℤ) (hg : ∀ e, 0 ≤ g e ∧ g e ≤ I.capacity e) (M : ℕ) (e : Fin I.m) :
    (phaseInstance I b g M).capacity (Fin.castAdd I.m e) =
      min (2 * min (((I.capacity e : ℤ) - g e).toNat) M + b e) M := by
  have hge := hg e
  have hraw : (((2 * I.capacity e + b e : ℕ) : ℤ) - 2 * g e).toNat =
      2 * ((I.capacity e : ℤ) - g e).toNat + b e := by
    omega
  simp only [Fin.addCases_left]
  rw [hraw]
  exact min_two_mul_add_nat _ _ _

/-- The reverse slot capacity of `phaseInstance` is a function of the capped
flow. -/
theorem phaseInstance_capacity_reverse (I : Circulation) (b : Fin I.m → ℕ)
    (g : Fin I.m → ℤ) (hg : ∀ e, 0 ≤ g e) (M : ℕ) (e : Fin I.m) :
    (phaseInstance I b g M).capacity (Fin.natAdd I.m e) =
      min (2 * min (g e).toNat M) M := by
  have hge := hg e
  have hraw : (2 * g e).toNat = 2 * (g e).toNat := by
    omega
  simp only [Fin.addCases_right]
  rw [hraw]
  exact min_two_mul_nat _ _

/-- After augmenting `2 * g` by a feasible integral flow `d` of the phase
instance, the new capped residual capacity follows the exact natural-number
recurrence. -/
theorem cappedResidual_after_augment (I : Circulation) (b : Fin I.m → ℕ)
    (g : Fin I.m → ℤ) (hg : ∀ e, 0 ≤ g e ∧ g e ≤ I.capacity e) (M : ℕ)
    (d : Fin (I.m + I.m) → ℤ)
    (hd : (phaseInstance I b g M).Feasible (fun a => (d a : ℝ)))
    (e : Fin I.m) :
    min ((((doubled I b).capacity e : ℤ) - intAugment I.m (fun k => 2 * g k) d e).toNat) M =
      min (2 * min (((I.capacity e : ℤ) - g e).toNat) M + b e +
        (d (Fin.natAdd I.m e)).toNat - (d (Fin.castAdd I.m e)).toNat) M := by
  have hge := hg e
  have hfwd := phaseInstance_delta_bounds I b g M d hd (Fin.castAdd I.m e)
  have hrev := phaseInstance_delta_bounds I b g M d hd (Fin.natAdd I.m e)
  have hcap_f : (phaseInstance I b g M).capacity (Fin.castAdd I.m e) =
      min (2 * ((I.capacity e : ℤ) - g e).toNat + b e) M := by
    rw [phaseInstance_capacity_forward I b g hg M e, ← min_two_mul_add_nat]
  have hdf_le : (d (Fin.castAdd I.m e)).toNat ≤ min (2 * ((I.capacity e : ℤ) - g e).toNat + b e) M :=
    hcap_f ▸ hfwd.2
  have hdf_M : (d (Fin.castAdd I.m e)).toNat ≤ M := le_trans hdf_le (Nat.min_le_right _ _)
  have hdf_raw : (d (Fin.castAdd I.m e)).toNat ≤ 2 * ((I.capacity e : ℤ) - g e).toNat + b e :=
    le_trans hdf_le (Nat.min_le_left _ _)
  have htoNat :
      (((doubled I b).capacity e : ℤ) - intAugment I.m (fun k => 2 * g k) d e).toNat =
        2 * ((I.capacity e : ℤ) - g e).toNat + b e +
          (d (Fin.natAdd I.m e)).toNat - (d (Fin.castAdd I.m e)).toNat := by
    dsimp only [doubled, intAugment, intProject]
    omega
  rw [htoNat]
  exact min_two_mul_add_add_sub_nat _ _ _ _ _ hdf_M

/-- After augmenting `2 * g` by a feasible integral flow `d` of the phase
instance, the new capped flow follows the exact natural-number recurrence. -/
theorem cappedFlow_after_augment (I : Circulation) (b : Fin I.m → ℕ)
    (g : Fin I.m → ℤ) (hg : ∀ e, 0 ≤ g e ∧ g e ≤ I.capacity e) (M : ℕ)
    (d : Fin (I.m + I.m) → ℤ)
    (hd : (phaseInstance I b g M).Feasible (fun a => (d a : ℝ)))
    (e : Fin I.m) :
    min (intAugment I.m (fun k => 2 * g k) d e).toNat M =
      min (2 * min (g e).toNat M +
        (d (Fin.castAdd I.m e)).toNat - (d (Fin.natAdd I.m e)).toNat) M := by
  have hge := hg e
  have hfwd := phaseInstance_delta_bounds I b g M d hd (Fin.castAdd I.m e)
  have hrev := phaseInstance_delta_bounds I b g M d hd (Fin.natAdd I.m e)
  have hcap_r : (phaseInstance I b g M).capacity (Fin.natAdd I.m e) =
      min (2 * (g e).toNat) M := by
    rw [phaseInstance_capacity_reverse I b g (fun k => (hg k).1) M e, ← min_two_mul_nat]
  have hdr_le : (d (Fin.natAdd I.m e)).toNat ≤ min (2 * (g e).toNat) M :=
    hcap_r ▸ hrev.2
  have hdr_M : (d (Fin.natAdd I.m e)).toNat ≤ M := le_trans hdr_le (Nat.min_le_right _ _)
  have hdr_raw : (d (Fin.natAdd I.m e)).toNat ≤ 2 * (g e).toNat :=
    le_trans hdr_le (Nat.min_le_left _ _)
  have htoNat :
      (intAugment I.m (fun k => 2 * g k) d e).toNat =
        2 * (g e).toNat + (d (Fin.castAdd I.m e)).toNat - (d (Fin.natAdd I.m e)).toNat := by
    dsimp only [intAugment, intProject]
    omega
  rw [htoNat]
  exact min_two_mul_add_sub_nat _ _ _ _ hdr_M

end MinCostFlow.Narrow
