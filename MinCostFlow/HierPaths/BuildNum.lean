module

public import MinCostFlow.HierPaths.BuildMain
public import MinCostFlow.HierPaths.Params

/-!
# The numbers of the construction

The construction (`static_construction`) is stated for any numbers `M, r, Δ, L, L', x, b` and
any router scales `b̂_j`. Here we bound what it gives in terms of the numbers of
`HierPaths/Params.lean`. Write `V = 2^v` with `v = vxOf m`, so that `xOf m + 2 ≤ V`.

* `FParam_le`: when `ℓ(M) ≤ V`, the core's loss is `F ≤ 2^87 a₀ V^6`, so `P_r = F^r` is at most
  `2^{r (87 + a₀ + 6 v)}` (`PParam_le`).
* `rho_le`: the router's load bound `ρ = Δ R` is at most `2^28 b̂^2 V^5`, when `Δ ≤ 64 V`,
  `L ≤ V` and `1 ≤ b̂`. The other two bounds are smaller (`pathLen_le_cong`).
* `exp_inner` and `exp_root`: the exponents fit in `a h v` when `a ≥ 223 + 2 a₀`.
* `bh_ge_root` and `bh_ge_inner`: the router scales `100 d` at the root and `4 P_r` below are
  large enough for the expansions `min(φ, 1)/50` and `1/(2 P_r)`, when `1/d ≤ φ`.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-! ## The core numbers -/

/-- For `M = 2^x` we have `x + 1 ≤ ℓ(M) ≤ x + 2`. -/
theorem ell_two_pow (x : ℕ) : x + 1 ≤ ell (2 ^ x) ∧ ell (2 ^ x) ≤ x + 2 := by
  unfold ell
  have h1 := Nat.one_le_two_pow (n := x)
  constructor
  · show x < _
    rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
    omega
  · rw [Nat.clog_le_iff_le_pow (by norm_num), pow_succ, pow_succ]
    omega

/-- **The core's loss**: `F ≤ 2^87 a₀ V^6` when `ℓ(M) ≤ V`. -/
theorem FParam_le {cfg : ParamConfig} {M V : ℕ} (hV : ell M ≤ V) (hV1 : 1 ≤ V) :
    FParam cfg M ≤ 2 ^ 87 * cfg.a₀ * V ^ 6 := by
  have hD : deltaParam M ≤ 2 ^ 12 * V := by unfold deltaParam tParam LParam; omega
  have hL : LParam M ≤ 4 * V := by unfold LParam; omega
  have hV2 : 1 ≤ V ^ 2 := Nat.one_le_pow _ _ hV1
  have hd : dCore M + 1 ≤ 2 ^ 27 * V ^ 2 := by
    have h1 : dCore M ≤ 3200 * (2 ^ 12 * V) * (4 * V) := by
      unfold dCore; exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) hL
    have h2 : 3200 * (2 ^ 12 * V) * (4 * V) = 52428800 * V ^ 2 := by ring
    rw [h2] at h1
    generalize V ^ 2 = W at *
    omega
  have hR : RCore M ≤ 2 ^ 52 * V ^ 4 := by
    calc RCore M ≤ 1600 * (2 ^ 12 * V) * (2 ^ 27 * V ^ 2) * (4 * V) := by
          unfold RCore
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hD) hd) hL
      _ = 1600 * 2 ^ 41 * V ^ 4 := by ring
      _ ≤ 2 ^ 52 * V ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  calc FParam cfg M ≤ 1920 * cfg.a₀ * (2 ^ 12 * V) ^ 2 * (2 ^ 52 * V ^ 4) := by
        unfold FParam
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 2)) hR
    _ = 1920 * 2 ^ 76 * cfg.a₀ * V ^ 6 := by ring
    _ ≤ 2 ^ 87 * cfg.a₀ * V ^ 6 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))

/-- `P_r = F^r ≤ 2^{r (87 + a₀ + 6 v)}` when `ℓ(M) ≤ 2^v`. -/
theorem PParam_le {cfg : ParamConfig} {M v : ℕ} (hV : ell M ≤ 2 ^ v) (r : ℕ) :
    PParam cfg M r ≤ 2 ^ (r * (87 + cfg.a₀ + 6 * v)) := by
  have hF := FParam_le (cfg := cfg) hV Nat.one_le_two_pow
  have ha : cfg.a₀ ≤ 2 ^ cfg.a₀ := (Nat.lt_two_pow_self).le
  have hF' : FParam cfg M ≤ 2 ^ (87 + cfg.a₀ + 6 * v) := by
    calc FParam cfg M ≤ 2 ^ 87 * 2 ^ cfg.a₀ * (2 ^ v) ^ 6 :=
          hF.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha))
      _ = 2 ^ (87 + cfg.a₀ + 6 * v) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  unfold PParam
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left hF' r

/-! ## The router numbers -/

/-- The path length is below the congestion. -/
theorem pathLen_le_cong {Δ bh L : ℕ} (hΔ : 1 ≤ Δ) (hb : 1 ≤ bh) (hL : 1 ≤ L) :
    routePathLen Δ bh L ≤ routeCong Δ bh L := by
  unfold routeCong routeBatchH
  have h1 : 1 ≤ 16 * bh * Δ := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 16 by norm_num) hb) hΔ
    simpa using this
  calc routePathLen Δ bh L ≤ routePathLen Δ bh L + 1 := Nat.le_succ _
    _ ≤ 16 * bh * Δ * (routePathLen Δ bh L + 1) := Nat.le_mul_of_pos_left _ h1
    _ ≤ _ := Nat.le_mul_of_pos_right _ hL

/-- **The load of the router**: `Δ R ≤ 2^28 b̂^2 V^5` when `Δ ≤ 64 V` and `L ≤ V`. -/
theorem rho_le {Δ bh L V : ℕ} (hΔ : Δ ≤ 64 * V) (hL : L ≤ V) (hb : 1 ≤ bh) (hV : 1 ≤ V) :
    Δ * routeCong Δ bh L ≤ 2 ^ 28 * bh ^ 2 * V ^ 5 := by
  have hd : routePathLen Δ bh L + 1 ≤ 2 ^ 12 * bh * V ^ 2 := by
    have h1 : routePathLen Δ bh L ≤ 32 * (64 * V) * bh * V := by
      unfold routePathLen
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hΔ)) hL
    have h2 : 32 * (64 * V) * bh * V = 2 ^ 11 * (bh * V ^ 2) := by ring
    have h3 : 1 ≤ bh * V ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by positivity))
    have h4 : 2 ^ 12 * bh * V ^ 2 = 2 ^ 12 * (bh * V ^ 2) := by ring
    rw [h2] at h1
    rw [h4]
    generalize bh * V ^ 2 = W at *
    omega
  calc Δ * routeCong Δ bh L
      ≤ (64 * V) * (16 * bh * (64 * V) * (2 ^ 12 * bh * V ^ 2) * V) := by
        unfold routeCong routeBatchH
        exact Nat.mul_le_mul hΔ (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΔ) hd) hL)
    _ = 2 ^ 28 * bh ^ 2 * V ^ 5 := by ring

/-- The exponent at depths `j ≥ 1`: `32 + 2h(87 + a₀ + 6v) + 5v ≤ a h v`. -/
theorem exp_inner {a a₀ h v : ℕ} (ha : 223 + 2 * a₀ ≤ a) (hh : 1 ≤ h) (hv : 1 ≤ v) :
    32 + 2 * (h * (87 + a₀ + 6 * v)) + 5 * v ≤ a * h * v := by
  have hhv : 1 ≤ h * v := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h1 : v ≤ h * v := Nat.le_mul_of_pos_left _ hh
  have h2 : h ≤ h * v := Nat.le_mul_of_pos_right _ hv
  have h3 : h * a₀ ≤ h * v * a₀ := Nat.mul_le_mul_right _ h2
  have h4 : (223 + 2 * a₀) * (h * v) ≤ a * (h * v) := Nat.mul_le_mul_right _ ha
  have e1 : a * h * v = a * (h * v) := by ring
  have e2 : 2 * (h * (87 + a₀ + 6 * v)) = 174 * h + 2 * (h * a₀) + 12 * (h * v) := by ring
  have e3 : (223 + 2 * a₀) * (h * v) = 223 * (h * v) + 2 * (h * v * a₀) := by ring
  rw [e1, e2]
  rw [e3] at h4
  generalize h * v = P at *
  generalize h * a₀ = Q at *
  generalize P * a₀ = S at *
  generalize a * P = T at *
  omega

/-- The exponent at the root: `42 + 5 v ≤ a h v`. -/
theorem exp_root {a h v : ℕ} (ha : 47 ≤ a) (hh : 1 ≤ h) (hv : 1 ≤ v) :
    42 + 5 * v ≤ a * h * v := by
  have h1 : v ≤ h * v := Nat.le_mul_of_pos_left _ hh
  have h4 : 47 * (h * v) ≤ a * (h * v) := Nat.mul_le_mul_right _ ha
  have hhv : 1 ≤ h * v := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e1 : a * h * v = a * (h * v) := by ring
  rw [e1]
  generalize h * v = P at *
  generalize a * P = T at *
  omega

/-! ## The router scales -/

/-- At the root, `b̂ = 100 d` is enough for the expansion `min(φ, 1)/50` when `1/d ≤ φ`. -/
theorem bh_ge_root {φ : ℝ} {dd : ℕ} (hd : 1 ≤ dd) (hφ : 1 / (dd : ℝ) ≤ φ) :
    max 2 (2 / (min φ 1 / 50)) ≤ ((100 * dd : ℕ) : ℝ) := by
  have hdd : (1 : ℝ) ≤ dd := by exact_mod_cast hd
  have hpos : (0 : ℝ) < 1 / (dd : ℝ) := by positivity
  have hle1 : 1 / (dd : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hdd
  have hm : 1 / (dd : ℝ) ≤ min φ 1 := le_min hφ hle1
  have hmpos : 0 < min φ 1 := lt_of_lt_of_le hpos hm
  push_cast
  apply max_le (by linarith)
  calc 2 / (min φ 1 / 50) = 100 / min φ 1 := by field_simp; ring
    _ ≤ 100 / (1 / (dd : ℝ)) := div_le_div_of_nonneg_left (by norm_num) hpos hm
    _ = 100 * dd := by field_simp

/-- Below the root, `b̂ = 4 P` is enough for the expansion `1/(2 P)`. -/
theorem bh_ge_inner {P : ℕ} (hP : 1 ≤ P) :
    max 2 (2 / (1 / (2 * P : ℝ))) ≤ ((4 * P : ℕ) : ℝ) := by
  have hP' : (1 : ℝ) ≤ P := by exact_mod_cast hP
  push_cast
  apply max_le (by linarith)
  have : (2 : ℝ) / (1 / (2 * P)) = 4 * P := by field_simp; ring
  rw [this]

end MinCostFlow.HierPaths
