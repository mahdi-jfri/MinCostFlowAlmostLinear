module

public import MinCostFlow.ExpanderDecomp.Params
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameter bounds and envelope fit for `ExpanderDecompositionUsed`

This file proves explicit upper bounds on the parameters and shows that the resulting conductance
`φ(m) = 1 / Q` and total time `totalTimeRaw` fit the target shape of `ExpanderDecompositionUsed` at
`ε = 1 / 200` and `r = rOf m` for all `m ≥ thresholdB1 envelopeCr`.

Main results:
* Elementary upper bounds on the outer parameters and on `F`, `W`: `bOut_le`, `ROut_le`, `Lambda_le`, `DOut_le`,
  `HDepth_le`, `QOut_le`, `FParam_le`, `WParam_le`.
* Total time closed form: `totalTimeRaw_le`.
* Explicit envelope constants `envelopeK cfg` and `envelopeCr = 1 / 2`, and the target inequalities:
  - `NParam_sq_le_rpow`: `N^2 ≤ (m + 2)^{K / r}`;
  - `WParam_pow_le_log_rpow`: `W^{40 r^2} ≤ log(m + 2)^{K r^2}`;
  - `QOut_le_envelope` and `phiOut_ge_used`: `1 / φ ≤ 200 K log(m + 2)^{K r^2}`;
  - `totalTimeRaw_le_envelope` and `totalTimeRaw_le_used`:
    `totalTimeRaw ≤ K (n + (m + 2)^{1 + K / r} log(m + 2)^{K r^2} / (1 / 200)^2)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Expander

/-- Constant `w · 24^6` appearing in `W ≤ (w · 24^6) · (log(m + 2))^6`. -/
def wLogConst (cfg : ParamConfig) : ℕ := cfg.wConst * 24 ^ 6

/-- Explicit integer envelope constant `K_nat` for `ExpanderDecompositionUsed`. -/
def envelopeKNat (cfg : ParamConfig) : ℕ :=
  max cfg.KStar (40 * (Nat.clog 2 (wLogConst cfg) + 6))

/-- Explicit real envelope constant `K > 0` for `ExpanderDecompositionUsed`. -/
def envelopeK (cfg : ParamConfig) : ℝ := (envelopeKNat cfg : ℝ)

/-- Explicit threshold constant `cr = 1 / 2 > 0` for `ExpanderDecompositionUsed`. -/
noncomputable def envelopeCr : ℝ := 1 / 2

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Expander

/-! ### Elementary integer upper bounds -/

/-- Elementary bound: `b_out ≤ 2^5 κ E L`. -/
theorem bOut_le (cfg : ParamConfig) (M : ℕ) :
    bOut cfg M ≤ 2 ^ 5 * cfg.kappa * cfg.E * LParam M := by
  unfold bOut
  have hL : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have h1 : LParam M + 1 ≤ 2 * LParam M := by omega
  calc 16 * cfg.kappa * (LParam M + 1) * cfg.E
      ≤ 16 * cfg.kappa * (2 * LParam M) * cfg.E := by gcongr
    _ = 2 ^ 5 * cfg.kappa * cfg.E * LParam M := by ring

/-- Elementary bound: `R_out ≤ 2^16 b_out^2 L^2`. -/
theorem ROut_le (cfg : ParamConfig) (M : ℕ) :
    ROut cfg M ≤ 2 ^ 16 * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by
  unfold ROut dOut
  have hb : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have hL : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have h1 : 1 ≤ bOut cfg M * LParam M := Nat.mul_pos hb hL
  have hd : 320 * bOut cfg M * LParam M + 1 ≤ 321 * (bOut cfg M * LParam M) := by
    have : 320 * bOut cfg M * LParam M = 320 * (bOut cfg M * LParam M) := by ring
    omega
  calc 160 * bOut cfg M * (320 * bOut cfg M * LParam M + 1) * LParam M
      ≤ 160 * bOut cfg M * (321 * (bOut cfg M * LParam M)) * LParam M := by gcongr
    _ = (160 * 321) * ((bOut cfg M) ^ 2 * (LParam M) ^ 2) := by ring
    _ ≤ 2 ^ 16 * ((bOut cfg M) ^ 2 * (LParam M) ^ 2) :=
        Nat.mul_le_mul_right _ (by decide)
    _ = 2 ^ 16 * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by ring

/-- Elementary bound: `Λ ≤ 2^38 P b_out^2 L^4`. -/
theorem Lambda_le (cfg : ParamConfig) (M r : ℕ) :
    Lambda cfg M r ≤ 2 ^ 38 * PParam cfg M r * (bOut cfg M) ^ 2 * (LParam M) ^ 4 := by
  unfold Lambda
  have hL : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have ht1 : tParam M + 1 ≤ 2 * tParam M := by
    have := one_le_tParam M; omega
  have hR := ROut_le cfg M
  calc 2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1)
      ≤ 2 * PParam cfg M r * tParam M * (2 ^ 16 * (bOut cfg M) ^ 2 * (LParam M) ^ 2) *
          (2 * tParam M) := by gcongr
    _ = 2 ^ 18 * (tParam M) ^ 2 * PParam cfg M r * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by ring
    _ = 2 ^ 38 * PParam cfg M r * (bOut cfg M) ^ 2 * (LParam M) ^ 4 := by
        unfold tParam; ring

/-- Elementary bound: `D ≤ 2^52 A P b_out^3 L^5`. -/
theorem DOut_le (cfg : ParamConfig) (M r : ℕ) :
    DOut cfg M r ≤ 2 ^ 52 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 5 := by
  unfold DOut
  have hLam := Lambda_le cfg M r
  calc 16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M
      ≤ 16 * cfg.A * tParam M *
          (2 ^ 38 * PParam cfg M r * (bOut cfg M) ^ 2 * (LParam M) ^ 4) * bOut cfg M := by gcongr
    _ = 2 ^ 52 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 5 := by
        unfold tParam; ring

/-- Elementary bound: `H_depth ≤ 2^56 A P b_out^3 L^6`. -/
theorem HDepth_le (cfg : ParamConfig) (M r : ℕ) :
    HDepth cfg M r ≤ 2 ^ 56 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 6 := by
  unfold HDepth
  have hell : 1 ≤ ell M := one_le_ell M
  have hD1 : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have hL : 4 ≤ LParam M := four_le_LParam M
  have he1 : 16 * (ell M + 1) ≤ 8 * LParam M := by unfold LParam; omega
  have h1 : 16 * DOut cfg M r * (ell M + 1) + 2 ≤ 16 * DOut cfg M r * LParam M := by
    have hmul : 16 * DOut cfg M r * (ell M + 1) ≤ 8 * DOut cfg M r * LParam M := by
      calc 16 * DOut cfg M r * (ell M + 1) = DOut cfg M r * (16 * (ell M + 1)) := by ring
        _ ≤ DOut cfg M r * (8 * LParam M) := Nat.mul_le_mul_left _ he1
        _ = 8 * DOut cfg M r * LParam M := by ring
    have h2 : 2 ≤ 8 * DOut cfg M r * LParam M := by nlinarith
    have hadd : 8 * DOut cfg M r * LParam M + 8 * DOut cfg M r * LParam M =
        16 * DOut cfg M r * LParam M := by ring
    omega
  have hD := DOut_le cfg M r
  calc 16 * DOut cfg M r * (ell M + 1) + 2
      ≤ 16 * DOut cfg M r * LParam M := h1
    _ ≤ 16 * (2 ^ 52 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 5) * LParam M := by
        gcongr
    _ = 2 ^ 56 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 6 := by ring

/-- Elementary bound: `Q ≤ 2^69 A κ^3 E^3 P L^8 = C₁ P L^8`. -/
theorem QOut_le (cfg : ParamConfig) (M r : ℕ) :
    QOut cfg M r ≤ cfg.C1 * PParam cfg M r * (LParam M) ^ 8 := by
  unfold QOut ParamConfig.C1
  have hD1 : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have hQ : 2 * DOut cfg M r + 2 ≤ 4 * DOut cfg M r := by omega
  have hD := DOut_le cfg M r
  have hb := bOut_le cfg M
  calc 2 * DOut cfg M r + 2
      ≤ 4 * DOut cfg M r := hQ
    _ ≤ 4 * (2 ^ 52 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 5) := by gcongr
    _ ≤ 4 * (2 ^ 52 * cfg.A * PParam cfg M r *
          (2 ^ 5 * cfg.kappa * cfg.E * LParam M) ^ 3 * (LParam M) ^ 5) := by gcongr
    _ = 2 ^ 69 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3 * PParam cfg M r * (LParam M) ^ 8 := by ring

/-- Elementary bound: `F ≤ 2^74 a₀ L^6`. -/
theorem FParam_le (cfg : ParamConfig) (M : ℕ) :
    FParam cfg M ≤ 2 ^ 74 * cfg.a₀ * (LParam M) ^ 6 := by
  unfold FParam RCore dCore deltaParam tParam
  have hL : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have hL2 : 1 ≤ (LParam M) ^ 2 := by nlinarith
  have hd : 3200 * (1024 * LParam M) * LParam M + 1 ≤ 3276801 * (LParam M) ^ 2 := by
    have : 3200 * (1024 * LParam M) * LParam M = 3276800 * (LParam M) ^ 2 := by ring
    omega
  calc 1920 * cfg.a₀ * (1024 * LParam M) ^ 2 *
        (1600 * (1024 * LParam M) * (3200 * (1024 * LParam M) * LParam M + 1) * LParam M)
      ≤ 1920 * cfg.a₀ * (1024 * LParam M) ^ 2 *
        (1600 * (1024 * LParam M) * (3276801 * (LParam M) ^ 2) * LParam M) := by gcongr
    _ = (1920 * 1024 ^ 2 * 1600 * 1024 * 3276801) * (cfg.a₀ * (LParam M) ^ 6) := by ring
    _ ≤ 2 ^ 74 * (cfg.a₀ * (LParam M) ^ 6) := Nat.mul_le_mul_right _ (by decide)
    _ = 2 ^ 74 * cfg.a₀ * (LParam M) ^ 6 := by ring

/-- Elementary bound: `W ≤ w L^6` where `w = 2^74 a₀ + 3 c₀ A + 3`. -/
theorem WParam_le (cfg : ParamConfig) (M : ℕ) :
    WParam cfg M ≤ cfg.wConst * (LParam M) ^ 6 := by
  unfold WParam ParamConfig.wConst
  have hF := FParam_le cfg M
  have hL : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
  have hL6 : 1 ≤ (LParam M) ^ 6 := Nat.one_le_pow 6 _ hL
  have hL_le : LParam M ≤ (LParam M) ^ 6 := by
    calc LParam M = (LParam M) ^ 1 := (pow_one _).symm
      _ ≤ (LParam M) ^ 6 := Nat.pow_le_pow_right hL (by decide)
  have hcA : 3 * cfg.c0 * cfg.A ≤ 3 * cfg.c0 * cfg.A * (LParam M) ^ 6 :=
    Nat.le_mul_of_pos_right _ hL6
  have hexp : (2 ^ 74 * cfg.a₀ + 3 * cfg.c0 * cfg.A + 3) * (LParam M) ^ 6 =
      2 ^ 74 * cfg.a₀ * (LParam M) ^ 6 + 3 * cfg.c0 * cfg.A * (LParam M) ^ 6 +
        3 * (LParam M) ^ 6 := by ring
  omega

/-! ### Total time bound and `Q` in terms of `W` -/

/-- `Q ≤ C₁ W^{r + 8}`. -/
theorem QOut_le_C1_W_pow (cfg : ParamConfig) (M r : ℕ) :
    QOut cfg M r ≤ cfg.C1 * (WParam cfg M) ^ (r + 8) := by
  have hQ := QOut_le cfg M r
  have hFW : FParam cfg M ≤ WParam cfg M := by unfold WParam; omega
  have hLW : LParam M ≤ WParam cfg M := by unfold WParam; omega
  have hP : PParam cfg M r ≤ (WParam cfg M) ^ r := Nat.pow_le_pow_left hFW r
  have hL8 : (LParam M) ^ 8 ≤ (WParam cfg M) ^ 8 := Nat.pow_le_pow_left hLW 8
  calc QOut cfg M r ≤ cfg.C1 * PParam cfg M r * (LParam M) ^ 8 := hQ
    _ ≤ cfg.C1 * (WParam cfg M) ^ r * (WParam cfg M) ^ 8 := by gcongr
    _ = cfg.C1 * (WParam cfg M) ^ (r + 8) := by ring

/-- `C₁ ≤ K_*`. -/
theorem ParamConfig.C1_le_KStar (cfg : ParamConfig) : cfg.C1 ≤ cfg.KStar := by
  unfold ParamConfig.C1 ParamConfig.KStar
  have hu : 1 ≤ cfg.u ^ 3 := Nat.one_le_pow 3 _ cfg.hu
  have hk : 1 ≤ cfg.kappa ^ 3 := Nat.one_le_pow 3 _ (le_trans (by decide) cfg.kappa_pos)
  have hE : 1 ≤ cfg.E ^ 3 := Nat.one_le_pow 3 _ cfg.hE
  have h2 : 2 ^ 69 ≤ 2 ^ 150 := Nat.pow_le_pow_right (by decide) (by decide)
  calc 2 ^ 69 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3
      = 2 ^ 69 * 1 * cfg.A * (cfg.kappa ^ 3 * 1) * (cfg.E ^ 3 * 1) := by ring
    _ ≤ 2 ^ 150 * cfg.u ^ 3 * cfg.A * (cfg.kappa ^ 3 * cfg.kappa ^ 3) *
          (cfg.E ^ 3 * cfg.E ^ 3) := by gcongr
    _ = 2 ^ 150 * cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6 := by ring

/-- Pure natural-number core of the total time bound `totalTimeRaw_le`, keeping `W` and `c₀` abstract for fast elaboration. -/
private theorem totalTimeRaw_le_aux {n M r N L W H Lam b t A k E u : ℕ}
    (hr : 1 ≤ r) (hW1 : 1 ≤ W) (hLW : L ≤ W) (hN1 : 1 ≤ N)
    (hA1 : 1 ≤ A) (hk1 : 1 ≤ k) (hE1 : 1 ≤ E)
    (ht_eq : t = 1024 * L) (ht_add : t + 1 ≤ 2 ^ 11 * W)
    (hb : b ≤ 2 ^ 5 * k * E * L)
    (hH : H ≤ 2 ^ 71 * A * k ^ 3 * E ^ 3 * W ^ (r + 9))
    (hLam : Lam ≤ 2 ^ 48 * k ^ 2 * E ^ 2 * W ^ (r + 6)) :
    (2 ^ 40 * u ^ 3) *
        (n + M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
          M * Lam ^ 2 * L ^ 2) ≤
      (2 ^ 150 * u ^ 3 * A * k ^ 6 * E ^ 6) * (n + M * N ^ 2 * W ^ (40 * r ^ 2)) := by
  have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow 2 _ hN1
  have hexp1 : 10 * r ^ 2 + r + 20 ≤ 40 * r ^ 2 := by nlinarith
  have hexp2 : r + 16 ≤ 40 * r ^ 2 := by nlinarith
  have hexp3 : r + 10 ≤ 40 * r ^ 2 := by nlinarith
  have hexp4 : 2 * r + 14 ≤ 40 * r ^ 2 := by nlinarith
  have hk3 : k ^ 3 ≤ k ^ 6 := Nat.pow_le_pow_right hk1 (by decide)
  have hE3 : E ^ 3 ≤ E ^ 6 := Nat.pow_le_pow_right hE1 (by decide)
  have hk4 : k ^ 4 ≤ k ^ 6 := Nat.pow_le_pow_right hk1 (by decide)
  have hE4 : E ^ 4 ≤ E ^ 6 := Nat.pow_le_pow_right hE1 (by decide)
  have htermA : H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10)) ≤
      2 ^ 82 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) := by
    calc H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10))
        ≤ (2 ^ 71 * A * k ^ 3 * E ^ 3 * W ^ (r + 9)) *
            ((2 ^ 11 * W) * N ^ 2 * W ^ (10 * r ^ 2 + 10)) :=
          Nat.mul_le_mul hH (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ht_add))
      _ = 2 ^ 82 * A * k ^ 3 * E ^ 3 * (N ^ 2 * W ^ (10 * r ^ 2 + r + 20)) := by ring
      _ ≤ 2 ^ 82 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk3) hE3)
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 hexp1))
  have htermB : H * (t * b ^ 3 * L ^ 3) ≤
      2 ^ 96 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) := by
    have hb3 : b ^ 3 ≤ (2 ^ 5 * k * E * L) ^ 3 := Nat.pow_le_pow_left hb 3
    have hL7 : L ^ 7 ≤ W ^ 7 := Nat.pow_le_pow_left hLW 7
    have hB0 : t * b ^ 3 * L ^ 3 ≤ 2 ^ 25 * k ^ 3 * E ^ 3 * W ^ 7 := by
      calc t * b ^ 3 * L ^ 3
          ≤ (2 ^ 10 * L) * (2 ^ 5 * k * E * L) ^ 3 * L ^ 3 := by
              rw [ht_eq, show (1024 : ℕ) = 2 ^ 10 by decide]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb3)
        _ = 2 ^ 25 * k ^ 3 * E ^ 3 * L ^ 7 := by ring
        _ ≤ 2 ^ 25 * k ^ 3 * E ^ 3 * W ^ 7 := Nat.mul_le_mul_left _ hL7
    calc H * (t * b ^ 3 * L ^ 3)
        ≤ (2 ^ 71 * A * k ^ 3 * E ^ 3 * W ^ (r + 9)) * (2 ^ 25 * k ^ 3 * E ^ 3 * W ^ 7) :=
          Nat.mul_le_mul hH hB0
      _ = 2 ^ 96 * A * k ^ 6 * E ^ 6 * (1 * W ^ (r + 16)) := by ring
      _ ≤ 2 ^ 96 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hN2 (Nat.pow_le_pow_right hW1 hexp2))
  have htermC : H * L ≤ 2 ^ 71 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) := by
    calc H * L
        ≤ (2 ^ 71 * A * k ^ 3 * E ^ 3 * W ^ (r + 9)) * W := Nat.mul_le_mul hH hLW
      _ = 2 ^ 71 * A * k ^ 3 * E ^ 3 * (1 * W ^ (r + 10)) := by ring
      _ ≤ 2 ^ 71 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk3) hE3)
            (Nat.mul_le_mul hN2 (Nat.pow_le_pow_right hW1 hexp3))
  have htermD : Lam ^ 2 * L ^ 2 ≤ 2 ^ 96 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) := by
    have hLam2 : Lam ^ 2 ≤ (2 ^ 48 * k ^ 2 * E ^ 2 * W ^ (r + 6)) ^ 2 :=
      Nat.pow_le_pow_left hLam 2
    have hL2 : L ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hLW 2
    calc Lam ^ 2 * L ^ 2
        ≤ (2 ^ 48 * k ^ 2 * E ^ 2 * W ^ (r + 6)) ^ 2 * W ^ 2 := Nat.mul_le_mul hLam2 hL2
      _ = 2 ^ 96 * 1 * k ^ 4 * E ^ 4 * (1 * W ^ (2 * r + 14)) := by ring
      _ ≤ 2 ^ 96 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) :=
          Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hA1) hk4) hE4)
            (Nat.mul_le_mul hN2 (Nat.pow_le_pow_right hW1 hexp4))
  have hsum_inner :
      H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) + Lam ^ 2 * L ^ 2 ≤
      2 ^ 110 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) := by
    have hdist :
        H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) =
          H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10)) + H * (t * b ^ 3 * L ^ 3) + H * L := by
      ring
    have hcoeff : (2 ^ 82 + 2 ^ 96 + 2 ^ 71 + 2 ^ 96) *
        (A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2))) ≤
        2 ^ 110 * (A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2))) :=
      Nat.mul_le_mul_right _ (by decide)
    have hr1 : 2 ^ 82 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) +
        2 ^ 96 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) +
        2 ^ 71 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) +
        2 ^ 96 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) =
        (2 ^ 82 + 2 ^ 96 + 2 ^ 71 + 2 ^ 96) *
          (A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2))) := by ring
    have hr2 : 2 ^ 110 * (A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2))) =
        2 ^ 110 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2)) := by ring
    omega
  have hC_le : 2 ^ 40 * u ^ 3 ≤ 2 ^ 150 * u ^ 3 * A * k ^ 6 * E ^ 6 := by
    have h1 : 1 ≤ A * k ^ 6 * E ^ 6 :=
      Nat.mul_pos (Nat.mul_pos hA1 (Nat.pow_pos hk1)) (Nat.pow_pos hE1)
    have h2 : 2 ^ 40 ≤ 2 ^ 150 := Nat.pow_le_pow_right (by decide) (by decide)
    calc 2 ^ 40 * u ^ 3 = 2 ^ 40 * u ^ 3 * 1 := (mul_one _).symm
      _ ≤ 2 ^ 150 * u ^ 3 * (A * k ^ 6 * E ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ h2) h1
      _ = 2 ^ 150 * u ^ 3 * A * k ^ 6 * E ^ 6 := by ring
  have hmain :
      M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
        M * Lam ^ 2 * L ^ 2 ≤
      2 ^ 110 * A * k ^ 6 * E ^ 6 * (M * N ^ 2 * W ^ (40 * r ^ 2)) := by
    calc M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
          M * Lam ^ 2 * L ^ 2
        = M * (H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
            Lam ^ 2 * L ^ 2) := by ring
      _ ≤ M * (2 ^ 110 * A * k ^ 6 * E ^ 6 * (N ^ 2 * W ^ (40 * r ^ 2))) :=
          Nat.mul_le_mul_left M hsum_inner
      _ = 2 ^ 110 * A * k ^ 6 * E ^ 6 * (M * N ^ 2 * W ^ (40 * r ^ 2)) := by ring
  calc (2 ^ 40 * u ^ 3) *
        (n + M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
          M * Lam ^ 2 * L ^ 2)
      = (2 ^ 40 * u ^ 3) * n +
          (2 ^ 40 * u ^ 3) *
            (M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
              M * Lam ^ 2 * L ^ 2) := by ring
    _ ≤ (2 ^ 150 * u ^ 3 * A * k ^ 6 * E ^ 6) * n +
          (2 ^ 40 * u ^ 3) * (2 ^ 110 * A * k ^ 6 * E ^ 6 * (M * N ^ 2 * W ^ (40 * r ^ 2))) :=
        Nat.add_le_add (Nat.mul_le_mul_right n hC_le) (Nat.mul_le_mul_left _ hmain)
    _ = (2 ^ 150 * u ^ 3 * A * k ^ 6 * E ^ 6) * (n + M * N ^ 2 * W ^ (40 * r ^ 2)) := by ring

/-- **Total time bound**: for `1 ≤ r`, `totalTimeRaw cfg n M r ≤ K_* · (n + M · N^2 · W^{40 r^2})`. -/
theorem totalTimeRaw_le (cfg : ParamConfig) (n M : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    totalTimeRaw cfg n M r ≤
      cfg.KStar * (n + M * (NOf M r) ^ 2 * (WParam cfg M) ^ (40 * r ^ 2)) := by
  have hFW : FParam cfg M ≤ WParam cfg M := by unfold WParam; omega
  have hLW : LParam M ≤ WParam cfg M := by unfold WParam; omega
  have hP : PParam cfg M r ≤ (WParam cfg M) ^ r := Nat.pow_le_pow_left hFW r
  have hb := bOut_le cfg M
  have hH : HDepth cfg M r ≤
      2 ^ 71 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3 * (WParam cfg M) ^ (r + 9) := by
    have hH0 := HDepth_le cfg M r
    have hb3 : (bOut cfg M) ^ 3 ≤ (2 ^ 5 * cfg.kappa * cfg.E * LParam M) ^ 3 :=
      Nat.pow_le_pow_left hb 3
    have hL9 : (LParam M) ^ 9 ≤ (WParam cfg M) ^ 9 := Nat.pow_le_pow_left hLW 9
    calc HDepth cfg M r
        ≤ 2 ^ 56 * cfg.A * PParam cfg M r * (bOut cfg M) ^ 3 * (LParam M) ^ 6 := hH0
      _ ≤ 2 ^ 56 * cfg.A * (WParam cfg M) ^ r *
            (2 ^ 5 * cfg.kappa * cfg.E * LParam M) ^ 3 * (LParam M) ^ 6 :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ hP) hb3)
      _ = 2 ^ 71 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3 * ((WParam cfg M) ^ r * (LParam M) ^ 9) := by
          ring
      _ ≤ 2 ^ 71 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3 * ((WParam cfg M) ^ r * (WParam cfg M) ^ 9) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL9)
      _ = 2 ^ 71 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3 * (WParam cfg M) ^ (r + 9) := by ring
  have hLam : Lambda cfg M r ≤
      2 ^ 48 * cfg.kappa ^ 2 * cfg.E ^ 2 * (WParam cfg M) ^ (r + 6) := by
    have hL0 := Lambda_le cfg M r
    have hb2 : (bOut cfg M) ^ 2 ≤ (2 ^ 5 * cfg.kappa * cfg.E * LParam M) ^ 2 :=
      Nat.pow_le_pow_left hb 2
    have hL6 : (LParam M) ^ 6 ≤ (WParam cfg M) ^ 6 := Nat.pow_le_pow_left hLW 6
    calc Lambda cfg M r
        ≤ 2 ^ 38 * PParam cfg M r * (bOut cfg M) ^ 2 * (LParam M) ^ 4 := hL0
      _ ≤ 2 ^ 38 * (WParam cfg M) ^ r *
            (2 ^ 5 * cfg.kappa * cfg.E * LParam M) ^ 2 * (LParam M) ^ 4 :=
          Nat.mul_le_mul_right _
            (Nat.mul_le_mul (Nat.mul_le_mul_left _ hP) hb2)
      _ = 2 ^ 48 * cfg.kappa ^ 2 * cfg.E ^ 2 * ((WParam cfg M) ^ r * (LParam M) ^ 6) := by ring
      _ ≤ 2 ^ 48 * cfg.kappa ^ 2 * cfg.E ^ 2 * ((WParam cfg M) ^ r * (WParam cfg M) ^ 6) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hL6)
      _ = 2 ^ 48 * cfg.kappa ^ 2 * cfg.E ^ 2 * (WParam cfg M) ^ (r + 6) := by ring
  have ht_add : tParam M + 1 ≤ 2 ^ 11 * WParam cfg M := by
    have h1 : tParam M + 1 ≤ 2 * tParam M := by have := one_le_tParam M; omega
    calc tParam M + 1 ≤ 2 * tParam M := h1
      _ = 2 ^ 11 * LParam M := by unfold tParam; ring
      _ ≤ 2 ^ 11 * WParam cfg M := Nat.mul_le_mul_left _ hLW
  unfold totalTimeRaw ParamConfig.CTotal ParamConfig.KStar
  exact totalTimeRaw_le_aux hr
    (by unfold WParam; omega) hLW
    (le_trans (by decide) (four_le_NOf M r))
    (le_trans (by decide) cfg.A_pos)
    (le_trans (by decide) cfg.kappa_pos)
    cfg.hE rfl ht_add hb hH hLam

/-! ### Logarithmic bounds and fit to `ExpanderDecompositionUsed` -/

private theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [lt_inv_comm₀ (by norm_num) hpos] at h1
    linarith
  have h3 := Real.log_lt_log (Real.exp_pos _) h2
  simpa [Real.log_exp] using h3

private theorem log_two_lt_one : Real.log 2 < 1 := by
  have h1 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 := Real.log_lt_log (by norm_num) h1
  simpa [Real.log_exp] using h2

theorem envelopeCr_pos : (0 : ℝ) < envelopeCr := by
  unfold envelopeCr; norm_num

theorem envelopeK_pos (cfg : ParamConfig) : 0 < envelopeK cfg := by
  unfold envelopeK envelopeKNat ParamConfig.KStar
  have hA := cfg.A_pos
  have hk := cfg.kappa_pos
  have hE := cfg.hE
  have hu := cfg.hu
  have hpos : 0 < 2 ^ 150 * cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6 := by positivity
  exact_mod_cast lt_of_lt_of_le hpos (le_max_left _ _)

private theorem ten_le_envelopeK (cfg : ParamConfig) : (10 : ℝ) ≤ envelopeK cfg := by
  unfold envelopeK envelopeKNat ParamConfig.KStar
  have hA : 1 ≤ cfg.A := le_trans (by decide) cfg.A_pos
  have hk : 1 ≤ cfg.kappa := le_trans (by decide) cfg.kappa_pos
  have hE : 1 ≤ cfg.E := cfg.hE
  have hu : 1 ≤ cfg.u := cfg.hu
  have h10 : 10 ≤ 2 ^ 150 * cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6 := by
    have h1 : 1 ≤ cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hu) hA) (Nat.pow_pos hk)) (Nat.pow_pos hE)
    calc 10 ≤ 2 ^ 150 * 1 := by decide
      _ ≤ 2 ^ 150 * (cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6) :=
          Nat.mul_le_mul_left _ h1
      _ = 2 ^ 150 * cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6 := by ring
  exact_mod_cast le_trans h10 (le_max_left _ _)

/-- For `m ≥ thresholdB1 envelopeCr`, `2 ≤ log(m + 2)` (derived directly from `rOf_le_cr_log`
at `envelopeCr = 1 / 2`). -/
theorem two_le_log_of_thresholdB1 {m : ℕ} (hm : thresholdB1 envelopeCr ≤ m) :
    (2 : ℝ) ≤ Real.log ((m : ℝ) + 2) := by
  obtain ⟨hr1, hrlog⟩ := rOf_le_cr_log envelopeCr_pos hm
  have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmono : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log hm_pos (by linarith)
  have hr1r : (1 : ℝ) ≤ (rOf m : ℝ) := by exact_mod_cast hr1
  unfold envelopeCr at hrlog
  linarith

/-- For every `m`, `ℓ(m) · log 2 ≤ 3 · log(m + 2)`. -/
theorem ell_mul_log_two_le (m : ℕ) :
    (ell m : ℝ) * Real.log 2 ≤ 3 * Real.log ((m : ℝ) + 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hclog : ell m ≤ Nat.log 2 (2 * m + 2) + 1 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (2 * m + 2)))
  have hpow : (2 : ℝ) ^ (Nat.log 2 (2 * m + 2)) ≤ 2 * ((m : ℝ) + 2) := by
    have hnat : 2 ^ Nat.log 2 (2 * m + 2) ≤ 2 * m + 2 := Nat.pow_log_le_self 2 (by omega)
    have hnat2 : 2 ^ Nat.log 2 (2 * m + 2) ≤ 2 * (m + 2) := by omega
    exact_mod_cast hnat2
  have hlog_pow : (Nat.log 2 (2 * m + 2) : ℝ) * Real.log 2 ≤
      Real.log 2 + Real.log ((m : ℝ) + 2) := by
    have h1 := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at h1
    exact h1
  have hlog2_le : Real.log 2 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hcast : (ell m : ℝ) ≤ (Nat.log 2 (2 * m + 2) : ℝ) + 1 := by exact_mod_cast hclog
  calc (ell m : ℝ) * Real.log 2
      ≤ ((Nat.log 2 (2 * m + 2) : ℝ) + 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hcast hlog2.le
    _ = (Nat.log 2 (2 * m + 2) : ℝ) * Real.log 2 + Real.log 2 := by ring
    _ ≤ (Real.log 2 + Real.log ((m : ℝ) + 2)) + Real.log 2 := by linarith
    _ ≤ 3 * Real.log ((m : ℝ) + 2) := by linarith

/-- For every `m`, `L(m) ≤ 24 · log(m + 2)`. -/
theorem LParam_le_twentyFour_log (m : ℕ) :
    (LParam m : ℝ) ≤ 24 * Real.log ((m : ℝ) + 2) := by
  have h1 := ell_mul_log_two_le m
  have h2 := half_lt_log_two
  have hell_nn : (0 : ℝ) ≤ ell m := Nat.cast_nonneg _
  have h3 : (ell m : ℝ) * (1 / 2 : ℝ) ≤ (ell m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le hell_nn
  unfold LParam
  push_cast
  linarith

/-- For `m ≥ thresholdB1 envelopeCr`, `N(m)^2 ≤ (m + 2)^{K / rOf m}`. -/
theorem NParam_sq_le_rpow (cfg : ParamConfig) {m : ℕ} (hm : thresholdB1 envelopeCr ≤ m) :
    (NParam m : ℝ) ^ 2 ≤ ((m : ℝ) + 2) ^ (envelopeK cfg / (rOf m : ℝ)) := by
  obtain ⟨hr1, hrlog⟩ := rOf_le_cr_log envelopeCr_pos hm
  have hrpos : (0 : ℝ) < rOf m := by exact_mod_cast (by omega : 0 < rOf m)
  have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlogm_le : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log hm_pos (by linarith)
  have hr_le_log : (rOf m : ℝ) ≤ Real.log ((m : ℝ) + 2) := by
    unfold envelopeCr at hrlog
    have hlogm_nn : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    linarith
  have hceil_le : (max 2 (ceilDiv (ell m) (rOf m)) : ℝ) ≤ (ell m : ℝ) / (rOf m : ℝ) + 2 := by
    have hcd : (ceilDiv (ell m) (rOf m) : ℝ) ≤ (ell m : ℝ) / (rOf m : ℝ) + 1 := by
      have hmul : (rOf m : ℝ) * (ceilDiv (ell m) (rOf m) : ℝ) ≤ (ell m : ℝ) + (rOf m : ℝ) := by
        have hnat := mul_ceilDiv_le (a := ell m) hr1
        have hnat' : rOf m * ceilDiv (ell m) (rOf m) ≤ ell m + rOf m := by omega
        exact_mod_cast hnat'
      have hdiv : (ceilDiv (ell m) (rOf m) : ℝ) ≤ ((ell m : ℝ) + (rOf m : ℝ)) / (rOf m : ℝ) := by
        rw [le_div_iff₀ hrpos]; linarith
      have hsplit : ((ell m : ℝ) + (rOf m : ℝ)) / (rOf m : ℝ) = (ell m : ℝ) / (rOf m : ℝ) + 1 := by
        field_simp
      linarith
    have h2 : (2 : ℝ) ≤ (ell m : ℝ) / (rOf m : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (ell m : ℝ) / (rOf m : ℝ) := by positivity
      linarith
    exact max_le h2 (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt : Real.log 2 < 1 := log_two_lt_one
  have hell_bound := ell_mul_log_two_le m
  have hexp_le :
      (2 * (max 2 (ceilDiv (ell m) (rOf m)) : ℝ)) * Real.log 2 ≤
        Real.log ((m : ℝ) + 2) * (envelopeK cfg / (rOf m : ℝ)) := by
    have hK10 : (10 : ℝ) ≤ envelopeK cfg := ten_le_envelopeK cfg
    have hlog_nn : 0 ≤ Real.log ((m : ℝ) + 2) := le_trans (by norm_num) (two_le_log_of_thresholdB1 hm)
    have hterm1 : (2 * ((ell m : ℝ) / (rOf m : ℝ))) * Real.log 2 ≤
        6 * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) := by
      have hrew : (2 * ((ell m : ℝ) / (rOf m : ℝ))) * Real.log 2 =
          2 * ((ell m : ℝ) * Real.log 2) / (rOf m : ℝ) := by ring
      rw [hrew]
      exact div_le_div_of_nonneg_right (by linarith) hrpos.le
    have hterm2 : 4 * Real.log 2 ≤ 4 * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) := by
      rw [le_div_iff₀ hrpos]
      have h1 : 4 * Real.log 2 * (rOf m : ℝ) ≤ 4 * 1 * (rOf m : ℝ) := by
        have := hrpos.le; nlinarith
      linarith
    have h10 : 10 * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) ≤
        Real.log ((m : ℝ) + 2) * (envelopeK cfg / (rOf m : ℝ)) := by
      have hrew : Real.log ((m : ℝ) + 2) * (envelopeK cfg / (rOf m : ℝ)) =
          envelopeK cfg * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) := by ring
      rw [hrew]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK10 hlog_nn) hrpos.le
    calc (2 * (max 2 (ceilDiv (ell m) (rOf m)) : ℝ)) * Real.log 2
        ≤ (2 * ((ell m : ℝ) / (rOf m : ℝ) + 2)) * Real.log 2 := by
            exact mul_le_mul_of_nonneg_right (by linarith) hlog2_pos.le
      _ = (2 * ((ell m : ℝ) / (rOf m : ℝ))) * Real.log 2 + 4 * Real.log 2 := by ring
      _ ≤ 6 * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) + 4 * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) := by
            linarith
      _ = 10 * Real.log ((m : ℝ) + 2) / (rOf m : ℝ) := by ring
      _ ≤ Real.log ((m : ℝ) + 2) * (envelopeK cfg / (rOf m : ℝ)) := h10
  have hlhs : (NParam m : ℝ) ^ 2 =
      Real.exp ((2 * (max 2 (ceilDiv (ell m) (rOf m)) : ℝ)) * Real.log 2) := by
    unfold NParam NOf
    rw [← Nat.cast_pow, ← Nat.pow_mul, Nat.mul_comm]
    have hpow : ((2 ^ (2 * max 2 (ceilDiv (ell m) (rOf m))) : ℕ) : ℝ) =
        (2 : ℝ) ^ (2 * max 2 (ceilDiv (ell m) (rOf m))) := by push_cast; rfl
    rw [hpow, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  have hrhs : ((m : ℝ) + 2) ^ (envelopeK cfg / (rOf m : ℝ)) =
      Real.exp (Real.log ((m : ℝ) + 2) * (envelopeK cfg / (rOf m : ℝ))) :=
    Real.rpow_def_of_pos (by positivity) _
  rw [hlhs, hrhs]
  exact Real.exp_le_exp.mpr hexp_le

/-- For `m ≥ thresholdB1 envelopeCr`, `W^{40 r^2} ≤ log(m + 2)^{K r^2}`. -/
theorem WParam_pow_le_log_rpow (cfg : ParamConfig) {m : ℕ} (hm : thresholdB1 envelopeCr ≤ m) :
    (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2) ≤
      Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) := by
  have hlog2 : (2 : ℝ) ≤ Real.log ((m : ℝ) + 2) := two_le_log_of_thresholdB1 hm
  have hlog1 : (1 : ℝ) ≤ Real.log ((m : ℝ) + 2) := by linarith
  have hlog_pos : 0 < Real.log ((m : ℝ) + 2) := by linarith
  set kB := Nat.clog 2 (wLogConst cfg)
  have hW_le : (WParam cfg m : ℝ) ≤ Real.log ((m : ℝ) + 2) ^ (kB + 6) := by
    have h1 : (WParam cfg m : ℝ) ≤ (cfg.wConst : ℝ) * (LParam m : ℝ) ^ 6 := by
      exact_mod_cast WParam_le cfg m
    have h2 : (LParam m : ℝ) ^ 6 ≤ (24 * Real.log ((m : ℝ) + 2)) ^ 6 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (LParam_le_twentyFour_log m) 6
    have h3 : (wLogConst cfg : ℝ) ≤ (2 : ℝ) ^ kB := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) (wLogConst cfg)
    have h4 : (2 : ℝ) ^ kB ≤ Real.log ((m : ℝ) + 2) ^ kB :=
      pow_le_pow_left₀ (by norm_num) hlog2 kB
    calc (WParam cfg m : ℝ)
        ≤ (cfg.wConst : ℝ) * (LParam m : ℝ) ^ 6 := h1
      _ ≤ (cfg.wConst : ℝ) * (24 * Real.log ((m : ℝ) + 2)) ^ 6 :=
            mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (wLogConst cfg : ℝ) * Real.log ((m : ℝ) + 2) ^ 6 := by
            unfold wLogConst; push_cast; ring
      _ ≤ Real.log ((m : ℝ) + 2) ^ kB * Real.log ((m : ℝ) + 2) ^ 6 :=
            mul_le_mul_of_nonneg_right (le_trans h3 h4) (by positivity)
      _ = Real.log ((m : ℝ) + 2) ^ (kB + 6) := by rw [pow_add]
  have hpow : (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2) ≤
      Real.log ((m : ℝ) + 2) ^ ((kB + 6) * (40 * (rOf m) ^ 2)) := by
    calc (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2)
        ≤ (Real.log ((m : ℝ) + 2) ^ (kB + 6)) ^ (40 * (rOf m) ^ 2) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hW_le _
      _ = Real.log ((m : ℝ) + 2) ^ ((kB + 6) * (40 * (rOf m) ^ 2)) := by rw [← pow_mul]
  have hexp_nat : 40 * (kB + 6) ≤ envelopeKNat cfg := le_max_right _ _
  have hexp_real : (((kB + 6) * (40 * (rOf m) ^ 2) : ℕ) : ℝ) ≤
      envelopeK cfg * (rOf m : ℝ) ^ 2 := by
    have h1 : (40 * (kB + 6) : ℝ) ≤ envelopeK cfg := by
      unfold envelopeK; exact_mod_cast hexp_nat
    have h2 : (((kB + 6) * (40 * (rOf m) ^ 2) : ℕ) : ℝ) =
        (40 * (kB + 6) : ℝ) * (rOf m : ℝ) ^ 2 := by push_cast; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2)
      ≤ Real.log ((m : ℝ) + 2) ^ ((kB + 6) * (40 * (rOf m) ^ 2)) := hpow
    _ = Real.log ((m : ℝ) + 2) ^ (((kB + 6) * (40 * (rOf m) ^ 2) : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
    _ ≤ Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 hexp_real

/-- **Inverse-conductance envelope bound**: for `m ≥ thresholdB1 envelopeCr`,
`1 / φ = Q ≤ 200 · K · log(m + 2)^{K r^2}`. -/
theorem QOut_le_envelope (cfg : ParamConfig) {m : ℕ} (hm : thresholdB1 envelopeCr ≤ m) :
    (QOut cfg m (rOf m) : ℝ) ≤
      200 * envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) := by
  have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hr1 : 1 ≤ rOf m := one_le_rOf (by omega)
  have hW1 : 1 ≤ WParam cfg m := by unfold WParam; omega
  have hQ_nat : QOut cfg m (rOf m) ≤ cfg.KStar * (WParam cfg m) ^ (40 * (rOf m) ^ 2) := by
    calc QOut cfg m (rOf m)
        ≤ cfg.C1 * (WParam cfg m) ^ (rOf m + 8) := QOut_le_C1_W_pow cfg m (rOf m)
      _ ≤ cfg.KStar * (WParam cfg m) ^ (40 * (rOf m) ^ 2) := by
            apply Nat.mul_le_mul cfg.C1_le_KStar
            apply Nat.pow_le_pow_right hW1
            nlinarith
  have hQ_r : (QOut cfg m (rOf m) : ℝ) ≤
      (cfg.KStar : ℝ) * (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2) := by
    exact_mod_cast hQ_nat
  have hKStar_le : (cfg.KStar : ℝ) ≤ envelopeK cfg := by
    unfold envelopeK envelopeKNat
    exact_mod_cast (le_max_left cfg.KStar (40 * (Nat.clog 2 (wLogConst cfg) + 6)))
  have hW_rpow := WParam_pow_le_log_rpow cfg hm
  have hlog_pos : 0 < Real.log ((m : ℝ) + 2) := lt_of_lt_of_le (by norm_num) (two_le_log_of_thresholdB1 hm)
  have hrpow_nn : 0 ≤ Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
    (Real.rpow_pos_of_pos hlog_pos _).le
  have hK_nn : 0 ≤ envelopeK cfg := (envelopeK_pos cfg).le
  calc (QOut cfg m (rOf m) : ℝ)
      ≤ (cfg.KStar : ℝ) * (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2) := hQ_r
    _ ≤ envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
        mul_le_mul hKStar_le hW_rpow (by positivity) hK_nn
    _ ≤ 200 * envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) := by
        have : 0 ≤ envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
          mul_nonneg hK_nn hrpow_nn
        linarith

/-- **Conductance fit to `ExpanderDecompositionUsed`**: for `m ≥ thresholdB1 envelopeCr`,
`((1 : ℕ) / (200 : ℕ)) / (K · log(m + 2)^{K r^2}) ≤ φ(m) = 1 / Q(m, rOf m)`. -/
theorem phiOut_ge_used (cfg : ParamConfig) {m : ℕ} (hm : thresholdB1 envelopeCr ≤ m) :
    (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
        (envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2)) ≤
      phiOut cfg m (rOf m) := by
  unfold phiOut
  have hQ_pos : (0 : ℝ) < (QOut cfg m (rOf m) : ℝ) := by unfold QOut; positivity
  have hlog_pos : 0 < Real.log ((m : ℝ) + 2) := lt_of_lt_of_le (by norm_num) (two_le_log_of_thresholdB1 hm)
  have hrpow_pos : 0 < Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
    Real.rpow_pos_of_pos hlog_pos _
  have hK_pos : 0 < envelopeK cfg := envelopeK_pos cfg
  have hQ := QOut_le_envelope cfg hm
  have hlhs :
      (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) /
          (envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2)) =
        1 / (200 * envelopeK cfg * Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2)) := by
    push_cast
    field_simp
  rw [hlhs]
  exact one_div_le_one_div_of_le hQ_pos hQ

/-- **Time envelope bound**: for `m ≥ thresholdB1 envelopeCr` and any `n : ℕ`,
`totalTimeRaw cfg n m (rOf m) ≤ K · (n + (m + 2)^{1 + K / r} · log(m + 2)^{K r^2} · 200^2)`. -/
theorem totalTimeRaw_le_envelope (cfg : ParamConfig) (n : ℕ) {m : ℕ}
    (hm : thresholdB1 envelopeCr ≤ m) :
    (totalTimeRaw cfg n m (rOf m) : ℝ) ≤
      envelopeK cfg * (n + ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
        Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) * 200 ^ 2) := by
  have hm4 : 4 ≤ m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have hr1 : 1 ≤ rOf m := one_le_rOf (by omega)
  have hraw : (totalTimeRaw cfg n m (rOf m) : ℝ) ≤
      (cfg.KStar : ℝ) * ((n : ℝ) + (m : ℝ) * (NParam m : ℝ) ^ 2 *
        (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2)) := by
    exact_mod_cast totalTimeRaw_le cfg n m hr1
  have hKStar_le : (cfg.KStar : ℝ) ≤ envelopeK cfg := by
    unfold envelopeK envelopeKNat
    exact_mod_cast (le_max_left cfg.KStar (40 * (Nat.clog 2 (wLogConst cfg) + 6)))
  have hK_nn : 0 ≤ envelopeK cfg := (envelopeK_pos cfg).le
  have hN := NParam_sq_le_rpow cfg hm
  have hW := WParam_pow_le_log_rpow cfg hm
  have hm_le : (m : ℝ) ≤ (m : ℝ) + 2 := by linarith
  have hm2_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hlog_pos : 0 < Real.log ((m : ℝ) + 2) := lt_of_lt_of_le (by norm_num) (two_le_log_of_thresholdB1 hm)
  have hrpow1 : ((m : ℝ) + 2) * ((m : ℝ) + 2) ^ (envelopeK cfg / (rOf m : ℝ)) =
      ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) := by
    rw [Real.rpow_add hm2_pos, Real.rpow_one]
  have hprod : (m : ℝ) * (NParam m : ℝ) ^ 2 * (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2) ≤
      ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
        Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) * 200 ^ 2 := by
    have h1 : (m : ℝ) * (NParam m : ℝ) ^ 2 ≤ ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) := by
      rw [← hrpow1]
      exact mul_le_mul hm_le hN (by positivity) hm2_pos.le
    have h2 : (m : ℝ) * (NParam m : ℝ) ^ 2 * (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2) ≤
        ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
          Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
      mul_le_mul h1 hW (by positivity) (Real.rpow_pos_of_pos hm2_pos _).le
    have hnn : 0 ≤ ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
        Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) :=
      mul_nonneg (Real.rpow_pos_of_pos hm2_pos _).le (Real.rpow_pos_of_pos hlog_pos _).le
    linarith
  calc (totalTimeRaw cfg n m (rOf m) : ℝ)
      ≤ (cfg.KStar : ℝ) * ((n : ℝ) + (m : ℝ) * (NParam m : ℝ) ^ 2 *
          (WParam cfg m : ℝ) ^ (40 * (rOf m) ^ 2)) := hraw
    _ ≤ envelopeK cfg * ((n : ℝ) + ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
          Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) * 200 ^ 2) :=
        mul_le_mul hKStar_le (add_le_add_right hprod _) (by positivity) hK_nn

/-- **Time fit to `ExpanderDecompositionUsed`** (with the exact casts of
`MinCostFlow/ExpanderDecomp/Statement.lean`). -/
theorem totalTimeRaw_le_used (cfg : ParamConfig) (n : ℕ) {m : ℕ}
    (hm : thresholdB1 envelopeCr ≤ m) :
    (totalTimeRaw cfg n m (rOf m) : ℝ) ≤
      envelopeK cfg * (n + ((m : ℝ) + 2) ^ (1 + envelopeK cfg / rOf m) *
        Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) := by
  have h := totalTimeRaw_le_envelope cfg n hm
  have hrew : ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
        Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2 =
      ((m : ℝ) + 2) ^ (1 + envelopeK cfg / (rOf m : ℝ)) *
        Real.log ((m : ℝ) + 2) ^ (envelopeK cfg * (rOf m : ℝ) ^ 2) * 200 ^ 2 := by
    push_cast
    ring
  rw [hrew]
  exact h

end MinCostFlow.ExpanderDecomp
