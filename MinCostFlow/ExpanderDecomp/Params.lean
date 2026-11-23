module

public import MinCostFlow.Expander.ExpanderDecomp
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Parameters, integer schedule, and monotonicity for the expander decomposition

This file defines the global integer schedule (for the recursion depth `r = rOf m`), the core and
outer parameters, and the closed-form time bounds of the expander decomposition.

Main results:
* Schedule bounds: `four_le_NOf`, `four_dvd_NOf`, `two_mul_add_two_le_NOf_pow`, and
  `NOf_pow_add_two_le_two_pow_L` (with specializations to `r = rOf M` for `2 ≤ M`).
* The core cost recurrence gives the closed-form bound (`coreTimeBound_rec`), and the
  size-sensitive core bound (`coreTimeBound_size_sensitive`).
* Auxiliary inequalities used by the core and outer algorithms (`512 * L + 19 ≤ Δ`, `12 ∣ P_q`,
  `12 * Λ ≤ Q`, `2 * a₀ ≤ b_out`, etc.).
* Monotonicity: `rOf_mono`, monotonicity of every quantity in `Q`, and
  `phiOut_pos`, `phiOut_le_one`, `phiOut_antitone`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Expander

/-- Base integer constants entering the expander-decomposition parameters:
* `a₀`: inverse cloud-expander expansion (`α = 1 / a₀ ≤ α₀`);
* `a`: trimming volume constant (`C ≤ a / φ₀`, `A = 16 a`);
* `E`: inverse crossing-edge error (`ε = 1 / E`, with `E = 200` for the target);
* `u`: machine constant dominating primitive routine coefficients (BFS, trimming, scans). -/
structure ParamConfig where
  /-- Inverse cloud-expander expansion constant `a₀ ≥ 1`. -/
  a₀ : ℕ
  /-- Trimming volume constant `a ≥ 1`. -/
  a : ℕ
  /-- Inverse error parameter `E ≥ 1` (`ε = 1 / E`). -/
  E : ℕ
  /-- Primitive-cost coefficient `u ≥ 1`. -/
  u : ℕ
  /-- `a₀ ≥ 1`. -/
  ha₀ : 1 ≤ a₀
  /-- `a ≥ 1`. -/
  ha : 1 ≤ a
  /-- `E ≥ 1`. -/
  hE : 1 ≤ E
  /-- `u ≥ 1`. -/
  hu : 1 ≤ u

namespace ParamConfig

/-- Default configuration matching `ExplicitExpander.alpha0 = 1/12`, `FakeEdges.removeFake_spec`,
`ε = 1/200`, and unit machine constant `u = 1`. -/
def default : ParamConfig where
  a₀ := 12
  a := 15
  E := 200
  u := 1
  ha₀ := by decide
  ha := by decide
  hE := by decide
  hu := by decide

/-- `A = 16 a`. -/
def A (cfg : ParamConfig) : ℕ := 16 * cfg.a

/-- `κ = 2(a₀ + 1)`. -/
def kappa (cfg : ParamConfig) : ℕ := 2 * (cfg.a₀ + 1)

/-- Core path-length coefficient `d₀ = 3276801`. -/
def d0 : ℕ := 3276801

/-- Core congestion coefficient `R₀ = 1600 · 1024 · d₀`. -/
def R0 : ℕ := 1600 * 1024 * d0

/-- One-shot recurrence coefficient `s₀`. -/
def s0 (cfg : ParamConfig) : ℕ :=
  4 * cfg.u * 1024 ^ 2 * d0 * R0 + 2 ^ 30 * cfg.u ^ 3 + 2048

/-- Core recurrence coefficient `c₀ = 4096 s₀`. -/
def c0 (cfg : ParamConfig) : ℕ := 4096 * cfg.s0

/-- Constant factor `w = 2^74 a₀ + 3 c₀ A + 3` in `W ≤ w L^6`. -/
def wConst (cfg : ParamConfig) : ℕ := 2 ^ 74 * cfg.a₀ + 3 * cfg.c0 * cfg.A + 3

/-- Constant factor `C = 2^40 u^3` in the total time formula. -/
def CTotal (cfg : ParamConfig) : ℕ := 2 ^ 40 * cfg.u ^ 3

/-- Constant factor `C₁ = 2^69 A κ^3 E^3` in `Q ≤ C₁ P L^8`. -/
def C1 (cfg : ParamConfig) : ℕ := 2 ^ 69 * cfg.A * cfg.kappa ^ 3 * cfg.E ^ 3

/-- Constant factor `K_* = 2^150 u^3 A κ^6 E^6` in the total time bound. -/
def KStar (cfg : ParamConfig) : ℕ :=
  2 ^ 150 * cfg.u ^ 3 * cfg.A * cfg.kappa ^ 6 * cfg.E ^ 6

end ParamConfig

/-! ### Global integer schedule (adapted to depth `r = rOf M`) -/

/-- Integer ceiling division `⌈a / b⌉` (returns `0` when `b = 0`). -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- `ℓ = ⌈log₂(2M + 2)⌉`. -/
def ell (M : ℕ) : ℕ := Nat.clog 2 (2 * M + 2)

/-- `L = 4ℓ`. -/
def LParam (M : ℕ) : ℕ := 4 * ell M

/-- Branching factor `N = 2^{max(2, ⌈ℓ / r⌉)}` for depth `r`. -/
def NOf (M r : ℕ) : ℕ := 2 ^ max 2 (ceilDiv (ell M) r)

/-- Branching factor `N` specialized to `r = rOf M`. -/
def NParam (M : ℕ) : ℕ := NOf M (rOf M)

/-! ### Core and outer parameters -/

/-- Round and degree bound `t = Δ = 1024 L`. -/
def tParam (M : ℕ) : ℕ := 1024 * LParam M

/-- Core maximum degree bound `Δ = t = 1024 L`. -/
def deltaParam (M : ℕ) : ℕ := tParam M

/-- Core routing path-length bound `d_c = 3200 Δ L`. -/
def dCore (M : ℕ) : ℕ := 3200 * deltaParam M * LParam M

/-- Core routing congestion bound `R_c = 1600 Δ (d_c + 1) L`. -/
def RCore (M : ℕ) : ℕ := 1600 * deltaParam M * (dCore M + 1) * LParam M

/-- Core per-level expansion loss `F = 1920 a₀ Δ^2 R_c`. -/
def FParam (cfg : ParamConfig) (M : ℕ) : ℕ :=
  1920 * cfg.a₀ * (deltaParam M) ^ 2 * RCore M

/-- Core inverse expansion `P_q = F^q` at level `q`. -/
def PParam (cfg : ParamConfig) (M q : ℕ) : ℕ := (FParam cfg M) ^ q

/-- Core deficit denominator `D_q = A Δ P_q` at level `q`. -/
def DCore (cfg : ParamConfig) (M q : ℕ) : ℕ := cfg.A * deltaParam M * PParam cfg M q

/-- Recurrence base `W = F + 3 c₀ A + L + 2`. -/
def WParam (cfg : ParamConfig) (M : ℕ) : ℕ :=
  FParam cfg M + 3 * cfg.c0 * cfg.A + LParam M + 2

/-- Closed-form core time bound `N^{q+1} W^{10 q^2 + 10}`. -/
def coreTimeBound (cfg : ParamConfig) (M r q : ℕ) : ℕ :=
  (NOf M r) ^ (q + 1) * (WParam cfg M) ^ (10 * q ^ 2 + 10)

/-- Outer sparsity denominator `b_out = 16 κ (L + 1) E`. -/
def bOut (cfg : ParamConfig) (M : ℕ) : ℕ :=
  16 * cfg.kappa * (LParam M + 1) * cfg.E

/-- Outer routing path-length bound `d_out = 320 b_out L`. -/
def dOut (cfg : ParamConfig) (M : ℕ) : ℕ :=
  320 * bOut cfg M * LParam M

/-- Outer routing congestion bound `R_out = 160 b_out (d_out + 1) L`. -/
def ROut (cfg : ParamConfig) (M : ℕ) : ℕ :=
  160 * bOut cfg M * (dOut cfg M + 1) * LParam M

/-- Outer conductance denominator `Λ = 2 P_r t R_out (t + 1)`. -/
def Lambda (cfg : ParamConfig) (M r : ℕ) : ℕ :=
  2 * PParam cfg M r * tParam M * ROut cfg M * (tParam M + 1)

/-- Outer deficit denominator `D = 16 A t Λ b_out`. -/
def DOut (cfg : ParamConfig) (M r : ℕ) : ℕ :=
  16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M

/-- Base-case edge threshold and inverse conductance `Q = 2 D + 2`. -/
def QOut (cfg : ParamConfig) (M r : ℕ) : ℕ :=
  2 * DOut cfg M r + 2

/-- Outer conductance `φ(M) = 1 / Q`. -/
noncomputable def phiOut (cfg : ParamConfig) (M r : ℕ) : ℝ :=
  1 / (QOut cfg M r : ℝ)

/-- Global outer recursion depth bound `H_depth = 16 D (ℓ + 1) + 2`. -/
def HDepth (cfg : ParamConfig) (M r : ℕ) : ℕ :=
  16 * DOut cfg M r * (ell M + 1) + 2

/-- The closed-form total time of the expander decomposition. -/
def totalTimeRaw (cfg : ParamConfig) (n M r : ℕ) : ℕ :=
  cfg.CTotal *
    (n + M * HDepth cfg M r *
        ((tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
          tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 +
          LParam M) +
      M * (Lambda cfg M r) ^ 2 * (LParam M) ^ 2)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Expander

/-! ### Basic positivity and divisibility bounds -/

theorem ParamConfig.A_pos (cfg : ParamConfig) : 16 ≤ cfg.A := by
  unfold ParamConfig.A; have := cfg.ha; omega

theorem ParamConfig.kappa_pos (cfg : ParamConfig) : 4 ≤ cfg.kappa := by
  unfold ParamConfig.kappa; have := cfg.ha₀; omega

theorem ParamConfig.c0_pos (cfg : ParamConfig) : 1 ≤ cfg.c0 := by
  unfold ParamConfig.c0 ParamConfig.s0; omega

theorem one_le_ell (M : ℕ) : 1 ≤ ell M := by
  unfold ell
  by_contra h
  have h0 : Nat.clog 2 (2 * M + 2) = 0 := by omega
  have hle : 2 * M + 2 ≤ 2 ^ 0 := h0 ▸ Nat.le_pow_clog (by norm_num) (2 * M + 2)
  omega

theorem four_le_LParam (M : ℕ) : 4 ≤ LParam M := by
  unfold LParam; have := one_le_ell M; omega

theorem one_le_tParam (M : ℕ) : 1 ≤ tParam M := by
  unfold tParam; have := four_le_LParam M; omega

theorem rOf_lt_ell (M : ℕ) : rOf M < ell M := by
  by_cases hM : M = 0
  · subst hM
    rw [rOf_zero]
    exact one_le_ell 0
  · have h1 : (rOf M) ^ 3 ≤ Nat.log 2 M := rOf_pow_le M
    have h2 : rOf M ≤ (rOf M) ^ 3 := by
      rcases Nat.eq_zero_or_pos (rOf M) with h0 | hpos
      · simp [h0]
      · calc rOf M = rOf M * 1 := (mul_one _).symm
          _ ≤ rOf M * (rOf M * rOf M) := Nat.mul_le_mul_left _ (by nlinarith)
          _ = (rOf M) ^ 3 := by ring
    have h3 : 2 ^ (Nat.log 2 M) < 2 * M + 2 := by
      have hpow : 2 ^ (Nat.log 2 M) ≤ M := Nat.pow_log_le_self 2 hM
      omega
    have h4 : Nat.log 2 M < ell M := by
      unfold ell
      by_contra hge
      have hle : Nat.clog 2 (2 * M + 2) ≤ Nat.log 2 M := by omega
      have hpow1 : 2 * M + 2 ≤ 2 ^ Nat.clog 2 (2 * M + 2) :=
        Nat.le_pow_clog (by norm_num) (2 * M + 2)
      have hpow2 : 2 ^ Nat.clog 2 (2 * M + 2) ≤ 2 ^ Nat.log 2 M :=
        Nat.pow_le_pow_right (by norm_num) hle
      omega
    omega

theorem rOf_le_ell (M : ℕ) : rOf M ≤ ell M :=
  le_of_lt (rOf_lt_ell M)

/-! ### Schedule bounds -/

theorem le_mul_ceilDiv {a b : ℕ} (hb : 1 ≤ b) : a ≤ b * ceilDiv a b := by
  unfold ceilDiv
  have hmod : (a + b - 1) % b < b := Nat.mod_lt _ (by omega)
  have hdiv : b * ((a + b - 1) / b) + (a + b - 1) % b = a + b - 1 := Nat.div_add_mod _ _
  omega

theorem mul_ceilDiv_le {a b : ℕ} (_hb : 1 ≤ b) : b * ceilDiv a b ≤ a + b - 1 := by
  unfold ceilDiv
  exact Nat.mul_div_le (a + b - 1) b

theorem four_le_NOf (M r : ℕ) : 4 ≤ NOf M r := by
  unfold NOf
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ max 2 (ceilDiv (ell M) r) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)

theorem four_dvd_NOf (M r : ℕ) : 4 ∣ NOf M r := by
  unfold NOf
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_max_left 2 (ceilDiv (ell M) r))
  rw [hk, Nat.pow_add]
  exact ⟨2 ^ k, by ring⟩

/-- **Schedule bound, lower**: `N^r ≥ 2M + 2` whenever `r ≥ 1`. -/
theorem two_mul_add_two_le_NOf_pow (M : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    2 * M + 2 ≤ (NOf M r) ^ r := by
  unfold NOf
  rw [← Nat.pow_mul]
  have hexp : ell M ≤ max 2 (ceilDiv (ell M) r) * r := by
    calc ell M ≤ r * ceilDiv (ell M) r := le_mul_ceilDiv hr
      _ = ceilDiv (ell M) r * r := Nat.mul_comm _ _
      _ ≤ max 2 (ceilDiv (ell M) r) * r := Nat.mul_le_mul_right r (le_max_right _ _)
  calc 2 * M + 2 ≤ 2 ^ ell M := Nat.le_pow_clog (by norm_num) (2 * M + 2)
    _ ≤ 2 ^ (max 2 (ceilDiv (ell M) r) * r) := Nat.pow_le_pow_right (by norm_num) hexp

/-- **Schedule bound, upper**: `N^r + 2 ≤ 2^L` whenever `1 ≤ r ≤ ℓ`. -/
theorem NOf_pow_add_two_le_two_pow_L (M : ℕ) {r : ℕ} (hr1 : 1 ≤ r) (hrl : r ≤ ell M) :
    (NOf M r) ^ r + 2 ≤ 2 ^ LParam M := by
  unfold NOf LParam
  rw [← Nat.pow_mul]
  have hexp : max 2 (ceilDiv (ell M) r) * r ≤ 3 * ell M := by
    rcases le_total 2 (ceilDiv (ell M) r) with h | h
    · rw [max_eq_right h, Nat.mul_comm]
      have h1 := mul_ceilDiv_le (a := ell M) hr1
      omega
    · rw [max_eq_left h]
      omega
  have h1 : 2 ^ (max 2 (ceilDiv (ell M) r) * r) ≤ 2 ^ (3 * ell M) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hell : 1 ≤ ell M := one_le_ell M
  have h2 : 2 ≤ 2 ^ (3 * ell M) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * ell M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 2 ^ (3 * ell M) + 2 ^ (3 * ell M) = 2 ^ (3 * ell M + 1) := by
    rw [Nat.pow_succ]; ring
  have h4 : 2 ^ (3 * ell M + 1) ≤ 2 ^ (4 * ell M) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Schedule bounds specialized to `r = rOf M` for `2 ≤ M`. -/
theorem schedule_rOf {M : ℕ} (hM : 2 ≤ M) :
    4 ≤ NParam M ∧ 2 * M + 2 ≤ (NParam M) ^ (rOf M) ∧
      (NParam M) ^ (rOf M) + 2 ≤ 2 ^ LParam M :=
  ⟨four_le_NOf M (rOf M),
    two_mul_add_two_le_NOf_pow M (one_le_rOf hM),
    NOf_pow_add_two_le_two_pow_L M (one_le_rOf hM) (rOf_le_ell M)⟩

/-! ### Auxiliary inequalities used by the core and outer algorithms -/

theorem core_rounds_le_delta (M : ℕ) : 512 * LParam M + 19 ≤ deltaParam M := by
  unfold deltaParam tParam
  have := four_le_LParam M
  omega

theorem outer_rounds_le_t (M : ℕ) : 512 * LParam M + 1 ≤ tParam M := by
  unfold tParam
  have := four_le_LParam M
  omega

theorem one_le_FParam (cfg : ParamConfig) (M : ℕ) : 1 ≤ FParam cfg M := by
  unfold FParam RCore dCore deltaParam tParam
  have ha₀ : 0 < cfg.a₀ := cfg.ha₀
  have hL : 0 < LParam M := lt_of_lt_of_le (by decide) (four_le_LParam M)
  change 0 < _
  positivity

theorem one_le_PParam (cfg : ParamConfig) (M q : ℕ) : 1 ≤ PParam cfg M q :=
  Nat.one_le_pow q (FParam cfg M) (one_le_FParam cfg M)

theorem twelve_dvd_FParam (cfg : ParamConfig) (M : ℕ) : 12 ∣ FParam cfg M := by
  unfold FParam
  exact ⟨160 * cfg.a₀ * (deltaParam M) ^ 2 * RCore M, by ring⟩

theorem twelve_dvd_PParam (cfg : ParamConfig) (M : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    12 ∣ PParam cfg M q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hq
  unfold PParam
  rw [Nat.pow_succ]
  exact dvd_mul_of_dvd_right (twelve_dvd_FParam cfg M) _

theorem two_mul_a0_le_bOut (cfg : ParamConfig) (M : ℕ) : 2 * cfg.a₀ ≤ bOut cfg M := by
  unfold bOut ParamConfig.kappa
  have hL : 1 ≤ LParam M + 1 := by omega
  have hE : 1 ≤ cfg.E := cfg.hE
  calc 2 * cfg.a₀ ≤ 16 * (2 * (cfg.a₀ + 1)) := by omega
    _ = 16 * (2 * (cfg.a₀ + 1)) * 1 * 1 := by ring
    _ ≤ 16 * (2 * (cfg.a₀ + 1)) * (LParam M + 1) * cfg.E :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hL) hE

theorem E_le_bOut (cfg : ParamConfig) (M : ℕ) : cfg.E ≤ bOut cfg M := by
  unfold bOut
  have h1 : 1 ≤ 16 * cfg.kappa * (LParam M + 1) := by
    have := cfg.kappa_pos
    have := four_le_LParam M
    nlinarith
  calc cfg.E = 1 * cfg.E := (one_mul _).symm
    _ ≤ 16 * cfg.kappa * (LParam M + 1) * cfg.E := Nat.mul_le_mul_right _ h1

theorem cut_budget_denom (cfg : ParamConfig) (M : ℕ) :
    16 * cfg.kappa * (ell M + 1) * cfg.E ≤ bOut cfg M := by
  unfold bOut LParam
  have h1 : ell M + 1 ≤ 4 * ell M + 1 := by omega
  have h2 : 16 * cfg.kappa * (ell M + 1) ≤ 16 * cfg.kappa * (4 * ell M + 1) :=
    Nat.mul_le_mul_left _ h1
  exact Nat.mul_le_mul_right _ h2

theorem one_le_bOut (cfg : ParamConfig) (M : ℕ) : 1 ≤ bOut cfg M :=
  le_trans cfg.hE (E_le_bOut cfg M)

theorem one_le_ROut (cfg : ParamConfig) (M : ℕ) : 1 ≤ ROut cfg M := by
  unfold ROut
  have hb : 0 < bOut cfg M := one_le_bOut cfg M
  have hL : 0 < LParam M := lt_of_lt_of_le (by decide) (four_le_LParam M)
  change 0 < _
  positivity

theorem one_le_Lambda (cfg : ParamConfig) (M r : ℕ) : 1 ≤ Lambda cfg M r := by
  unfold Lambda
  have hP : 0 < PParam cfg M r := one_le_PParam cfg M r
  have ht : 0 < tParam M := one_le_tParam M
  have hR : 0 < ROut cfg M := one_le_ROut cfg M
  change 0 < _
  positivity

theorem one_le_DOut (cfg : ParamConfig) (M r : ℕ) : 1 ≤ DOut cfg M r := by
  unfold DOut
  have hA : 0 < cfg.A := lt_of_lt_of_le (by decide) cfg.A_pos
  have ht : 0 < tParam M := one_le_tParam M
  have hL : 0 < Lambda cfg M r := one_le_Lambda cfg M r
  have hb : 0 < bOut cfg M := one_le_bOut cfg M
  change 0 < _
  positivity

theorem twelve_mul_Lambda_le_QOut (cfg : ParamConfig) (M r : ℕ) :
    12 * Lambda cfg M r ≤ QOut cfg M r := by
  unfold QOut DOut
  have hA := cfg.A_pos
  have ht := one_le_tParam M
  have hb := one_le_bOut cfg M
  have h1 : 12 ≤ 2 * (16 * cfg.A * tParam M * bOut cfg M) := by
    calc 12 ≤ 2 * (16 * 16 * 1 * 1) := by decide
      _ ≤ 2 * (16 * cfg.A * tParam M * bOut cfg M) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hA) ht) hb)
  have h2 : 12 * Lambda cfg M r ≤ 2 * (16 * cfg.A * tParam M * bOut cfg M) * Lambda cfg M r :=
    Nat.mul_le_mul_right _ h1
  have h3 : 2 * (16 * cfg.A * tParam M * bOut cfg M) * Lambda cfg M r =
      2 * (16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M) := by ring
  omega

/-! ### Core time recurrence, closed-form bound, and size-sensitive bound -/

/-- Pure natural-number helper for the core recurrence step, keeping `W` and `c₀`
opaque so arithmetic tactics stay fast. -/
private theorem coreTimeBound_rec_aux {N L F W cA q Tprev : ℕ}
    (hN1 : 1 ≤ N) (hW_cA : 3 * cA ≤ W) (hW_F : F ≤ W) (hW_L : L ≤ W) (hW1 : 1 ≤ W)
    (hq : 1 ≤ q) (hprev : Tprev ≤ N ^ q * W ^ (10 * (q - 1) ^ 2 + 10)) :
    cA * (N ^ (q + 1) * L ^ 9 * F ^ q + N * L ^ 2 * F ^ q * Tprev + N ^ q * L ^ 4 * F ^ (3 * q)) ≤
      N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) := by
  have hterm1 : 3 * cA * (N ^ (q + 1) * L ^ 9 * F ^ q) ≤
      N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) := by
    have hL9 : L ^ 9 ≤ W ^ 9 := Nat.pow_le_pow_left hW_L 9
    have hFq : F ^ q ≤ W ^ q := Nat.pow_le_pow_left hW_F q
    calc 3 * cA * (N ^ (q + 1) * L ^ 9 * F ^ q)
        ≤ W * (N ^ (q + 1) * W ^ 9 * W ^ q) :=
          Nat.mul_le_mul hW_cA (Nat.mul_le_mul (Nat.mul_le_mul_left _ hL9) hFq)
      _ = N ^ (q + 1) * W ^ (q + 10) := by ring
      _ ≤ N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by nlinarith))
  have hterm2 : 3 * cA * (N * L ^ 2 * F ^ q * Tprev) ≤
      N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) := by
    have hL2 : L ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hW_L 2
    have hFq : F ^ q ≤ W ^ q := Nat.pow_le_pow_left hW_F q
    have hexp : 10 * (q - 1) ^ 2 + 10 + q + 3 ≤ 10 * q ^ 2 + 10 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hq
      simp only [Nat.add_sub_cancel]
      nlinarith
    calc 3 * cA * (N * L ^ 2 * F ^ q * Tprev)
        ≤ W * (N * W ^ 2 * W ^ q * (N ^ q * W ^ (10 * (q - 1) ^ 2 + 10))) :=
          Nat.mul_le_mul hW_cA
            (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hL2) hFq) hprev)
      _ = N ^ (q + 1) * W ^ (10 * (q - 1) ^ 2 + 10 + q + 3) := by ring
      _ ≤ N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 hexp)
  have hterm3 : 3 * cA * (N ^ q * L ^ 4 * F ^ (3 * q)) ≤
      N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) := by
    have hNq : N ^ q ≤ N ^ (q + 1) := Nat.pow_le_pow_right hN1 (Nat.le_succ q)
    have hL4 : L ^ 4 ≤ W ^ 4 := Nat.pow_le_pow_left hW_L 4
    have hF3 : F ^ (3 * q) ≤ W ^ (3 * q) := Nat.pow_le_pow_left hW_F (3 * q)
    calc 3 * cA * (N ^ q * L ^ 4 * F ^ (3 * q))
        ≤ W * (N ^ (q + 1) * W ^ 4 * W ^ (3 * q)) :=
          Nat.mul_le_mul hW_cA (Nat.mul_le_mul (Nat.mul_le_mul hNq hL4) hF3)
      _ = N ^ (q + 1) * W ^ (3 * q + 5) := by ring
      _ ≤ N ^ (q + 1) * W ^ (10 * q ^ 2 + 10) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by nlinarith))
  have hlhs : 3 * (cA * (N ^ (q + 1) * L ^ 9 * F ^ q + N * L ^ 2 * F ^ q * Tprev +
        N ^ q * L ^ 4 * F ^ (3 * q))) =
      3 * cA * (N ^ (q + 1) * L ^ 9 * F ^ q) +
      3 * cA * (N * L ^ 2 * F ^ q * Tprev) +
      3 * cA * (N ^ q * L ^ 4 * F ^ (3 * q)) := by ring
  omega

/-- **Core recurrence step**: if `T_{q-1} ≤ coreTimeBound cfg M r (q - 1)`, then the
right-hand side of the core cost recurrence is bounded by `coreTimeBound cfg M r q = N^{q+1} W^{10 q^2 + 10}`. -/
theorem coreTimeBound_rec (cfg : ParamConfig) (M r : ℕ) {q : ℕ} (hq : 1 ≤ q)
    {Tprev : ℕ} (hprev : Tprev ≤ coreTimeBound cfg M r (q - 1)) :
    cfg.c0 * cfg.A *
      ((NOf M r) ^ (q + 1) * (LParam M) ^ 9 * (FParam cfg M) ^ q +
        NOf M r * (LParam M) ^ 2 * (FParam cfg M) ^ q * Tprev +
        (NOf M r) ^ q * (LParam M) ^ 4 * (FParam cfg M) ^ (3 * q)) ≤
      coreTimeBound cfg M r q := by
  have hqsub : q - 1 + 1 = q := by omega
  have hprev' : Tprev ≤ (NOf M r) ^ q * (WParam cfg M) ^ (10 * (q - 1) ^ 2 + 10) := by
    simpa [coreTimeBound, hqsub] using hprev
  have hW_cA : 3 * (cfg.c0 * cfg.A) ≤ WParam cfg M := by
    unfold WParam
    have : 3 * (cfg.c0 * cfg.A) = 3 * cfg.c0 * cfg.A := by ring
    omega
  exact coreTimeBound_rec_aux
    (le_trans (by decide) (four_le_NOf M r))
    hW_cA
    (by unfold WParam; omega)
    (by unfold WParam; omega)
    (by unfold WParam; omega)
    hq hprev'

/-- **Size-sensitive core bound**: when calling `Core` on an outer subproblem of size `p` with the least valid
level `q ≤ r` (so `N^{q-1} < p`), `coreTimeBound cfg M r q ≤ p · N^2 · W^{10 r^2 + 10}`. -/
theorem coreTimeBound_size_sensitive (cfg : ParamConfig) (M r : ℕ) {q p : ℕ}
    (hq1 : 1 ≤ q) (hqr : q ≤ r) (hp : (NOf M r) ^ (q - 1) < p) :
    coreTimeBound cfg M r q ≤ p * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) := by
  unfold coreTimeBound
  have hN : (NOf M r) ^ (q + 1) ≤ p * (NOf M r) ^ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hq1
    simp only [Nat.add_sub_cancel] at hp
    have heq : (NOf M r) ^ (k + 1 + 1) = (NOf M r) ^ k * (NOf M r) ^ 2 := by ring
    rw [heq]
    exact Nat.mul_le_mul_right _ (le_of_lt hp)
  have hW : (WParam cfg M) ^ (10 * q ^ 2 + 10) ≤ (WParam cfg M) ^ (10 * r ^ 2 + 10) := by
    apply Nat.pow_le_pow_right (by unfold WParam; omega)
    nlinarith
  exact Nat.mul_le_mul hN hW

/-! ### Monotonicity of all quantities appearing in `Q` and antitonicity of `φ` -/

theorem cubeRoot_mono : Monotone cubeRoot := by
  intro x y hxy
  by_contra hlt
  have hle : cubeRoot y + 1 ≤ cubeRoot x := by omega
  have h1 : y < (cubeRoot y + 1) ^ 3 := lt_cubeRoot_succ_pow y
  have h2 : (cubeRoot y + 1) ^ 3 ≤ (cubeRoot x) ^ 3 := Nat.pow_le_pow_left hle 3
  have h3 : (cubeRoot x) ^ 3 ≤ x := cubeRoot_pow_le x
  omega

theorem rOf_mono : Monotone rOf := by
  intro m₁ m₂ h
  by_contra hlt
  have hle : rOf m₂ + 1 ≤ rOf m₁ := by omega
  have h1 : Nat.log 2 m₂ < (rOf m₂ + 1) ^ 3 := lt_rOf_succ_pow m₂
  have h2 : (rOf m₂ + 1) ^ 3 ≤ (rOf m₁) ^ 3 := Nat.pow_le_pow_left hle 3
  have h3 : (rOf m₁) ^ 3 ≤ Nat.log 2 m₁ := rOf_pow_le m₁
  have h4 : Nat.log 2 m₁ ≤ Nat.log 2 m₂ := Nat.log_mono_right h
  omega

theorem ell_mono : Monotone ell := fun _ _ h =>
  Nat.clog_mono_right 2 (by omega)

theorem LParam_mono : Monotone LParam := fun _ _ h =>
  Nat.mul_le_mul_left 4 (ell_mono h)

theorem tParam_mono : Monotone tParam := fun _ _ h =>
  Nat.mul_le_mul_left 1024 (LParam_mono h)

theorem deltaParam_mono : Monotone deltaParam := tParam_mono

theorem dCore_mono : Monotone dCore := fun _ _ h =>
  Nat.mul_le_mul (Nat.mul_le_mul_left 3200 (deltaParam_mono h)) (LParam_mono h)

theorem RCore_mono : Monotone RCore := fun _ _ h =>
  Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left 1600 (deltaParam_mono h))
      (Nat.add_le_add_right (dCore_mono h) 1))
    (LParam_mono h)

theorem FParam_mono (cfg : ParamConfig) : Monotone (FParam cfg) := fun _ _ h =>
  Nat.mul_le_mul
    (Nat.mul_le_mul_left (1920 * cfg.a₀) (Nat.pow_le_pow_left (deltaParam_mono h) 2))
    (RCore_mono h)

theorem WParam_mono (cfg : ParamConfig) : Monotone (WParam cfg) := fun _ _ h => by
  unfold WParam
  have h1 := FParam_mono cfg h
  have h2 := LParam_mono h
  omega

theorem PParam_rOf_mono (cfg : ParamConfig) : Monotone fun M => PParam cfg M (rOf M) := by
  intro M₁ M₂ h
  unfold PParam
  calc (FParam cfg M₁) ^ (rOf M₁)
      ≤ (FParam cfg M₂) ^ (rOf M₁) := Nat.pow_le_pow_left (FParam_mono cfg h) _
    _ ≤ (FParam cfg M₂) ^ (rOf M₂) :=
        Nat.pow_le_pow_right (one_le_FParam cfg M₂) (rOf_mono h)

theorem bOut_mono (cfg : ParamConfig) : Monotone (bOut cfg) := fun _ _ h =>
  Nat.mul_le_mul_right cfg.E
    (Nat.mul_le_mul_left (16 * cfg.kappa) (Nat.add_le_add_right (LParam_mono h) 1))

theorem dOut_mono (cfg : ParamConfig) : Monotone (dOut cfg) := fun _ _ h =>
  Nat.mul_le_mul (Nat.mul_le_mul_left 320 (bOut_mono cfg h)) (LParam_mono h)

theorem ROut_mono (cfg : ParamConfig) : Monotone (ROut cfg) := fun _ _ h =>
  Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left 160 (bOut_mono cfg h))
      (Nat.add_le_add_right (dOut_mono cfg h) 1))
    (LParam_mono h)

theorem Lambda_rOf_mono (cfg : ParamConfig) : Monotone fun M => Lambda cfg M (rOf M) := fun _ _ h =>
  Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (PParam_rOf_mono cfg h)) (tParam_mono h))
      (ROut_mono cfg h))
    (Nat.add_le_add_right (tParam_mono h) 1)

theorem DOut_rOf_mono (cfg : ParamConfig) : Monotone fun M => DOut cfg M (rOf M) := fun _ _ h =>
  Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul_left (16 * cfg.A) (tParam_mono h))
      (Lambda_rOf_mono cfg h))
    (bOut_mono cfg h)

theorem QOut_rOf_mono (cfg : ParamConfig) : Monotone fun M => QOut cfg M (rOf M) := by
  intro M₁ M₂ h
  dsimp only
  unfold QOut
  have h1 : DOut cfg M₁ (rOf M₁) ≤ DOut cfg M₂ (rOf M₂) := DOut_rOf_mono cfg h
  omega

theorem HDepth_rOf_mono (cfg : ParamConfig) : Monotone fun M => HDepth cfg M (rOf M) := by
  intro M₁ M₂ h
  dsimp only
  unfold HDepth
  have h1 : DOut cfg M₁ (rOf M₁) ≤ DOut cfg M₂ (rOf M₂) := DOut_rOf_mono cfg h
  have h2 : ell M₁ ≤ ell M₂ := ell_mono h
  have h3 : 16 * DOut cfg M₁ (rOf M₁) * (ell M₁ + 1) ≤ 16 * DOut cfg M₂ (rOf M₂) * (ell M₂ + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 h1) (Nat.add_le_add_right h2 1)
  omega

theorem phiOut_pos (cfg : ParamConfig) (M r : ℕ) : 0 < phiOut cfg M r := by
  unfold phiOut QOut
  positivity

theorem phiOut_le_one (cfg : ParamConfig) (M r : ℕ) : phiOut cfg M r ≤ 1 := by
  unfold phiOut QOut
  rw [div_le_one (by positivity)]
  have h : (2 : ℝ) ≤ (2 * DOut cfg M r + 2 : ℕ) := by
    exact_mod_cast (by omega : 2 ≤ 2 * DOut cfg M r + 2)
  linarith

/-- **Antitonicity of `φ`**: `φ(M) = 1 / Q(M, rOf M)` is antitone in `M`. -/
theorem phiOut_antitone (cfg : ParamConfig) : Antitone fun M => phiOut cfg M (rOf M) := by
  intro M₁ M₂ h
  unfold phiOut
  have hpos : (0 : ℝ) < (QOut cfg M₁ (rOf M₁) : ℝ) := by
    unfold QOut; positivity
  have hle : (QOut cfg M₁ (rOf M₁) : ℝ) ≤ (QOut cfg M₂ (rOf M₂) : ℝ) := by
    exact_mod_cast QOut_rOf_mono cfg h
  exact one_div_le_one_div_of_le hpos hle

end MinCostFlow.ExpanderDecomp
