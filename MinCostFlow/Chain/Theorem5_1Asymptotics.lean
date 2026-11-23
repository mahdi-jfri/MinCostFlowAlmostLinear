module

public import MinCostFlow.Chain.Theorem5_1Helpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.1 Subpolynomial Asymptotics (`jtree.tex`, pages 15 & 25–31)

Parameterized `exp(O(log^{(1+β)/2} m · log log m))` / `m^{o(1)}` bounds for Theorem 5.1,
including `alg2TimeFactor`, `alg2KappaLower`, `tendsto_log_alg2TimeFactor_div_log`,
and `theorem_5_1_asymptotic_exponents`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section Asymptotics
private lemma one_le_log_add_two {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ Real.log ((m : ℝ) + 2) := by
  have h3 : Real.exp 1 ≤ (m : ℝ) + 2 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith [Real.exp_one_lt_three]
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) h3

/-- Lift an `exp(C * log(M+2)^β * log(log(M+2)+2))` upper bound to exponent `(1 + β) / 2`
whenever `1 ≤ M`, `β < 1`, and `0 ≤ C`. -/
lemma exp_rpow_le_half_one_add {M : ℕ} {β C x : ℝ} (hM : 1 ≤ M) (hβ1 : β < 1) (hC : 0 ≤ C)
    (hx : x ≤ Real.exp (C * (Real.log ((M : ℝ) + 2)) ^ β *
      Real.log (Real.log ((M : ℝ) + 2) + 2))) :
    x ≤ Real.exp (C * (Real.log ((M : ℝ) + 2)) ^ ((1 + β) / 2) *
      Real.log (Real.log ((M : ℝ) + 2) + 2)) := by
  have hL1 : 1 ≤ Real.log ((M : ℝ) + 2) := one_le_log_add_two hM
  have hLL0 : 0 ≤ Real.log (Real.log ((M : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hrpow : (Real.log ((M : ℝ) + 2)) ^ β ≤ (Real.log ((M : ℝ) + 2)) ^ ((1 + β) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  exact le_trans hx (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hC) hLL0))

/-- Depth choice `d = ⌈(log(M₀ + 2))^{(1 - β)/2}⌉` balancing `M₀^{1/d}` with `(γ_ℓ γ_r)^d`
against sparse-core exponent `β ∈ (0, 1)`. -/
noncomputable def chosenD (β : ℝ) (M₀ : ℕ) : ℕ :=
  Nat.ceil ((Real.log ((M₀ : ℝ) + 2)) ^ ((1 - β) / 2))

lemma chosenD_bounds {β : ℝ} (hβ1 : β < 1) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    1 ≤ chosenD β M₀ ∧
    (Real.log ((M₀ : ℝ) + 2)) ^ ((1 - β) / 2) ≤ (chosenD β M₀ : ℝ) ∧
    (chosenD β M₀ : ℝ) ≤ 2 * (Real.log ((M₀ : ℝ) + 2)) ^ ((1 - β) / 2) := by
  have hL1 : 1 ≤ Real.log ((M₀ : ℝ) + 2) := one_le_log_add_two hM₀
  have hexp_nn : 0 ≤ (1 - β) / 2 := by linarith
  have hpow1 : 1 ≤ (Real.log ((M₀ : ℝ) + 2)) ^ ((1 - β) / 2) := Real.one_le_rpow hL1 hexp_nn
  refine ⟨Nat.ceil_pos.mpr (by linarith), Nat.le_ceil _, ?_⟩
  have hlt := Nat.ceil_lt_add_one (by linarith : 0 ≤ (Real.log ((M₀ : ℝ) + 2)) ^ ((1 - β) / 2))
  change (chosenD β M₀ : ℝ) < (Real.log ((M₀ : ℝ) + 2)) ^ ((1 - β) / 2) + 1 at hlt
  linarith

/-- Any subpolynomial envelope `exp(C * (log x)^a * log (log x + 2))` with `0 ≤ a < 1` is `x^{o(1)}`. -/
theorem exp_subpoly_mul_loglog_le_rpow {a C δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, 3 ≤ x →
      Real.exp (C * (Real.log x) ^ a * Real.log (Real.log x + 2)) ≤ B * x ^ δ := by
  by_cases hC : C ≤ 0
  · refine ⟨1, zero_lt_one, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := by linarith
    have hu1 : 1 ≤ Real.log x := by
      have : Real.exp 1 ≤ x := le_trans Real.exp_one_lt_three.le hx
      simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
    have hpow_nn : 0 ≤ (Real.log x) ^ a := Real.rpow_nonneg (by linarith) a
    have hlog_nn : 0 ≤ Real.log (Real.log x + 2) := Real.log_nonneg (by linarith)
    have hneg : C * (Real.log x) ^ a * Real.log (Real.log x + 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC hpow_nn) hlog_nn
    have h1 : Real.exp (C * (Real.log x) ^ a * Real.log (Real.log x + 2)) ≤ 1 :=
      Real.exp_le_one_iff.mpr hneg
    have h2 : 1 ≤ x ^ δ := Real.one_le_rpow hx1 hδ.le
    linarith
  · push Not at hC
    let θ := (1 - a) / 2
    have hθ_pos : 0 < θ := by simp only [θ]; linarith
    let a' := a + θ
    have ha'_pos : 0 < a' := by simp only [a', θ]; linarith
    have ha'_lt : a' < 1 := by simp only [a', θ]; linarith
    have h1ma'_pos : 0 < 1 - a' := by simp only [a', θ]; linarith
    let K := C * (3 : ℝ) ^ θ / θ
    have hK_pos : 0 < K := by positivity
    let U₀ := max 1 ((K / δ) ^ (1 / (1 - a')))
    refine ⟨Real.exp (K * U₀ ^ a'), Real.exp_pos _, fun x hx => ?_⟩
    have hx_pos : 0 < x := by linarith
    set u := Real.log x
    have hu1 : 1 ≤ u := by
      have : Real.exp 1 ≤ x := le_trans Real.exp_one_lt_three.le hx
      simpa [u, Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
    have hu_pos : 0 < u := by linarith
    have hlog_le : Real.log (u + 2) ≤ (3 : ℝ) ^ θ / θ * u ^ θ := by
      have hy_pos : 0 < u + 2 := by linarith
      have hyθ_pos : 0 < (u + 2) ^ θ := Real.rpow_pos_of_pos hy_pos θ
      have hsub1 : Real.log ((u + 2) ^ θ) ≤ (u + 2) ^ θ - 1 :=
        Real.log_le_sub_one_of_pos hyθ_pos
      rw [Real.log_rpow hy_pos] at hsub1
      have hlog_raw : Real.log (u + 2) ≤ (u + 2) ^ θ / θ :=
        (le_div_iff₀ hθ_pos).mpr (by linarith)
      have hpow3 : (u + 2) ^ θ ≤ (3 * u) ^ θ :=
        Real.rpow_le_rpow hy_pos.le (by linarith) hθ_pos.le
      rw [Real.mul_rpow (by norm_num) hu_pos.le] at hpow3
      calc
        Real.log (u + 2) ≤ (u + 2) ^ θ / θ := hlog_raw
        _ ≤ ((3 : ℝ) ^ θ * u ^ θ) / θ := div_le_div_of_nonneg_right hpow3 hθ_pos.le
        _ = (3 : ℝ) ^ θ / θ * u ^ θ := by ring
    have hcomb : C * u ^ a * Real.log (u + 2) ≤ K * u ^ a' := by
      have hua_nn : 0 ≤ u ^ a := Real.rpow_nonneg hu_pos.le a
      have h1 : C * u ^ a * Real.log (u + 2) ≤ C * u ^ a * ((3 : ℝ) ^ θ / θ * u ^ θ) :=
        mul_le_mul_of_nonneg_left hlog_le (mul_nonneg hC.le hua_nn)
      have hadd : u ^ a * u ^ θ = u ^ a' := (Real.rpow_add hu_pos a θ).symm
      calc
        C * u ^ a * Real.log (u + 2)
            ≤ C * u ^ a * ((3 : ℝ) ^ θ / θ * u ^ θ) := h1
        _ = (C * (3 : ℝ) ^ θ / θ) * (u ^ a * u ^ θ) := by ring
        _ = K * u ^ a' := by rw [hadd]
    have hKu : K * u ^ a' ≤ K * U₀ ^ a' + δ * u := by
      by_cases huU : u ≤ U₀
      · have hle : u ^ a' ≤ U₀ ^ a' := Real.rpow_le_rpow hu_pos.le huU ha'_pos.le
        have hKa' : K * u ^ a' ≤ K * U₀ ^ a' := mul_le_mul_of_nonneg_left hle hK_pos.le
        linarith [mul_pos hδ hu_pos]
      · have hU_lt : (K / δ) ^ (1 / (1 - a')) ≤ u := le_trans (le_max_right _ _) (le_of_not_ge huU)
        have hKδ_nn : 0 ≤ K / δ := by positivity
        have hpow_le : K / δ ≤ u ^ (1 - a') := by
          have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hKδ_nn _) hU_lt h1ma'_pos.le
          rwa [← Real.rpow_mul hKδ_nn, one_div_mul_cancel h1ma'_pos.ne', Real.rpow_one] at h1
        have hmul := mul_le_mul_of_nonneg_right hpow_le (Real.rpow_nonneg hu_pos.le a')
        rw [← Real.rpow_add hu_pos, sub_add_cancel, Real.rpow_one] at hmul
        have hKu_le : K * u ^ a' ≤ δ * u := by
          have := mul_le_mul_of_nonneg_left hmul hδ.le
          have hK_eq : δ * (K / δ * u ^ a') = K * u ^ a' := by field_simp [hδ.ne']
          linarith
        have hKU_nn : 0 ≤ K * U₀ ^ a' :=
          mul_nonneg hK_pos.le (Real.rpow_nonneg (by linarith [le_max_left 1 ((K / δ) ^ (1 / (1 - a')))]) _)
        linarith
    have hExp : Real.exp (C * u ^ a * Real.log (u + 2)) ≤ Real.exp (K * U₀ ^ a' + δ * u) :=
      Real.exp_le_exp.mpr (le_trans hcomb hKu)
    have hRpow : Real.exp (δ * u) = x ^ δ := by
      simp only [u]
      rw [mul_comm, Real.rpow_def_of_pos hx_pos]
    rw [Real.exp_add, hRpow] at hExp
    exact hExp

private lemma exp_pow_nat (x : ℝ) (n : ℕ) : (Real.exp x) ^ n = Real.exp ((n : ℝ) * x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← Real.exp_add, Nat.cast_succ]; ring_nf

private lemma asymptotic_exponents_core
    (d : ℕ) (hd : 1 ≤ d)
    {C_γ C_ψ C_N L E B γℓ γr σtot σg cT cL Ψ_g M1d k logF_p logF_2 logN1 : ℝ}
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hL1 : 1 ≤ L) (hE1 : 1 ≤ E) (hB1 : 1 ≤ B)
    (hB_le_E : B ≤ E) (hd_mul_B : (d : ℝ) * B ≤ 2 * E) (hL_le_E : L ≤ Real.exp E)
    (hγℓ1 : 1 ≤ γℓ) (hγℓ : γℓ ≤ Real.exp (C_γ * B))
    (hγr1 : 1 ≤ γr) (hγr : γr ≤ Real.exp (C_γ * B))
    (hσtot : σtot ≤ Real.exp (C_γ * E))
    (hσg0 : 0 ≤ σg) (hσg : σg ≤ Real.exp (C_γ * B))
    (hcT0 : 0 ≤ cT) (hcT : cT ≤ Real.exp (C_γ * B))
    (hcL0 : 0 ≤ cL) (hcL : cL ≤ Real.exp (C_γ * B))
    (hΨ1 : 1 ≤ Ψ_g) (hΨ : Ψ_g ≤ Real.exp (C_ψ * B))
    (hM1d0 : 0 ≤ M1d) (hM1d : M1d ≤ Real.exp (1 * E))
    (hk0 : 0 ≤ k) (hk : k ≤ Real.exp (2 * E))
    (hd1 : (d : ℝ) + 1 ≤ Real.exp (3 * E))
    (hlogFp1 : 1 ≤ logF_p) (hlogFp : logF_p ≤ Real.exp (C_γ * E))
    (hlogF21 : 1 ≤ logF_2) (hlogF2 : logF_2 ≤ Real.exp (C_γ * E))
    (hlogN1_1 : 1 ≤ logN1) (hlogN1 : logN1 ≤ C_N * L) :
    1 / kappaBound d γℓ σtot σg ≤ Real.exp ((15 + 5 * C_γ) * E) ∧
    (((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
      2 * logN1 * (γℓ + 3)) *
      (((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1) *
      (16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1) +
      logN1 * (2 * (γℓ + 3) + 1) ≤
      Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
  have hE_nn : 0 ≤ E := le_trans zero_le_one hE1
  have hL_nn : 0 ≤ L := le_trans zero_le_one hL1
  have hTwoB : ∀ m : ℕ, (2 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * B) := fun m => by
    have h2 : (2 : ℝ) ≤ Real.exp B := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
      (Real.exp_le_exp.mpr hB1)
    calc
      (2 : ℝ) ^ m ≤ (Real.exp B) ^ m := pow_le_pow_left₀ (by norm_num) h2 m
      _ = Real.exp ((m : ℝ) * B) := exp_pow_nat B m
  have hTwoE : ∀ m : ℕ, (2 : ℝ) ^ m ≤ Real.exp ((m : ℝ) * E) := fun m =>
    le_trans (hTwoB m) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB_le_E (Nat.cast_nonneg m)))
  have hPowD : ∀ c : ℝ, 0 ≤ c → (Real.exp (c * B)) ^ d ≤ Real.exp ((2 * c) * E) :=
    fun c hc => by
    rw [exp_pow_nat]
    refine Real.exp_le_exp.mpr ?_
    calc
      (d : ℝ) * (c * B) = c * ((d : ℝ) * B) := by ring
      _ ≤ c * (2 * E) := mul_le_mul_of_nonneg_left hd_mul_B hc
      _ = (2 * c) * E := by ring
  have hBE_Cγ : Real.exp (C_γ * B) ≤ Real.exp (C_γ * E) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hB_le_E hCγ)
  have hd1_sq : ((d : ℝ) + 1) ^ 2 ≤ Real.exp (6 * E) := by
    calc
      ((d : ℝ) + 1) ^ 2 ≤ (Real.exp (3 * E)) ^ 2 := pow_le_pow_left₀ (by positivity) hd1 2
      _ = Real.exp (6 * E) := by rw [exp_pow_nat]; ring_nf
  have h2d3_le : 2 * (d : ℝ) + 3 ≤ Real.exp (5 * E) := by
    have h1 : 2 * (d : ℝ) + 3 ≤ 2 ^ 2 * ((d : ℝ) + 1) := by linarith
    calc
      2 * (d : ℝ) + 3 ≤ 2 ^ 2 * ((d : ℝ) + 1) := h1
      _ ≤ Real.exp (2 * E) * Real.exp (3 * E) :=
        mul_le_mul (by simpa using hTwoE 2) hd1 (by positivity) (by positivity)
      _ = Real.exp (5 * E) := by rw [← Real.exp_add]; ring_nf
  have hσtot_le : σtot + 1 ≤ Real.exp ((1 + C_γ) * E) := by
    have h1_le : 1 ≤ Real.exp (C_γ * E) := Real.one_le_exp (mul_nonneg hCγ hE_nn)
    calc
      σtot + 1 ≤ 2 ^ 1 * Real.exp (C_γ * E) := by linarith only [hσtot, h1_le]
      _ ≤ Real.exp (1 * E) * Real.exp (C_γ * E) :=
        mul_le_mul (by simpa using hTwoE 1) le_rfl (by positivity) (by positivity)
      _ = Real.exp ((1 + C_γ) * E) := by rw [← Real.exp_add]; ring_nf
  have hγℓ_nn : 0 ≤ γℓ := le_trans zero_le_one hγℓ1
  have hγr_nn : 0 ≤ γr := le_trans zero_le_one hγr1
  have hκ_base : (2 * γℓ * (1 + 2 * σg)) ^ d ≤ Real.exp ((6 + 4 * C_γ) * E) := by
    have h1_le : 1 ≤ Real.exp (C_γ * B) := Real.one_le_exp (mul_nonneg hCγ (le_trans zero_le_one hB1))
    have hsg : 1 + 2 * σg ≤ 4 * Real.exp (C_γ * B) := by linarith only [hσg, h1_le]
    have hbase_le : 2 * γℓ * (1 + 2 * σg) ≤ Real.exp ((3 + 2 * C_γ) * B) := by
      calc
        2 * γℓ * (1 + 2 * σg) ≤ 2 * Real.exp (C_γ * B) * (4 * Real.exp (C_γ * B)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hγℓ (by norm_num)) hsg (by positivity) (by positivity)
        _ = 2 ^ 3 * (Real.exp (C_γ * B) * Real.exp (C_γ * B)) := by ring
        _ ≤ Real.exp (3 * B) * Real.exp ((2 * C_γ) * B) := by
          rw [← Real.exp_add]
          exact mul_le_mul (by simpa using hTwoB 3)
            (Real.exp_le_exp.mpr (by ring_nf; exact le_rfl)) (by positivity) (by positivity)
        _ = Real.exp ((3 + 2 * C_γ) * B) := by rw [← Real.exp_add]; ring_nf
    calc
      (2 * γℓ * (1 + 2 * σg)) ^ d ≤ (Real.exp ((3 + 2 * C_γ) * B)) ^ d :=
        pow_le_pow_left₀ (by positivity) hbase_le d
      _ ≤ Real.exp ((2 * (3 + 2 * C_γ)) * E) := hPowD _ (by positivity)
      _ = Real.exp ((6 + 4 * C_γ) * E) := by ring_nf
  have hKappa_bound : 1 / kappaBound d γℓ σtot σg ≤ Real.exp ((15 + 5 * C_γ) * E) := by
    unfold kappaBound
    rw [one_div_one_div]
    calc
      (σtot + 1) * (((d : ℝ) + 1) * (2 * (d : ℝ) + 3) * (2 * γℓ * (1 + 2 * σg)) ^ d)
          ≤ Real.exp ((1 + C_γ) * E) *
              (Real.exp (3 * E) * Real.exp (5 * E) * Real.exp ((6 + 4 * C_γ) * E)) := by
        have h35 : ((d : ℝ) + 1) * (2 * (d : ℝ) + 3) ≤ Real.exp (3 * E) * Real.exp (5 * E) :=
          mul_le_mul hd1 h2d3_le (by positivity) (by positivity)
        have h35k : ((d : ℝ) + 1) * (2 * (d : ℝ) + 3) * (2 * γℓ * (1 + 2 * σg)) ^ d ≤
            Real.exp (3 * E) * Real.exp (5 * E) * Real.exp ((6 + 4 * C_γ) * E) :=
          mul_le_mul h35 hκ_base (by positivity) (by positivity)
        exact mul_le_mul hσtot_le h35k (by positivity) (by positivity)
      _ = Real.exp ((15 + 5 * C_γ) * E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hCfac_le : ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p ≤
      Real.exp ((14 + 14 * C_γ) * E) := by
    have hcoeff : 8 * cT + 81 * cL + 430 ≤ Real.exp ((10 + C_γ) * E) := by
      set X := Real.exp (C_γ * E)
      have hX1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hCγ hE_nn)
      have hcT_X : cT ≤ X := le_trans hcT hBE_Cγ
      have hcL_X : cL ≤ X := le_trans hcL hBE_Cγ
      have h210 : 8 * cT + 81 * cL + 430 ≤ 2 ^ 10 * X := by linarith only [hX1, hcT_X, hcL_X]
      calc
        8 * cT + 81 * cL + 430 ≤ 2 ^ 10 * X := h210
        _ ≤ Real.exp (10 * E) * X :=
          mul_le_mul_of_nonneg_right (by simpa using hTwoE 10) (by positivity)
        _ = Real.exp ((10 + C_γ) * E) := by simp only [X]; rw [← Real.exp_add]; ring_nf
    have hγprod : γr * γℓ ^ (3 * d + 2) ≤ Real.exp ((12 * C_γ) * E) := by
      have hE1B : 1 ≤ Real.exp (C_γ * B) := Real.one_le_exp (mul_nonneg hCγ (le_trans zero_le_one hB1))
      have h1 : γr * γℓ ^ (3 * d + 2) ≤ Real.exp (C_γ * B) * (Real.exp (C_γ * B)) ^ (3 * d + 2) :=
        mul_le_mul hγr (pow_le_pow_left₀ hγℓ_nn hγℓ _) (by positivity) (by positivity)
      have h2 : Real.exp (C_γ * B) * (Real.exp (C_γ * B)) ^ (3 * d + 2) =
          (Real.exp (C_γ * B)) ^ (3 * d + 3) := by rw [← pow_succ']
      have h3 : (Real.exp (C_γ * B)) ^ (3 * d + 3) ≤ (Real.exp (C_γ * B)) ^ (6 * d) :=
        pow_le_pow_right₀ hE1B (by omega)
      calc
        γr * γℓ ^ (3 * d + 2) ≤ (Real.exp (C_γ * B)) ^ (6 * d) := le_trans h1 (h2 ▸ h3)
        _ = ((Real.exp (C_γ * B)) ^ d) ^ 6 := by rw [mul_comm 6 d, pow_mul]
        _ ≤ (Real.exp ((2 * C_γ) * E)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) (hPowD _ hCγ) 6
        _ = Real.exp ((12 * C_γ) * E) := by rw [exp_pow_nat]; ring_nf
    have h12 := mul_le_mul hd1 hcoeff (by positivity) (by positivity)
    have h123 := mul_le_mul h12 hM1d hM1d0 (by positivity)
    have h1234 := mul_le_mul h123 hγprod (by positivity) (by positivity)
    calc
      ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p
          ≤ Real.exp (3 * E) * Real.exp ((10 + C_γ) * E) * Real.exp (1 * E) *
              Real.exp ((12 * C_γ) * E) * Real.exp (C_γ * E) :=
        mul_le_mul h1234 hlogFp (le_trans zero_le_one hlogFp1) (by positivity)
      _ = Real.exp ((14 + 14 * C_γ) * E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hlogN_le : logN1 ≤ Real.exp ((C_N + 1) * E) := by
    have hCN_exp : C_N ≤ Real.exp (C_N * E) := by
      have h1 : C_N ≤ Real.exp C_N := by linarith only [Real.add_one_le_exp C_N]
      exact le_trans h1 (Real.exp_le_exp.mpr (le_mul_of_one_le_right (by linarith only [hCN]) hE1))
    calc
      logN1 ≤ C_N * L := hlogN1
      _ ≤ Real.exp (C_N * E) * Real.exp E := mul_le_mul hCN_exp hL_le_E hL_nn (by positivity)
      _ = Real.exp ((C_N + 1) * E) := by rw [← Real.exp_add]; ring_nf
  have hγℓ3 : γℓ + 3 ≤ Real.exp ((2 + C_γ) * E) := by
    set X := Real.exp (C_γ * E)
    have h1 : 1 ≤ X := Real.one_le_exp (mul_nonneg hCγ hE_nn)
    have hγ_X : γℓ ≤ X := le_trans hγℓ hBE_Cγ
    calc
      γℓ + 3 ≤ 2 ^ 2 * X := by linarith only [h1, hγ_X]
      _ ≤ Real.exp (2 * E) * X :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 2) (by positivity)
      _ = Real.exp ((2 + C_γ) * E) := by simp only [X]; rw [← Real.exp_add]; ring_nf
  have hSfac_le : ((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1 ≤
      Real.exp ((29 + 4 * C_ψ) * E) := by
    have hbase : 20 * Ψ_g ≤ Real.exp ((5 + C_ψ) * B) := by
      have h1 : (1 : ℝ) ≤ Real.exp (C_ψ * B) := Real.one_le_exp (mul_nonneg hCψ (le_trans zero_le_one hB1))
      calc
        20 * Ψ_g ≤ 2 ^ 5 * Real.exp (C_ψ * B) := by linarith only [hΨ, h1]
        _ ≤ Real.exp (5 * B) * Real.exp (C_ψ * B) :=
          mul_le_mul_of_nonneg_right (by simpa using hTwoB 5) (by positivity)
        _ = Real.exp ((5 + C_ψ) * B) := by rw [← Real.exp_add]; ring_nf
    have h20pow : (20 * Ψ_g) ^ (d + 1) ≤ Real.exp ((20 + 4 * C_ψ) * E) := by
      have h1 : (1 : ℝ) ≤ 20 * Ψ_g := by linarith only [hΨ1]
      calc
        (20 * Ψ_g) ^ (d + 1) ≤ (20 * Ψ_g) ^ (2 * d) := pow_le_pow_right₀ h1 (by omega)
        _ ≤ (Real.exp ((5 + C_ψ) * B)) ^ (2 * d) := pow_le_pow_left₀ (by positivity) hbase _
        _ = ((Real.exp ((5 + C_ψ) * B)) ^ d) ^ 2 := by rw [mul_comm 2 d, pow_mul]
        _ ≤ (Real.exp ((2 * (5 + C_ψ)) * E)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (hPowD _ (by positivity)) 2
        _ = Real.exp ((20 + 4 * C_ψ) * E) := by rw [exp_pow_nat]; ring_nf
    have hprod : ((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k ≤
        Real.exp (6 * E) * Real.exp ((20 + 4 * C_ψ) * E) * Real.exp (2 * E) :=
      mul_le_mul (mul_le_mul hd1_sq h20pow (by positivity) (by positivity)) hk hk0 (by positivity)
    have h28 : Real.exp (6 * E) * Real.exp ((20 + 4 * C_ψ) * E) * Real.exp (2 * E) =
        Real.exp ((28 + 4 * C_ψ) * E) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h1_le : (1 : ℝ) ≤ Real.exp ((28 + 4 * C_ψ) * E) :=
      Real.one_le_exp (mul_nonneg (by linarith only [hCψ]) hE_nn)
    calc
      ((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1 ≤ 2 ^ 1 * Real.exp ((28 + 4 * C_ψ) * E) := by
        linarith only [hprod, h28, h1_le]
      _ ≤ Real.exp (1 * E) * Real.exp ((28 + 4 * C_ψ) * E) :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 1) (by positivity)
      _ = Real.exp ((29 + 4 * C_ψ) * E) := by rw [← Real.exp_add]; ring_nf
  have hRfac_le : 16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1 ≤
      Real.exp ((16 + 3 * C_γ) * E) := by
    have h2d : (2 : ℝ) ^ d ≤ Real.exp (2 * E) :=
      le_trans (hTwoB d) (Real.exp_le_exp.mpr hd_mul_B)
    have hγrd : γr ^ d ≤ Real.exp ((2 * C_γ) * E) :=
      le_trans (pow_le_pow_left₀ hγr_nn hγr _) (hPowD _ hCγ)
    have hmain : 16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 ≤ Real.exp ((14 + 3 * C_γ) * E) := by
      have h1 := mul_le_mul (mul_le_mul (mul_le_mul hd1_sq h2d (by positivity) (by positivity))
        hγrd (by positivity) (by positivity)) hk hk0 (by positivity)
      have h2 := mul_le_mul h1 hlogF2 (le_trans zero_le_one hlogF21) (by positivity)
      have h16 : (16 : ℝ) ≤ Real.exp (4 * E) := by simpa [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num] using hTwoE 4
      have h3 : 16 * (((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2) ≤
          Real.exp (4 * E) * (Real.exp (6 * E) * Real.exp (2 * E) * Real.exp ((2 * C_γ) * E) *
            Real.exp (2 * E) * Real.exp (C_γ * E)) :=
        mul_le_mul h16 h2 (by positivity) (by positivity)
      have h_eq : Real.exp (4 * E) * (Real.exp (6 * E) * Real.exp (2 * E) * Real.exp ((2 * C_γ) * E) *
          Real.exp (2 * E) * Real.exp (C_γ * E)) = Real.exp ((14 + 3 * C_γ) * E) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
      calc 16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2
          = 16 * (((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2) := by ring
        _ ≤ Real.exp ((14 + 3 * C_γ) * E) := h_eq ▸ h3
    have hd_sub : ((d : ℝ) + 1) ^ 2 ≤ Real.exp ((14 + 3 * C_γ) * E) :=
      le_trans hd1_sq (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith only [hCγ]) hE_nn))
    have h1_sub : (1 : ℝ) ≤ Real.exp ((14 + 3 * C_γ) * E) :=
      Real.one_le_exp (mul_nonneg (by linarith only [hCγ]) hE_nn)
    calc
      16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1
          ≤ 3 * Real.exp ((14 + 3 * C_γ) * E) := by linarith only [hmain, hd_sub, h1_sub]
      _ ≤ 2 ^ 2 * Real.exp ((14 + 3 * C_γ) * E) := by
        linarith only [Real.exp_pos ((14 + 3 * C_γ) * E)]
      _ ≤ Real.exp (2 * E) * Real.exp ((14 + 3 * C_γ) * E) :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 2) (by positivity)
      _ = Real.exp ((16 + 3 * C_γ) * E) := by rw [← Real.exp_add]; ring_nf
  have hColl :
      (((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
        2 * logN1 * (γℓ + 3)) *
        (((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1) *
        (16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1) +
        logN1 * (2 * (γℓ + 3) + 1) ≤
      Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
    have hLctTerm : 2 * logN1 * (γℓ + 3) ≤ Real.exp ((4 + C_γ + C_N) * E) := by
      have h12 : 2 * logN1 ≤ Real.exp (1 * E) * Real.exp ((C_N + 1) * E) :=
        mul_le_mul (by simpa using hTwoE 1) hlogN_le (le_trans zero_le_one hlogN1_1) (by positivity)
      have h123 := mul_le_mul h12 hγℓ3 (by linarith only [hγℓ_nn]) (by positivity)
      have h_eq : Real.exp (1 * E) * Real.exp ((C_N + 1) * E) * Real.exp ((2 + C_γ) * E) =
          Real.exp ((4 + C_γ + C_N) * E) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      linarith only [h123, h_eq]
    have hSumPref :
        ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
          2 * logN1 * (γℓ + 3) ≤ Real.exp ((15 + 18 * C_γ + C_N) * E) := by
      have h_a : Real.exp ((14 + 14 * C_γ) * E) ≤ Real.exp ((14 + 18 * C_γ + C_N) * E) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hCγ, hCN]) hE_nn)
      have h_b : Real.exp ((4 + C_γ + C_N) * E) ≤ Real.exp ((14 + 18 * C_γ + C_N) * E) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [hCγ]) hE_nn)
      have hsum :
          ((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
            2 * logN1 * (γℓ + 3) ≤ 2 ^ 1 * Real.exp ((14 + 18 * C_γ + C_N) * E) := by
        linarith only [hCfac_le, hLctTerm, h_a, h_b]
      calc
        _ ≤ Real.exp (1 * E) * Real.exp ((14 + 18 * C_γ + C_N) * E) :=
          le_trans hsum (mul_le_mul_of_nonneg_right (by simpa using hTwoE 1) (by positivity))
        _ = Real.exp ((15 + 18 * C_γ + C_N) * E) := by rw [← Real.exp_add]; ring_nf
    have hBig :
        (((d : ℝ) + 1) * (8 * cT + 81 * cL + 430) * M1d * (γr * γℓ ^ (3 * d + 2)) * logF_p +
          2 * logN1 * (γℓ + 3)) *
          (((d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (d + 1) * k + 1) *
          (16 * ((d : ℝ) + 1) ^ 2 * 2 ^ d * γr ^ d * k * logF_2 + ((d : ℝ) + 1) ^ 2 + 1) ≤
        Real.exp ((61 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
      have h12 := mul_le_mul hSumPref hSfac_le (by positivity) (by positivity)
      have h123 := mul_le_mul h12 hRfac_le (by positivity) (by positivity)
      have h_eq : Real.exp ((15 + 18 * C_γ + C_N) * E) * Real.exp ((29 + 4 * C_ψ) * E) *
          Real.exp ((16 + 3 * C_γ) * E) = Real.exp ((60 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have hle61 : Real.exp ((60 + 21 * C_γ + 4 * C_ψ + C_N) * E) ≤
          Real.exp ((61 + 21 * C_γ + 4 * C_ψ + C_N) * E) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hE_nn)
      exact le_trans h123 (h_eq.le.trans hle61)
    have hTail : logN1 * (2 * (γℓ + 3) + 1) ≤
        Real.exp ((61 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
      have h2γ1 : 2 * (γℓ + 3) + 1 ≤ 2 ^ 2 * (γℓ + 3) := by linarith only [hγℓ_nn]
      have h21 : 2 * (γℓ + 3) + 1 ≤ Real.exp (2 * E) * Real.exp ((2 + C_γ) * E) :=
        le_trans h2γ1 (mul_le_mul (by simpa using hTwoE 2) hγℓ3 (by linarith only [hγℓ_nn]) (by positivity))
      have h12 := mul_le_mul hlogN_le h21 (by positivity) (by positivity)
      have h_eq : Real.exp ((C_N + 1) * E) * (Real.exp (2 * E) * Real.exp ((2 + C_γ) * E)) =
          Real.exp ((5 + C_γ + C_N) * E) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      exact le_trans h12 (h_eq ▸ Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (by linarith only [hCγ, hCψ]) hE_nn))
    calc
      _ ≤ 2 ^ 1 * Real.exp ((61 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by linarith only [hBig, hTail]
      _ ≤ Real.exp (1 * E) * Real.exp ((61 + 21 * C_γ + 4 * C_ψ + C_N) * E) :=
        mul_le_mul_of_nonneg_right (by simpa using hTwoE 1) (by positivity)
      _ = Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by rw [← Real.exp_add]; ring_nf
  exact ⟨hKappa_bound, hColl⟩

/-- Parameterized Theorem 5.1 asymptotic exponent lemma (`jtree.tex` page 30, with
the restated Theorem 8.6): for any subpolynomial sparse-core growth exponent `β ∈ (0, 1)`,
setting `d = chosenD β cfg.P.M₀` gives BOTH:
* approximation factor `1 / alg2Kappa ≤ exp(C_κ * log(M₀+2)^{(1+β)/2} * log(log(M₀+2)+2))`,
* amortized runtime factor `alg2CollapsedFactor ≤ exp(C_rt * log(M₀+2)^{(1+β)/2} * log(log(M₀+2)+2))`,
and hence both are `M₀^{o(1)}` (`exp_subpoly_mul_loglog_le_rpow`).
In particular:
* `β = 8/9` (`jtree.tex`, Lemma 5.17 as printed) gives `(1 + β)/2 = 17/18` (`exp(-O(log^{17/18} m log log m))`);
* `β = 23/24` (restated Theorem 8.6 / Theorem 8.2 in `MinCostFlow.Expander.Section8Asymptotics`)
  gives `(1 + β)/2 = 47/48`, still `m^{o(1)}`.
This relaxed variant allows `hσT` and `hσL` up to `L^{(1+β)/2}`. -/
theorem theorem_5_1_asymptotic_exponents_at (n_last : ℕ) {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last n_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    1 / alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) := by
  let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  let LL := Real.log (L + 2)
  have hL1 : 1 ≤ L := one_le_log_add_two hM₀
  have hL_pos : 0 < L := by linarith
  have hLL1 : 1 ≤ LL := by
    have : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_three]
    simpa only [LL, Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
  have hDb := chosenD_bounds hβ1 hM₀
  have hd_lo : L ^ ((1 - β) / 2) ≤ (cfg.P.d : ℝ) := by rw [hD]; exact hDb.2.1
  have hd_hi : (cfg.P.d : ℝ) ≤ 2 * L ^ ((1 - β) / 2) := by rw [hD]; exact hDb.2.2
  have ha0 : 0 ≤ (1 + β) / 2 := by linarith
  have ha_ge_β : β ≤ (1 + β) / 2 := by linarith
  have hLa1 : 1 ≤ L ^ ((1 + β) / 2) := Real.one_le_rpow hL1 ha0
  have hLβ1 : 1 ≤ L ^ β := Real.one_le_rpow hL1 hβ0.le
  set E := L ^ ((1 + β) / 2) * LL
  set B := L ^ β * LL
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le hLa1 hLL1
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le hLβ1 hLL1
  have hB_le_E : B ≤ E :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL1 ha_ge_β) (by linarith)
  have hd_mul_B : (cfg.P.d : ℝ) * B ≤ 2 * E := by
    have hpow : L ^ ((1 - β) / 2) * L ^ β = L ^ ((1 + β) / 2) := by
      rw [← Real.rpow_add hL_pos]; congr 1; ring
    calc
      (cfg.P.d : ℝ) * B ≤ (2 * L ^ ((1 - β) / 2)) * (L ^ β * LL) :=
        mul_le_mul_of_nonneg_right hd_hi (by positivity)
      _ = 2 * (L ^ ((1 - β) / 2) * L ^ β) * LL := by ring
      _ = 2 * E := by rw [hpow]; simp only [E]; ring
  have hL_le_E : L ≤ Real.exp E := by
    have h1 : L ≤ Real.exp LL := by rw [Real.exp_log (by linarith)]; linarith
    have hLL_le_E : LL ≤ E := by
      have : 1 * LL ≤ L ^ ((1 + β) / 2) * LL := mul_le_mul_of_nonneg_right hLa1 (by linarith)
      linarith
    exact le_trans h1 (Real.exp_le_exp.mpr hLL_le_E)
  have hTwoE2 : (2 : ℝ) ^ 2 ≤ Real.exp (2 * E) := by
    have h2 : (2 : ℝ) ≤ Real.exp E := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
      (Real.exp_le_exp.mpr hE1)
    calc
      (2 : ℝ) ^ 2 ≤ (Real.exp E) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = Real.exp (2 * E) := by rw [exp_pow_nat]; simp
  have hM1 : (1 : ℝ) ≤ (cfg.P.M₀ : ℝ) := by exact_mod_cast hM₀
  have hM_pos : (0 : ℝ) < (cfg.P.M₀ : ℝ) := by linarith
  have hd_pos : (0 : ℝ) < (cfg.P.d : ℝ) := Nat.cast_pos.mpr cfg.P.hd
  have hM1d0 : 0 ≤ (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := by positivity
  have hM1d : (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) ≤ Real.exp (1 * E) := by
    have hlogM : Real.log (cfg.P.M₀ : ℝ) ≤ L :=
      Real.log_le_log hM_pos (by linarith [hM_pos])
    have hdiv_le : Real.log (cfg.P.M₀ : ℝ) / (cfg.P.d : ℝ) ≤ L / L ^ ((1 - β) / 2) :=
      le_trans (div_le_div_of_nonneg_right hlogM hd_pos.le)
        (div_le_div_of_nonneg_left (by linarith) (by positivity) hd_lo)
    have hL_pow_div : L / L ^ ((1 - β) / 2) = L ^ ((1 + β) / 2) := by
      nth_rw 1 [← Real.rpow_one L]
      rw [← Real.rpow_sub hL_pos]
      congr 1; ring
    have hexp_le : Real.log (cfg.P.M₀ : ℝ) / (cfg.P.d : ℝ) ≤ 1 * E := by
      rw [hL_pow_div] at hdiv_le
      have hLE : L ^ ((1 + β) / 2) ≤ E :=
        le_mul_of_one_le_right (by linarith only [hLa1]) hLL1
      linarith only [hdiv_le, hLE]
    rw [Real.rpow_def_of_pos hM_pos, mul_one_div]
    exact Real.exp_le_exp.mpr hexp_le
  have hk_le : (cfg.P.k : ℝ) ≤ Real.exp (2 * E) := by
    have h21 : (2 : ℝ) ≤ Real.exp (1 * E) := by
      simpa using le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_le_exp.mpr hE1)
    calc
      (cfg.P.k : ℝ) ≤ 2 * (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) := cfg.P.hk_upper
      _ ≤ Real.exp (1 * E) * Real.exp (1 * E) :=
        mul_le_mul h21 hM1d hM1d0 (by positivity)
      _ = Real.exp (2 * E) := by rw [← Real.exp_add]; ring_nf
  have hd1_le : (cfg.P.d : ℝ) + 1 ≤ Real.exp (3 * E) := by
    have hd_L : (cfg.P.d : ℝ) + 1 ≤ 4 * L := by
      have h1 : L ^ ((1 - β) / 2) ≤ L := by
        calc
          L ^ ((1 - β) / 2) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
          _ = L := Real.rpow_one L
      linarith
    calc
      (cfg.P.d : ℝ) + 1 ≤ 2 ^ 2 * L := by linarith
      _ ≤ Real.exp (2 * E) * Real.exp E :=
        mul_le_mul hTwoE2 hL_le_E hL_pos.le (by positivity)
      _ = Real.exp (3 * E) := by rw [← Real.exp_add]; ring_nf
  have hlogF0_1 : 1 ≤ logFactor cfg.P cfg.N₀ := one_le_logFactor cfg.P cfg.N₀
  have hlogF_1 : 1 ≤ 2 * logFactor cfg.P cfg.N₀ := by linarith
  have hlogF_E : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * E) := by
    simpa only [L, LL, E, mul_assoc] using hlogF
  have hlogF_p : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1) ≤
      Real.exp (C_γ * E) :=
    le_trans (pow_le_pow_right₀ hlogF_1 (by omega :
      max cfg.TP.p_T cfg.LP.p_last + 1 ≤ max cfg.TP.p_T cfg.LP.p_last + 3)) hlogF_E
  have hlogF_2 : (logFactor cfg.P cfg.N₀) ^ 2 ≤ Real.exp (C_γ * E) := by
    have hle : (logFactor cfg.P cfg.N₀) ^ 2 ≤ (2 * logFactor cfg.P cfg.N₀) ^ 2 := by
      gcongr; linarith
    exact le_trans hle (le_trans (pow_le_pow_right₀ hlogF_1 (by omega :
      2 ≤ max cfg.TP.p_T cfg.LP.p_last + 3)) hlogF_E)
  have hlogN1 : 1 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    linarith
  have hcore := asymptotic_exponents_core cfg.P.d cfg.P.hd hCγ hCψ hCN hL1 hE1 hB1
    hB_le_E hd_mul_B hL_le_E
    (hTP.2.2.1 (cfg.P.M₀ ^ 2)) (by simpa only [L, LL, B, mul_assoc] using hγℓ)
    (hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)) (by simpa only [L, LL, B, mul_assoc] using hγr)
    (max_le (by simpa only [L, LL, E, mul_assoc] using hσT)
      (by simpa only [L, LL, E, mul_assoc] using hσL))
    (le_max_left _ _) (by simpa only [L, LL, B, mul_assoc] using hσM)
    hTP.2.2.2.2.2.2.2.2.2 (by simpa only [L, LL, B, mul_assoc] using hcT)
    hLP.2.2.2.2 (by simpa only [L, LL, B, mul_assoc] using hcL)
    (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) (by simpa only [L, LL, B, mul_assoc] using hΨ)
    hM1d0 hM1d (Nat.cast_nonneg _) hk_le hd1_le
    (one_le_pow₀ hlogF_1) hlogF_p (one_le_pow₀ hlogF0_1) hlogF_2
    hlogN1 hlogN
  refine ⟨?_, ?_⟩
  · have h1 : 1 / alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last ≤
        Real.exp ((15 + 5 * C_γ) * E) := by
      simpa only [alg2KappaAt, alg2SigmaTotAt, alg2SigmaGame] using hcore.1
    simpa only [E, mul_assoc] using h1
  · have h2 : alg2CollapsedFactor cfg ≤ Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) := by
      unfold alg2CollapsedFactor
      dsimp only
      exact hcore.2
    simpa only [E, mul_assoc] using h2

/-- Parameterized Theorem 5.1 asymptotic exponent lemma (`jtree.tex` page 30), specialized to
the own-level vertex cap `n_last = levelM cfg.TP cfg.P cfg.P.d + 1`. -/
theorem theorem_5_1_asymptotic_exponents_own {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last (levelM cfg.TP cfg.P cfg.P.d + 1) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    1 / alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) :=
  theorem_5_1_asymptotic_exponents_at (levelM cfg.TP cfg.P cfg.P.d + 1) hβ0 hβ1 hM₀ hD hTP hLP
    hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN

theorem theorem_5_1_asymptotic_exponents_relaxed {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    1 / alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) :=
  theorem_5_1_asymptotic_exponents_at cfg.N₀ hβ0 hβ1 hM₀ hD hTP hLP hCγ hCψ hCN hγℓ hγr
    hσT hσL hσM hcT hcL hΨ hlogF hlogN

/-- Parameterized Theorem 5.1 asymptotic exponent lemma (`jtree.tex` page 30), taking the
original `L^β` bounds on `hσT` and `hσL` and delegating to
`theorem_5_1_asymptotic_exponents_relaxed`. -/
theorem theorem_5_1_asymptotic_exponents {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hLP : cfg.LP.Valid)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
    let LL := Real.log (L + 2)
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := 62 + 21 * C_γ + 4 * C_ψ + C_N
    1 / alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ Real.exp (C_κ * L ^ a * LL) ∧
    alg2CollapsedFactor cfg ≤ Real.exp (C_rt * L ^ a * LL) :=
  theorem_5_1_asymptotic_exponents_relaxed hβ0 hβ1 hM₀ hD hTP hLP hCγ hCψ hCN hγℓ hγr
    (exp_rpow_le_half_one_add hM₀ hβ1 hCγ hσT)
    (exp_rpow_le_half_one_add hM₀ hβ1 hCγ hσL)
    hσM hcT hcL hΨ hlogF hlogN

/-- Explicit subpolynomial factor `m^{o(1)}`:
`exp(C * (log(m + 2))^a * log(log(m + 2) + 2))` (`jtree.tex` page 15). -/
noncomputable def alg2TimeFactor (C a : ℝ) (m : ℕ) : ℝ :=
  Real.exp (C * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2))

/-- Explicit inverse-subpolynomial lower bound on the min-ratio cycle quality `κ`:
`exp(-C * (log(m + 2))^a * log(log(m + 2) + 2))`. -/
noncomputable def alg2KappaLower (C a : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-(C * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2)))

lemma alg2TimeFactor_pos (C a : ℝ) (m : ℕ) : 0 < alg2TimeFactor C a m :=
  Real.exp_pos _

lemma alg2KappaLower_pos (C a : ℝ) (m : ℕ) : 0 < alg2KappaLower C a m :=
  Real.exp_pos _

lemma alg2TimeFactor_le_rpow {C a δ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hδ : 0 < δ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → alg2TimeFactor C a m ≤ B * (m : ℝ) ^ δ := by
  obtain ⟨B0, hB0_pos, hB0⟩ := exp_subpoly_mul_loglog_le_rpow (C := |C|) ha0 ha1 hδ
  refine ⟨max 1 (B0 * (3 : ℝ) ^ δ), le_max_left _ _, fun m hm => ?_⟩
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_m2 : (m : ℝ) + 2 ≤ 3 * (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hL : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hLL : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hExpC : alg2TimeFactor C a m ≤
      Real.exp (|C| * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hL a)) hLL)
  have hB_step : B0 * ((m : ℝ) + 2) ^ δ ≤ B0 * (3 * (m : ℝ)) ^ δ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hm_m2 hδ.le) hB0_pos.le
  have h3pow : B0 * (3 * (m : ℝ)) ^ δ = (B0 * (3 : ℝ) ^ δ) * (m : ℝ) ^ δ := by
    rw [Real.mul_rpow (by norm_num) hm_nn, mul_assoc]
  have hMax : (B0 * (3 : ℝ) ^ δ) * (m : ℝ) ^ δ ≤ max 1 (B0 * (3 : ℝ) ^ δ) * (m : ℝ) ^ δ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hm_nn _)
  exact le_trans hExpC (le_trans (hB0 _ hm3)
    (le_trans (h3pow ▸ hB_step) hMax))

/-- **Proof that `alg2TimeFactor C a m = m^{o(1)}`** for all `0 ≤ a < 1` (`jtree.tex` page 15):
`log (alg2TimeFactor C a m) / log m → 0` as `m → ∞`. -/
theorem tendsto_log_alg2TimeFactor_div_log (C : ℝ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Filter.Tendsto (fun m : ℕ => Real.log (alg2TimeFactor C a m) / Real.log (m : ℝ))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨B, hB_pos, hB⟩ := exp_subpoly_mul_loglog_le_rpow (C := |C|) ha0 ha1 (by positivity : 0 < ε / 4)
  have hTend := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_gt_atTop (max 1 (2 * |Real.log B| / ε)))
  rw [Filter.eventually_atTop] at hTend
  obtain ⟨N0, hN0⟩ := hTend
  refine ⟨max N0 2, fun m hm => ?_⟩
  have hm2 : 2 ≤ m := le_trans (le_max_right _ _) hm
  have hN0m := hN0 m (le_trans (le_max_left _ _) hm)
  have hlogm_gt1 : 1 < Real.log (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN0m
  have hlogm_pos : 0 < Real.log (m : ℝ) := by linarith
  have hmR_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hL : 0 ≤ Real.log ((m : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hLL : 0 ≤ Real.log (Real.log ((m : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
  have hm2_sq : (m : ℝ) + 2 ≤ (m : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    nlinarith
  have hlog_m2 : Real.log ((m : ℝ) + 2) ≤ 2 * Real.log (m : ℝ) := by
    have h1 : Real.log ((m : ℝ) + 2) ≤ Real.log ((m : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hm2_sq
    simpa [Real.log_pow] using h1
  have hExp_ub : |C| * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2) ≤
      Real.log B + (ε / 2) * Real.log (m : ℝ) := by
    have hle := hB ((m : ℝ) + 2) hm3
    have hlog := Real.log_le_log (Real.exp_pos _) hle
    have hm2_pow : 0 < ((m : ℝ) + 2) ^ (ε / 4) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.log_exp, Real.log_mul hB_pos.ne' hm2_pow.ne', Real.log_rpow (by linarith)] at hlog
    have hq : (ε / 4) * Real.log ((m : ℝ) + 2) ≤ (ε / 2) * Real.log (m : ℝ) := by nlinarith
    linarith
  have hAbs_num : |Real.log (alg2TimeFactor C a m)| =
      |C| * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2) := by
    rw [alg2TimeFactor, Real.log_exp, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hL a), abs_of_nonneg hLL]
  have hLogB_div : Real.log B / Real.log (m : ℝ) < ε / 2 := by
    have hgt : 2 * |Real.log B| / ε < Real.log (m : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hN0m
    rw [div_lt_iff₀ hlogm_pos]
    have h1 := (div_lt_iff₀ hε).mp hgt
    have h2 : Real.log B ≤ |Real.log B| := le_abs_self _
    linarith
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlogm_pos, hAbs_num]
  have hDiv_le : (|C| * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2)) /
      Real.log (m : ℝ) ≤ Real.log B / Real.log (m : ℝ) + ε / 2 := by
    rw [div_le_iff₀ hlogm_pos]
    calc
      |C| * (Real.log ((m : ℝ) + 2)) ^ a * Real.log (Real.log ((m : ℝ) + 2) + 2)
          ≤ Real.log B + (ε / 2) * Real.log (m : ℝ) := hExp_ub
      _ = (Real.log B / Real.log (m : ℝ) + ε / 2) * Real.log (m : ℝ) := by
        field_simp [hlogm_pos.ne']
  linarith

lemma one_add_log_le_alg2CollapsedFactor (cfg : Alg2Config) (hV : cfg.ValidNoHidden) :
    1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ alg2CollapsedFactor cfg := by
  have hln : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    linarith
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have h2γ : 1 ≤ 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1 := by linarith
  have hNonneg : 0 ≤ ((((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
      (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
      (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
      (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)) +
      2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) *
      (((cfg.P.d : ℝ) + 1) ^ 2 * (20 * alg2PsiGame cfg.Ψ cfg.P.M₀) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1) *
      (16 * ((cfg.P.d : ℝ) + 1) ^ 2 * 2 ^ cfg.P.d * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d *
        (cfg.P.k : ℝ) * (logFactor cfg.P cfg.N₀) ^ 2 + ((cfg.P.d : ℝ) + 1) ^ 2 + 1) := by
    have := hV.hTP.2.2.2.2.2.2.2.2.2; have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2); have := one_le_logFactor cfg.P cfg.N₀
    have := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀; positivity
  unfold alg2CollapsedFactor
  dsimp only
  nlinarith

lemma two_ceil_γℓ_succ_le_alg2TimeFactor {cfg : Alg2Config} {β C_γ C_ψ C_N : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hM₀ : 1 ≤ cfg.P.M₀)
    (hTP : cfg.TP.Valid) (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2))) :
    2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1) ≤
      alg2TimeFactor (62 + 21 * C_γ + 4 * C_ψ + C_N) ((1 + β) / 2) cfg.P.M₀ := by
  let L := Real.log ((cfg.P.M₀ : ℝ) + 2)
  let LL := Real.log (L + 2)
  let E := L ^ ((1 + β) / 2) * LL
  have hL1 : 1 ≤ L := one_le_log_add_two hM₀
  have hLL1 : 1 ≤ LL := by
    have : Real.exp 1 ≤ L + 2 := by linarith [Real.exp_one_lt_three]
    simpa only [LL, Real.log_exp] using Real.log_le_log (Real.exp_pos 1) this
  have hE1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hL1 (by linarith)) hLL1
  have hB_le_E : L ^ β * LL ≤ E :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) (by linarith)
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hCeil : (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) < cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 1 :=
    Nat.ceil_lt_add_one (le_trans zero_le_one hγ1)
  have h2Ceil : 2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1) ≤ 6 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
    linarith
  have hγ_E : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ Real.exp (C_γ * E) := by
    refine le_trans hγℓ (Real.exp_le_exp.mpr ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hB_le_E hCγ
  have h6_exp2 : (6 : ℝ) ≤ Real.exp 2 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have h6_exp2E : (6 : ℝ) ≤ Real.exp (2 * E) :=
    le_trans h6_exp2 (Real.exp_le_exp.mpr (by linarith))
  calc
    2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1) ≤ 6 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := h2Ceil
    _ ≤ Real.exp (2 * E) * Real.exp (C_γ * E) :=
      mul_le_mul h6_exp2E hγ_E (le_trans zero_le_one hγ1) (Real.exp_pos _).le
    _ = Real.exp ((2 + C_γ) * E) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((62 + 21 * C_γ + 4 * C_ψ + C_N) * E) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    _ = alg2TimeFactor (62 + 21 * C_γ + 4 * C_ψ + C_N) ((1 + β) / 2) cfg.P.M₀ := by
      simp only [alg2TimeFactor, E, L, LL, mul_assoc]

end Asymptotics

end MinCostFlow.Chain
