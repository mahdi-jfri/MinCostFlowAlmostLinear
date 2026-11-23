module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The arithmetic of the budget of a step with `0 < j`

This file is the arithmetic part of `stepPos_budget` (`DynSpannerAmortPos.lean`), stated with
real variables only. The variables are the sizes of the step (written in the docstrings of the two
lemmas), and the hypotheses are the bounds of `stepPos_facts` and of the sparsifier call. The two
lemmas cover the two branches of the step: `E_aff` nonempty (`stepPos_arith_nonempty`) and empty
(`stepPos_arith_empty`).

The proof is the same in both. With `W = sLen · Y` (`Y = E_L Δ₁`) and `X = K₁ Λ W`:
* every size is at most a constant times `W`: `|S_{j-1}| ≤ 2 sLen`, `j ≤ ℓ ≤ Y`, and
  `|E_aff| · Z ≤ 2 W` whenever `V Z ≤ Y`, which covers `Z = 1, ℓ, ℓ², γ (ℓ + 1), γ² (ℓ + 1)`,
  `γ ℓ` and `(ℓ + 1)²` by the slack `V (ℓ + 1)² γ² ≤ Y`;
* the sparsifier, `J̃` and the log factors are at most a constant times `X`;
* the old levels `oS` are paid by the potential: `oS + Φ₁ ≤ Φ₀ + |E(J̃)|`;
* the constants and the terms in `L` are paid by `(L + 1) Enc(u) ≥ L + 1`.
Then the constant `C ≥ 2 T + 8 R + 400000` covers each coefficient.
-/

namespace MinCostFlow.DynSpanner.Program

public section

/-- The common bounds of both branches, in terms of `W = sLen · Y`. -/
private lemma stepPos_arith_common {j s a cr cand Sc SE sLen V ℓ Y : ℝ}
    (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (hsL : 0 ≤ sLen) (hs0 : 0 ≤ s) (hs : s ≤ 2 * sLen)
    (ha0 : 0 ≤ a) (ha : a ≤ s * V) (hcr : cr ≤ s * (j * V)) (hcand0 : 0 ≤ cand)
    (hcand : cand ≤ cr) (hSc : Sc ≤ cand * ℓ) (hSE : SE ≤ a * ℓ)
    (hV0 : 0 ≤ V) (hℓ1 : 1 ≤ ℓ) (hVℓ2 : V * ℓ ^ 2 ≤ Y) (hVY : V ≤ Y) (hVℓ : V * ℓ ≤ Y)
    (hℓY : ℓ ≤ Y) (hY1 : 1 ≤ Y) :
    s ≤ 2 * (sLen * Y) ∧ j * s ≤ 2 * (sLen * Y) ∧ a ≤ 2 * (sLen * Y) ∧
      cr ≤ 2 * (sLen * Y) ∧ Sc ≤ 2 * (sLen * Y) ∧ cand * j ≤ 2 * (sLen * Y) ∧
      a * j ≤ 2 * (sLen * Y) ∧ SE ≤ 2 * (sLen * Y) ∧
      (∀ Z : ℝ, 0 ≤ Z → V * Z ≤ Y → a * Z ≤ 2 * (sLen * Y)) := by
  have hY0 : 0 ≤ Y := by linarith
  have haV : a ≤ 2 * sLen * V := by
    have := mul_le_mul_of_nonneg_right hs hV0
    linarith
  have haX : ∀ Z : ℝ, 0 ≤ Z → V * Z ≤ Y → a * Z ≤ 2 * (sLen * Y) := fun Z hZ0 hZ => by
    have h1 : a * Z ≤ 2 * sLen * V * Z := mul_le_mul_of_nonneg_right haV hZ0
    have h2 : 2 * sLen * (V * Z) ≤ 2 * sLen * Y := mul_le_mul_of_nonneg_left hZ (by linarith)
    linarith
  have hcrX : ∀ Z : ℝ, 0 ≤ Z → V * (ℓ * Z) ≤ Y → cr * Z ≤ 2 * (sLen * Y) := fun Z hZ0 hZ => by
    have h1 : cr * Z ≤ s * (j * V) * Z := mul_le_mul_of_nonneg_right hcr hZ0
    have h2 : j * V * Z ≤ V * (ℓ * Z) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjℓ hV0) hZ0
      linarith
    have h3 : s * (j * V * Z) ≤ s * (V * (ℓ * Z)) := mul_le_mul_of_nonneg_left h2 hs0
    have h4 : s * (V * (ℓ * Z)) ≤ 2 * sLen * Y :=
      mul_le_mul hs hZ (mul_nonneg hV0 (mul_nonneg (by linarith) hZ0)) (by linarith)
    linarith
  have hsW : s ≤ 2 * (sLen * Y) := by
    have : sLen ≤ sLen * Y := le_mul_of_one_le_right hsL hY1
    linarith
  have hjs : j * s ≤ 2 * (sLen * Y) := by
    have h1 : j * s ≤ Y * s := mul_le_mul_of_nonneg_right (le_trans hjℓ hℓY) hs0
    have h2 : Y * s ≤ Y * (2 * sLen) := mul_le_mul_of_nonneg_left hs hY0
    linarith
  have ha2 : a ≤ 2 * (sLen * Y) := by simpa using haX 1 zero_le_one (by simpa using hVY)
  have haℓ : a * ℓ ≤ 2 * (sLen * Y) := haX ℓ (by linarith) hVℓ
  have hcr1 : cr ≤ 2 * (sLen * Y) := by simpa using hcrX 1 zero_le_one (by simpa using hVℓ)
  have hcrℓ : cr * ℓ ≤ 2 * (sLen * Y) := hcrX ℓ (by linarith) (by rw [← pow_two]; exact hVℓ2)
  have hcandℓ : cand * ℓ ≤ 2 * (sLen * Y) :=
    le_trans (mul_le_mul_of_nonneg_right hcand (by linarith)) hcrℓ
  have hcandj : cand * j ≤ 2 * (sLen * Y) :=
    le_trans (mul_le_mul_of_nonneg_left hjℓ hcand0) hcandℓ
  have haj : a * j ≤ 2 * (sLen * Y) := le_trans (mul_le_mul_of_nonneg_left hjℓ ha0) haℓ
  exact ⟨hsW, hjs, ha2, hcr1, le_trans hSc hcandℓ, hcandj, haj, le_trans hSE haℓ, haX⟩

/-- The products of `ℓ` and `γ` that the budget uses are at most `(ℓ + 1)² γ²`. -/
lemma slack_le {ℓ γ : ℝ} (hℓ1 : 1 ≤ ℓ) (hγ1 : 1 ≤ γ) :
    1 ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧ ℓ ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧ ℓ ^ 2 ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧
      γ * (ℓ + 1) ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧ γ ^ 2 * (ℓ + 1) ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧
      γ * ℓ ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧ γ ≤ (ℓ + 1) ^ 2 * γ ^ 2 ∧
      (ℓ + 1) ^ 2 ≤ (ℓ + 1) ^ 2 * γ ^ 2 := by
  have hγγ : γ ≤ γ ^ 2 := by rw [pow_two]; exact le_mul_of_one_le_left (by linarith) hγ1
  have hγ2 : 1 ≤ γ ^ 2 := le_trans hγ1 hγγ
  have hl0 : 0 ≤ ℓ + 1 := by linarith
  have hll : ℓ + 1 ≤ (ℓ + 1) ^ 2 := by
    rw [pow_two]; exact le_mul_of_one_le_left hl0 (by linarith)
  have hsq : ℓ ^ 2 ≤ (ℓ + 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hA : (ℓ + 1) ^ 2 ≤ (ℓ + 1) ^ 2 * γ ^ 2 := le_mul_of_one_le_right (by positivity) hγ2
  have hB : γ ^ 2 * (ℓ + 1) ≤ (ℓ + 1) ^ 2 * γ ^ 2 := by
    rw [mul_comm ((ℓ + 1) ^ 2)]; exact mul_le_mul_of_nonneg_left hll (by positivity)
  have hC : γ * (ℓ + 1) ≤ γ ^ 2 * (ℓ + 1) := mul_le_mul_of_nonneg_right hγγ hl0
  have hD : γ * ℓ ≤ γ * (ℓ + 1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hE : γ ≤ γ * ℓ := le_mul_of_one_le_right (by linarith) hℓ1
  refine ⟨by linarith, by linarith, by linarith, by linarith, hB, by linarith, by linarith, hA⟩

/-- **The budget of the nonempty branch, as arithmetic.** The variables: `Lr = L`, `j`, `enc` the
encoding size of the update, `s = |S_{j-1}|`, `a = |E_aff|`, `cr` and `cand` the candidates,
`Sc`, `SE` the lengths of their old walks, `Jn = |V(J)|`, `Jt = |E(J̃)|`, `oS` the old levels,
`Φ0`, `Φ1` the potential, `UH`, `D`, `Q` the guest's time bound, `Tr` the translation, `Sout`,
`SoutEmb`, `Smid`, `Srw` the lengths of the output, shortcut, composed and new walks,
`t = L + 1 - j`, and the factors of the budget. -/
theorem stepPos_arith_nonempty
    {Lr j enc s a cr cand Sc SE Jn Jt oS Φ0 Φ1 UH D Q KtI ΛJt ΛJs len Tr Sout SoutEmb Smid Srw t
      sLen V ℓ γ Y Λ Λ₁ K₁ Ks T R C : ℝ}
    (hL : 1 ≤ Lr) (henc : 1 ≤ enc) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (ht : t ≤ Lr + 1) (hjL : j ≤ Lr)
    (hsL : 0 ≤ sLen) (hs0 : 0 ≤ s) (hs : s ≤ 2 * sLen) (ha1 : 1 ≤ a) (ha : a ≤ s * V)
    (hcr : cr ≤ s * (j * V)) (hcand0 : 0 ≤ cand) (hcand : cand ≤ cr)
    (hSc : Sc ≤ cand * ℓ) (hSE : SE ≤ a * ℓ) (hJn0 : 0 ≤ Jn) (hJn : Jn ≤ 2 * a)
    (hV0 : 0 ≤ V) (hℓ1 : 1 ≤ ℓ) (hγ1 : 1 ≤ γ) (hQY : V * (ℓ + 1) ^ 2 * γ ^ 2 ≤ Y)
    (hℓY : ℓ ≤ Y) (hY1 : 1 ≤ Y)
    (hΛ1 : 1 ≤ Λ) (hK₁ : 1 ≤ K₁) (hKs0 : 0 ≤ Ks) (hKs : Ks ≤ K₁) (hKtI0 : 0 ≤ KtI)
    (hKtI : KtI ≤ K₁)
    (hJt : Jt ≤ Ks * Jn * γ * ΛJs) (hΛJs0 : 0 ≤ ΛJs) (hΛJs : ΛJs ≤ Λ)
    (hlen0 : 0 ≤ len) (hlen : len ≤ ℓ + 1)
    (hQ : Q ≤ KtI * (1 + Jn + a * γ ^ 2 * len) * ΛJt + 1) (hΛJt0 : 0 ≤ ΛJt) (hΛJt : ΛJt ≤ Λ)
    (hTr : Tr ≤ T * a * (ℓ + 1) ^ 2 * Λ₁ + 500 * a * γ) (hΛ₁ : Λ₁ ≤ Λ) (hΛ₁0 : 0 ≤ Λ₁)
    (hSout : Sout ≤ a * (2 * γ)) (hSoutEmb : SoutEmb ≤ Sout) (hSmid : Smid ≤ a * (γ * (ℓ + 1)))
    (hSrw : Srw ≤ a * (3 * γ * ℓ))
    (hpot : oS + Φ1 ≤ Φ0 + Jt) (hT0 : 0 ≤ T) (hR0 : 0 ≤ R) (hUH : 0 ≤ UH) (hD : 0 ≤ D)
    (hC : 2 * T + 8 * R + 400000 ≤ C) :
    (500 * (Lr + 1) + 1100) + (20 * t + 20) +
        (100 * cr + 100 * (j * s) + 100 * s + 100 * j + 100 * Sc + 40 * (cand * j) +
          160 * cand + a * (35 * j + 60) + 800 * SE + 2000 * a + 1200) +
        (((R + 6) * Q + Tr + 400 * Sout + 70 * Smid + 120 * SoutEmb + 800 * SE + 800 * Smid +
            400 * Srw + 100 * SE + 1440 * oS + 150 * t + 3150 * Jt + 2185 * a + 3525) +
          (35 * s + 500 * a + 30 * Jn + 95 * UH + 450) + 40) + 330 +
        35 * Lr + 520 + 90 * D + 90 * a + 240 * UH + 240 ≤
      C * ((Lr + 1) * enc + UH + D + sLen * (22 * K₁ * Y * Λ)) + 1440 * (Φ0 - Φ1) := by
  obtain ⟨k1, kℓ, kℓ2, kγl1, kγ2, kγℓ, kγ, kl2⟩ := slack_le hℓ1 hγ1
  have key : ∀ Z : ℝ, Z ≤ (ℓ + 1) ^ 2 * γ ^ 2 → V * Z ≤ Y := fun Z hZ => by
    have := mul_le_mul_of_nonneg_left hZ hV0
    linarith
  have hVY : V ≤ Y := by simpa using key 1 k1
  have hVℓ : V * ℓ ≤ Y := key ℓ kℓ
  have hVℓ2 : V * ℓ ^ 2 ≤ Y := key _ kℓ2
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨hsW, hjs, ha2, hcr1, hScW, hcandj, haj, hSEW, haX⟩ :=
    stepPos_arith_common hj1 hjℓ hsL hs0 hs ha0 ha hcr hcand0 hcand hSc hSE hV0 hℓ1
      hVℓ2 hVY hVℓ hℓY hY1
  have hγ0 : 0 ≤ γ := by linarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hγ20 : 0 ≤ γ ^ 2 := by positivity
  set W := sLen * Y with hW
  have hW0 : 0 ≤ W := mul_nonneg hsL (by linarith)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hK0 : 0 ≤ K₁ := by linarith
  have hΛW0 : 0 ≤ Λ * W := mul_nonneg hΛ0 hW0
  set X := K₁ * Λ * W with hX
  have hΛW : Λ * W ≤ X := by
    have : Λ * W ≤ K₁ * (Λ * W) := le_mul_of_one_le_left hΛW0 hK₁
    rw [hX]; linarith
  have hWX : W ≤ X := le_trans (le_mul_of_one_le_left hW0 hΛ1) hΛW
  -- The walks.
  have haγ : a * γ ≤ 2 * W := haX γ hγ0 (key γ kγ)
  have haγl1 : a * (γ * (ℓ + 1)) ≤ 2 * W :=
    haX _ (mul_nonneg hγ0 (by linarith)) (key _ kγl1)
  have haγℓ : a * (γ * ℓ) ≤ 2 * W := haX _ (mul_nonneg hγ0 hℓ0) (key _ kγℓ)
  have hal2 : a * (ℓ + 1) ^ 2 ≤ 2 * W := haX _ (by positivity) (key _ kl2)
  -- `J̃`.
  have hJt4 : Jt ≤ 4 * X := by
    have h1 : Jt ≤ Ks * (2 * a) * γ * Λ := by
      refine le_trans hJt ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJn hKs0)
        hγ0) hΛJs hΛJs0 (mul_nonneg (mul_nonneg hKs0 (by linarith)) hγ0)
    have h3 : 2 * Ks * Λ * (a * γ) ≤ 2 * Ks * Λ * (2 * W) :=
      mul_le_mul_of_nonneg_left haγ (mul_nonneg (by linarith) hΛ0)
    have h4 : Ks * (Λ * W) ≤ K₁ * (Λ * W) := mul_le_mul_of_nonneg_right hKs hΛW0
    have h5 : Ks * (2 * a) * γ * Λ = 2 * Ks * Λ * (a * γ) := by ring
    rw [hX]; linarith
  -- The guest's time bound.
  have hQ8 : Q ≤ 8 * X + 1 := by
    have hsz : 1 + Jn + a * γ ^ 2 * len ≤ 4 * (a * (γ ^ 2 * (ℓ + 1))) := by
      have h1 : a * γ ^ 2 * len ≤ a * γ ^ 2 * (ℓ + 1) :=
        mul_le_mul_of_nonneg_left hlen (mul_nonneg ha0 hγ20)
      have h2 : a ≤ a * (γ ^ 2 * (ℓ + 1)) :=
        le_mul_of_one_le_right ha0
          (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hγ1) (by linarith))
      have h3 : a * γ ^ 2 * (ℓ + 1) = a * (γ ^ 2 * (ℓ + 1)) := by ring
      linarith
    have hsz0 : 0 ≤ 1 + Jn + a * γ ^ 2 * len := by
      have := mul_nonneg (mul_nonneg ha0 hγ20) hlen0
      linarith
    have haγ2 : a * (γ ^ 2 * (ℓ + 1)) ≤ 2 * W :=
      haX _ (mul_nonneg hγ20 (by linarith)) (key _ kγ2)
    have hin : KtI * (1 + Jn + a * γ ^ 2 * len) * ΛJt ≤ K₁ * (8 * W) * Λ :=
      mul_le_mul (mul_le_mul hKtI (by linarith) hsz0 hK0) hΛJt hΛJt0
        (mul_nonneg hK0 (by linarith))
    have h5 : K₁ * (8 * W) * Λ = 8 * X := by rw [hX]; ring
    linarith
  -- The translation.
  have hTr' : Tr ≤ 2 * T * X + 1000 * W := by
    have h3 : T * a * (ℓ + 1) ^ 2 * Λ₁ ≤ T * (2 * W) * Λ := by
      calc T * a * (ℓ + 1) ^ 2 * Λ₁ = T * (a * (ℓ + 1) ^ 2) * Λ₁ := by ring
        _ ≤ T * (2 * W) * Λ := mul_le_mul (mul_le_mul_of_nonneg_left hal2 hT0) hΛ₁ hΛ₁0
            (mul_nonneg hT0 (by linarith))
    have h5 : T * (2 * W) * Λ ≤ 2 * T * X := by
      have := mul_le_mul_of_nonneg_left hΛW (show 0 ≤ 2 * T by linarith)
      linarith
    linarith
  have hRQ : (R + 6) * Q ≤ (R + 6) * (8 * X + 1) := mul_le_mul_of_nonneg_left hQ8 (by linarith)
  -- The budget.
  have hE' : Lr + 1 ≤ (Lr + 1) * enc := le_mul_of_one_le_right (by linarith) henc
  have hCE : (5000 + R) * ((Lr + 1) * enc) ≤ C * ((Lr + 1) * enc) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hRE : R * (Lr + 1) ≤ R * ((Lr + 1) * enc) := mul_le_mul_of_nonneg_left hE' hR0
  have hRL : R ≤ R * (Lr + 1) := le_mul_of_one_le_right hR0 (by linarith)
  have hCX : (2 * T + 8 * R + 50000) * X ≤ C * (22 * X) := by
    have := mul_le_mul_of_nonneg_right (show 2 * T + 8 * R + 50000 ≤ 22 * C by linarith)
      (le_trans hW0 hWX)
    linarith
  have hCUH : 335 * UH ≤ C * UH := mul_le_mul_of_nonneg_right (by linarith) hUH
  have hCD : 90 * D ≤ C * D := mul_le_mul_of_nonneg_right (by linarith) hD
  have hbud : sLen * (22 * K₁ * Y * Λ) = 22 * X := by rw [hX, hW]; ring
  rw [hbud]
  have hjLr : j ≤ Lr + 1 := by linarith
  have hSoutW : Sout ≤ 4 * W := by linarith
  have hSmidW : Smid ≤ 2 * W := by linarith
  have hSrwW : Srw ≤ 6 * W := by
    have : a * (3 * γ * ℓ) = 3 * (a * (γ * ℓ)) := by ring
    linarith
  have hJnW : Jn ≤ 4 * W := by linarith
  have hcandW : cand ≤ 2 * W := by linarith
  have hajW : a * (35 * j + 60) ≤ 70 * W + 120 * W := by
    have : a * (35 * j + 60) = 35 * (a * j) + 60 * a := by ring
    linarith
  have hpot' : 1440 * oS ≤ 1440 * (Φ0 - Φ1) + 1440 * Jt := by linarith
  have hconst : (7425 : ℝ) ≤ 3713 * (Lr + 1) := by linarith
  have hX0 : 0 ≤ X := le_trans hW0 hWX
  have hCsplit : C * ((Lr + 1) * enc + UH + D + 22 * X) =
      C * ((Lr + 1) * enc) + C * UH + C * D + C * (22 * X) := by ring
  rw [hCsplit]
  clear_value W X
  linarith [hSoutEmb, hSout, hSmid, hSrw, hSE, hSEW, hScW, hTr', hRQ, hJt4]

/-- **The budget of the empty branch, as arithmetic.** The variables are those of
`stepPos_arith_nonempty`; here `oS + Φ1 ≤ Φ0`, since the new level `j` is empty. -/
theorem stepPos_arith_empty
    {Lr j enc s a cr cand Sc SE Jn oS Φ0 Φ1 UH D t sLen V ℓ Y Λ K₁ R C T : ℝ}
    (hL : 1 ≤ Lr) (henc : 1 ≤ enc) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (ht : t ≤ Lr + 1) (hjL : j ≤ Lr)
    (hsL : 0 ≤ sLen) (hs0 : 0 ≤ s) (hs : s ≤ 2 * sLen) (ha0 : 0 ≤ a) (ha : a ≤ s * V)
    (hcr : cr ≤ s * (j * V)) (hcand0 : 0 ≤ cand) (hcand : cand ≤ cr)
    (hSc : Sc ≤ cand * ℓ) (hSE : SE ≤ a * ℓ) (hJn : Jn ≤ 2 * a)
    (hV0 : 0 ≤ V) (hℓ1 : 1 ≤ ℓ) (hVℓ2 : V * ℓ ^ 2 ≤ Y) (hVY : V ≤ Y) (hVℓ : V * ℓ ≤ Y)
    (hℓY : ℓ ≤ Y) (hY1 : 1 ≤ Y) (hΛ1 : 1 ≤ Λ) (hK₁ : 1 ≤ K₁)
    (hpot : oS + Φ1 ≤ Φ0) (hT0 : 0 ≤ T) (hR0 : 0 ≤ R) (hUH : 0 ≤ UH) (hD : 0 ≤ D)
    (hC : 2 * T + 8 * R + 400000 ≤ C) :
    (500 * (Lr + 1) + 1100) + (20 * t + 20) +
        (100 * cr + 100 * (j * s) + 100 * s + 100 * j + 100 * Sc + 40 * (cand * j) +
          160 * cand + a * (35 * j + 60) + 800 * SE + 2000 * a + 1200) +
        ((1440 * oS + 150 * t + 2100) + (35 * s + 500 * a + 30 * Jn + 95 * UH + 450) + 40) +
        330 + 35 * Lr + 520 + 90 * D + 90 * a + 240 * UH + 240 ≤
      C * ((Lr + 1) * enc + UH + D + sLen * (22 * K₁ * Y * Λ)) + 1440 * (Φ0 - Φ1) := by
  obtain ⟨hsW, hjs, ha2, hcr1, hScW, hcandj, haj, hSEW, -⟩ :=
    stepPos_arith_common hj1 hjℓ hsL hs0 hs ha0 ha hcr hcand0 hcand hSc hSE hV0 hℓ1
      hVℓ2 hVY hVℓ hℓY hY1
  set W := sLen * Y with hW
  have hW0 : 0 ≤ W := mul_nonneg hsL (by linarith)
  have hX : W ≤ K₁ * Λ * W := by
    have h1 : 1 ≤ K₁ * Λ := one_le_mul_of_one_le_of_one_le hK₁ hΛ1
    exact le_mul_of_one_le_left hW0 h1
  have hE' : Lr + 1 ≤ (Lr + 1) * enc := le_mul_of_one_le_right (by linarith) henc
  have hCE : 5000 * ((Lr + 1) * enc) ≤ C * ((Lr + 1) * enc) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hCX : 50000 * (K₁ * Λ * W) ≤ C * (22 * (K₁ * Λ * W)) := by
    have := mul_le_mul_of_nonneg_right (show (50000 : ℝ) ≤ 22 * C by linarith)
      (le_trans hW0 hX)
    linarith
  have hCUH : 335 * UH ≤ C * UH := mul_le_mul_of_nonneg_right (by linarith) hUH
  have hCD : 90 * D ≤ C * D := mul_le_mul_of_nonneg_right (by linarith) hD
  have hbud : sLen * (22 * K₁ * Y * Λ) = 22 * (K₁ * Λ * W) := by rw [hW]; ring
  rw [hbud]
  have hjLr : j ≤ Lr + 1 := by linarith
  have hJnW : Jn ≤ 4 * W := by linarith
  have hcandW : cand ≤ 2 * W := by linarith
  have hajW : a * (35 * j + 60) ≤ 70 * W + 120 * W := by
    have : a * (35 * j + 60) = 35 * (a * j) + 60 * a := by ring
    linarith
  have hconst : (7425 : ℝ) ≤ 3713 * (Lr + 1) := by linarith
  have hCsplit : C * ((Lr + 1) * enc + UH + D + 22 * (K₁ * Λ * W)) =
      C * ((Lr + 1) * enc) + C * UH + C * D + C * (22 * (K₁ * Λ * W)) := by ring
  rw [hCsplit]
  linarith

end

end MinCostFlow.DynSpanner.Program
