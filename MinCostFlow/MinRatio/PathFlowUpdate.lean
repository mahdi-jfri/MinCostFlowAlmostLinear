module

public import MinCostFlow.Chain.Algorithm2
public import MinCostFlow.MinRatio.DetectorThreshold

/-!
# Matching routed flow to the Algorithm 2 update

Algorithm 2 (page 29) rescales the selected circulation by its gradient
inner product before routing it. With a fixed-point multiplier, the
actual normalization is its exact product with that inner product.
The following lemmas connect the normalized increment and its
absolute value to the model's two edge accounts.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- If the inner product is nonzero, choosing the actual normalization
from the stored multiplier recovers that multiplier exactly. -/
theorem pathFlow_normalization {inner : ℝ} (hinner : inner ≠ 0)
    (P : ℕ) (multiplier : ℤ) :
    -(-(((multiplier : ℝ) / (2 : ℝ) ^ P) * inner) / inner) =
      (multiplier : ℝ) / (2 : ℝ) ^ P := by
  rw [neg_div, neg_neg, mul_div_cancel_right₀ _ hinner]

/-- On a successful update, each live edge receives the normalized
signed and absolute increments in its two accounts. -/
theorem algorithm2_update_pathFlow {cfg : Alg2Config} (st : Alg2State cfg)
    (U : List Update) (g length : ℕ → ℝ) (P : ℕ) (multiplier : ℤ)
    (C : ℕ → ℝ) (s' : Alg2State cfg) :
    let G' := (translateBatch st.extG st.extToInt st.intToExt st.nextFresh U).1
    let inner := G'.inner g C
    let actual := -(((multiplier : ℝ) / (2 : ℝ) ^ P) * inner)
    inner ≠ 0 →
    algorithm2_update cfg st U g length actual = (s', some C) →
    ∀ e ∈ G'.E, ∀ coefficient : ℤ, C e = (coefficient : ℝ) →
      s'.flow e = st.flow e + (((multiplier * coefficient : ℤ) : ℝ) / (2 : ℝ) ^ P) ∧
      s'.detectAccum e = st.detectAccum e +
        (((|multiplier * coefficient| : ℤ) : ℝ) / (2 : ℝ) ^ P) := by
  dsimp only
  intro hinner hout e he coefficient hcoef
  unfold algorithm2_update at hout
  dsimp only at hout
  split at hout
  · simp only [Prod.mk.injEq, reduceCtorEq, and_false] at hout
  · rename_i dir hloop
    simp only [Prod.mk.injEq, Option.some.injEq] at hout
    obtain ⟨hstate, hdir⟩ := hout
    subst s'
    subst C
    have hscale : 0 < (2 : ℝ) ^ P := pow_pos (zero_lt_two : (0 : ℝ) < 2) _
    have hchange :
        (((multiplier : ℝ) / (2 : ℝ) ^ P) * dir e) =
          (((multiplier * coefficient : ℤ) : ℝ) / (2 : ℝ) ^ P) := by
      rw [hcoef, Int.cast_mul, div_mul_eq_mul_div]
    have habs : |((((multiplier * coefficient : ℤ) : ℝ) / (2 : ℝ) ^ P))| =
        (((|multiplier * coefficient| : ℤ) : ℝ) / (2 : ℝ) ^ P) := by
      rw [abs_div, abs_of_pos hscale, Int.cast_abs]
    simp only [ite_eq_left he, pathFlow_normalization hinner, hchange, habs, and_self]

/-- On failure, Update leaves both original edge accounts intact,
including on a call that translated a batch of edge names. -/
theorem algorithm2_update_failure_accounts {cfg : Alg2Config} (st s' : Alg2State cfg)
    (U : List Update) (g length : ℕ → ℝ) (actual : ℝ)
    (hout : algorithm2_update cfg st U g length actual = (s', none)) :
    s'.flow = st.flow ∧ s'.detectAccum = st.detectAccum := by
  unfold algorithm2_update at hout
  dsimp only at hout
  split at hout
  · simp only [Prod.mk.injEq, and_true] at hout
    subst s'
    exact ⟨rfl, rfl⟩
  · simp only [Prod.mk.injEq, Option.some_ne_none, and_false] at hout

/-- Algorithm 2 (page 29) preserves nonnegativity of the accumulated
absolute flow in both successful and failed updates. -/
theorem algorithm2_update_detectAccum_nonneg {cfg : Alg2Config} (st : Alg2State cfg)
    (U : List Update) (g length : ℕ → ℝ) (actual : ℝ)
    (ha : ∀ e, 0 ≤ st.detectAccum e) (e : ℕ) :
    0 ≤ (algorithm2_update cfg st U g length actual).1.detectAccum e := by
  unfold algorithm2_update
  dsimp only
  split
  · exact ha e
  · exact add_nonneg (ha e) (abs_nonneg _)

/-- Algorithm 2 starts the accumulated absolute flow at zero. -/
theorem algorithm2_init_detectAccum_zero (cfg : Alg2Config) (G : MGraph)
    (g length : ℕ → ℝ) (e : ℕ) :
    (algorithm2_init cfg G g length).detectAccum e = 0 := by
  rfl

/-- Resetting a reported account and leaving the other accounts in
place preserves nonnegativity, including on names outside the live graph. -/
theorem algorithm2_detect_detectAccum_nonneg {cfg : Alg2Config} (st : Alg2State cfg)
    (ha : ∀ e, 0 ≤ st.detectAccum e) (e : ℕ) :
    0 ≤ (algorithm2_detect cfg st).2.detectAccum e := by
  unfold algorithm2_detect
  dsimp only
  split
  · exact le_rfl
  · exact ha e

/-- Detect leaves each live edge with a nonnegative account strictly
below the reporting boundary whenever epsilon is positive. -/
theorem algorithm2_detect_accum_below {cfg : Alg2Config} (st : Alg2State cfg)
    (ha : ∀ e, 0 ≤ st.detectAccum e) (heps : 0 < cfg.ε)
    (e : ℕ) (he : e ∈ st.extG.E) :
    0 ≤ (algorithm2_detect cfg st).2.detectAccum e ∧
      st.extℓ e * (algorithm2_detect cfg st).2.detectAccum e < cfg.ε := by
  unfold algorithm2_detect
  dsimp only
  by_cases hr : cfg.ε ≤ st.extℓ e * st.detectAccum e
  · simp [he, hr, heps]
  · simp [he, hr, ha e, lt_of_not_ge hr]

/-- The model's Detect reset has the same integer account as the
fixed-point threshold test. This applies before refreshing lengths. -/
theorem algorithm2_detect_accum_dyadic {cfg : Alg2Config} (st : Alg2State cfg)
    (P : ℕ) (e : ℕ) (account : ℤ) (he : e ∈ st.extG.E)
    (hl : 0 < st.extℓ e)
    (ha : st.detectAccum e = (account : ℝ) / (2 : ℝ)^P) :
    let next : ℤ := if detectorThreshold P cfg.ε (st.extℓ e) ≤ account then 0 else account
    (algorithm2_detect cfg st).2.detectAccum e = (next : ℝ) / (2 : ℝ)^P := by
  dsimp only
  have ht : cfg.ε ≤ st.extℓ e * st.detectAccum e ↔
      detectorThreshold P cfg.ε (st.extℓ e) ≤ account := by
    rw [ha, detectorThreshold_test P cfg.ε (st.extℓ e) account hl, sub_nonneg]
  unfold algorithm2_detect
  dsimp only
  by_cases hr : detectorThreshold P cfg.ε (st.extℓ e) ≤ account
  · simp [he, hr, ht.mpr hr]
  · have hn : ¬ cfg.ε ≤ st.extℓ e * st.detectAccum e := fun h => hr (ht.mp h)
    simpa [he, hr, hn] using ha

/-- The live model account after Detect has an exact numerator.
Pairing that numerator with the refreshed length gives a bounded
detector residual at the same precision. -/
theorem algorithm2_detect_refresh_residual {cfg : Alg2Config} (st : Alg2State cfg)
    (P E e : ℕ) (account : ℤ) (newLength : ℝ) (he : e ∈ st.extG.E)
    (heps : 0 < cfg.ε) (hepsU : cfg.ε ≤ (2 : ℝ)^E)
    (hold : 1 / (2 : ℝ)^E ≤ st.extℓ e) (hnew : 1 / (2 : ℝ)^E ≤ newLength)
    (ha : 0 ≤ st.detectAccum e) (haccount : st.detectAccum e = (account : ℝ) / (2 : ℝ)^P) :
    ∃ next : ℤ,
      (algorithm2_detect cfg st).2.detectAccum e = (next : ℝ) / (2 : ℝ)^P ∧
      |((next - detectorThreshold P cfg.ε newLength : ℤ) : ℝ) / (2 : ℝ)^P| ≤
        (2 : ℝ)^(2 * E + 1) := by
  have hP : 0 < (2 : ℝ)^P := pow_pos zero_lt_two _
  have hE : 0 < 1 / (2 : ℝ)^E := one_div_pos.mpr (pow_pos zero_lt_two _)
  have hnonneg : 0 ≤ account := by
    rw [haccount, le_div_iff₀ hP, zero_mul] at ha
    exact_mod_cast ha
  refine ⟨if detectorThreshold P cfg.ε (st.extℓ e) ≤ account then 0 else account, ?_, ?_⟩
  · exact algorithm2_detect_accum_dyadic st P e account he (hE.trans_le hold) haccount
  · exact detectorThreshold_refresh_scaled_bound P E cfg.ε (st.extℓ e) newLength account
      heps hepsU hold hnew hnonneg

end MinCostFlow.MinRatio
