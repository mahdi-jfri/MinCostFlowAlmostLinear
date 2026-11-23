module

public import MinCostFlow.Chain.Ordered.LevelInvariants
public import MinCostFlow.SparseCore.LSFInit
public import MinCostFlow.SparseCore.BundleCoreParamsWith
public import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.LSF.Theorem22
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# LSF initializers for the concrete ordered chain

The concrete chain (`Chain/Ordered/ConcreteDefs.lean`) runs the bundle tool on an LSF
initializer `lsfInit`. Its parameters are fixed by one constant `C_lsst`: the stretch bound of
`bundleCoreParamsMach` is `mwuK0 C_lsst · k · log⁶`, and the MWU bound `concreteSigmaMWUMach` has
the constant `30 · mwuK0 C_lsst`. An initializer fits `C_lsst` when it meets the hypotheses of
Lemma 5.5 (`IsApproxMWUInit`, page 20) with constants that these bounds cover. This is
`IsConcreteLSFInit`.

The file proves three things.
1. `IsConcreteLSFInit.validFor`: a fitting initializer gives a valid initial LSF on every
   branch at stretch constant `mwuK0 C_lsst` (`IsValidLSFInitFor`). The proof is that of
   `IsApproxMWUInit.toValidLSFInitFor`, with the bound `K_σ ≤ mwuK0 C_lsst` in place of the raised
   constant.
2. `isConcreteLSFInit_initLSFOnline`: the online initializer of `theorem_2_2`'s oracle fits its
   own constant. Its constants (`α = 1`, `K_σ = mwuK0 C_lsst`, `K_ρ = 10`) come from
   `initLSFOnline_isApproxMWUInit`. So the hypothesis can hold (`exists_isConcreteLSFInit`).
3. `initBundleTreeWith_bucket_bound`: the bucket count of `initBundleTreeWith lsfInit` on a
   component, for lengths in `[e^{-A}, e^B]`, as for the online initializer
   (`initBundleTree_bucket_bound`). Only the stretch bound of the initial LSF is used.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Bundle

section ConcreteLSFInit

/-- `lsfInit` is an approximate MWU initializer (`IsApproxMWUInit`, the hypotheses of Lemma 5.5,
page 20) whose constants fit the concrete chain at `C_lsst`: its stretch constant `K_σ` is at most
`mwuK0 C_lsst`, and the MWU constant `3 K_ρ K₀` of
`sparseCoreBundleRestartToolMachWith_toolMWUOrdRestart` is at most `30 · mwuK0 C_lsst`. -/
def IsConcreteLSFInit (lsfInit : LSFInit) (C_lsst : ℝ) : Prop :=
  ∃ C₀ α K_σ K_ρ : ℝ, IsApproxMWUInit lsfInit C₀ α K_σ K_ρ ∧ 1 ≤ K_ρ ∧
    K_σ ≤ mwuK0 C_lsst ∧
    3 * K_ρ * max K_σ (max (112 * (1 + α) * max 1 C₀) 2240) ≤ 30 * mwuK0 C_lsst

/-- A fitting initializer gives a valid initial LSF on every branch `j < k` at stretch constant
`mwuK0 C_lsst`. The proof follows `IsApproxMWUInit.toValidLSFInitFor`: Lemma 5.4 for
`initLSFWith` (`initLSFWith_spec`, `initLSFWith_inv`) at stretch constant `K_σ`, raised to
`mwuK0 C_lsst` by `K_σ ≤ mwuK0 C_lsst`. -/
theorem IsConcreteLSFInit.validFor {lsfInit : LSFInit} {C_lsst : ℝ}
    (h : IsConcreteLSFInit lsfInit C_lsst) {k j : ℕ} (hj : j < k) :
    IsValidLSFInitFor lsfInit C_lsst k j := by
  obtain ⟨C₀, α, K_σ, K_ρ, hA, _, hKσ, _⟩ := h
  intro G₀ ℓ₀ hG₀ hV₀ hℓ₀ hk
  obtain ⟨thresh, _, _, v, T_raw, r₀, C_reps, π, W_T, _, _, _, _, _, hv_pos, hp, _, hEq⟩ :=
    hA G₀ ℓ₀ k hG₀ hV₀ hℓ₀ hk
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsp := initLSFWith_spec hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
  have hinv := initLSFWith_inv hG₀ hV₀ hℓ₀ (hv_pos j hj.le) hk_real (hp j hj)
  rw [hEq j hj]
  exact ⟨lsfInvAny_of_with (lsfInvWith_mono_K hinv hKσ), hsp.1, hsp.2.1, hsp.2.2.2.1,
    hsp.2.2.2.2.1, hsp.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- A fitting initializer gives the constants of `IsApproxMWUInit` with the MWU bound of the
concrete chain. -/
theorem IsConcreteLSFInit.mwu {lsfInit : LSFInit} {C_lsst : ℝ}
    (h : IsConcreteLSFInit lsfInit C_lsst) :
    ∃ C₀ α K_σ K_ρ : ℝ, IsApproxMWUInit lsfInit C₀ α K_σ K_ρ ∧ 1 ≤ K_ρ ∧
      3 * K_ρ * max K_σ (max (112 * (1 + α) * max 1 C₀) 2240) ≤ 30 * mwuK0 C_lsst :=
  let ⟨C₀, α, K_σ, K_ρ, hA, hKρ, _, hK⟩ := h
  ⟨C₀, α, K_σ, K_ρ, hA, hKρ, hK⟩

/-- The online initializer `initLSFOnline oracle C_lsst` fits `C_lsst`. By
`initLSFOnline_isApproxMWUInit` its constants are `α = 1`, `K_σ = 6272 · max 1 C_lsst =
mwuK0 C_lsst` and `K_ρ = 10`, so `K₀ = mwuK0 C_lsst` and `3 K_ρ K₀ = 30 · mwuK0 C_lsst`. -/
theorem isConcreteLSFInit_initLSFOnline
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst) :
    IsConcreteLSFInit (initLSFOnline oracle C_lsst) C_lsst := by
  refine ⟨C_lsst, 1, 6272 * max 1 C_lsst, 10,
    initLSFOnline_isApproxMWUInit oracle C_lsst hLSST, by norm_num, le_of_eq rfl, ?_⟩
  have h1 : (1 : ℝ) ≤ max 1 C_lsst := le_max_left _ _
  have hK₀ : max (6272 * max 1 C_lsst) (max (112 * (1 + 1) * max 1 C_lsst) 2240) =
      6272 * max 1 C_lsst :=
    max_eq_left (max_le (by linarith) (by linarith))
  rw [hK₀]
  unfold mwuK0
  linarith

/-- `IsConcreteLSFInit` can hold: the online initializer of the oracle of `theorem_2_2` fits the
oracle's constant (`isConcreteLSFInit_initLSFOnline`). -/
theorem exists_isConcreteLSFInit : ∃ (lsfInit : LSFInit) (C_lsst : ℝ),
    IsConcreteLSFInit lsfInit C_lsst := by
  obtain ⟨oracle, C_lsst, hLSST⟩ := theorem_2_2
  exact ⟨initLSFOnline oracle C_lsst, C_lsst, isConcreteLSFInit_initLSFOnline hLSST⟩

/-- For a valid initializer at `(k, j)` and stretch constant `mwuK0 C_lsst`, a valid graph `G`
with lengths in `[exp (-A), exp B]` (`0 ≤ A`, `0 ≤ B`), and
`mwuK0 C_lsst * k * log^6(G.n + 2) ≤ σ_cap` (`2 ≤ σ_cap`), every component `C` has at most
`⌈(A + B + log σ_cap) / log 2⌉ + 2` active buckets in `initBundleTreeWith`. The proof is that of
`initBundleTree_bucket_bound`: each core length is the stretch times the length, and the stretch
lies in `[1, σ_cap]` (Lemma 5.4 for the initial LSF, through `compLSFInv_initWith` and
`CompLSFInv.to_Holds`). -/
theorem initBundleTreeWith_bucket_bound
    (lsfInit : LSFInit) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {j : ℕ} (hValid : IsValidLSFInitFor lsfInit C_lsst k j)
    {G : MGraph} (hG : G.IsValid) {ℓ : ℕ → ℝ} {A B σ_cap : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hσ_ge : 2 ≤ σ_cap)
    (hσ : mwuK0 C_lsst * (k : ℝ) * (Real.log ((G.n : ℝ) + 2)) ^ 6 ≤ σ_cap)
    (hℓ : ∀ e ∈ G.E, Real.exp (-A) ≤ ℓ e ∧ ℓ e ≤ Real.exp B)
    (ord : ℕ → List End) (C : Finset ℕ) (hC : C ∈ components G) :
    ((initBundleTreeWith lsfInit L sparsify k M N G ℓ ord j).activeBuckets C).card ≤
      Nat.ceil ((A + B + Real.log σ_cap) / Real.log 2) + 2 := by
  classical
  rw [initBundleTreeWith_activeBuckets_apply]
  set cs₀ := initCompLSFWith lsfInit G ℓ k j
  set C₀ := coreGraph G cs₀.lsf
  by_cases hV : G.V.Nonempty
  · have hℓ_pos : ∀ e ∈ G.E, 0 < ℓ e := fun e he => lt_of_lt_of_le (Real.exp_pos _) (hℓ e he).1
    have hInv := compLSFInv_initWith hValid hG hV hℓ_pos hk
    have hHolds : cs₀.lsf.Holds G ℓ (mwuK0 C_lsst * (k : ℝ) * (Real.log ((G.n : ℝ) + 2)) ^ 6) :=
      hInv.to_Holds (ℓ := ℓ) hℓ_pos (fun _ _ _ _ => rfl)
    have hσ_pos : 0 < σ_cap := by linarith
    have hB2 : 0 ≤ B + Real.log σ_cap := add_nonneg hB (Real.log_nonneg (by linarith))
    have hsub := bucketOf_image_card_le_of_bounds (A := A) (B := B + Real.log σ_cap) hA hB2
      (Eset := C₀.E.filter fun e => C₀.tail e ∈ C)
      (f := fun e => coreLen cs₀.lsf (safeLen G ℓ) e) ?_
    · rwa [show A + (B + Real.log σ_cap) = A + B + Real.log σ_cap by ring] at hsub
    intro e he
    have heCore : e ∈ C₀.E := (Finset.mem_filter.mp he).1
    have heG : e ∈ G.E := (Finset.mem_sdiff.mp heCore).1
    have hsafe : safeLen G ℓ e = ℓ e := by simp [safeLen, heG]
    have hℓ_nn : ∀ f ∈ G.E, 0 ≤ ℓ f := fun f hf => (hℓ_pos f hf).le
    have hw1 : 1 ≤ cs₀.lsf.wstr e :=
      le_trans (one_le_stretch hHolds.2.1.2.2.2.2 hℓ_nn heG) (hHolds.2.2.2 e heG).1
    have hw_le : cs₀.lsf.wstr e ≤ σ_cap := le_trans (hHolds.2.2.2 e heG).2 hσ
    have hℓe := hℓ e heG
    have hℓe_nn : 0 ≤ ℓ e := (hℓ_pos e heG).le
    refine ⟨?_, ?_⟩
    · change Real.exp (-A) ≤ cs₀.lsf.wstr e * safeLen G ℓ e
      rw [hsafe]
      calc Real.exp (-A) = 1 * Real.exp (-A) := by ring
        _ ≤ 1 * ℓ e := mul_le_mul_of_nonneg_left hℓe.1 zero_le_one
        _ ≤ cs₀.lsf.wstr e * ℓ e := mul_le_mul_of_nonneg_right hw1 hℓe_nn
    · change cs₀.lsf.wstr e * safeLen G ℓ e ≤ Real.exp (B + Real.log σ_cap)
      rw [hsafe, Real.exp_add, Real.exp_log hσ_pos]
      calc cs₀.lsf.wstr e * ℓ e ≤ σ_cap * Real.exp B :=
            mul_le_mul hw_le hℓe.2 hℓe_nn hσ_pos.le
        _ = Real.exp B * σ_cap := by ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hV
    exfalso
    simp [components, hV] at hC

end ConcreteLSFInit

end MinCostFlow.Chain.Ordered

end
