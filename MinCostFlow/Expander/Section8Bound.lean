module

public import MinCostFlow.Expander.Section8Asymptotics
public import MinCostFlow.Expander.Section8Static
public import MinCostFlow.DynSpanner.Complexity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dynamic Spanner Exponential Absorption for Chosen `L` (`Theorem 8.2`)

Combines `DynSpanner.theorem_8_2` (`MinCostFlow/DynSpanner/Complexity.lean`) with the static
sparsifier bounds of `Section8Static.lean` and the asymptotic lemmas of `Section8Asymptotics.lean`
at depth `L = chosenL M` to bound all nine quantities of Theorem 8.2 (page 39) by
`exp(C_dyn * log(M + 2) ^ (23 / 24))`.
-/

namespace MinCostFlow.Expander

public section

noncomputable section

/-- Exponential absorption for `DynSpanner.theorem_8_2` at `L = chosenL M` when
`mMax ≤ M` and `(G₀.n + splitBound : ℝ) ≤ C_n * (M + 2)^{r_n}` (`1 ≤ C_n, 1 ≤ r_n`), for
parameters whose runtime constant grows at most like `K_t · exp(C_t · log(mMax + 2)^{23/24})`. -/
theorem theorem_8_2_absorbed_at_of_le
    {sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
    {params : ℕ → DynSpanner.SparsifyParams}
    {C_γ K_s K_t C_t C_n r_n : ℝ}
    (hCγ : 0 < C_γ) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t) (hCt : 0 ≤ C_t) (hCn : 1 ≤ C_n)
    (hrn : 1 ≤ r_n)
    (hSpecAll : ∀ mMax : ℕ,
      (params mMax).K_s = K_s ∧ (params mMax).p_s = 1 ∧
      (params mMax).K_t ≤ K_t * Real.exp (C_t * Real.log ((mMax : ℝ) + 2) ^ (23 / 24 : ℝ)) ∧
      (params mMax).p_t = 1 ∧
      (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      DynSpanner.SparsifySpec mMax (params mMax) sparsify) :
    let C_dyn : ℝ := 2100 + 2 * K_t + 200 * K_s + 200 * C_γ + 4000 * C_n + 250 * r_n + 4 * C_t
    0 < C_dyn ∧
    ∀ {G₀ : MGraph} {mMax M splitBound : ℕ} {Us : List (List Update)},
      G₀.IsValid → G₀.m ≤ mMax → mMax ≤ M →
      ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n →
      G₀.BatchIsValid Us.flatten →
      (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
      DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
      let L := chosenL M
      let nMax := G₀.n + splitBound
      let q := DynSpanner.phaseBase nMax L
      let initOut := DynSpanner.init G₀ L q sparsify
      let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
      let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
      let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
      let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
        | some U => ((st t').G.batchEnc U : ℝ)
        | none => 0
      let B := Real.exp (C_dyn * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))
      ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
      ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
      (∀ t ≤ Us.length,
        (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
        (st t).G.IsSubgraph (st t).H ∧
        ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
        Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
        (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
        Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
          B * (G₀.maxDeg : ℝ)) ∧
      (∀ t < Us.length, ∀ U, Us[t]? = some U →
        res t = DynSpanner.update
            (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten (DynSpanner.batchPrefixLen Us t))
            U sparsify ∧
        (res t).state = st (t + 1) ∧
        (st t).H.BatchIsValid (res t).UH ∧
        (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
        (res t).D ⊆ (st (t + 1)).H.E ∧
        (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
          eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
          eH ∉ (res t).D →
          eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
      (∀ t ≤ Us.length,
        (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
          B * ((G₀.n : ℝ) + batchTotal t)) ∧
        (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
          B * ((G₀.maxDeg : ℝ) + 1) * encTotal t)) := by
  intro C_dyn
  refine ⟨by positivity, ?_⟩
  intro G₀ mMax M splitBound Us hVG₀ hGm₀ hmM hnCap hBV hds hSplits L nMax q initOut st res
    batchTotal encTotal B
  set P := params mMax
  obtain ⟨hPKs, hPps, hPKt, hPpt, hγℓ_m, hγc_m, hSpec⟩ := hSpecAll mMax
  have h82 := DynSpanner.theorem_8_2 hVG₀ (one_le_chosenL M) hGm₀ hSpec hBV hds hSplits
  dsimp only at h82
  rcases h82 with ⟨hInitM, hInitC, hStage, hStep, hCum⟩
  have hM2_pos : 0 < Real.log ((M : ℝ) + 2) := by linarith only [half_le_log_add_two_nat M]
  have hm2_pos : 0 < Real.log ((mMax : ℝ) + 2) := by linarith only [half_le_log_add_two_nat mMax]
  have hlog_mono : Real.log ((mMax : ℝ) + 2) ≤ Real.log ((M : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    have : (mMax : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    linarith only [this]
  have hrpow78_mono : Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
      Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) :=
    Real.rpow_le_rpow hm2_pos.le hlog_mono (by norm_num)
  have hγℓ_M : P.γ_ℓ ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
    le_trans hγℓ_m (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrpow78_mono hCγ.le))
  have hγc_M : P.γ_c ≤ Real.exp (C_γ * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
    le_trans hγc_m (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrpow78_mono hCγ.le))
  have hγℓ_nn : 0 ≤ P.γ_ℓ := by linarith only [P.hγ_ℓ]
  have hγc_nn : 0 ≤ P.γ_c := by linarith only [P.hγ_c]
  obtain ⟨hγℓ_23, h3L_γ, hvcong_pow, hEL_pow⟩ :=
    exp_gamma_pow_L_bounds hCγ hγℓ_nn hγc_nn M hγℓ_M hγc_M
  let C_Λ : ℝ := 4 * C_n + r_n + 2
  let C_Λexp : ℝ := 2 * C_Λ + 3
  let C_B0 : ℝ := 2 * K_s + 2 * C_γ + C_Λexp
  let C_stage : ℝ := 12 + C_B0
  let C_root : ℝ := 2 * C_n + r_n
  let D_log : ℝ := 2 * C_stage + 64 * C_n + r_n
  have hCΛ_nn : 0 ≤ C_Λ := by positivity
  have hΛs_le_mul : 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) ≤
      C_Λ * Real.log ((M : ℝ) + 2) :=
    one_add_log_sum_le hCn hrn (le_trans hGm₀ hmM) hnCap
  have hΛs_exp : 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) ≤
      Real.exp (C_Λexp * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    have hC_exp := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) hCΛ_nn
      (by norm_num) (by norm_num) M
    have hlog_exp := log_add_two_le_exp_rpow (a := (23 / 24 : ℝ))
      (by norm_num) (by norm_num) M
    calc 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)
        ≤ C_Λ * Real.log ((M : ℝ) + 2) := hΛs_le_mul
      _ ≤ Real.exp (2 * C_Λ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (3 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
          mul_le_mul hC_exp hlog_exp hM2_pos.le (Real.exp_pos _).le
      _ = Real.exp (C_Λexp * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add]; dsimp only [C_Λexp]; ring_nf
  have hΛ0_le : (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s ≤
      1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    rw [hPps, pow_one]
    have hGn_le : (G₀.n : ℝ) ≤ (nMax : ℝ) := by dsimp only [nMax]; push_cast; linarith
    have hgpos : 0 < (G₀.n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) G₀.n, Nat.cast_nonneg (α := ℝ) G₀.m]
    linarith only [Real.log_le_log hgpos (by linarith only [hGn_le] :
      (G₀.n : ℝ) + (G₀.m : ℝ) + 2 ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2)]
  have hΛt_le : (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t ≤
      1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    rw [hPpt, pow_one]
    have ha_le : ((DynSpanner.activeSubgraph G₀).n : ℝ) ≤ (nMax : ℝ) := by
      have h1 : (DynSpanner.activeSubgraph G₀).n ≤ G₀.n := DynSpanner.activeSubgraph_n_le G₀
      have h2 : (DynSpanner.activeSubgraph G₀).n ≤ nMax := le_trans h1 (Nat.le_add_right _ _)
      exact_mod_cast h2
    have hapos : 0 < ((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) (DynSpanner.activeSubgraph G₀).n,
        Nat.cast_nonneg (α := ℝ) G₀.m]
    linarith only [Real.log_le_log hapos (by linarith only [ha_le] :
      ((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2 ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2)]
  have hΛs_eq : (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s =
      1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    rw [hPps, pow_one]
  have hΛ_eq : (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P.p_s P.p_t) =
      1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    rw [hPps, hPpt, max_self, pow_one]
  have hΛs_nn : 0 ≤ 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    have h1 : (1 : ℝ) ≤ (nMax : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]
    linarith only [Real.log_nonneg h1]
  have hΛ0_nn : 0 ≤ (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := by
    have h1 : (1 : ℝ) ≤ (G₀.n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) G₀.n, Nat.cast_nonneg (α := ℝ) G₀.m]
    exact pow_nonneg (by linarith only [Real.log_nonneg h1]) _
  have hΛt_nn :
      0 ≤ (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t := by
    have h1 : (1 : ℝ) ≤ ((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2 := by
      linarith only [Nat.cast_nonneg (α := ℝ) (DynSpanner.activeSubgraph G₀).n,
        Nat.cast_nonneg (α := ℝ) G₀.m]
    exact pow_nonneg (by linarith only [Real.log_nonneg h1]) _
  have hPKs_nn : 0 ≤ P.K_s := P.hK_s
  have hPKt_nn : 0 ≤ P.K_t := P.hK_t
  have hKs_exp : K_s ≤ Real.exp (2 * K_s * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
    nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) hKs (by norm_num) (by norm_num) M
  have hKt_exp0 : K_t ≤ Real.exp (2 * K_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
    nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) hKt (by norm_num) (by norm_num) M
  have hE_M : Real.exp (C_t * Real.log ((mMax : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤
      Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm2_pos.le hlog_mono (by norm_num)) hCt
  have hE1 : (1 : ℝ) ≤ Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
    Real.one_le_exp (mul_nonneg hCt (Real.rpow_nonneg hM2_pos.le _))
  have hKtE : P.K_t ≤ K_t * Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
    le_trans hPKt (mul_le_mul_of_nonneg_left hE_M hKt)
  have hKt_exp : P.K_t ≤ Real.exp ((2 * K_t + C_t) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    calc P.K_t ≤ K_t * Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := hKtE
      _ ≤ Real.exp (2 * K_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
          mul_le_mul_of_nonneg_right hKt_exp0 (Real.exp_pos _).le
      _ = Real.exp ((2 * K_t + C_t) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add]; ring_nf
  have hB0_exp : P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
      Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    rw [hPKs]
    calc K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
        ≤ Real.exp (2 * K_s * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (2 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (C_Λexp * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          have h12 := mul_le_mul hKs_exp hγℓ_23 hγℓ_nn (Real.exp_pos _).le
          exact mul_le_mul h12 hΛs_exp hΛs_nn (by positivity)
      _ = Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; dsimp only [C_B0]; ring_nf
  have hB0_nn : 0 ≤ P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) := by positivity
  have hStage_exp : ((L : ℝ) + 1) * P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
      Real.exp (C_stage * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
    calc ((L : ℝ) + 1) * P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
        = ((L : ℝ) + 1) * (P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) := by
          ring
      _ ≤ Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
          mul_le_mul (chosenL_add_one_le_exp M) hB0_exp hB0_nn (Real.exp_pos _).le
      _ = Real.exp (C_stage * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [← Real.exp_add]; dsimp only [C_stage]; ring_nf
  have hH0_bd : (initOut.state.H.m : ℝ) ≤
      Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * (G₀.n : ℝ) := by
    calc (initOut.state.H.m : ℝ)
        ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ *
            (1 + Real.log ((G₀.n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_s := hInitM
      _ ≤ P.K_s * (G₀.n : ℝ) * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) := by
          exact mul_le_mul_of_nonneg_left hΛ0_le (mul_nonneg (mul_nonneg hPKs_nn (Nat.cast_nonneg _)) hγℓ_nn)
      _ = (P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * (G₀.n : ℝ) := by ring
      _ ≤ Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * (G₀.n : ℝ) :=
          mul_le_mul_of_nonneg_right hB0_exp (Nat.cast_nonneg _)
  have hB0_le_dyn : C_B0 ≤ C_dyn := by
    dsimp only [C_B0, C_Λexp, C_Λ, C_dyn]
    linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
  have hStage_le_dyn : C_stage ≤ C_dyn := by
    dsimp only [C_stage, C_B0, C_Λexp, C_Λ, C_dyn]
    linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
  have hInitM_final : (initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ) :=
    le_trans hH0_bd (mul_le_mul_of_nonneg_right (rpow_23_24_exp_mono hB0_le_dyn M) (Nat.cast_nonneg _))
  have hInitC_final : (initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1) := by
    have hc1 : P.K_t * ((DynSpanner.activeSubgraph G₀).n : ℝ) *
          (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t ≤
        (P.K_t * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * (G₀.n : ℝ) := by
      have ha_le : ((DynSpanner.activeSubgraph G₀).n : ℝ) ≤ (G₀.n : ℝ) := by
        exact_mod_cast DynSpanner.activeSubgraph_n_le G₀
      calc P.K_t * ((DynSpanner.activeSubgraph G₀).n : ℝ) *
            (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t
          ≤ (P.K_t * (G₀.n : ℝ)) * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) := by
            have hKprod : P.K_t * ((DynSpanner.activeSubgraph G₀).n : ℝ) ≤ P.K_t * (G₀.n : ℝ) :=
              mul_le_mul_of_nonneg_left ha_le hPKt_nn
            exact mul_le_mul hKprod hΛt_le hΛt_nn (mul_nonneg hPKt_nn (Nat.cast_nonneg _))
        _ = (P.K_t * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * (G₀.n : ℝ) := by
            ring
    have hc2 : P.K_t * ((G₀.m : ℝ) * P.γ_ℓ ^ 2) *
          (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t ≤
        (P.K_t * P.γ_ℓ ^ 2 * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * (G₀.m : ℝ) := by
      calc P.K_t * ((G₀.m : ℝ) * P.γ_ℓ ^ 2) *
            (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t
          ≤ P.K_t * ((G₀.m : ℝ) * P.γ_ℓ ^ 2) * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hΛt_le
              (mul_nonneg hPKt_nn (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
        _ = (P.K_t * P.γ_ℓ ^ 2 * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * (G₀.m : ℝ) := by
            ring
    let C_ic : ℝ := 2 * K_t + C_t + 4 * C_γ + C_Λexp + C_B0 + 12
    have hic_le_dyn : C_ic + 12 ≤ C_dyn := by
      dsimp only [C_ic, C_B0, C_Λexp, C_Λ, C_dyn]
      linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
    have h6_exp : (6 : ℝ) ≤ Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      have h := nonneg_const_le_exp_rpow (K := 6) (a := (23 / 24 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) M
      norm_num at h; exact h
    have h3_exp : (3 : ℝ) ≤ Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      have h1 := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) (by norm_num : (0 : ℝ) ≤ 3)
        (by norm_num) (by norm_num) M
      refine le_trans h1 (rpow_23_24_exp_mono ?_ M)
      dsimp only [C_ic, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
    have ht1 : P.K_t * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
        Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      calc P.K_t * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
          ≤ Real.exp ((2 * K_t + C_t) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
              Real.exp (C_Λexp * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
            mul_le_mul hKt_exp hΛs_exp hΛs_nn (Real.exp_pos _).le
        _ = Real.exp ((2 * K_t + C_t + C_Λexp) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            apply rpow_23_24_exp_mono
            dsimp only [C_ic, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
    have ht2 : P.K_t * P.γ_ℓ ^ 2 * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
        Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      have hγℓ_sq : P.γ_ℓ ^ 2 ≤ Real.exp (4 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        calc P.γ_ℓ ^ 2 ≤ Real.exp (2 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) ^ 2 :=
              pow_le_pow_left₀ hγℓ_nn hγℓ_23 2
          _ = Real.exp (4 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [sq, ← Real.exp_add]; ring_nf
      calc P.K_t * P.γ_ℓ ^ 2 * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
          ≤ Real.exp ((2 * K_t + C_t) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
              Real.exp (4 * C_γ * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
              Real.exp (C_Λexp * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            have h12 := mul_le_mul hKt_exp hγℓ_sq (sq_nonneg _) (Real.exp_pos _).le
            exact mul_le_mul h12 hΛs_exp hΛs_nn (by positivity)
        _ = Real.exp ((2 * K_t + C_t + 4 * C_γ + C_Λexp) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        _ ≤ Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            apply rpow_23_24_exp_mono
            dsimp only [C_ic, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
    have ht3 : Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤
        Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      have hCΛexp_nn : 0 ≤ C_Λexp := by dsimp only [C_Λexp, C_Λ]; positivity
      apply rpow_23_24_exp_mono; dsimp only [C_ic]; linarith only [hKt, hCt, hCγ.le, hCΛexp_nn]
    have ht4 : P.γ_ℓ ≤ Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      refine le_trans hγℓ_23 (rpow_23_24_exp_mono ?_ M)
      dsimp only [C_ic, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
    have ht5 : (L : ℝ) + 1 ≤ Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      refine le_trans (chosenL_add_one_le_exp M) (rpow_23_24_exp_mono ?_ M)
      dsimp only [C_ic, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
    let a1 := P.K_t * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
    let a2 := P.K_t * P.γ_ℓ ^ 2 * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
    let a3 := Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))
    have h1 : (initOut.cost : ℝ) ≤
        a1 * (G₀.n : ℝ) + a2 * (G₀.m : ℝ) + (G₀.n : ℝ) + (G₀.m : ℝ) +
          a3 * (G₀.n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + ((L : ℝ) + 1) := by
      calc (initOut.cost : ℝ)
          ≤ P.K_t * (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ ^ 2) *
              (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
              (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ +
              (L : ℝ) + 1 := hInitC
        _ = P.K_t * ((DynSpanner.activeSubgraph G₀).n : ℝ) *
              (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
            P.K_t * ((G₀.m : ℝ) * P.γ_ℓ ^ 2) *
              (1 + Real.log (((DynSpanner.activeSubgraph G₀).n : ℝ) + (G₀.m : ℝ) + 2)) ^ P.p_t +
            (G₀.n : ℝ) + (G₀.m : ℝ) + (initOut.state.H.m : ℝ) + (G₀.m : ℝ) * P.γ_ℓ +
            ((L : ℝ) + 1) := by ring
        _ ≤ a1 * (G₀.n : ℝ) + a2 * (G₀.m : ℝ) + (G₀.n : ℝ) + (G₀.m : ℝ) +
            a3 * (G₀.n : ℝ) + (G₀.m : ℝ) * P.γ_ℓ + ((L : ℝ) + 1) := by
            linarith only [hc1, hc2, hH0_bd]
    have hsplit_sum : (initOut.cost : ℝ) ≤
        (a1 + a2 + a3 + P.γ_ℓ + ((L : ℝ) + 1) + 3) * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1) := by
      have ha1 : 0 ≤ a1 := by dsimp only [a1]; positivity
      have ha2 : 0 ≤ a2 := by dsimp only [a2]; positivity
      have ha3 : 0 ≤ a3 := (Real.exp_pos _).le
      have hGn_nn : 0 ≤ (G₀.n : ℝ) := Nat.cast_nonneg _
      have hGm_nn : 0 ≤ (G₀.m : ℝ) := Nat.cast_nonneg _
      have hL_nn : 0 ≤ (L : ℝ) + 1 := by positivity
      nlinarith only [h1, ha1, ha2, ha3, hγℓ_nn, hL_nn, hGn_nn, hGm_nn]
    have hcoeff : a1 + a2 + a3 + P.γ_ℓ + ((L : ℝ) + 1) + 3 ≤ B := by
      calc a1 + a2 + a3 + P.γ_ℓ + ((L : ℝ) + 1) + 3
          ≤ 6 * Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            dsimp only [a1, a2, a3]; linarith only [ht1, ht2, ht3, ht4, ht5, h3_exp]
        _ ≤ Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
              Real.exp (C_ic * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
            mul_le_mul_of_nonneg_right h6_exp (Real.exp_pos _).le
        _ = Real.exp ((C_ic + 12) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ B := rpow_23_24_exp_mono hic_le_dyn M
    exact le_trans hsplit_sum (mul_le_mul_of_nonneg_right hcoeff (by positivity))
  have hStage_final : ∀ t ≤ Us.length,
      (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
      (st t).G.IsSubgraph (st t).H ∧
      ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
      Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
      (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
      Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        B * (G₀.maxDeg : ℝ) := by
    intro t ht
    obtain ⟨hG_eq, hSub, hHm, hEmb, hLen, hVcong⟩ := hStage t ht
    have hHm' : ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) := by
      have hHm1 : ((st t).H.m : ℝ) ≤ (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) := by
        simpa only [hPps, pow_one] using hHm
      calc ((st t).H.m : ℝ)
          ≤ ((L : ℝ) + 1) * P.K_s * P.γ_ℓ *
              (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) * (nMax : ℝ) := by
            linarith only [hHm1]
        _ ≤ B * (nMax : ℝ) :=
            mul_le_mul_of_nonneg_right (le_trans hStage_exp (rpow_23_24_exp_mono hStage_le_dyn M))
              (Nat.cast_nonneg _)
    have hLen' : (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B := by
      have hc : 36 + 12 * C_γ ≤ C_dyn := by
        dsimp only [C_dyn]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
      exact le_trans hLen (le_trans h3L_γ (rpow_23_24_exp_mono hc M))
    have hVcong' : Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
        B * (G₀.maxDeg : ℝ) := by
      have hc : 108 + 21 * C_γ ≤ C_dyn := by
        dsimp only [C_dyn]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
      exact le_trans hVcong (mul_le_mul_of_nonneg_right
        (le_trans hvcong_pow (rpow_23_24_exp_mono hc M)) (Nat.cast_nonneg _))
    exact ⟨hG_eq, hSub, hHm', hEmb, hLen', hVcong'⟩
  have hCum_final : ∀ t ≤ Us.length,
      (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
        B * ((G₀.n : ℝ) + batchTotal t)) ∧
      (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
      (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
        B * ((G₀.maxDeg : ℝ) + 1) * encTotal t) := by
    intro t ht
    obtain ⟨hUH_raw, hEncH_raw, hD_raw, hCost_raw⟩ := hCum t ht
    have hUH : (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) * P.K_s * P.γ_ℓ *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * batchTotal t := by
      simpa only [hPps, pow_one] using hUH_raw
    have hEncH : (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ)) ≤
        4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
        (2 + 2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4)) * (L : ℝ) *
          ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) * P.K_s * P.γ_ℓ *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) * batchTotal t := by
      simpa only [hPps, pow_one] using hEncH_raw
    have hD : (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ)) ≤
        6 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) * P.K_s * P.γ_ℓ *
          ((3 : ℝ) ^ L * P.γ_ℓ ^ (L + 1) + 1) *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) * batchTotal t := by
      simpa only [hPps, pow_one] using hD_raw
    have hCost : (∑ t' ∈ Finset.range t, ((res t').cost : ℝ)) ≤
        90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) * (P.K_t + P.K_s + 1) *
          ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
            P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
          ((G₀.maxDeg : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) * encTotal t := by
      have hmax : max (params mMax).p_s (params mMax).p_t = 1 := by
        rw [hPps, hPpt, max_self]
      rw [hmax, pow_one] at hCost_raw
      exact hCost_raw
    have hnRoot := nRoot_le_exp hCn (by linarith only [hrn]) hnCap
    have hL_exp := chosenL_le_exp M
    have hCore_exp : (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
          P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
        Real.exp ((6 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
      have h1 : (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            (P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) ≤
          Real.exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (C_root * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
            Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h12 := mul_le_mul hL_exp hnRoot (by positivity) (by positivity)
        exact mul_le_mul h12 hB0_exp (by positivity) (by positivity)
      calc (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))
          = (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
              (P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) := by ring
        _ ≤ _ := h1
        _ = Real.exp ((6 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
            rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hUH_bd : (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ)) ≤ B * batchTotal t := by
      have h12_exp : (12 : ℝ) ≤ Real.exp (24 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h := nonneg_const_le_exp_rpow (K := 12) (a := (23 / 24 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) M
        norm_num at h; exact h
      have hmain : 12 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
          Real.exp ((30 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        calc _ = 12 * ((L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
              P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) := by ring
          _ ≤ Real.exp (24 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((6 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
              mul_le_mul h12_exp hCore_exp (by positivity) (by positivity)
          _ = Real.exp ((30 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [← Real.exp_add]; ring_nf
      have h2_le : (2 : ℝ) ≤
          Real.exp ((30 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num) (by norm_num) M
        refine le_trans h (rpow_23_24_exp_mono ?_ M)
        dsimp only [C_root, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
      have h2_exp : (2 : ℝ) ≤ Real.exp (4 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h := nonneg_const_le_exp_rpow (K := 2) (a := (23 / 24 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) M
        norm_num at h; exact h
      have hc : 34 + C_root + C_B0 ≤ C_dyn := by
        dsimp only [C_root, C_B0, C_Λexp, C_Λ, C_dyn]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
      have hcoeff : 2 + 12 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤ B := by
        calc _ ≤ 2 * Real.exp ((30 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
                linarith only [h2_le, hmain]
          _ ≤ Real.exp (4 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((30 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
              mul_le_mul_of_nonneg_right h2_exp (Real.exp_pos _).le
          _ = Real.exp ((34 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ B := rpow_23_24_exp_mono hc M
      exact le_trans hUH (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _))
    have hMH_bd : (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
        Real.exp (C_stage * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((nMax : ℝ) + 2) := by
      have h1 : (L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
            (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) =
          (((L : ℝ) + 1) * P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) *
            (nMax : ℝ) := by ring
      rw [h1]
      have hn_le2 : (nMax : ℝ) ≤ (nMax : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) nMax]
      exact mul_le_mul hStage_exp hn_le2 (Nat.cast_nonneg _) (Real.exp_pos _).le
    have hH0_bd2 : (initOut.state.H.m : ℝ) ≤
        Real.exp (C_stage * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) * ((nMax : ℝ) + 2) := by
      have hGn_le2 : (G₀.n : ℝ) ≤ (nMax : ℝ) + 2 := by
        dsimp only [nMax]; push_cast; linarith only [Nat.cast_nonneg (α := ℝ) G₀.n,
          Nat.cast_nonneg (α := ℝ) splitBound]
      have hB0_le_st : Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤
          Real.exp (C_stage * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
        rpow_23_24_exp_mono (by dsimp only [C_stage]; linarith only) M
      exact le_trans hH0_bd (mul_le_mul hB0_le_st hGn_le2 (Nat.cast_nonneg _) (Real.exp_pos _).le)
    have hCstage_nn : 0 ≤ C_stage := by
      dsimp only [C_stage, C_B0, C_Λexp, C_Λ]; positivity
    have hlog_MH : Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) * P.γ_ℓ *
          (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) ≤
        D_log * Real.log ((M : ℝ) + 2) := by
      simpa only [D_log] using log_linear_le_mul_log hCstage_nn hCn hrn (by positivity) hMH_bd hnCap
    have hlog_H0 : Real.log (2 * (initOut.state.H.m : ℝ) + 2) ≤ D_log * Real.log ((M : ℝ) + 2) := by
      have h1 : 2 * (initOut.state.H.m : ℝ) + 2 ≤ 6 * (initOut.state.H.m : ℝ) + 10 := by
        linarith only [Nat.cast_nonneg (α := ℝ) initOut.state.H.m]
      have h2 := Real.log_le_log (by positivity) h1
      have h3 := log_linear_le_mul_log hCstage_nn hCn hrn (Nat.cast_nonneg _) hH0_bd2 hnCap
      exact le_trans h2 (by simpa only [D_log] using h3)
    have hEncH_bd : (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ)) ≤
        B * ((G₀.n : ℝ) + batchTotal t) := by
      have hD_nn : 0 ≤ D_log := by dsimp only [D_log, C_stage, C_B0, C_Λexp, C_Λ]; positivity
      have hlog_exp := log_add_two_le_exp_rpow (a := (23 / 24 : ℝ)) (by norm_num) (by norm_num) M
      have hterm1 : 4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) ≤
          B * (G₀.n : ℝ) := by
        have h4D : 0 ≤ 4 * D_log := by positivity
        have h4D_exp := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) h4D
          (by norm_num) (by norm_num) M
        have hc : 2 * (4 * D_log) + 3 + C_B0 ≤ C_dyn := by
          dsimp only [D_log, C_stage, C_B0, C_Λexp, C_Λ, C_dyn]
          linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
        have hlog0_nn : 0 ≤ Real.log (2 * (initOut.state.H.m : ℝ) + 2) := by
          have : (1 : ℝ) ≤ 2 * (initOut.state.H.m : ℝ) + 2 := by
            linarith only [Nat.cast_nonneg (α := ℝ) initOut.state.H.m]
          exact Real.log_nonneg this
        have hmul1 : 4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) ≤
            (4 * D_log * Real.log ((M : ℝ) + 2) *
              Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) * (G₀.n : ℝ) := by
          have h4Hm := mul_le_mul_of_nonneg_left hH0_bd (by norm_num : (0 : ℝ) ≤ 4)
          have h12 := mul_le_mul h4Hm hlog_H0 hlog0_nn (by positivity)
          exact le_trans h12 (le_of_eq (by ring))
        have hcoeff1 : 4 * D_log * Real.log ((M : ℝ) + 2) *
              Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) ≤ B := by
          calc _ ≤ Real.exp (2 * (4 * D_log) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                  Real.exp (3 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                  Real.exp (C_B0 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
                have h12 := mul_le_mul h4D_exp hlog_exp hM2_pos.le (by positivity)
                exact mul_le_mul h12 (le_refl _) (Real.exp_pos _).le (by positivity)
            _ = Real.exp ((2 * (4 * D_log) + 3 + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
                rw [← Real.exp_add, ← Real.exp_add]; ring_nf
            _ ≤ B := rpow_23_24_exp_mono hc M
        exact le_trans hmul1 (mul_le_mul_of_nonneg_right hcoeff1 (Nat.cast_nonneg _))
      have hterm2 : 2 + 2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) *
              P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4)) *
            (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤ B := by
        have h1_le_2L : (1 : ℝ) ≤ 2 * Real.log ((M : ℝ) + 2) := by
          linarith only [half_le_log_add_two_nat M]
        have hdeg_lin : 2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) *
              P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4)) ≤
            (24 * D_log + 72) * Real.log ((M : ℝ) + 2) := by
          linarith only [hlog_MH, h1_le_2L]
        have h24_nn : 0 ≤ 24 * D_log + 72 := by positivity
        have h24_exp := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) h24_nn
          (by norm_num) (by norm_num) M
        have hdeg_exp : 2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) *
              P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4)) ≤
            Real.exp ((48 * D_log + 147) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          calc _ ≤ (24 * D_log + 72) * Real.log ((M : ℝ) + 2) := hdeg_lin
            _ ≤ Real.exp (2 * (24 * D_log + 72) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                  Real.exp (3 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
                mul_le_mul h24_exp hlog_exp hM2_pos.le (by positivity)
            _ = Real.exp ((48 * D_log + 147) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
                rw [← Real.exp_add]; ring_nf
        have hprod_exp : 2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) *
              P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4)) *
            (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤
            Real.exp ((48 * D_log + 153 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          calc _ = (2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) *
                    P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4))) *
                  ((L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
                    P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) := by ring
            _ ≤ Real.exp ((48 * D_log + 147) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                  Real.exp ((6 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
                mul_le_mul hdeg_exp hCore_exp (by positivity) (by positivity)
            _ = Real.exp ((48 * D_log + 153 + C_root + C_B0) *
                  Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
                rw [← Real.exp_add]; ring_nf
        have h2_le : (2 : ℝ) ≤
            Real.exp ((48 * D_log + 153 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          have h := nonneg_const_le_exp_rpow (a := (23 / 24 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
            (by norm_num) (by norm_num) M
          refine le_trans h (rpow_23_24_exp_mono ?_ M)
          dsimp only [D_log, C_stage, C_root, C_B0, C_Λexp, C_Λ]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
        have h2_exp : (2 : ℝ) ≤ Real.exp (4 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          have h := nonneg_const_le_exp_rpow (K := 2) (a := (23 / 24 : ℝ))
            (by norm_num) (by norm_num) (by norm_num) M
          norm_num at h; exact h
        have hc : 48 * D_log + 157 + C_root + C_B0 ≤ C_dyn := by
          dsimp only [D_log, C_stage, C_root, C_B0, C_Λexp, C_Λ, C_dyn]
          linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
        calc _ ≤ 2 * Real.exp ((48 * D_log + 153 + C_root + C_B0) *
                Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              linarith only [h2_le, hprod_exp]
          _ ≤ Real.exp (4 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((48 * D_log + 153 + C_root + C_B0) *
                  Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
              mul_le_mul_of_nonneg_right h2_exp (Real.exp_pos _).le
          _ = Real.exp ((48 * D_log + 157 + C_root + C_B0) *
                Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ B := rpow_23_24_exp_mono hc M
      calc (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ))
          ≤ 4 * (initOut.state.H.m : ℝ) * Real.log (2 * (initOut.state.H.m : ℝ) + 2) +
              (2 + 2 * (6 + 3 * (4 * Real.log (6 * ((L + 1 : ℝ) * P.K_s * (nMax : ℝ) *
                    P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) + 10) + 4)) *
                  (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
                  P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) *
                batchTotal t := hEncH
        _ ≤ B * (G₀.n : ℝ) + B * batchTotal t :=
            add_le_add hterm1 (mul_le_mul_of_nonneg_right hterm2 (Nat.cast_nonneg _))
        _ = B * ((G₀.n : ℝ) + batchTotal t) := by ring
    have hD_bd : (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ)) ≤ B * batchTotal t := by
      have h6_exp : (6 : ℝ) ≤ Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h := nonneg_const_le_exp_rpow (K := 6) (a := (23 / 24 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) M
        norm_num at h; exact h
      have h1_le : (1 : ℝ) ≤ Real.exp ((36 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
        Real.one_le_exp (by positivity)
      have h2_exp : (2 : ℝ) ≤ Real.exp (4 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h := nonneg_const_le_exp_rpow (K := 2) (a := (23 / 24 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) M
        norm_num at h; exact h
      have hbr_exp : (3 : ℝ) ^ L * P.γ_ℓ ^ (L + 1) + 1 ≤
          Real.exp ((40 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        calc (3 : ℝ) ^ L * P.γ_ℓ ^ (L + 1) + 1
            ≤ 2 * Real.exp ((36 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              linarith only [h3L_γ, h1_le]
          _ ≤ Real.exp (4 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((36 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
              mul_le_mul_of_nonneg_right h2_exp (Real.exp_pos _).le
          _ = Real.exp ((40 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [← Real.exp_add]; ring_nf
      have hc : 58 + 12 * C_γ + C_root + C_B0 ≤ C_dyn := by
        dsimp only [C_root, C_B0, C_Λexp, C_Λ, C_dyn]
        linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
      have hcoeff : 6 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            P.K_s * P.γ_ℓ * ((3 : ℝ) ^ L * P.γ_ℓ ^ (L + 1) + 1) *
            (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤ B := by
        calc _ = 6 * ((L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
                P.K_s * P.γ_ℓ * (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) *
              ((3 : ℝ) ^ L * P.γ_ℓ ^ (L + 1) + 1) := by ring
          _ ≤ Real.exp (12 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((6 + C_root + C_B0) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((40 + 12 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              have h12 := mul_le_mul h6_exp hCore_exp (by positivity) (by positivity)
              exact mul_le_mul h12 hbr_exp (by positivity) (by positivity)
          _ = Real.exp ((58 + 12 * C_γ + C_root + C_B0) *
                Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add]; ring_nf
          _ ≤ B := rpow_23_24_exp_mono hc M
      exact le_trans hD (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _))
    have hCost_bd : (∑ t' ∈ Finset.range t, ((res t').cost : ℝ)) ≤
        B * ((G₀.maxDeg : ℝ) + 1) * encTotal t := by
      have h90_exp : (90 : ℝ) ≤ Real.exp (180 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h := nonneg_const_le_exp_rpow (K := 90) (a := (23 / 24 : ℝ))
          (by norm_num) (by norm_num) (by norm_num) M
        norm_num at h; exact h
      have hKtKs1_exp : P.K_t + P.K_s + 1 ≤
          Real.exp ((2 * (K_t + K_s + 1) + C_t) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
        have h0 := nonneg_const_le_exp_rpow (K := K_t + K_s + 1) (a := (23 / 24 : ℝ))
          (by positivity) (by norm_num) (by norm_num) M
        have h1 : P.K_t + P.K_s + 1 ≤ (K_t + K_s + 1) *
            Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
          rw [hPKs]; nlinarith only [hKtE, hE1, hKs]
        calc P.K_t + P.K_s + 1 ≤ (K_t + K_s + 1) *
              Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := h1
          _ ≤ Real.exp ((2 * (K_t + K_s + 1)) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
              Real.exp (C_t * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
            mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le
          _ = _ := by rw [← Real.exp_add]; ring_nf
      have h_core_cost : 90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
            (P.K_t + P.K_s + 1) *
            ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
              P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
            (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ≤ B := by
        have hc : 180 + 6 + C_root + (2 * (K_t + K_s + 1) + C_t) + (216 + 57 * C_γ) + C_Λexp ≤
            C_dyn := by
          dsimp only [C_root, C_Λexp, C_Λ, C_dyn]; linarith only [hKs, hKt, hCt, hCγ.le, hCn, hrn]
        calc _ = 90 * ((L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) *
                (P.K_t + P.K_s + 1) *
                ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
                  P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
                (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) := by ring
          _ ≤ Real.exp (180 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                (Real.exp (6 * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                  Real.exp (C_root * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))) *
                Real.exp ((2 * (K_t + K_s + 1) + C_t) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp ((216 + 57 * C_γ) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) *
                Real.exp (C_Λexp * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              have hLnr := mul_le_mul hL_exp hnRoot (by positivity) (by positivity)
              have h12 := mul_le_mul h90_exp hLnr (by positivity) (by positivity)
              have h123 := mul_le_mul h12 hKtKs1_exp (by linarith only [hPKt_nn, hPKs_nn])
                (by positivity)
              have h1234 := mul_le_mul h123 hEL_pow (by positivity) (by positivity)
              exact mul_le_mul h1234 hΛs_exp hΛs_nn (by positivity)
          _ = Real.exp ((180 + 6 + C_root + (2 * (K_t + K_s + 1) + C_t) +
                  (216 + 57 * C_γ) + C_Λexp) * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
                ← Real.exp_add]; ring_nf
          _ ≤ B := rpow_23_24_exp_mono hc M
      have henc_nn : 0 ≤ encTotal t := by
        dsimp only [encTotal]
        refine Finset.sum_nonneg fun t' _ => ?_
        cases Us[t']? <;> positivity
      have hdeg_nn : 0 ≤ (G₀.maxDeg : ℝ) + 1 := by positivity
      calc (∑ t' ∈ Finset.range t, ((res t').cost : ℝ))
          ≤ 90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
              (P.K_t + P.K_s + 1) *
              ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
                P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
              ((G₀.maxDeg : ℝ) + 1) *
              (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) * encTotal t := hCost
        _ = (90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) *
              (P.K_t + P.K_s + 1) *
              ((3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P.γ_c ^ (L + 1) *
                P.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) *
              (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2))) *
              ((G₀.maxDeg : ℝ) + 1) * encTotal t := by ring
        _ ≤ B * ((G₀.maxDeg : ℝ) + 1) * encTotal t :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h_core_cost hdeg_nn) henc_nn
    exact ⟨hUH_bd, hEncH_bd, hD_bd, hCost_bd⟩
  exact ⟨hInitM_final, hInitC_final, hStage_final, hStep, hCum_final⟩


private lemma eight_ninths_loglog_le (L : ℝ) (hL : (1 / 2 : ℝ) ≤ L) :
    L ^ (8 / 9 : ℝ) * Real.log (L + 2) ^ (4 / 3 : ℝ) ≤ 2000 * L ^ (23 / 24 : ℝ) := by
  have hLpos : 0 < L := by linarith
  set u : ℝ := L + 2 with hu
  have hupos : 0 < u := by rw [hu]; linarith
  have hlog_nn : 0 ≤ Real.log u := Real.log_nonneg (by rw [hu]; linarith)
  -- `log u ≤ (96 / 5) · u ^ (5 / 96)`
  have h1 : Real.log u ≤ (96 / 5) * u ^ (5 / 96 : ℝ) := by
    have hp := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hupos (5 / 96 : ℝ))
    rw [Real.log_rpow hupos] at hp
    linarith
  have hupow_nn : 0 ≤ u ^ (5 / 96 : ℝ) := Real.rpow_nonneg hupos.le _
  have h2 : Real.log u ^ (4 / 3 : ℝ) ≤ (96 / 5 : ℝ) ^ (4 / 3 : ℝ) * u ^ (5 / 72 : ℝ) := by
    calc Real.log u ^ (4 / 3 : ℝ) ≤ ((96 / 5) * u ^ (5 / 96 : ℝ)) ^ (4 / 3 : ℝ) :=
          Real.rpow_le_rpow hlog_nn h1 (by norm_num)
      _ = (96 / 5 : ℝ) ^ (4 / 3 : ℝ) * u ^ (5 / 72 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hupow_nn, ← Real.rpow_mul hupos.le]
          norm_num
  have h3 : (96 / 5 : ℝ) ^ (4 / 3 : ℝ) ≤ 400 := by
    calc (96 / 5 : ℝ) ^ (4 / 3 : ℝ) ≤ (96 / 5 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ 400 := by rw [Real.rpow_two]; norm_num
  have h4 : u ^ (5 / 72 : ℝ) ≤ 5 * L ^ (5 / 72 : ℝ) := by
    calc u ^ (5 / 72 : ℝ) ≤ (5 * L) ^ (5 / 72 : ℝ) :=
          Real.rpow_le_rpow hupos.le (by rw [hu]; linarith) (by norm_num)
      _ = (5 : ℝ) ^ (5 / 72 : ℝ) * L ^ (5 / 72 : ℝ) := Real.mul_rpow (by norm_num) hLpos.le
      _ ≤ 5 * L ^ (5 / 72 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
          calc (5 : ℝ) ^ (5 / 72 : ℝ) ≤ (5 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 5 := Real.rpow_one 5
  have hL89_nn : 0 ≤ L ^ (8 / 9 : ℝ) := Real.rpow_nonneg hLpos.le _
  have hsum : L ^ (8 / 9 : ℝ) * L ^ (5 / 72 : ℝ) = L ^ (23 / 24 : ℝ) := by
    rw [← Real.rpow_add hLpos]; norm_num
  have h5 : Real.log u ^ (4 / 3 : ℝ) ≤ 2000 * L ^ (5 / 72 : ℝ) := by
    have h400 : (96 / 5 : ℝ) ^ (4 / 3 : ℝ) * u ^ (5 / 72 : ℝ) ≤ 400 * (5 * L ^ (5 / 72 : ℝ)) :=
      mul_le_mul h3 h4 (Real.rpow_nonneg hupos.le _) (by norm_num)
    linarith
  calc L ^ (8 / 9 : ℝ) * Real.log u ^ (4 / 3 : ℝ) ≤ L ^ (8 / 9 : ℝ) * (2000 * L ^ (5 / 72 : ℝ)) :=
        mul_le_mul_of_nonneg_left h5 hL89_nn
    _ = 2000 * L ^ (23 / 24 : ℝ) := by rw [← hsum]; ring

/-- Exponential absorption for `DynSpanner.theorem_8_2` at `L = chosenL M` for parameters with
a uniform runtime constant `K_t`, the case `C_t = 0` of `theorem_8_2_absorbed_at_of_le`. -/
theorem theorem_8_2_absorbed_at
    {sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
    {params : ℕ → DynSpanner.SparsifyParams}
    {C_γ K_s K_t C_n r_n : ℝ}
    (hCγ : 0 < C_γ) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t) (hCn : 1 ≤ C_n) (hrn : 1 ≤ r_n)
    (hSpecAll : ∀ mMax : ℕ,
      (params mMax).K_s = K_s ∧ (params mMax).p_s = 1 ∧
      (params mMax).K_t = K_t ∧ (params mMax).p_t = 1 ∧
      (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      DynSpanner.SparsifySpec mMax (params mMax) sparsify) :
    let C_dyn : ℝ := 2100 + 2 * K_t + 200 * K_s + 200 * C_γ + 4000 * C_n + 250 * r_n
    0 < C_dyn ∧
    ∀ {G₀ : MGraph} {mMax M splitBound : ℕ} {Us : List (List Update)},
      G₀.IsValid → G₀.m ≤ mMax → mMax ≤ M →
      ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n →
      G₀.BatchIsValid Us.flatten →
      (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
      DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
      let L := chosenL M
      let nMax := G₀.n + splitBound
      let q := DynSpanner.phaseBase nMax L
      let initOut := DynSpanner.init G₀ L q sparsify
      let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
      let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
      let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
      let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
        | some U => ((st t').G.batchEnc U : ℝ)
        | none => 0
      let B := Real.exp (C_dyn * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))
      ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
      ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
      (∀ t ≤ Us.length,
        (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
        (st t).G.IsSubgraph (st t).H ∧
        ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
        Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
        (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
        Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
          B * (G₀.maxDeg : ℝ)) ∧
      (∀ t < Us.length, ∀ U, Us[t]? = some U →
        res t = DynSpanner.update
            (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten (DynSpanner.batchPrefixLen Us t))
            U sparsify ∧
        (res t).state = st (t + 1) ∧
        (st t).H.BatchIsValid (res t).UH ∧
        (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
        (res t).D ⊆ (st (t + 1)).H.E ∧
        (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
          eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
          eH ∉ (res t).D →
          eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
      (∀ t ≤ Us.length,
        (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
          B * ((G₀.n : ℝ) + batchTotal t)) ∧
        (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
          B * ((G₀.maxDeg : ℝ) + 1) * encTotal t)) := by
  have h := theorem_8_2_absorbed_at_of_le (sparsify := sparsify) (params := params) (C_t := 0)
    hCγ hKs hKt le_rfl hCn hrn (fun mMax => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hSpecAll mMax
      exact ⟨h1, h2, by rw [h3, zero_mul, Real.exp_zero, mul_one], h4, h5, h6, h7⟩)
  simpa only [mul_zero, add_zero] using h

/-- Exponential absorption for `DynSpanner.theorem_8_2` at `L = chosenL M` for a static
sparsifier whose runtime carries the factor `γ_t ≤ exp(C_q · log^{8/9}(mMax + 2) ·
log(log(mMax + 2) + 2)^{4/3})` (`DynSpanner.SparsifySpecWithTime`). Since `8/9 < 23/24`, this
factor is absorbed into `exp(C_dyn · log(M + 2)^{23/24})` with a larger constant. -/
theorem theorem_8_2_absorbed_at_with_time
    {sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut}
    {params : ℕ → DynSpanner.SparsifyParams}
    {C_γ K_s K_t C_q C_n r_n : ℝ}
    (hCγ : 0 < C_γ) (hKs : 0 ≤ K_s) (hKt : 0 ≤ K_t) (hCq : 0 ≤ C_q) (hCn : 1 ≤ C_n)
    (hrn : 1 ≤ r_n)
    (hSpecAll : ∀ mMax : ℕ,
      (params mMax).K_s = K_s ∧ (params mMax).p_s = 1 ∧
      (params mMax).K_t = K_t ∧ (params mMax).p_t = 1 ∧
      (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
        Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
      DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) :
    let C_dyn : ℝ := 2100 + 2 * K_t + 200 * K_s + 200 * C_γ + 4000 * C_n + 250 * r_n + 4 * (2000 * C_q)
    0 < C_dyn ∧
    ∀ {G₀ : MGraph} {mMax M splitBound : ℕ} {Us : List (List Update)},
      G₀.IsValid → G₀.m ≤ mMax → mMax ≤ M →
      ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n * ((M : ℝ) + 2) ^ r_n →
      G₀.BatchIsValid Us.flatten →
      (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
      DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
      let L := chosenL M
      let nMax := G₀.n + splitBound
      let q := DynSpanner.phaseBase nMax L
      let initOut := DynSpanner.init G₀ L q sparsify
      let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
      let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
      let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
      let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
        | some U => ((st t').G.batchEnc U : ℝ)
        | none => 0
      let B := Real.exp (C_dyn * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))
      ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
      ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
      (∀ t ≤ Us.length,
        (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
        (st t).G.IsSubgraph (st t).H ∧
        ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
        Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
        (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
        Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
          B * (G₀.maxDeg : ℝ)) ∧
      (∀ t < Us.length, ∀ U, Us[t]? = some U →
        res t = DynSpanner.update
            (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten (DynSpanner.batchPrefixLen Us t))
            U sparsify ∧
        (res t).state = st (t + 1) ∧
        (st t).H.BatchIsValid (res t).UH ∧
        (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
        (res t).D ⊆ (st (t + 1)).H.E ∧
        (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
          eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
          eH ∉ (res t).D →
          eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
      (∀ t ≤ Us.length,
        (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
          B * ((G₀.n : ℝ) + batchTotal t)) ∧
        (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
          B * ((G₀.maxDeg : ℝ) + 1) * encTotal t)) := by
  refine theorem_8_2_absorbed_at_of_le (sparsify := sparsify)
    (params := fun mMax => (params mMax).absorbTime) (C_t := 2000 * C_q)
    hCγ hKs hKt (by positivity) hCn hrn (fun mMax => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hSpecAll mMax
  refine ⟨h1, h2, ?_, h4, h5, h6, DynSpanner.sparsifySpecWithTime_iff_absorb.mp h8⟩
  show (params mMax).K_t * (params mMax).γ_t ≤ _
  rw [h3]
  refine mul_le_mul_of_nonneg_left (le_trans h7 (Real.exp_le_exp.mpr ?_)) hKt
  have hL := eight_ninths_loglog_le (Real.log ((mMax : ℝ) + 2)) (half_le_log_add_two_nat mMax)
  rw [mul_assoc]
  calc C_q * (Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
        Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ))
      ≤ C_q * (2000 * Real.log ((mMax : ℝ) + 2) ^ (23 / 24 : ℝ)) :=
        mul_le_mul_of_nonneg_left hL hCq
    _ = 2000 * C_q * Real.log ((mMax : ℝ) + 2) ^ (23 / 24 : ℝ) := by ring

end

end

end MinCostFlow.Expander
