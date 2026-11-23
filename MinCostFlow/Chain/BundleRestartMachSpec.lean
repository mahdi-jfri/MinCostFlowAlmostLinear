module

public import MinCostFlow.Chain.BundleRestartMachBound
public import MinCostFlow.Chain.BundleRestartFull
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 5.17 for the machine cost

This file proves `sparseCoreBundleRestartToolMachWith_isSpecOrdRestart` (and its `IsApproxMWUInit`
corollaries `sparseCoreBundleRestartToolMachWith_isSpecOrdRestart_of_isApproxMWUInit` and
`toolMachWith_isSpecOrdRestart`, as well as the `initLSFOnline` specialization
`sparseCoreBundleRestartToolMach_isSpecOrdRestart`): the tool with the machine cost `machCost`
meets `IsSpecOrdRestart` with the parameters `bundleCoreParamsMachWith E spanConst`. Items 1, 2,
4, 5, and 6 do not read the cost and agree with `sparseCoreBundleRestartToolWith` by
`SparseCoreBundleNonMachEq` (`sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq`).
The cost items are proved here:
* item 3 (`bundleRestartMachWith_restartCost`): one restart adds `singleBundleRestartMachCost`,
  bounded via `singleBundleRestartMachInner_pre_le` and `bundleLogFactor_le`;
* item 7 (`bundleRestartMachWith_totalCost_le`): the sum over the branches of
  `bundleBranchWith_machCost_restart_le`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

private lemma list_sum_count_eq_length'' (xs : List ℕ) (k : ℕ) (h : ∀ j ∈ xs, j < k) :
    ∑ j ∈ Finset.range k, xs.count j = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x < k := h x List.mem_cons_self
    have hxs : ∀ j ∈ xs, j < k := fun j hj => h j (List.mem_cons_of_mem x hj)
    have hsplit : ∑ j ∈ Finset.range k, (x :: xs).count j =
        ∑ j ∈ Finset.range k, (xs.count j + if j = x then 1 else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjx : j = x
      · subst hjx; simp [List.count_cons_self]
      · simp [List.count_cons_of_ne (Ne.symm hjx), hjx]
    rw [hsplit, Finset.sum_add_distrib, ih hxs]
    simp [Finset.mem_range.mpr hx]

/-- `1 ≤ log (M + N + 2)` when `N ≥ 1`, since `e < 3`. -/
private lemma one_le_log_MN (M N : ℕ) (hN : 1 ≤ N) : 1 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) := by
  have h3 : Real.exp 1 ≤ (M : ℝ) + (N : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [Real.exp_one_lt_three, Nat.cast_nonneg (α := ℝ) M]
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) h3

/-- Item 3 of `IsSpecOrdRestart` (cost part) for the machine cost (any `lsfInit`, `params`,
`spanConst`): a restart does not lower the cost and adds at most
`c_T' · (M + 1) · γ_r(M) · log^{p_T'}(M + N + 2)`. -/
theorem bundleRestartMachWith_restartCost (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M)) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params spanConst
    let P' := bundleCoreParamsMachWith E spanConst
    let pre := fun t => (Tm.runOrdAfterUpdate k M N D ord restarts t).1
    ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl Tm.restart (pre r)
      Tm.cost st' ≤ Tm.cost (Tm.restart st' j') ∧
      (Tm.cost (Tm.restart st' j') : ℝ) ≤ (Tm.cost st' : ℝ) +
        P'.c_T * ((M : ℝ) + 1) * P'.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T := by
  intro Tm P' pre r hr p j' hpref st'
  set Tb := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
  set P := bundleCoreParams E
  have hNM := sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit E.C_lsst E.L sparsify
    params spanConst k M N D ord restarts r
  have hf_p := foldl_bundleRestart_props lsfInit E.C_lsst E.L sparsify (pre r) p
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
      ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
    have hN1 : 1 ≤ N := le_trans (Finset.card_pos.mpr hV₀) hN
    have hj' : j' < k := hrest r hr j' (hpref.subset (by simp))
    have hrun := runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts r
    have hne_pre : (pre r).isNonempty = true := hNM.1.isNonempty.trans (hrun.1.trans (decide_eq_true hV₀))
    have hk_pre : (pre r).k = k := hNM.1.k.trans hrun.2.2.1
    have hord_pre : (pre r).ord = ord r := hNM.1.ord.trans (hrun.2.2.2.2 hV₀).1
    have hne_st' : st'.isNonempty = true := hf_p.1.trans hne_pre
    have hk_st' : st'.k = k := hf_p.2.1.trans hk_pre
    have hord_st' : st'.ord = ord r := hf_p.2.2.1.trans hord_pre
    have hrc := bundleRestartToolMachWith_restart_cost_eq lsfInit E.C_lsst E.L sparsify params
      spanConst st' j' hne_st' (hk_st'.symm ▸ hj')
    dsimp only at hrc
    have hsm_eq : singleBundleRestartMachCost E.L sparsify (st'.trees j') st'.ord =
        singleBundleRestartMachCost E.L sparsify ((pre r).trees j') (ord r) := by
      rw [hord_st', ← hord_pre]
      exact foldl_bundleRestartWith_singleMachCost_eq lsfInit E.C_lsst E.L sparsify p (pre r)
        hne_pre j'
    have hPar := (runOrdAfterRestartsMachWith_params lsfInit E.C_lsst E.L sparsify params spanConst
      k M N D ord restarts r j').1
    have hAB_b : ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j').activeBuckets =
        (initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j').activeBuckets :=
      (runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify k M N τ hk D ord restarts
        hG₀ hV₀ hℓ₀ hD hOrd j' (hHyps.hInit j' hj') r hr).2.2.2.2.1
    have hSB_b : ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j').splitBound =
        bundleSplitBudget k M :=
      (runOrdAfterRestarts_bun_inv lsfInit E.C_lsst E.L sparsify k M N τ hk D ord restarts
        hG₀ hV₀ hℓ₀ hD hOrd j' (hHyps.hInit j' hj') r hr).2.2.1
    have hsm_inner : singleBundleRestartMachCost E.L sparsify ((pre r).trees j') (ord r) =
        (((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j').cs.G.m + 1 +
          ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j').activeComps.sum fun C =>
            ((initBundleTreeWith lsfInit E.L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j').activeBuckets C).sum
              fun b => spanConst * spanInitBound (params M) E.L (bundleSplitBudget k M)
                (normGraph (restartBucketBundle
                  ((Tb.runOrdAfterUpdate k M N D ord restarts r).1.trees j') (ord r) C b).graph)) *
          bundleLogFactor M N := by
      rw [singleBundleRestartMachCost_eq_inner, hPar.1, hPar.2.1,
        singleBundleRestartMachInner_of_nonMachEq sparsify (hNM.1.trees j')
          hPar.2.2.1 hPar.2.2.2.1 hSB_b (ord r), hAB_b]
    have hInner := singleBundleRestartMachInner_pre_le E lsfInit sparsify params spanConst
      k M N τ D ord restarts hk hG₀ hV₀ hℓ₀ hD hOrd hM hN hThresh hHyps hParams r j' hj' hr
    set Lg := Real.log ((M : ℝ) + (N : ℝ) + 2)
    have hL1 : 1 ≤ Lg := one_le_log_MN M N hN1
    have hLg_nn : 0 ≤ Lg := by linarith
    have hγr_nn : 0 ≤ P.γ_r M := by linarith [(bundleCoreParams_valid E).2.2.2.2.2.2.1 M]
    have hlg_le : (bundleLogFactor M N : ℝ) ≤ 16 * Lg ^ 2 := bundleLogFactor_le M N
    have hmul := mul_le_mul hInner hlg_le (Nat.cast_nonneg _) (by positivity)
    have hmax1 : ((max 1 spanConst : ℕ) : ℝ) = (spanConst : ℝ) := by rw [max_eq_right hConst]
    have hc_sp1 : (1 : ℝ) ≤ (spanConst : ℝ) := by exact_mod_cast hConst
    have hcoeff : 16 * (2 + (spanConst : ℝ) * (21 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 16)) ≤ P'.c_T := by
      dsimp only [P', bundleCoreParamsMachWith, bundleCoreParams]
      rw [hmax1]
      have h7_nn : (0 : ℝ) ≤ (7 : ℝ) ^ max E.p_s_hi E.p_t_hi := by positivity
      have hc_nn : (0 : ℝ) ≤ (spanConst : ℝ) := by linarith
      have hprod_nn : 0 ≤ (spanConst : ℝ) * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi := mul_nonneg hc_nn h7_nn
      have hcn : (spanConst : ℝ) ≤ (spanConst : ℝ) * E.c_n := le_mul_of_one_le_right hc_nn E.hc_n
      have hL : 16 * (2 + (spanConst : ℝ) * (21 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 16)) =
          32 + 336 * ((spanConst : ℝ) * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) + 256 * (spanConst : ℝ) := by ring
      have hR : (spanConst : ℝ) * (65 * (37810 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + E.c_n) + 18000) =
          2457650 * ((spanConst : ℝ) * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi) +
            65 * ((spanConst : ℝ) * E.c_n) + 18000 * (spanConst : ℝ) := by ring
      rw [hL, hR]
      linarith [hc_sp1, hprod_nn, hcn]
    have hpow : Lg ^ (P.p_T + 1) * Lg ^ 2 ≤ Lg ^ P'.p_T := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hL1 (by dsimp only [P', P, bundleCoreParamsMachWith]; omega)
    have hbound : (singleBundleRestartMachCost E.L sparsify ((pre r).trees j') (ord r) : ℝ) ≤
        P'.c_T * ((M : ℝ) + 1) * P'.γ_r M * Lg ^ P'.p_T := by
      rw [hsm_inner, Nat.cast_mul]
      refine le_trans hmul ?_
      have hL : (2 + (spanConst : ℝ) * (21 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 16)) *
            ((M : ℝ) + 1) * P.γ_r M * Lg ^ (P.p_T + 1) * (16 * Lg ^ 2) =
          (16 * (2 + (spanConst : ℝ) * (21 * (7 : ℝ) ^ max E.p_s_hi E.p_t_hi + 16))) *
            (((M : ℝ) + 1) * P.γ_r M * (Lg ^ (P.p_T + 1) * Lg ^ 2)) := by ring
      have hR : P'.c_T * ((M : ℝ) + 1) * P'.γ_r M * Lg ^ P'.p_T =
          P'.c_T * (((M : ℝ) + 1) * P.γ_r M * Lg ^ P'.p_T) := by
        dsimp only [P', bundleCoreParamsMachWith]; ring
      rw [hL, hR]
      exact mul_le_mul hcoeff (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity) (by have := (bundleCoreParamsMachWith_valid E spanConst).2.2.2.2.2.2.2.2.2; exact this)
    refine ⟨?_, ?_⟩
    · rw [hrc]; exact Nat.le_add_right _ _
    · rw [hrc, hsm_eq, Nat.cast_add]
      linarith
  · have hrunE := runOrdAfterRestarts_empty_case lsfInit E.C_lsst E.L sparsify k M N D ord
      restarts hV₀
    have hst'_hem : st'.isNonempty = false := hf_p.1.trans (hNM.1.isNonempty.trans (hrunE r).1)
    have hres_eq : Tm.restart st' j' = st' := by
      change (if st'.isNonempty = true then _ else st') = st'
      simp only [hst'_hem, Bool.false_eq_true, ↓reduceIte]
    have hlog_nn : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
    have hRHS : 0 ≤ P'.c_T * ((M : ℝ) + 1) * P'.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T := by
      have h1 : 0 ≤ P'.c_T := (bundleCoreParamsMachWith_valid E spanConst).2.2.2.2.2.2.2.2.2
      have h2 : 1 ≤ P'.γ_r M := (bundleCoreParamsMachWith_valid E spanConst).2.2.2.2.2.2.1 M
      have : 0 ≤ P'.γ_r M := by linarith
      positivity
    rw [hres_eq]
    exact ⟨le_rfl, by linarith⟩

/-- Item 3 of `IsSpecOrdRestart` (cost part) for `sparseCoreBundleRestartToolMach`. -/
theorem bundleRestartMach_restartCost (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M)) :
    let Tm := sparseCoreBundleRestartToolMach oracle E.C_lsst E.L sparsify params spanConst
    let P' := bundleCoreParamsMachWith E spanConst
    let pre := fun t => (Tm.runOrdAfterUpdate k M N D ord restarts t).1
    ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl Tm.restart (pre r)
      Tm.cost st' ≤ Tm.cost (Tm.restart st' j') ∧
      (Tm.cost (Tm.restart st' j') : ℝ) ≤ (Tm.cost st' : ℝ) +
        P'.c_T * ((M : ℝ) + 1) * P'.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T :=
  bundleRestartMachWith_restartCost E (initLSFOnline oracle E.C_lsst) sparsify params spanConst
    hConst k τ M N D ord restarts Ψ c w hk hG₀ hD hWeak hOrd hM hN hrest hThresh hHyps.toWith
    hParams

/-- Item 7 of `IsSpecOrdRestart` for the machine cost (any `lsfInit`, `params`, `spanConst`):
the cost after step `τ` is at most
`c_T' · (M + 1) · (k + R) · (k + 1) · γ_r(M) · log^{p_T'}(M + N + 2)`. -/
theorem bundleRestartMachWith_totalCost_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M)) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params spanConst
    let P' := bundleCoreParamsMachWith E spanConst
    (Tm.cost (Tm.runOrdAfterRestarts k M N D ord restarts τ) : ℝ) ≤
      P'.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P'.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T := by
  intro Tm P'
  have hValP := bundleCoreParamsMachWith_valid E spanConst
  have hγrM : 1 ≤ P'.γ_r M := hValP.2.2.2.2.2.2.1 M
  have hcT_nn : 0 ≤ P'.c_T := hValP.2.2.2.2.2.2.2.2.2
  have hlogMN_nn : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
  set G_M := P'.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P'.γ_r M *
    (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T with hG_Mdef
  have hG_M_nn : 0 ≤ G_M := by
    have : 0 ≤ P'.γ_r M := by linarith
    positivity
  set S := ((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) with hSdef
  have hgoal_eq : P'.c_T * ((M : ℝ) + 1) * ((k : ℝ) + (S : ℝ)) * ((k : ℝ) + 1) * P'.γ_r M *
      (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T = ((k : ℝ) + (S : ℝ)) * G_M := by
    rw [hG_Mdef]; ring
  rw [hgoal_eq]
  have hkS_nn : 0 ≤ (k : ℝ) + (S : ℝ) := by positivity
  have hNM := sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit E.C_lsst E.L sparsify
    params spanConst k M N D ord restarts τ
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord
      restarts τ
    have hne : (Tm.runOrdAfterRestarts k M N D ord restarts τ).isNonempty = true :=
      hNM.2.2.isNonempty.trans (hrun.2.1.trans (decide_eq_true hV₀))
    have hk_eq : (Tm.runOrdAfterRestarts k M N D ord restarts τ).k = k :=
      hNM.2.2.k.trans hrun.2.2.2.1
    have hcost : Tm.cost (Tm.runOrdAfterRestarts k M N D ord restarts τ) =
        ∑ j ∈ Finset.range k, ((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost :=
      (sparseCoreBundleRestartToolMachWith_cost_eq lsfInit E.C_lsst E.L sparsify params spanConst _).trans
        (by simp only [hne, ↓reduceIte, hk_eq])
    rw [hcost, Nat.cast_sum]
    have hS_eq : (S : ℝ) = ∑ j ∈ Finset.range k,
        ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) := by
      rw [Finset.sum_comm, hSdef, Nat.cast_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_le : r ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [← list_sum_count_eq_length'' (restarts r) k (hrest r hr_le), Nat.cast_sum]
    have hbranch : ∀ j ∈ Finset.range k,
        ((((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost : ℕ) : ℝ) ≤
          (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) * G_M := fun j hj =>
      bundleBranchWith_machCost_restart_le E lsfInit sparsify params spanConst hConst k τ M N D
        ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hHyps hParams hV₀ j
        (Finset.mem_range.mp hj)
    calc ∑ j ∈ Finset.range k,
            ((((Tm.runOrdAfterRestarts k M N D ord restarts τ).trees j).machCost : ℕ) : ℝ)
        ≤ ∑ j ∈ Finset.range k,
            (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) * G_M :=
          Finset.sum_le_sum hbranch
      _ = ((k : ℝ) + (S : ℝ)) * G_M := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, hS_eq]
          simp
  · have hrunE := runOrdAfterRestarts_empty_case lsfInit E.C_lsst E.L sparsify k M N D ord
      restarts hV₀
    have hcost0 : Tm.cost (Tm.runOrdAfterRestarts k M N D ord restarts τ) = 0 :=
      (sparseCoreBundleRestartToolMachWith_cost_eq lsfInit E.C_lsst E.L sparsify params spanConst _).trans
        (by rw [hNM.2.2.isNonempty, (hrunE τ).2.1]; rfl)
    rw [hcost0, Nat.cast_zero]
    exact mul_nonneg hkS_nn hG_M_nn

/-- Item 7 of `IsSpecOrdRestart` for `sparseCoreBundleRestartToolMach`. -/
theorem bundleRestartMach_totalCost_le (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D)
    (hParams : SparsifyParamsLe (params M) (E.P_fn M)) :
    let Tm := sparseCoreBundleRestartToolMach oracle E.C_lsst E.L sparsify params spanConst
    let P' := bundleCoreParamsMachWith E spanConst
    (Tm.cost (Tm.runOrdAfterRestarts k M N D ord restarts τ) : ℝ) ≤
      P'.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P'.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P'.p_T :=
  bundleRestartMachWith_totalCost_le E (initLSFOnline oracle E.C_lsst) sparsify params spanConst
    hConst k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh
    hHyps.toWith hParams

/-- Helper transferring the non-cost clauses of `IsSpecOrdRestart` (items 1, 2, 3a–3b, 4, 5, 6)
from `sparseCoreBundleRestartToolWith` to `sparseCoreBundleRestartToolMachWith` via
`SparseCoreBundleNonMachEq`. -/
theorem bundleRestartMachWith_nonCost_of_base
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (c w : ℕ → ℕ → ℝ) (P : SparseCoreParams)
    (hBase :
      let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
      let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
      let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
      let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
      (∀ t ≤ τ, ∀ j < k,
        (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
        IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
          (T.S (post t) j) (T.emb (post t) j) ∧
        ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
          ((T.lsfs (post t) j).F.R.card : ℝ) ≤
            P.c_R * ((M : ℝ) / (k : ℝ) +
              (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
                (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
      (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
        (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
        (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
          (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
        (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
        (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
        T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j)) ∧
      (∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
        let st' := p.foldl T.restart (pre r)
        (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
        (∀ b < k, b ≠ j' →
          T.S (T.restart st' j') b = T.S st' b ∧
          T.emb (T.restart st' j') b = T.emb st' b ∧
          T.rot (T.restart st' j') b = T.rot st' b)) ∧
      (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
        (s₀ = 0 ∨ j ∈ restarts s₀) →
        (∀ r, s₀ < r → r < t → j ∉ restarts r) →
        (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
          P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
        (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
          P.γ_r M * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
      (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
        (s₀ = 0 ∨ j ∈ restarts s₀) →
        (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
        ∃ Ψ' : ℝ,
          WeakHiddenStable (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
            (T.coreCOrdFrom k M N D ord restarts c s₀ j)
            (T.coreWOrdFrom k M N D ord restarts w s₀ j)) ∧
      (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
        (s₀ = 0 ∨ j ∈ restarts s₀) →
        (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
        OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
          (fun δ => T.rot (post (s₀ + δ)) j))) :
    let Tm := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let pre := fun t => (Tm.runOrdAfterUpdate k M N D ord restarts t).1
    let U_S := fun t => (Tm.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => Tm.runOrdAfterRestarts k M N D ord restarts t
    (∀ t ≤ τ, ∀ j < k,
      (Tm.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (Tm.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (Tm.S (post t) j) (Tm.emb (post t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((Tm.lsfs (post t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (Tm.lsfs (post t) j).F.F.E ⊆ (Tm.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (Tm.lsfs (post t) j).wstr e = (Tm.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (Tm.lsfs (post t) j).wstr e = 1) ∧
      (Tm.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
      Tm.S (pre t) j = (Tm.S (post (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl Tm.restart (pre r)
      (∀ b < k, Tm.lsfs (Tm.restart st' j') b = Tm.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        Tm.S (Tm.restart st' j') b = Tm.S st' b ∧
        Tm.emb (Tm.restart st' j') b = Tm.emb st' b ∧
        Tm.rot (Tm.restart st' j') b = Tm.rot st' b)) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (Tm.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      ∃ Ψ' : ℝ,
        WeakHiddenStable (Tm.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
          (Tm.coreCOrdFrom k M N D ord restarts c s₀ j)
          (Tm.coreWOrdFrom k M N D ord restarts w s₀ j)) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      OrderedUpTo (Tm.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => Tm.rot (post (s₀ + δ)) j)) := by
  intro Tm pre U_S post
  set Tb := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  have hNM := fun s => sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L
    sparsify params spanConst k M N D ord restarts s
  have hlsfs : ∀ s j, Tm.lsfs (post s) j = Tb.lsfs (Tb.runOrdAfterRestarts k M N D ord restarts s) j :=
    fun s j => SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst (hNM s).2.2 j
  have hS_post : ∀ s j, Tm.S (post s) j = Tb.S (Tb.runOrdAfterRestarts k M N D ord restarts s) j :=
    fun s j => SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst (hNM s).2.2 j
  have hS_pre : ∀ s j, Tm.S (pre s) j = Tb.S (Tb.runOrdAfterUpdate k M N D ord restarts s).1 j :=
    fun s j => SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst (hNM s).1 j
  have hemb : ∀ s j, Tm.emb (post s) j = Tb.emb (Tb.runOrdAfterRestarts k M N D ord restarts s) j :=
    fun s j => SparseCoreBundleNonMachEq.emb_eq lsfInit C_lsst L sparsify params spanConst (hNM s).2.2 j
  have hrot : ∀ s j, Tm.rot (post s) j = Tb.rot (Tb.runOrdAfterRestarts k M N D ord restarts s) j :=
    fun s j => SparseCoreBundleNonMachEq.rot_eq lsfInit C_lsst L sparsify params spanConst (hNM s).2.2 j
  have hU : ∀ s j, U_S s j = (Tb.runOrdAfterUpdate k M N D ord restarts s).2 j :=
    fun s j => congrFun (hNM s).2.1 j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht j hj
    rw [hlsfs t j, hS_post t j, hemb t j]
    exact hBase.1 t ht j hj
  · intro t ht1 htτ j hj
    rw [hlsfs t j, hlsfs (t - 1) j, hS_post (t - 1) j, hS_pre t j, hU t j]
    exact hBase.2.1 t ht1 htτ j hj
  · intro r hr p j' hpref
    have hfold : SparseCoreBundleNonMachEq (p.foldl Tm.restart (pre r))
        (p.foldl Tb.restart (Tb.runOrdAfterUpdate k M N D ord restarts r).1) :=
      SparseCoreBundleNonMachEq.foldl_restart lsfInit C_lsst L sparsify p (hNM r).1
    have hrest1 : SparseCoreBundleNonMachEq (Tm.restart (p.foldl Tm.restart (pre r)) j')
        (Tb.restart (p.foldl Tb.restart (Tb.runOrdAfterUpdate k M N D ord restarts r).1) j') :=
      SparseCoreBundleNonMachEq.restart lsfInit C_lsst L sparsify hfold j'
    have hb := hBase.2.2.1 r hr p j' hpref
    refine ⟨fun b hbk => ?_, fun b hbk hne => ?_⟩
    · exact (SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst hrest1 b).trans
        ((hb.1 b hbk).trans
          (SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst hfold b).symm)
    · exact ⟨(SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst hrest1 b).trans
          ((hb.2 b hbk hne).1.trans
            (SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst hfold b).symm),
        (SparseCoreBundleNonMachEq.emb_eq lsfInit C_lsst L sparsify params spanConst hrest1 b).trans
          ((hb.2 b hbk hne).2.1.trans
            (SparseCoreBundleNonMachEq.emb_eq lsfInit C_lsst L sparsify params spanConst hfold b).symm),
        (SparseCoreBundleNonMachEq.rot_eq lsfInit C_lsst L sparsify params spanConst hrest1 b).trans
          ((hb.2 b hbk hne).2.2.trans
            (SparseCoreBundleNonMachEq.rot_eq lsfInit C_lsst L sparsify params spanConst hfold b).symm)⟩
  · intro s₀ t hst htτ j hj hs₀ hNoRest
    have hb := hBase.2.2.2.1 s₀ t hst htτ j hj hs₀ hNoRest
    have h1 : (Finset.Icc (s₀ + 1) t).sum (fun s => (U_S s j).length) =
        (Finset.Icc (s₀ + 1) t).sum (fun s => ((Tb.runOrdAfterUpdate k M N D ord restarts s).2 j).length) :=
      Finset.sum_congr rfl fun s _ => by rw [hU s j]
    have h2 : (Finset.Icc (s₀ + 1) t).sum (fun s => (Tm.S (post (s - 1)) j).batchEnc (U_S s j)) =
        (Finset.Icc (s₀ + 1) t).sum (fun s =>
          (Tb.S (Tb.runOrdAfterRestarts k M N D ord restarts (s - 1)) j).batchEnc
            ((Tb.runOrdAfterUpdate k M N D ord restarts s).2 j)) :=
      Finset.sum_congr rfl fun s _ => by rw [hS_post (s - 1) j, hU s j]
    rw [h1, h2]; exact hb
  · intro s₀ t hst htτ j hj hs₀ hNoRest
    rw [sparseCoreBundleRestartToolMachWith_coreInstanceOrdFrom_eq,
      sparseCoreBundleRestartToolMachWith_coreCOrdFrom_eq,
      sparseCoreBundleRestartToolMachWith_coreWOrdFrom_eq]
    exact hBase.2.2.2.2.1 s₀ t hst htτ j hj hs₀ hNoRest
  · intro s₀ t hst htτ j hj hs₀ hNoRest
    rw [sparseCoreBundleRestartToolMachWith_coreInstanceOrdFrom_eq]
    have hrot_fun : (fun δ => Tm.rot (post (s₀ + δ)) j) =
        (fun δ => Tb.rot (Tb.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j) :=
      funext fun δ => hrot (s₀ + δ) j
    rw [hrot_fun]
    exact hBase.2.2.2.2.2 s₀ t hst htτ j hj hs₀ hNoRest

/-- **`IsSpecOrdRestart` for the machine cost (any `lsfInit`, `params`, `spanConst`).**
Under a per-instance `BundleCoreHypsAtWith` provider and `SparsifyParamsLe (params M) (E.P_fn M)`,
`sparseCoreBundleRestartToolMachWith` meets `IsSpecOrdRestart` with
`bundleCoreParamsMachWith E spanConst` (paper Lemma 5.17, pages 23–24). -/
theorem sparseCoreBundleRestartToolMachWith_isSpecOrdRestart (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (hParams : ∀ M, SparsifyParamsLe (params M) (E.P_fn M))
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestart (bundleCoreParamsMachWith E spanConst) := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hH := hHyps k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh
  have h := bundleRestartWith_spec E lsfInit sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hH
  have hNC := bundleRestartMachWith_nonCost_of_base lsfInit E.C_lsst E.L sparsify params spanConst
    k τ M N D ord restarts c w (bundleCoreParamsMachWith E spanConst)
    ⟨h.1, h.2.1, fun r hr p j' hpref => ⟨(h.2.2.1 r hr p j' hpref).1, (h.2.2.1 r hr p j' hpref).2.1⟩,
      h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hR := bundleRestartMachWith_restartCost E lsfInit sparsify params spanConst hConst
    k τ M N D ord restarts Ψ c w hk hG₀ hD hWeak hOrd hM hN hrest hThresh hH (hParams M)
  have hT := bundleRestartMachWith_totalCost_le E lsfInit sparsify params spanConst hConst
    k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hH (hParams M)
  exact ⟨hNC.1, hNC.2.1,
    fun r hr p j' hpref => ⟨(hNC.2.2.1 r hr p j' hpref).1, (hNC.2.2.1 r hr p j' hpref).2,
      (hR r hr p j' hpref).1, (hR r hr p j' hpref).2⟩,
    hNC.2.2.2.1, hNC.2.2.2.2.1, hNC.2.2.2.2.2, hT⟩

/-- `IsSpecOrdRestartNoHidden` for the machine cost (any `lsfInit`, `params`, `spanConst`). -/
theorem sparseCoreBundleRestartToolMachWith_isSpecOrdRestartNoHidden (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (hParams : ∀ M, SparsifyParamsLe (params M) (E.P_fn M))
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestartNoHidden (bundleCoreParamsMachWith E spanConst) :=
  (sparseCoreBundleRestartToolMachWith_isSpecOrdRestart E lsfInit sparsify params spanConst hConst
    hParams hHyps).toNoHidden

/-- **General `IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden` for
`sparseCoreBundleRestartToolMachWith`** from any approximate MWU LSF initializer
(`IsApproxMWUInit`). -/
theorem sparseCoreBundleRestartToolMachWith_isSpecOrdRestart_of_isApproxMWUInit
    (E : SparseCoreEnv) (α K_σ K_ρ : ℝ)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (hParams : ∀ M, SparsifyParamsLe (params M) (E.P_fn M))
    (hApprox : IsApproxMWUInit lsfInit E.C_lsst α K_σ K_ρ)
    (hSp : ∀ m, DynSpanner.SparsifySpec m (E.P_fn m) (sparsify m))
    (hBm : ∀ m, m ≤ E.B_fn m) :
    let E' : SparseCoreEnv := { E with C_lsst := max E.C_lsst (K_σ / 6272) }
    (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestart (bundleCoreParamsMachWith E' spanConst) ∧
      (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
          spanConst).IsSpecOrdRestartNoHidden (bundleCoreParamsMachWith E' spanConst) := by
  let E' : SparseCoreEnv := { E with C_lsst := max E.C_lsst (K_σ / 6272) }
  have hSpec :
      (sparseCoreBundleRestartToolMachWith lsfInit E'.C_lsst E'.L sparsify params
          spanConst).IsSpecOrdRestart (bundleCoreParamsMachWith E' spanConst) :=
    sparseCoreBundleRestartToolMachWith_isSpecOrdRestart E' lsfInit sparsify params spanConst
      hConst hParams
      (fun _ _ M _ _ _ _ _ _ _ _ _ hM _ _ =>
        bundleCoreHypsAtWith_of_B_ge_m (fun j hj => hApprox.toValidLSFInitFor hj)
          (hSp M) (le_trans hM (hBm M)))
  exact ⟨hSpec, hSpec.toNoHidden⟩

/-- **General `IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden` for
`sparseCoreBundleRestartToolMachWith`** from any approximate MWU LSF initializer (`IsApproxMWUInit`),
choosing `TP` independently of `lsfInit` and the input. -/
theorem toolMachWith_isSpecOrdRestart
    (E : SparseCoreEnv) (α K_σ K_ρ : ℝ) (_hα : 1 ≤ α) (_hKρ : 1 ≤ K_ρ)
    (spanConst : ℕ) (hConst : 1 ≤ spanConst) :
    ∃ TP : SparseCoreParams, TP.Valid ∧
      ∀ (lsfInit : LSFInit)
        (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
        (params : ℕ → SparsifyParams),
        (∀ M, SparsifyParamsLe (params M) (E.P_fn M)) →
        IsApproxMWUInit lsfInit E.C_lsst α K_σ K_ρ →
        (∀ m, DynSpanner.SparsifySpec m (E.P_fn m) (sparsify m)) → (∀ m, m ≤ E.B_fn m) →
        (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
            spanConst).IsSpecOrdRestart TP ∧
        (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
            spanConst).IsSpecOrdRestartNoHidden TP := by
  let E' : SparseCoreEnv := { E with C_lsst := max E.C_lsst (K_σ / 6272) }
  exact ⟨bundleCoreParamsMachWith E' spanConst, bundleCoreParamsMachWith_valid E' spanConst,
    fun lsfInit sparsify params hParams hApprox hSp hBm =>
      sparseCoreBundleRestartToolMachWith_isSpecOrdRestart_of_isApproxMWUInit E α K_σ K_ρ lsfInit
        sparsify params spanConst hConst hParams hApprox hSp hBm⟩

/-- **Unconditional** `ToolEmbedsSurvivingOrdRestart` for `sparseCoreBundleRestartToolMachWith`. -/
theorem sparseCoreBundleRestartToolMachWith_embedsSurvivingOrdRestart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).ToolEmbedsSurvivingOrdRestart := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh t ht j hj e he
  have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
    params spanConst k M N D ord restarts t).2.2
  rw [SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst hNM j] at he
  rw [SparseCoreBundleNonMachEq.emb_eq lsfInit C_lsst L sparsify params spanConst hNM j]
  exact sparseCoreBundleRestartToolWith_embedsSurvivingOrdRestart lsfInit C_lsst L sparsify
    k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh t ht j hj e he

/-- `ToolMWUOrdRestart` bound for `sparseCoreBundleRestartToolMachWith` under `IsApproxMWUInit`
and polynomial edge density `(D.G 0).m + 2 ≤ ((D.G 0).n + 2)^μ`. -/
theorem sparseCoreBundleRestartToolMachWith_toolMWUOrdRestart
    (lsfInit : LSFInit) (C_lsst α K_σ K_ρ : ℝ) (L μ : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (hKρ : 1 ≤ K_ρ)
    (hApprox : IsApproxMWUInit lsfInit C_lsst α K_σ K_ρ)
    {k M N τ : ℕ} {D : DynamicInstance} (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst
    let K₀ := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
    let K := 3 * K_ρ * K₀
    let σ_mwu := fun n => (μ : ℝ) * K * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) /
          (k : ℝ) ≤ σ_mwu (D.G t).n := by
  intro T K₀ K σ_mwu t ht e he
  have hsum : (∑ j ∈ Finset.range k,
      (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) =
      ∑ j ∈ Finset.range k, ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts k M N D ord
          restarts t) j).wstr e :=
    Finset.sum_congr rfl fun j _ => by
      have hNM := (sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
        params spanConst k M N D ord restarts t).2.2
      rw [SparseCoreBundleNonMachEq.lsfs_eq lsfInit C_lsst L sparsify params spanConst hNM j]
  rw [hsum]
  exact sparseCoreBundleRestartToolWith_toolMWUOrdRestart lsfInit C_lsst α K_σ K_ρ L μ sparsify
    hKρ hApprox ord restarts hk hG₀ hD hℓ hM_poly t ht e he

/-- **`IsSpecOrdRestart` for the machine cost.** -/
theorem sparseCoreBundleRestartToolMach_isSpecOrdRestart (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (hParams : ∀ M, SparsifyParamsLe (params M) (E.P_fn M))
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleRestartToolMach oracle E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestart (bundleCoreParamsMachWith E spanConst) :=
  sparseCoreBundleRestartToolMachWith_isSpecOrdRestart E (initLSFOnline oracle E.C_lsst) sparsify
    params spanConst hConst hParams
    (fun k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh =>
      (hHyps k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh).toWith)

/-- `IsSpecOrdRestartNoHidden` for `sparseCoreBundleRestartToolMach`. -/
theorem sparseCoreBundleRestartToolMach_isSpecOrdRestartNoHidden (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (hParams : ∀ M, SparsifyParamsLe (params M) (E.P_fn M))
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleRestartToolMach oracle E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestartNoHidden (bundleCoreParamsMachWith E spanConst) :=
  (sparseCoreBundleRestartToolMach_isSpecOrdRestart E oracle sparsify params spanConst hConst
    hParams hHyps).toNoHidden

/-- `IsSpecOrdRestart` for `sparseCoreBundleRestartToolMach` when `m ≤ E.B_fn m` for all `m`. -/
theorem sparseCoreBundleRestartToolMach_isSpecOrdRestart_of_B_ge_m (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (hParams : ∀ M, SparsifyParamsLe (params M) (E.P_fn M))
    (hLSST : HasLSSTSpec oracle E.C_lsst)
    (hSp : ∀ m, SparsifySpec m (E.P_fn m) (sparsify m))
    (hBm : ∀ m, m ≤ E.B_fn m) :
    (sparseCoreBundleRestartToolMach oracle E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestart (bundleCoreParamsMachWith E spanConst) :=
  sparseCoreBundleRestartToolMach_isSpecOrdRestart E oracle sparsify params spanConst hConst
    hParams (fun _ _ M _ _ _ _ _ _ _ _ _ hM _ _ =>
      bundleCoreHypsAt_of_B_ge_m hLSST (hSp M) (le_trans hM (hBm M)))

/-- **Non-vacuity** of `IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden` for
`sparseCoreBundleRestartToolMach` with `bundleCoreParamsMach (exBundleEnv C_lsst)`. -/
theorem ex_bundleRestartMach_isSpecOrdRestart :
    ∃ oracle C_lsst, HasLSSTSpec oracle C_lsst ∧
      let E := exBundleEnv C_lsst
      let T := sparseCoreBundleRestartToolMach oracle E.C_lsst E.L (fun _ => idSparsify) E.P_fn 1
      let P := bundleCoreParamsMach E
      P.Valid ∧ T.IsSpecOrdRestart P ∧ T.IsSpecOrdRestartNoHidden P := by
  obtain ⟨oracle, C_lsst, hLSST⟩ := theorem_2_2
  have hSpec := sparseCoreBundleRestartToolMach_isSpecOrdRestart_of_B_ge_m
    (exBundleEnv C_lsst) oracle (fun _ => idSparsify) (exBundleEnv C_lsst).P_fn 1 le_rfl
    (fun M => ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩)
    hLSST idSparsify_spec (fun m => Nat.le_succ m)
  exact ⟨oracle, C_lsst, hLSST, bundleCoreParamsMach_valid _, hSpec, hSpec.toNoHidden⟩

end MinCostFlow.Chain

end
