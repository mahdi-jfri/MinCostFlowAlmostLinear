module

public import MinCostFlow.Final.AssemblyDryRunSCParamWord
public import MinCostFlow.MinRatio.WireParamProg
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Concrete parameter-setup procedure discharging `DrySCInitBridgeHyps.hParam`

Assembles the uniform deterministic (`Stmt.NoRand`) Word-RAM procedure block `dryParamProcs` for
the dry-run witness `dryWitnessUsed`, proves its polylogarithmic time bound `dryParamCost_polylog`,
and proves `dryParamSetup_discharges_hParam`, which unconditionally discharges the exact
`DrySCInitBridgeHyps.hParam` obligation of `Final/AssemblyDryRunSC.lean`.

`SolverInnerOpenNoParam`, which installs `dryParamProcs` at offset `0` of `SolverInnerOpen`, is in
`Final/AssemblyDryRunSCParamOpen.lean`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio DynSpanner.Program

/-! ## Finite small-input lookup table and concrete procedure block -/

/-- Witness-only threshold above which `levelM` follows the exact integer formula and both
`pathDSBoundsContract` sums are at most `J.m ^ 3`. -/
def dryLevelMCut : ℕ :=
  Classical.choose exists_dryLevelM_threshold

/-- Exact parameter row `[d, branch, psi, quality, epsExp, N₀] ++ [lvlM 0, …, lvlM (d - 1)] ++
[depth]` for dimensions `(m, V)`, with the sparse-core depth `depth = chosenL (M₀ ^ 2)`. -/
def dryParamRow (m V : ℕ) : List ℕ :=
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let cfg := concreteCirculationCfgOfDims dryWitnessUsed m V
  [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, paramQuality threshold A m, paramEpsExp threshold A m V, cfg.N₀] ++
    (List.range cfg.P.d).map (Chain.levelM cfg.TP cfg.P) ++
    [Expander.chosenL (max m threshold ^ 2)]

/-- Finite lookup table covering all valid pairs `(I.m, solverPenalty J.m)` with
`1 ≤ J.m ≤ I.m < dryLevelMCut`. -/
def dryParamLookupEntries : List (ℕ × ℕ × List ℕ) :=
  (List.range dryLevelMCut).flatMap fun m =>
    (List.range m).map fun j =>
      (m, solverPenalty (j + 1), dryParamRow m (solverPenalty (j + 1)))

/-- Complete self-contained deterministic procedure block for dry-run parameter setup placed at
base index `b` (entry at `b`). -/
def dryParamProcs (b : ℕ) : List Stmt :=
  wireParamModule b
    (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    dryDecompK dryDecompThr dryWitnessDen
    sparsifyPathDSUsed.boundsProcs
    dryParamLookupEntries

/-- Determinism (`Stmt.NoRand`) of every procedure in `dryParamProcs`. -/
theorem dryParamProcs_noRand (b : ℕ) :
    ∀ s ∈ dryParamProcs b, s.NoRand :=
  wireParamModule_noRand _ _ _ _ _ _ _ _ (sparsifyPathDSUsed.hbounds_noRand _)

/-- Heap space bound `paramSpace` of `dryParamProcs` on `(source, J)`. -/
def dryParamSpace (_source J : Circulation) : ℕ :=
  wireParamSpace dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
    (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀

/-- Step-cost bound `paramCost` of `dryParamProcs` on `(source, J)`. -/
def dryParamCost (_source J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
    dryParamLookupEntries I.m V cfg.P.M₀ cfg.P.d (Expander.chosenL (cfg.P.M₀ ^ 2))

/-! ## Polylogarithmic cost bound (`O(log^{24} m)`) -/

private lemma size_le_mul_log_add_one {x c J_m : ℕ} (hc : 1 ≤ c) (hx : x ≤ c * (J_m + 2)) :
    x.size ≤ (c.size + 4) * (Nat.log 2 (J_m + 2) + 1) := by
  have h1 : J_m + 2 < 2 ^ (Nat.log 2 (J_m + 2) + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have h2 : c < 2 ^ c.size := Nat.lt_size_self c
  have h3 : x < 2 ^ (c.size + (Nat.log 2 (J_m + 2) + 1)) := by
    rw [pow_add]
    exact lt_of_le_of_lt hx (lt_of_le_of_lt (Nat.mul_lt_mul_of_pos_left h1 hc).le
      (Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)))
  have h4 : x.size ≤ c.size + (Nat.log 2 (J_m + 2) + 1) := Nat.size_le.mpr h3
  have hpos : 1 ≤ Nat.log 2 (J_m + 2) + 1 := by omega
  nlinarith

private lemma log_cost_poly_in_E (E cExp : ℕ) (hE : 1 ≤ E) (hc : 1 ≤ cExp) :
    let q := 38 * (cExp * E) ^ 8 + E
    let P := 4 * (q + E + 10)
    let L := P + E + 4
    71 * L + Num.logarithmCost L P E + 14 * E ≤
      10 ^ 12 * cExp ^ 24 * E ^ 24 := by
  intro q P L
  set X := cExp ^ 8 * E ^ 8
  have hE8 : E ≤ E ^ 8 := Nat.le_self_pow (by decide : 8 ≠ 0) E
  have h1E : 1 ≤ E ^ 8 := Nat.one_le_pow 8 E hE
  have hc8 : 1 ≤ cExp ^ 8 := Nat.one_le_pow 8 cExp hc
  have hX1 : 1 ≤ X := Nat.mul_pos hc8 h1E
  have hEX : E ≤ X := le_trans hE8 (Nat.le_mul_of_pos_left _ hc8)
  have hq : q ≤ 40 * X := by
    have hmul : (cExp * E) ^ 8 = X := mul_pow cExp E 8
    change 38 * (cExp * E) ^ 8 + E ≤ 40 * X
    rw [hmul]
    omega
  have hP : P ≤ 205 * X := by
    change 4 * (q + E + 10) ≤ 205 * X
    omega
  have hL : L ≤ 210 * X := by
    change P + E + 4 ≤ 210 * X
    omega
  have hX3 : X ^ 3 = cExp ^ 24 * E ^ 24 := by dsimp only [X]; ring
  have hXX2 : X ≤ X ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) X
  have hX2X3 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by decide)
  have hXX3 : X ≤ X ^ 3 := hXX2.trans hX2X3
  have h1X3 : 1 ≤ X ^ 3 := hX1.trans hXX3
  have hL2 : L ^ 2 ≤ 44100 * X ^ 2 := by
    calc L ^ 2 ≤ (210 * X) ^ 2 := Nat.pow_le_pow_left hL 2
      _ = 44100 * X ^ 2 := by ring
  have hP4 : P + 4 ≤ 209 * X := by omega
  have hterm1 : (E + 1) * (400 * L + 1000) ≤ (2 * X) * (85000 * X) := by
    apply Nat.mul_le_mul (by omega) (by omega)
  have hterm2 : (P + 4) * (500 * L ^ 2 + 2000 * L + 2000) ≤
      (209 * X) * (23000000 * X ^ 2) := by
    apply Nat.mul_le_mul hP4
    nlinarith only [hL, hL2, hX1, hXX2]
  unfold Num.logarithmCost
  rw [mul_assoc, ← hX3]
  have hprod1 : (2 * X) * (85000 * X) = 170000 * X ^ 2 := by ring
  have hprod2 : (209 * X) * (23000000 * X ^ 2) = 4807000000 * X ^ 3 := by ring
  rw [hprod1] at hterm1
  rw [hprod2] at hterm2
  nlinarith only [hL, hL2, hEX, hX1, hXX2, hX2X3, hXX3, h1X3, hterm1, hterm2]

private lemma chainDepthCost_poly_aux (B M d E : ℕ) (hB : 1 ≤ B)
    (hd : d ≤ (M + 2).size) (hE : (M + 2).size ≤ E) :
    let s := (M + 2).size
    let q := 38 * (B * s) ^ 8 + s
    let P := 4 * (q + s + 10)
    let L := P + s + 4
    71 * L + Num.logarithmCost L P s + 14 * s +
      (19 * d + 32) * M.size + 310 * (d - 1) + 537 ≤
      (10 ^ 12 * B ^ 24) * E ^ 24 + 400 * E ^ 2 + 1000 := by
  intro s q P L
  have hs1 : 1 ≤ s := Nat.size_pos.mpr (by omega)
  have hlog : 71 * L + Num.logarithmCost L P s + 14 * s ≤ 10 ^ 12 * B ^ 24 * s ^ 24 :=
    log_cost_poly_in_E s B hs1 hB
  have hpow : 10 ^ 12 * B ^ 24 * s ^ 24 ≤ (10 ^ 12 * B ^ 24) * E ^ 24 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE 24)
  have hMs : M.size ≤ E := (Nat.size_le_size (by omega)).trans hE
  have hdE : d ≤ E := hd.trans hE
  have hE1 : 1 ≤ E := hs1.trans hE
  have hEsq : E ≤ E ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) E
  have hdm : d * M.size ≤ E ^ 2 := by
    calc d * M.size ≤ E * E := Nat.mul_le_mul hdE hMs
      _ = E ^ 2 := by ring
  have hd_sub : d - 1 ≤ d := Nat.sub_le _ _
  have hexp : (19 * d + 32) * M.size = 19 * (d * M.size) + 32 * M.size := by ring
  have hquad : (19 * d + 32) * M.size + 310 * (d - 1) + 537 ≤ 400 * E ^ 2 + 1000 := by
    rw [hexp]; nlinarith only [hdm, hMs, hdE, hd_sub, hEsq, hE1]
  omega

private lemma sparseDepthCost_poly_aux (B M L_sp E : ℕ) (hB : 1 ≤ B)
    (hL : L_sp ≤ (M ^ 2 + 2).size) (hE : (M ^ 2 + 2).size ≤ E) :
    let s := (M ^ 2 + 2).size
    let q := 38 * (B * s) ^ 8 + s
    let P := 4 * (q + s + 10)
    let L := P + s + 4
    71 * L + Num.logarithmCost L P s + 14 * s + 166 * (L_sp - 1) + 368 ≤
      (10 ^ 12 * B ^ 24) * E ^ 24 + 200 * E + 400 := by
  intro s q P L
  have hs1 : 1 ≤ s := Nat.size_pos.mpr (by omega)
  have hlog : 71 * L + Num.logarithmCost L P s + 14 * s ≤ 10 ^ 12 * B ^ 24 * s ^ 24 :=
    log_cost_poly_in_E s B hs1 hB
  have hpow : 10 ^ 12 * B ^ 24 * s ^ 24 ≤ (10 ^ 12 * B ^ 24) * E ^ 24 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hE 24)
  have hLE : L_sp ≤ E := hL.trans hE
  have hsub : L_sp - 1 ≤ L_sp := Nat.sub_le _ _
  omega

private lemma polylog_combine_aux {K48 K24 cE lg L0 R wChain wSparse : ℕ}
    (hK48 : 600 ≤ K48) (hcE : 1 ≤ cE) (hlg : 1 ≤ lg)
    (hChain : wChain ≤ K48 * (cE * lg) ^ 24 + 400 * (cE * lg) ^ 2 + 1000)
    (hSparse : wSparse ≤ K24 * (cE * lg) ^ 24 + 200 * (cE * lg) + 400)
    {S : ℕ} (hRem : S + 1420 ≤ R * lg) :
    L0 + S + wChain + wSparse + 20 ≤
      (L0 + 2 * (K48 * cE ^ 24) + K24 * cE ^ 24 + R) * lg ^ 24 := by
  have h1_24 : 1 ≤ lg ^ 24 := Nat.one_le_pow 24 lg hlg
  have hlg1_24 : lg ≤ lg ^ 24 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hlg (by decide : 1 ≤ 24)
  have hlg2_24 : lg ^ 2 ≤ lg ^ 24 := Nat.pow_le_pow_right hlg (by decide : 2 ≤ 24)
  have hcE2 : cE ≤ cE ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) cE
  have hcE2_24 : cE ^ 2 ≤ cE ^ 24 := Nat.pow_le_pow_right hcE (by decide : 2 ≤ 24)
  have hC1 : K48 * (cE * lg) ^ 24 = (K48 * cE ^ 24) * lg ^ 24 := by rw [mul_pow, Nat.mul_assoc]
  have hC2 : K24 * (cE * lg) ^ 24 = (K24 * cE ^ 24) * lg ^ 24 := by rw [mul_pow, Nat.mul_assoc]
  have hQuad : 400 * (cE * lg) ^ 2 + 200 * (cE * lg) ≤ (K48 * cE ^ 24) * lg ^ 24 := by
    have h1 : 400 * (cE * lg) ^ 2 + 200 * (cE * lg) ≤ 600 * cE ^ 2 * lg ^ 24 := by
      rw [mul_pow]; nlinarith only [hlg1_24, hlg2_24, hcE, hcE2]
    have h2 : 600 * cE ^ 2 ≤ K48 * cE ^ 24 := Nat.mul_le_mul hK48 hcE2_24
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have hRem24 : S + 1420 ≤ R * lg ^ 24 := hRem.trans (Nat.mul_le_mul_left _ hlg1_24)
  have hL0 : L0 ≤ L0 * lg ^ 24 := Nat.le_mul_of_pos_right _ h1_24
  rw [hC1] at hChain
  rw [hC2] at hSparse
  have hExpand : (L0 + 2 * (K48 * cE ^ 24) + K24 * cE ^ 24 + R) * lg ^ 24 =
      L0 * lg ^ 24 + (K48 * cE ^ 24) * lg ^ 24 + (K48 * cE ^ 24) * lg ^ 24 +
        (K24 * cE ^ 24) * lg ^ 24 + R * lg ^ 24 := by ring
  rw [hExpand]
  omega

/-- **Polylogarithmic time bound**: `dryParamCost source J = O((log(J.m + 2) + 1) ^ 24)`,
with an explicit witness-only constant independent of `source` and `J`. -/
theorem dryParamCost_polylog :
    ∃ C : ℕ, ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
      dryParamCost source J ≤ C * (Nat.log 2 (J.m + 2) + 1) ^ 24 := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  obtain ⟨C₀_p, C₁_p, hC₀p, hC₁p, hden_sb⟩ :=
    Expander.decomposeImpl_phi_lb_subpoly ExpanderDecomp.expanderDecompositionUsed_holds
  obtain ⟨B_den, hBden, hBden_le⟩ :=
    Chain.exp_subpoly_mul_loglog_le_rpow (a := 2 / 3) (C := C₀_p) (δ := 1)
      (by norm_num) (by norm_num) (by norm_num)
  let K_den : ℕ := max 1 ⌈C₁_p * B_den⌉₊
  let cM : ℕ := 7 + threshold + 2
  let cE : ℕ := 2 * (cM.size + 4) + 2
  let K48 : ℕ := 10 ^ 12 * (2 ^ 48) ^ 24
  let K24 : ℕ := 10 ^ 12 * (2 ^ 24) ^ 24
  let R_lin : ℕ :=
    5000 * (cM.size + 4) + 2000 +
    120 * (dryDecompK + 1) * (2 * cE + 8) +
    sparsifyPathDSUsed.params.K_bounds * (dryWitnessDen.size + 2 * K_den.size + 3 * cE + 16) +
    65 * cE + 1620
  let C_tot : ℕ := lookupEntriesCost dryParamLookupEntries +
    2 * (K48 * cE ^ 24) + K24 * cE ^ 24 + R_lin
  refine ⟨C_tot, fun source J hJn hJm hCap => ?_⟩
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  set M₀ := cfg.P.M₀
  set L_sp := Expander.chosenL (M₀ ^ 2)
  set lg := Nat.log 2 (J.m + 2) + 1
  have hlg1 : 1 ≤ lg := by omega
  have hIm_le : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have hM0_eq : M₀ = max I.m threshold := (concreteCfg_scalars_eq dryWitnessUsed I.m V).1
  have hM0_le : M₀ ≤ (7 + threshold) * (J.m + 2) := by
    rw [hM0_eq]
    have h1 : max I.m threshold ≤ 7 * J.m + threshold := max_le (by omega) (by omega)
    have h2 : 7 * J.m + threshold ≤ (7 + threshold) * (J.m + 2) := by nlinarith only [hJm]
    omega
  have hM0_2_le : M₀ + 2 ≤ cM * (J.m + 2) := by
    change M₀ + 2 ≤ (7 + threshold + 2) * (J.m + 2)
    nlinarith only [hM0_le]
  have hM0_sz : (M₀ + 2).size ≤ (cM.size + 4) * lg :=
    size_le_mul_log_add_one (by change 1 ≤ 7 + threshold + 2; omega) hM0_2_le
  have hM0_sz_le : M₀.size ≤ (M₀ + 2).size := Nat.size_le_size (by omega)
  have hM2_sz : (M₀ ^ 2 + 2).size ≤ cE * lg := by
    have h1 : (M₀ ^ 2 + 2).size ≤ 2 * (M₀ + 2).size + 1 := by
      apply Nat.size_le.mpr
      have hm := Nat.lt_size_self (M₀ + 2)
      have hsq : (M₀ + 2) ^ 2 < 2 ^ (2 * (M₀ + 2).size) := by
        calc (M₀ + 2) ^ 2 < (2 ^ (M₀ + 2).size) ^ 2 := Nat.pow_lt_pow_left hm (by decide)
          _ = 2 ^ (2 * (M₀ + 2).size) := by rw [← pow_mul, mul_comm]
      have hlt : M₀ ^ 2 + 2 < (M₀ + 2) ^ 2 := by nlinarith
      have hpow : 2 ^ (2 * (M₀ + 2).size) ≤ 2 ^ (2 * (M₀ + 2).size + 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
    dsimp only [cE]; nlinarith only [h1, hM0_sz, hlg1]
  have hE1_le : (M₀ + 2).size ≤ cE * lg := by dsimp only [cE]; nlinarith only [hM0_sz, hlg1]
  -- Bound `wireParamChainDepthCost` and `wireParamSparseDepthCost`
  have hd_le : cfg.P.d ≤ (M₀ + 2).size := chosenD_le_size_add_two cfg.P.hM₀
  have hLsp_le : L_sp ≤ (M₀ ^ 2 + 2).size := by
    have h1 : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ) ≤
        Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := by
      have hge1 : 1 ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := by
        have h3 : (3 : ℝ) ≤ ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by
          have := cfg.P.hM₀; exact_mod_cast (show 3 ≤ M₀ ^ 2 + 2 by nlinarith)
        simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (Real.exp_one_lt_three.le.trans h3)
      calc Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ)
          ≤ Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
        _ = Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) := Real.rpow_one _
    have h2 : Real.log (((M₀ ^ 2 : ℕ) : ℝ) + 2) ≤ ((M₀ ^ 2 + 2).size : ℝ) := by
      have hlt : ((M₀ ^ 2 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) ^ (M₀ ^ 2 + 2).size := by
        exact_mod_cast (Nat.lt_size_self (M₀ ^ 2 + 2)).le
      have hl := Real.log_le_log (by positivity) hlt
      rw [Real.log_pow] at hl
      have : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) (M₀ ^ 2 + 2).size]
    exact Nat.ceil_le.mpr (h1.trans h2)
  have hChain_bd : wireParamChainDepthCost M₀ cfg.P.d ≤
      K48 * (cE * lg) ^ 24 + 400 * (cE * lg) ^ 2 + 1000 :=
    chainDepthCost_poly_aux (2 ^ 48) M₀ cfg.P.d (cE * lg) (Nat.one_le_pow 48 2 (by decide)) hd_le hE1_le
  have hSparse_bd : wireParamSparseDepthCost M₀ L_sp ≤
      K24 * (cE * lg) ^ 24 + 200 * (cE * lg) + 400 :=
    sparseDepthCost_poly_aux (2 ^ 24) M₀ L_sp (cE * lg) (Nat.one_le_pow 24 2 (by decide)) hLsp_le hM2_sz
  -- Bound `scalarParamsCost`
  have hV_sz : V.size ≤ 82 * (cM.size + 4) * lg + 5 := by
    have hVle : V ≤ 16 * M₀ ^ 81 := by
      have hJm_M0 : J.m ≤ M₀ :=
        ((solverConnectedAugmented_size J hJn hJm hCap).1).trans (le_max_left I.m threshold)
      exact (solverPenalty_le J.m hJm).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hJm_M0 81))
    have hsz : V.size ≤ (16 : ℕ).size + 81 * M₀.size := by
      have hc : (16 : ℕ) < 2 ^ (16 : ℕ).size := Nat.lt_size_self 16
      have hMs : M₀ ≤ 2 ^ M₀.size := (Nat.lt_size_self M₀).le
      have hpow : M₀ ^ 81 ≤ 2 ^ (81 * M₀.size) := by
        rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hMs 81
      apply Nat.size_le.mpr
      rw [pow_add]
      exact lt_of_le_of_lt hVle
        (lt_of_le_of_lt (Nat.mul_le_mul_left 16 hpow)
          (Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _)))
    have h16 : (16 : ℕ).size = 5 := by decide
    nlinarith only [hsz, h16, hM0_sz_le, hM0_sz]
  have hIm_sz : I.m.size ≤ (cM.size + 4) * lg :=
    (Nat.size_le_size (le_max_left I.m threshold)).trans (hM0_sz_le.trans hM0_sz)
  have hScal_bd : scalarParamsCost I.m V M₀ ≤ 5000 * (cM.size + 4) * lg + 2000 := by
    unfold scalarParamsCost Num.IPM.alphaExponent
    have h1 : (M₀.size + 1).size ≤ M₀.size + 1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have h4 : Nat.clog 2 (Num.IPM.alphaScale I.m V) ≤ I.m.size + V.size + 11 := by
      apply (Nat.clog_le_iff_le_pow (by decide)).mpr
      have h1000 : 1000 ≤ 2 ^ 10 := by decide
      have hsum : I.m.size + V.size ≤ 2 ^ (I.m.size + V.size) := (Nat.lt_two_pow_self).le
      calc 1000 * (I.m.size + V.size) ≤ 2 ^ 10 * 2 ^ (I.m.size + V.size) := Nat.mul_le_mul h1000 hsum
        _ = 2 ^ (10 + (I.m.size + V.size)) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (I.m.size + V.size + 11) := Nat.pow_le_pow_right (by decide) (by omega)
    nlinarith only [h1, h4, hIm_sz, hV_sz, hM0_sz_le, hM0_sz, hlg1]
  -- Bound `gammaAndLevelsCost`: `den ≤ K_den * (M₀ ^ 2 + 2)`
  have hden_le : drySparsifyDen M₀ ≤ K_den * (M₀ ^ 2 + 2) := by
    have h1 : (drySparsifyDen M₀ : ℝ) ≤ C₁_p * Expander.subpolyB1 C₀_p (M₀ ^ 2) := by
      have hsb := hden_sb (M₀ ^ 2)
      rwa [dryDecomp_phi_lb_eq, one_div_one_div] at hsb
    have hM2_3 : (3 : ℝ) ≤ ((M₀ ^ 2 : ℕ) : ℝ) + 2 := by
      have hM01 := cfg.P.hM₀
      exact_mod_cast (show 3 ≤ M₀ ^ 2 + 2 by nlinarith only [hM01])
    have h2 : Expander.subpolyB1 C₀_p (M₀ ^ 2) ≤ B_den * (((M₀ ^ 2 : ℕ) : ℝ) + 2) ^ (1 : ℝ) :=
      hBden_le (((M₀ ^ 2 : ℕ) : ℝ) + 2) hM2_3
    rw [Real.rpow_one] at h2
    have h3 : C₁_p * B_den ≤ (K_den : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈C₁_p * B_den⌉₊)
    have hfin : (drySparsifyDen M₀ : ℝ) ≤ ((K_den * (M₀ ^ 2 + 2) : ℕ) : ℝ) := by
      push_cast
      calc (drySparsifyDen M₀ : ℝ)
          ≤ C₁_p * (B_den * ((M₀ : ℝ) ^ 2 + 2)) := h1.trans (mul_le_mul_of_nonneg_left (by simpa using h2) (by linarith))
        _ = (C₁_p * B_den) * ((M₀ : ℝ) ^ 2 + 2) := by ring
        _ ≤ (K_den : ℝ) * ((M₀ : ℝ) ^ 2 + 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
    exact_mod_cast hfin
  have hlog_4M2 : Nat.log 2 (4 * M₀ ^ 2 + 2) ≤ 2 * (M₀ ^ 2 + 2).size + 4 := by
    have hlt : 4 * M₀ ^ 2 + 2 < 2 ^ ((M₀ ^ 2 + 2).size + 2) := by
      have h1 := Nat.lt_size_self (M₀ ^ 2 + 2)
      rw [pow_add]; norm_num; omega
    have h2 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
    omega
  have hlog_b1 : Nat.log 2 (drySparsifyDen M₀ + M₀ ^ 2 + 2) ≤
      K_den.size + (M₀ ^ 2 + 2).size + 4 := by
    have h1 : drySparsifyDen M₀ + M₀ ^ 2 + 2 ≤ (K_den + 1) * (M₀ ^ 2 + 2) := by nlinarith only [hden_le]
    have h2 : K_den + 1 < 2 ^ (K_den.size + 1) := by
      have := Nat.lt_size_self K_den; rw [pow_succ 2]; omega
    have h3 : M₀ ^ 2 + 2 < 2 ^ (M₀ ^ 2 + 2).size := Nat.lt_size_self _
    have hlt : drySparsifyDen M₀ + M₀ ^ 2 + 2 < 2 ^ (K_den.size + 1 + (M₀ ^ 2 + 2).size) := by
      rw [pow_add]; exact lt_of_le_of_lt h1 (Nat.mul_lt_mul'' h2 h3)
    have h4 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
    omega
  have hlog_b2 : Nat.log 2 (dryWitnessDen + drySparsifyCap M₀ + 2) ≤
      dryWitnessDen.size + K_den.size + 2 * (M₀ ^ 2 + 2).size + 10 := by
    have hcap_le : drySparsifyCap M₀ ≤ 36 * K_den * (M₀ ^ 2 + 2) ^ 2 + 1 := by
      unfold drySparsifyCap
      have : 36 * M₀ ^ 2 * drySparsifyDen M₀ ≤ 36 * (M₀ ^ 2 + 2) * (K_den * (M₀ ^ 2 + 2)) :=
        Nat.mul_le_mul (by omega) hden_le
      nlinarith only [this]
    have hsum : dryWitnessDen + drySparsifyCap M₀ + 2 ≤
        (dryWitnessDen + 36 * K_den + 3) * (M₀ ^ 2 + 2) ^ 2 := by
      have hsq1 : 1 ≤ (M₀ ^ 2 + 2) ^ 2 := Nat.one_le_pow 2 _ (by omega)
      nlinarith only [hcap_le, hsq1]
    have hc1 : dryWitnessDen + 36 * K_den + 3 < 2 ^ (dryWitnessDen.size + K_den.size + 7) := by
      have ha := Nat.lt_size_self dryWitnessDen
      have hb := Nat.lt_size_self K_den
      have hpa : 2 ^ dryWitnessDen.size ≤ 2 ^ (dryWitnessDen.size + K_den.size) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hpb : 2 ^ K_den.size ≤ 2 ^ (dryWitnessDen.size + K_den.size) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have h128 : 2 ^ (dryWitnessDen.size + K_den.size + 7) =
          128 * 2 ^ (dryWitnessDen.size + K_den.size) := by rw [pow_add]; ring
      have hpos : 1 ≤ 2 ^ (dryWitnessDen.size + K_den.size) := Nat.two_pow_pos _
      omega
    have hc2 : (M₀ ^ 2 + 2) ^ 2 < 2 ^ (2 * (M₀ ^ 2 + 2).size) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_lt_pow_left (Nat.lt_size_self (M₀ ^ 2 + 2)) (by decide)
    have hlt : dryWitnessDen + drySparsifyCap M₀ + 2 <
        2 ^ (dryWitnessDen.size + K_den.size + 7 + 2 * (M₀ ^ 2 + 2).size) := by
      rw [pow_add]; exact lt_of_le_of_lt hsum (Nat.mul_lt_mul'' hc1 hc2)
    have h4 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hlt
    omega
  -- Combine all 5 components of `wireParamCost`
  have hrOf_sq : (Expander.rOf (4 * M₀ ^ 2)) ^ 2 ≤ Nat.log 2 (4 * M₀ ^ 2 + 2) := by
    have hcube : (Expander.rOf (4 * M₀ ^ 2)) ^ 3 ≤ Nat.log 2 (4 * M₀ ^ 2) :=
      Expander.rOf_pow_le (4 * M₀ ^ 2)
    have hlog_mono : Nat.log 2 (4 * M₀ ^ 2) ≤ Nat.log 2 (4 * M₀ ^ 2 + 2) :=
      Nat.log_mono_right (by omega)
    have hsq_le : (Expander.rOf (4 * M₀ ^ 2)) ^ 2 ≤ (Expander.rOf (4 * M₀ ^ 2)) ^ 3 := by
      rcases Nat.eq_zero_or_pos (Expander.rOf (4 * M₀ ^ 2)) with hr0 | hrpos
      · simp [hr0]
      · exact Nat.pow_le_pow_right hrpos (by decide)
    exact (hsq_le.trans hcube).trans hlog_mono
  have hrem_bd :
      scalarParamsCost I.m V M₀ +
      gammaAndLevelsCost dryDecompK dryDecompThr dryWitnessDen M₀ L_sp cfg.P.d
        sparsifyPathDSUsed.params.K_bounds + 1420 ≤ R_lin * lg := by
    have hScal_lg : scalarParamsCost I.m V M₀ ≤ (5000 * (cM.size + 4) + 2000) * lg := by
      have h2000 : 2000 ≤ 2000 * lg := Nat.le_mul_of_pos_right 2000 hlg1
      rw [Nat.add_mul]
      exact hScal_bd.trans (Nat.add_le_add_left h2000 _)
    have hlog4_lg : Nat.log 2 (4 * M₀ ^ 2 + 2) + 4 ≤ (2 * cE + 8) * lg := by
      have h8 : 8 ≤ 8 * lg := Nat.le_mul_of_pos_right 8 hlg1
      rw [Nat.add_mul]; nlinarith only [hlog_4M2, hM2_sz, h8]
    have hphi_lg : 120 * (Nat.log 2 (4 * M₀ ^ 2 + 2) + dryDecompK * (Expander.rOf (4 * M₀ ^ 2)) ^ 2 + 4) ≤
        (120 * (dryDecompK + 1) * (2 * cE + 8)) * lg := by
      have hinner : Nat.log 2 (4 * M₀ ^ 2 + 2) + dryDecompK * (Expander.rOf (4 * M₀ ^ 2)) ^ 2 + 4 ≤
          (dryDecompK + 1) * (Nat.log 2 (4 * M₀ ^ 2 + 2) + 4) := by
        have h1 : dryDecompK * (Expander.rOf (4 * M₀ ^ 2)) ^ 2 ≤
            dryDecompK * (Nat.log 2 (4 * M₀ ^ 2 + 2) + 4) :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.add_mul, Nat.one_mul]; omega
      calc 120 * (Nat.log 2 (4 * M₀ ^ 2 + 2) + dryDecompK * (Expander.rOf (4 * M₀ ^ 2)) ^ 2 + 4)
          ≤ 120 * ((dryDecompK + 1) * (Nat.log 2 (4 * M₀ ^ 2 + 2) + 4)) := Nat.mul_le_mul_left 120 hinner
        _ ≤ 120 * ((dryDecompK + 1) * ((2 * cE + 8) * lg)) :=
          Nat.mul_le_mul_left 120 (Nat.mul_le_mul_left _ hlog4_lg)
        _ = (120 * (dryDecompK + 1) * (2 * cE + 8)) * lg := by ring
    have hK_lg : sparsifyPathDSUsed.params.K_bounds * (Nat.log 2 (drySparsifyDen M₀ + M₀ ^ 2 + 2) + 1) +
        sparsifyPathDSUsed.params.K_bounds * (Nat.log 2 (dryWitnessDen + drySparsifyCap M₀ + 2) + 1) ≤
        (sparsifyPathDSUsed.params.K_bounds * (dryWitnessDen.size + 2 * K_den.size + 3 * cE + 16)) * lg := by
      rw [← Nat.mul_add, Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith only [hlog_b1, hlog_b2, hM2_sz, hlg1]
    have htail_lg : 20 * L_sp + 45 * cfg.P.d + 200 + 1420 ≤ (65 * cE + 1620) * lg := by
      have h1620 : 1620 ≤ 1620 * lg := Nat.le_mul_of_pos_right 1620 hlg1
      rw [Nat.add_mul]; nlinarith only [hLsp_le, hM2_sz, hd_le, hE1_le, h1620]
    have hgam_eq : gammaAndLevelsCost dryDecompK dryDecompThr dryWitnessDen M₀ L_sp cfg.P.d
        sparsifyPathDSUsed.params.K_bounds =
      120 * (Nat.log 2 (4 * M₀ ^ 2 + 2) + dryDecompK * (Expander.rOf (4 * M₀ ^ 2)) ^ 2 + 4) +
        sparsifyPathDSUsed.params.K_bounds * (Nat.log 2 (drySparsifyDen M₀ + M₀ ^ 2 + 2) + 1) +
        sparsifyPathDSUsed.params.K_bounds * (Nat.log 2 (dryWitnessDen + drySparsifyCap M₀ + 2) + 1) +
        20 * L_sp + 45 * cfg.P.d + 200 := rfl
    have hR_mul : R_lin * lg =
        (5000 * (cM.size + 4) + 2000) * lg +
        (120 * (dryDecompK + 1) * (2 * cE + 8)) * lg +
        (sparsifyPathDSUsed.params.K_bounds * (dryWitnessDen.size + 2 * K_den.size + 3 * cE + 16)) * lg +
        (65 * cE + 1620) * lg := by
      dsimp only [R_lin]; ring
    have hreg : ∀ a b c d e f g h : ℕ,
        a + (b + c + d + e + f + g) + h = a + b + (c + d) + (e + f + g + h) := by
      intro a b c d e f g h; omega
    have hsum_le := Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add hScal_lg hphi_lg) hK_lg) htail_lg
    exact (congrArg (fun x => scalarParamsCost I.m V M₀ + x + 1420) hgam_eq).trans_le
      ((hreg _ _ _ _ _ _ _ _).trans_le (hsum_le.trans_eq hR_mul.symm))
  have hK48 : 600 ≤ K48 :=
    (by decide : 600 ≤ 10 ^ 12).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow 24 _ (Nat.one_le_pow 48 2 (by decide))))
  have hcE1 : 1 ≤ cE := by dsimp only [cE]; omega
  have hComb := polylog_combine_aux (L0 := lookupEntriesCost dryParamLookupEntries)
    hK48 hcE1 hlg1 hChain_bd hSparse_bd hrem_bd
  have hadd6 : ∀ a b c d e f : ℕ, a + b + c + d + e + f = a + (b + e) + c + d + f := by
    intro a b c d e f; omega
  have hReorder :
      dryParamCost source J =
      lookupEntriesCost dryParamLookupEntries +
        (scalarParamsCost I.m V M₀ +
          gammaAndLevelsCost dryDecompK dryDecompThr dryWitnessDen M₀ L_sp cfg.P.d
            sparsifyPathDSUsed.params.K_bounds) +
        wireParamChainDepthCost M₀ cfg.P.d + wireParamSparseDepthCost M₀ L_sp + 20 :=
    hadd6 _ _ _ _ _ _
  exact hReorder.trans_le hComb

/-! ## Main theorem discharging `DrySCInitBridgeHyps.hParam` -/

private lemma concreteCfgWithLast_eq_ofDims
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (SparseCore.lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) (J : Circulation) :
    concreteCirculationCfgWithLast W J =
      concreteCirculationCfgOfDims W (solverConnectedAugmented J).m (solverPenalty J.m) := rfl

private lemma concreteCfgWithLast_P_eq
    {lastTool : LastLevelTool} {C_last : ℝ}
    {hLast : lastTool.IsSpec (SparseCore.lastLevelParams C_last)}
    (W : ConcreteChainWitnessWithLast lastTool C_last hLast) (J : Circulation)
    (hM01 : 1 ≤ max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast W)) :
    (concreteCirculationCfgWithLast W J).P =
      Chain.concreteChainParams
        (max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast W)) hM01 := rfl

private lemma dryParamRow_eq_cfg (J : Circulation) :
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    dryParamRow I.m V =
      [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, k, k + Num.IPM.alphaExponent I.m V + 10, cfg.N₀] ++
        (List.range cfg.P.d).map (levelM cfg.TP cfg.P) ++
        [Expander.chosenL (max I.m threshold ^ 2)] :=
  congrArg (fun (c : Alg2Config) =>
    [c.P.d, c.P.k, ⌈c.Ψ⌉₊,
      paramQuality (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m,
      paramEpsExp (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m
        (solverPenalty J.m),
      c.N₀] ++ (List.range c.P.d).map (levelM c.TP c.P) ++
      [Expander.chosenL (max (solverConnectedAugmented J).m
        (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)])
    (concreteCfgWithLast_eq_ofDims dryWitnessUsed J).symm

private theorem initParamSetupContract_congr
    {w m V L P d₁ d₂ b₁ b₂ psi₁ psi₂ q₁ q₂ e₁ e₂ n₁ n₂ s₁ s₂ c₁ c₂ cD : ℕ}
    {lvlM : ℕ → ℕ} {p : Program} {proc : ℕ}
    (hd : d₁ = d₂) (hb : b₁ = b₂) (hpsi : psi₁ = psi₂) (hq : q₁ = q₂)
    (he : e₁ = e₂) (hn : n₁ = n₂) (hs : s₁ = s₂) (hc : c₁ = c₂)
    (h : MeetsContract w p proc
      (initParamSetupContract w m V L P d₂ b₂ psi₂ q₂ e₂ n₂ cD lvlM s₂ c₂)) :
    MeetsContract w p proc
      (initParamSetupContract w m V L P d₁ b₁ psi₁ q₁ e₁ n₁ cD lvlM s₁ c₁) := by
  subst hd; subst hb; subst hpsi; subst hq; subst he; subst hn; subst hs; subst hc; exact h

private lemma lt_of_eq_left {a b c : ℕ} (h : a = b) (hlt : a < c) : b < c :=
  h ▸ hlt

private lemma le_of_eq_left {a b c : ℕ} (h : a = b) (hle : a ≤ c) : b ≤ c :=
  h ▸ hle

/-- The sparse-core depth `chosenL (M₀ ^ 2)` that the parameter setup writes fits in a word. It is
at most `4 * M₀ + 1` (`chosenL_sq_le_four_mul_add_one`), `4 * M₀ = N₀ < 2 ^ w`, and `2 ^ w` is
even, so `4 * M₀ + 1 < 2 ^ w`. -/
theorem dryParam_depth_lt_two_pow (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J _hw =>
      Expander.chosenL (max (solverConnectedAugmented J).m
          (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2) <
        2 ^ dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source := by
  intro source J hJn hJm hCost hCap hw
  obtain ⟨hw14, -, -, -, -, -, -, -, -, -, -, -, hNW, -⟩ :=
    dryParam_outputs_lt_two_pow B hB source J hJn hJm hCost hCap hw
  have hscalars := concreteCfg_scalars_eq dryWitnessUsed (solverConnectedAugmented J).m
    (solverPenalty J.m)
  have hM0 : (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ =
      max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) :=
    hscalars.1
  have hN0 : (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ =
      paramN0 (concreteEdgeThresholdWithLast dryWitnessUsed) (solverConnectedAugmented J).m :=
    hscalars.2.1
  have h1 := chosenL_sq_le_four_mul_add_one
    ((concreteCirculationCfgWithLast dryWitnessUsed J).P.hM₀.trans hM0.le)
  have h2 : 4 * max (solverConnectedAugmented J).m (concreteEdgeThresholdWithLast dryWitnessUsed) <
      2 ^ dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source :=
    lt_of_eq_left hN0 hNW
  have h3 : 2 ^ dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source =
      2 * 2 ^ (dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source - 1) := by
    rw [← pow_succ']; congr 1
  omega

/-- **Main theorem (Step 4)**: for any `Psc : DrySparseCorePieces`, `openInner : SolverInnerOpen`,
and inner bounds `(B, hB)`, if `dryParamProcs` is placed at `dryParamSetupProc Psc.sc openInner`
inside `dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode`, then the exact
`DrySCInitBridgeHyps.hParam` obligation holds unconditionally with space `dryParamSpace` and
polylogarithmic cost `dryParamCost`. -/
theorem dryParamSetup_discharges_hParam
    (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (hPlace : (dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode).HasAt
      (dryParamSetupProc Psc.sc openInner)
      (dryParamProcs (dryParamSetupProc Psc.sc openInner))) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source
      let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
      MeetsContract w p (dryParamSetupProc Psc.sc openInner)
        (initParamSetupContract w I.m V F.limbs F.fmt.precision cfg.P.d cfg.P.k
          ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10) cfg.N₀
          (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2))
          (levelM cfg.TP cfg.P) (dryParamSpace source J) (dryParamCost source J)) := by
  intro source J hJn hJm hCost hCap hw I V k F cfg w p
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let b := dryParamSetupProc Psc.sc openInner
  have hPlace' : p.HasAt b (wireParamModule b threshold A dryDecompK dryDecompThr dryWitnessDen
      sparsifyPathDSUsed.boundsProcs dryParamLookupEntries) := hPlace
  obtain ⟨hw14, h220000W, hmW, hVW, hthrW, hM0_2W, halphaScaleW,
      hdW, hbrW, hpsiW, hqW, hepsW, hNW, hlvlW⟩ :=
    dryParam_outputs_lt_two_pow B hB source J hJn hJm hCost hCap hw
  have hscalars := concreteCfg_scalars_eq dryWitnessUsed I.m V
  have hM0_eq : cfg.P.M₀ = max I.m threshold := hscalars.1
  have hN0_eq : cfg.N₀ = paramN0 threshold I.m := hscalars.2.1
  have hPsi_eq : ⌈cfg.Ψ⌉₊ = paramPsi threshold A I.m V := hscalars.2.2.1
  have hM01 : 1 ≤ max I.m threshold := cfg.P.hM₀.trans hM0_eq.le
  have hP_eq : cfg.P = Chain.concreteChainParams (max I.m threshold) hM01 :=
    concreteCfgWithLast_P_eq dryWitnessUsed J hM01
  have hdLe : cfg.P.d ≤ (max I.m threshold + 2).size :=
    (chosenD_le_size_add_two cfg.P.hM₀).trans (congrArg (fun M => (M + 2).size) hM0_eq).le
  have hw2 : 2 < 2 ^ w := by
    have h1 : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hSpaceEq : dryParamSpace source J =
      wireParamSpace dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
        (max I.m threshold) :=
    congrArg (wireParamSpace dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params) hM0_eq
  by_cases hlt : I.m < dryLevelMCut
  · -- Small-input branch: finite table lookup
    have hCostEq : dryParamCost source J =
        wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
          dryParamLookupEntries I.m V (max I.m threshold) cfg.P.d
          (Expander.chosenL (max I.m threshold ^ 2)) :=
      congrArg (fun M => wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
        dryParamLookupEntries I.m V M cfg.P.d (Expander.chosenL (M ^ 2))) hM0_eq
    have hJm_le_Im : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm (fun e => (hCap e).1)).1
    have hRow := dryParamRow_eq_cfg J
    have hdepW : Expander.chosenL (max I.m threshold ^ 2) < 2 ^ w :=
      dryParam_depth_lt_two_pow B hB source J hJn hJm hCost hCap hw
    have hmem : (I.m, V, [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, k, k + Num.IPM.alphaExponent I.m V + 10, cfg.N₀] ++
        (List.range cfg.P.d).map (levelM cfg.TP cfg.P) ++
        [Expander.chosenL (max I.m threshold ^ 2)]) ∈ dryParamLookupEntries := by
      unfold dryParamLookupEntries
      refine List.mem_flatMap.mpr ⟨I.m, List.mem_range.mpr hlt, ?_⟩
      refine List.mem_map.mpr ⟨J.m - 1, List.mem_range.mpr (by omega), ?_⟩
      have hpen : solverPenalty (J.m - 1 + 1) = V :=
        congrArg solverPenalty (by omega : J.m - 1 + 1 = J.m)
      exact Prod.ext rfl (Prod.ext hpen ((congrArg (dryParamRow I.m) hpen).trans hRow))
    have huniq : ∀ e ∈ dryParamLookupEntries, e.1 = I.m → e.2.1 = V →
        e.2.2 = [cfg.P.d, cfg.P.k, ⌈cfg.Ψ⌉₊, k, k + Num.IPM.alphaExponent I.m V + 10, cfg.N₀] ++
          (List.range cfg.P.d).map (levelM cfg.TP cfg.P) ++
          [Expander.chosenL (max I.m threshold ^ 2)] := by
      intro e he h1 h2
      unfold dryParamLookupEntries at he
      obtain ⟨m', _, he'⟩ := List.mem_flatMap.mp he
      obtain ⟨j', _, rfl⟩ := List.mem_map.mp he'
      dsimp only at h1 h2 ⊢
      exact (congrArg₂ dryParamRow h1 h2).trans hRow
    exact initParamSetupContract_congr rfl rfl rfl rfl rfl rfl hSpaceEq hCostEq
      (wireParamModule_meetsContract_hit hPlace' hM01 hdLe hw2 hmW hVW
        hdW hbrW hpsiW hqW hepsW hNW hlvlW hdepW hmem huniq)
  · -- General branch: `dryLevelMCut ≤ I.m`
    have hge : dryLevelMCut ≤ I.m := Nat.le_of_not_lt hlt
    have hmiss : ∀ e ∈ dryParamLookupEntries, I.m ≠ e.1 ∨ V ≠ e.2.1 := by
      intro e he
      unfold dryParamLookupEntries at he
      obtain ⟨m', hm', he'⟩ := List.mem_flatMap.mp he
      obtain ⟨j', _, rfl⟩ := List.mem_map.mp he'
      have hm'_lt : m' < dryLevelMCut := List.mem_range.mp hm'
      exact Or.inl (by omega)
    have hMcutSpec := Classical.choose_spec exists_dryLevelM_threshold
    obtain ⟨_, _, hlvlM_eq, _, _⟩ := hMcutSpec.2 J hJn hJm (fun e => (hCap e).1) hge
    obtain ⟨h4M2W, hcubeW, hdenW, hcapW, hwitW, hcw1, hcw2, hnumW⟩ :=
      dryParam_general_word_bounds B hB source J hJn hJm hCost hCap hw hge
    have hk_eq : k = paramQuality threshold A I.m := rfl
    have heps_eq : k + Num.IPM.alphaExponent I.m V + 10 = paramEpsExp threshold A I.m V := rfl
    have hd_eq : cfg.P.d = (Chain.concreteChainParams (max I.m threshold) hM01).d :=
      congrArg ChainParams.d hP_eq
    have hbr_eq : cfg.P.k = (Chain.concreteChainParams (max I.m threshold) hM01).k :=
      congrArg ChainParams.k hP_eq
    have hCostEq : dryParamCost source J =
        wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
          dryParamLookupEntries I.m V (max I.m threshold)
          (Chain.concreteChainParams (max I.m threshold) hM01).d
          (Expander.chosenL (max I.m threshold ^ 2)) := by
      have h1 : dryParamCost source J =
          wireParamCost dryDecompK dryDecompThr dryWitnessDen sparsifyPathDSUsed.params
            dryParamLookupEntries I.m V (max I.m threshold) cfg.P.d
            (Expander.chosenL (max I.m threshold ^ 2)) :=
        congrArg (fun M => wireParamCost dryDecompK dryDecompThr dryWitnessDen
          sparsifyPathDSUsed.params dryParamLookupEntries I.m V M cfg.P.d
          (Expander.chosenL (M ^ 2))) hM0_eq
      exact h1.trans (congrArg (fun d => wireParamCost dryDecompK dryDecompThr dryWitnessDen
        sparsifyPathDSUsed.params dryParamLookupEntries I.m V (max I.m threshold) d
        (Expander.chosenL (max I.m threshold ^ 2))) hd_eq)
    have hM0_2W' : max I.m threshold + 2 < 2 ^ w :=
      lt_of_eq_left (congrArg (· + 2) hM0_eq) hM0_2W
    have hN0W' : 4 * max I.m threshold < 2 ^ w :=
      lt_of_eq_left hN0_eq hNW
    have hpsiW' : paramPsi threshold A I.m V < 2 ^ w :=
      lt_of_eq_left hPsi_eq hpsiW
    have h4M2W' : 4 * max I.m threshold ^ 2 + 2 < 2 ^ w :=
      lt_of_eq_left (congrArg (fun M => 4 * M ^ 2 + 2) hM0_eq) h4M2W
    have hcubeW' : (Nat.log 2 (4 * max I.m threshold ^ 2 + 2) + 2) ^ 3 < 2 ^ w :=
      lt_of_eq_left (congrArg (fun M => (Nat.log 2 (4 * M ^ 2 + 2) + 2) ^ 3) hM0_eq) hcubeW
    have hdenW' : drySparsifyDen (max I.m threshold) < 2 ^ w :=
      lt_of_eq_left (congrArg drySparsifyDen hM0_eq) hdenW
    have hcapW' : drySparsifyCap (max I.m threshold) < 2 ^ w :=
      lt_of_eq_left (congrArg drySparsifyCap hM0_eq) hcapW
    have hcw1' : sparsifyPathDSUsed.params.cw *
        (Nat.log 2 (drySparsifyDen (max I.m threshold) + max I.m threshold ^ 2 +
          sparsifyPathDSUsed.params.gExp (drySparsifyDen (max I.m threshold)) (max I.m threshold ^ 2) +
          sparsifyPathDSUsed.params.gDel (drySparsifyDen (max I.m threshold)) (max I.m threshold ^ 2) + 2) + 1) ≤ w :=
      le_of_eq_left (congrArg (fun M => sparsifyPathDSUsed.params.cw *
        (Nat.log 2 (drySparsifyDen M + M ^ 2 +
          sparsifyPathDSUsed.params.gExp (drySparsifyDen M) (M ^ 2) +
          sparsifyPathDSUsed.params.gDel (drySparsifyDen M) (M ^ 2) + 2) + 1)) hM0_eq) hcw1
    have hcw2' : sparsifyPathDSUsed.params.cw *
        (Nat.log 2 (dryWitnessDen + drySparsifyCap (max I.m threshold) +
          sparsifyPathDSUsed.params.gExp dryWitnessDen (drySparsifyCap (max I.m threshold)) +
          sparsifyPathDSUsed.params.gDel dryWitnessDen (drySparsifyCap (max I.m threshold)) + 2) + 1) ≤ w :=
      le_of_eq_left (congrArg (fun M => sparsifyPathDSUsed.params.cw *
        (Nat.log 2 (dryWitnessDen + drySparsifyCap M +
          sparsifyPathDSUsed.params.gExp dryWitnessDen (drySparsifyCap M) +
          sparsifyPathDSUsed.params.gDel dryWitnessDen (drySparsifyCap M) + 2) + 1)) hM0_eq) hcw2
    have hnumW' : ∀ i < (Chain.concreteChainParams (max I.m threshold) hM01).d,
        let M₀ := max I.m threshold
        let C := Chain.concreteChainParams M₀ hM01
        let L_sp := Expander.chosenL (M₀ ^ 2)
        let den := Expander.maxPhiDenOf dryDecompK dryDecompThr (M₀ ^ 2)
        let cap := 36 * M₀ ^ 2 * den + 1
        let g := (max (sparsifyPathDSUsed.params.gExp den (M₀ ^ 2))
          (sparsifyPathDSUsed.params.gExp dryWitnessDen cap)) ^ 2
        let γ := 3 ^ L_sp * g ^ (L_sp + 1)
        M₀ * γ ^ (i + 1) + C.k ^ i < 2 ^ w := fun i hi =>
      lt_of_eq_left
        (congrArg₂ (· + ·)
          (congrArg (fun M => M * (dryGammaNat M) ^ (i + 1)) hM0_eq)
          (congrArg (fun k => k ^ i) hbr_eq))
        (hnumW i (lt_of_lt_of_eq hi hd_eq.symm))
    have hlvlM' : ∀ i < (Chain.concreteChainParams (max I.m threshold) hM01).d,
        let M₀ := max I.m threshold
        let C := Chain.concreteChainParams M₀ hM01
        let L_sp := Expander.chosenL (M₀ ^ 2)
        let den := Expander.maxPhiDenOf dryDecompK dryDecompThr (M₀ ^ 2)
        let cap := 36 * M₀ ^ 2 * den + 1
        let g := (max (sparsifyPathDSUsed.params.gExp den (M₀ ^ 2))
          (sparsifyPathDSUsed.params.gExp dryWitnessDen cap)) ^ 2
        let γ := 3 ^ L_sp * g ^ (L_sp + 1)
        levelM cfg.TP cfg.P i = (M₀ * γ ^ (i + 1) + C.k ^ i - 1) / C.k ^ i := fun i _ =>
      (hlvlM_eq i).trans
        (congrArg₂ (fun a b => (a + b - 1) / b)
          (congrArg (fun M => M * (dryGammaNat M) ^ (i + 1)) hM0_eq)
          (congrArg (fun k => k ^ i) hbr_eq))
    exact initParamSetupContract_congr hd_eq hbr_eq hPsi_eq hk_eq heps_eq hN0_eq hSpaceEq hCostEq
      (wireParamModule_meetsContract_general hPlace'
        (fun hAt => sparsifyPathDSUsed.boundsSpec w p (b + wireParamBoundsOff) hAt)
        one_le_dryDecompK one_le_dryWitnessDen hM01 hw14 h220000W hmiss
        hmW hVW hthrW hM0_2W' hN0W' hqW halphaScaleW hepsW hpsiW'
        h4M2W' hcubeW' hdenW' hcapW' hwitW hcw1' hcw2' hnumW' hlvlM')

end MinCostFlow.Final.DryRun

end
