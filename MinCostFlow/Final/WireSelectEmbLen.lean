module

public import MinCostFlow.Final.AssemblyDryRunSCDeepFacts
public import MinCostFlow.Final.CappedQuality
public import MinCostFlow.MinRatio.OrdSolverRateBounds
public import MinCostFlow.MinRatio.OrdSolverReached

import Mathlib.Tactic

/-!
# Concrete `SubpolyNat` embedding-length bounds for `dryWitnessUsed` (`WireSelectEmbLen`)

Proves the concrete embedding-length, route-size, and stride bounds for the dry-run witness
`dryWitnessUsed` (`Final/AssemblyDryRun.lean`):

1. `dryMaxEmbLen m := 2 ^ cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
   (concreteQualityBudgetWithLast dryWitnessUsed) m`, together with:
   * `dryMaxEdges m := dryMaxEmbLen m + 1`,
   * `dryMaxPaths m := 2 * dryMaxEdges m`,
   * `drySlot m := 1 + 2 * dryMaxEmbLen m`.
2. `dryWitnessUsed_gammaEll_le_two_pow_k`: from `1 / 2 ^ k ≤ alg2KappaOwn`, the concrete
   sparsifier stretch `cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)` lies below `(2 : ℝ) ^ k`.
3. `progTool_embLen_le_dryMaxEmbLen_of_holds`, `progTool_embLen_le_dryMaxEmbLen_of_shiftLoop`,
   and `progTool_embLen_le_dryMaxEmbLen_of_reachedInv`: on every `ShiftLoopChainInv` and
   `OrdSolverReachedInv` state of `dryWitnessUsed`, every active core edge `e ∈ (C.activeCore i).E`
   (`i < cfg.P.d`) has `(C.activeEmb i e).length ≤ dryMaxEmbLen I.m` (and hence
   `(C.activeEmb i e).length + 1 ≤ dryMaxEdges I.m`).
4. `progTool_embLen_le_subpoly`: `SubpolyNat` for `dryMaxEmbLen`, `dryMaxEdges`, `dryMaxPaths`,
   and `drySlot` (from `cappedQuality_subpolynomial`).
5. `dryMaxEdges_add_maxPaths_lt`: `dryMaxEdges I.m + dryMaxPaths I.m < 2 ^ (3 * E + 20)`,
   directly matching clause 6 of `DryCapSimpleBounds` (`AssemblyDryRunSCEnvelope.lean`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling Scaling.Machine
  MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete `SubpolyNat` embedding-length, edge-route, path-route, and slot bounds -/

/-- Concrete upper bound on embedding walk length `(C.activeEmb i e).length` for `dryWitnessUsed`
as a function of the augmented edge count `m = I.m`. -/
def dryMaxEmbLen (m : ℕ) : ℕ :=
  2 ^ cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) m

/-- Concrete `maxEdges = maxEmbLen + 1` bound for `Select` / `FindCycle`. -/
def dryMaxEdges (m : ℕ) : ℕ :=
  dryMaxEmbLen m + 1

/-- Concrete `maxPaths = 2 * maxEdges` bound for `Select` / `FindCycle`. -/
def dryMaxPaths (m : ℕ) : ℕ :=
  2 * dryMaxEdges m

/-- Concrete `slot = 1 + 2 * maxEmbLen` word stride for `MEmbAt` in `SelectLevelBlocks`. -/
def drySlot (m : ℕ) : ℕ :=
  1 + 2 * dryMaxEmbLen m

theorem dryMaxEmbLen_subpoly : SubpolyNat dryMaxEmbLen := by
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  have hls1 : 1 ≤ logScale ((threshold : ℝ) + 1) :=
    logScale_one_le (by linarith [Nat.cast_nonneg (α := ℝ) threshold])
  have hls2 : 1 ≤ logScale (logScale ((threshold : ℝ) + 1)) :=
    logScale_one_le hls1
  have hls1_nn : 0 ≤ logScale ((threshold : ℝ) + 1) := le_trans zero_le_one hls1
  have hls2_nn : 0 ≤ logScale (logScale ((threshold : ℝ) + 1)) := le_trans zero_le_one hls2
  refine ⟨1, 65536 * ((A : ℝ) + 1) * (logScale ((threshold : ℝ) + 1)) ^ (47 / 48 : ℝ) *
    logScale (logScale ((threshold : ℝ) + 1)), by positivity, fun m => ?_⟩
  rw [one_mul]
  simpa [dryMaxEmbLen, threshold, A] using cappedQuality_subpolynomial threshold A m

/-- **`SubpolyNat` bounds on `dryMaxEmbLen`, `dryMaxEdges`, `dryMaxPaths`, and `drySlot`.** -/
theorem progTool_embLen_le_subpoly :
    SubpolyNat dryMaxEmbLen ∧
    SubpolyNat dryMaxEdges ∧
    SubpolyNat dryMaxPaths ∧
    SubpolyNat drySlot := by
  have hEmb := dryMaxEmbLen_subpoly
  have hEdges : SubpolyNat dryMaxEdges := hEmb.add_const 1
  have hPaths : SubpolyNat dryMaxPaths := hEdges.const_mul 2
  have hSlot : SubpolyNat drySlot := (SubpolyNat.const 1).add (hEmb.const_mul 2)
  exact ⟨hEmb, hEdges, hPaths, hSlot⟩

/-! ## 2. `cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ (2 : ℝ) ^ k` and `maxEdges + maxPaths < 2 ^ (3 * E + 20)` -/

/-- From `1 / 2 ^ k ≤ alg2KappaOwn`, the concrete sparse-core embedding length factor
`cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)` is bounded by `(dryMaxEmbLen I.m : ℝ)`. -/
theorem dryWitnessUsed_gammaEll_le_dryMaxEmbLen
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ (dryMaxEmbLen I.m : ℝ) := by
  intro I cfg
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let k := cappedQualityExponent threshold A I.m
  let V := solverPenalty J.m
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans
      ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, -⟩ :=
    concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
      (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  obtain ⟨⟨hκ_pos, hKappa⟩, _⟩ :=
    dryWitnessUsed.specWith (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) M₀ N₀ α Ψ ε
      hM₀1 hThresh hN₀ hPsi hα
  have hAge : 15 + 5 * dryWitnessUsed.C_γ ≤ (A : ℝ) := Nat.le_ceil _
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A hAge M₀ hKappa
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  set σ_tot := alg2SigmaTotOwn cfg.TP cfg.LP cfg.P cfg.N₀
  set σ_mwu_max := alg2SigmaGame cfg.σ_mwu cfg.N₀
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hVcfg.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hσ_mwu_nn : 0 ≤ σ_mwu_max := le_max_left 0 _
  have hbase_ge : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max) := by nlinarith
  have hbase_ge1 : 1 ≤ 2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max) := by nlinarith
  have hd1 : 1 ≤ cfg.P.d := cfg.P.hd
  have hpow_ge : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d := by
    calc cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)
        ≤ 2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max) := hbase_ge
      _ = (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ 1 := (pow_one _).symm
      _ ≤ (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d :=
          pow_le_pow_right₀ hbase_ge1 hd1
  have hσ_tot_nn : 0 ≤ σ_tot := by
    unfold σ_tot alg2SigmaTotOwn alg2SigmaTotAt
    exact le_trans zero_le_one ((hVcfg.hLP.1 _).trans (le_max_right _ _))
  have hd_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) := by
    have : (0 : ℝ) ≤ cfg.P.d := Nat.cast_nonneg _
    nlinarith
  have hdenom_ge : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      (σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d) := by
    have h1 : 1 ≤ (σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3)) := by nlinarith
    have hpow_nn : 0 ≤ (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d := by
      positivity
    calc cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)
        ≤ 1 * (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d := by linarith
      _ ≤ ((σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3))) *
            (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d :=
          mul_le_mul_of_nonneg_right h1 hpow_nn
      _ = (σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
            (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d) := by ring
  have hinv : (σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
      (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d) ≤ (2 : ℝ) ^ k := by
    have hκ_eq : alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ =
        1 / ((σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
          (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d)) := rfl
    have hκ_pos' : 0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := hκ_pos
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have h1 : 1 / alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ (2 : ℝ) ^ k := by
      rw [div_le_iff₀ hκ_pos']
      have h2 := (div_le_iff₀ h2k_pos).mp hk_le_κ
      linarith
    rwa [hκ_eq, one_div_one_div] at h1
  simpa [dryMaxEmbLen, k, threshold, A] using hdenom_ge.trans hinv

/-- Clause 6 of `DryCapSimpleBounds` for `dryMaxEdges` and `dryMaxPaths`:
`dryMaxEdges I.m + dryMaxPaths I.m < 2 ^ (3 * E + 20)`. -/
theorem dryMaxEdges_add_maxPaths_lt (J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let E := ipmQualityRangeExponent I.m V k
    dryMaxEdges I.m + dryMaxPaths I.m < 2 ^ (3 * E + 20) := by
  intro I V k E
  have hkE : k ≤ E := by
    dsimp only [E, ipmQualityRangeExponent, qualitySlackExponent]
    omega
  have h2k1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have hsum : dryMaxEdges I.m + dryMaxPaths I.m = 3 * 2 ^ k + 3 := by
    simp only [dryMaxPaths, dryMaxEdges, dryMaxEmbLen, k]; omega
  rw [hsum]
  have h1 : 3 * 2 ^ k + 3 < 2 ^ (k + 3) := by
    rw [pow_add]; norm_num; omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (by omega))

/-! ## 3. Embedding-length bounds on reached states of `dryWitnessUsed` -/

/-- From `TreeChain.Holds`, every active core edge `e` at level `i < C.d` has embedding length
`≤ ⌊γ_ℓ⌋₊` (or any `M : ℕ` with `γ_ℓ ≤ M`). -/
theorem embLen_le_of_holds {C : TreeChain} {G : MGraph} {ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {M : ℕ} (hM : γ_ℓ ≤ (M : ℝ)) :
    ∀ i < C.d, ∀ e ∈ (C.activeCore i).E, (C.activeEmb i e).length ≤ M := by
  intro i hi e he
  have hSp := C.activeS_isSparsified hH hi
  have hSup : (C.activeEmb i e).length ≤ (C.activeEmb i).length (C.activeCore i) :=
    Finset.le_sup (f := fun x => (C.activeEmb i x).length) he
  have hReal : ((C.activeEmb i e).length : ℝ) ≤ (M : ℝ) :=
    (Nat.cast_le.mpr hSup).trans (hSp.2.2.2.1.trans hM)
  exact_mod_cast hReal

/-- **Embedding-length bound on `ShiftLoopChainInv` for `dryWitnessUsed`:**
every active core edge `e` at level `i < cfg.P.d` has
`(C.activeEmb i e).length ≤ dryMaxEmbLen I.m` and
`(C.activeEmb i e).length + 1 ≤ dryMaxEdges I.m`. -/
theorem progTool_embLen_le_dryMaxEmbLen_of_shiftLoop
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {ch : ChainState (concreteCirculationCfgWithLast dryWitnessUsed J).T
      (concreteCirculationCfgWithLast dryWitnessUsed J).P}
    (hShift : Ordered.ShiftLoopChainInv (concreteCirculationCfgWithLast dryWitnessUsed J) ch) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ i < cfg.P.d, ∀ e ∈ (ch.toTreeChain.activeCore i).E,
      (ch.toTreeChain.activeEmb i e).length ≤ dryMaxEmbLen I.m ∧
      (ch.toTreeChain.activeEmb i e).length + 1 ≤ dryMaxEdges I.m := by
  intro I cfg i hi e he
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hH := (hShift.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hγ := dryWitnessUsed_gammaEll_le_dryMaxEmbLen J hJn hJm hCap
  have hle := embLen_le_of_holds hH hγ i hi e he
  exact ⟨hle, Nat.succ_le_succ hle⟩

/-- **Embedding-length bound on `OrdSolverReachedInv` for `dryWitnessUsed`:**
on every reached solver state `model`, every active core edge `e` at level `i < cfg.P.d` has
`(C.activeEmb i e).length ≤ dryMaxEmbLen I.m` and
`(C.activeEmb i e).length + 1 ≤ dryMaxEdges I.m`. -/
theorem progTool_embLen_le_dryMaxEmbLen_of_reachedInv
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {κ : ℝ} {G : MGraph} {P : ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J) L Rcore}
    (hm : G.m ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀)
    (hn : G.n ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)
    (h : OrdSolverReachedInv κ G P model tok) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ i < cfg.P.d, ∀ e ∈ (model.chain.toTreeChain.activeCore i).E,
      (model.chain.toTreeChain.activeEmb i e).length ≤ dryMaxEmbLen I.m ∧
      (model.chain.toTreeChain.activeEmb i e).length + 1 ≤ dryMaxEdges I.m := by
  intro I cfg i hi e he
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := h.2.1
  have hUncond := (Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdgeD hLenD
    (fun t ht => by rw [hGD t ht]; exact hm) (fun t ht => by rw [hGD t ht]; exact hn)).1 T_step le_rfl
  rw [← hEq] at hUncond
  have hInv := hUncond.1
  have hH := (hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hγ := dryWitnessUsed_gammaEll_le_dryMaxEmbLen J hJn hJm hCap
  have hle := embLen_le_of_holds hH hγ i hi e he
  exact ⟨hle, Nat.succ_le_succ hle⟩

end MinCostFlow.Final.DryRun
