module

public import MinCostFlow.MinRatio.ShiftQuotaBounds
public import MinCostFlow.MinRatio.OrdSolverReached
public import MinCostFlow.MinRatio.UpdateAssemblyBase
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Reached-state shift-quota word-size discharge (`MinRatioDetectedWith.stages_le`)

Links the stage bound `T ≤ 2 * G.m` of `MinRatioDetectedWith.stages_le`
(`IPM/Machine/MinRatioContract.lean`) to the polynomial shift-quota bounds and word-size discharge
of `MinRatio/ShiftQuotaBounds.lean`:

1. `concrete_m_le_iterationLimit`: for the connected augmented instance `I = solverConnectedAugmented J`
   and penalty `V = solverPenalty J.m`, `I.m ≤ IPM.iterationLimit I V (1 / 2 ^ k)`, so
   `2 * (namedInstance I).m + 1 ≤ 2 * IPM.iterationLimit I V (1 / 2 ^ k) + 1`.
2. `minRatioState_eraseFailure_eq_failState`, `alg2PreLoopState_sum_rebuildCount_le`,
   `detectedWith_preLoop_sum_rebuildCount_le`, `detectedWith_preLoop_shiftQuota_le`:
   for any state `model` satisfying `MinRatioDetectedWith` on `G`, the pre-loop state
   `model1 = alg2PreLoopState cfg model U gVec lVec` satisfies
   `∑ j ≤ d, model1.chain.rebuildCount j ≤ 2 * G.m + 1`, and hence every shift quota satisfies
   `shiftQuotaWord ... model1.chain.rebuildCount i ≤ (2 * G.m + 2) * shiftQuotaBase ^ (d + 1)`.
3. `concrete_quotaBound_lt_two_pow_wordSize` and `concrete_detectedWith_shiftQuota_lt_two_pow_wordSize`:
   for every chain witness `W`, there is a constant `C_q` depending only on `W` such that
   whenever `C_q ≤ allocationCoefficient`, the static bound `(2 * (namedInstance I).m + 2) *
   shiftQuotaBase ^ (d + 1)`, the pass limit `⌈2 * alg2PsiGame ...⌉₊`, and every reached pre-loop
   `shiftQuotaWord` fit strictly below `2 ^ w` at the final solver word size.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM IPM.Machine Scaling Final

/-! ## 1. `I.m ≤ IPM.iterationLimit I V (1 / 2 ^ k)` for concrete circulations -/

/-- For every valid circulation `J`, the augmented edge count `I.m` is bounded by the IPM
iteration limit `IPM.iterationLimit I V (1 / 2 ^ k)`. -/
theorem concrete_m_le_iterationLimit (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) (k : ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    I.m ≤ IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) := by
  dsimp only
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  have hImGe : 1 ≤ I.m := le_trans hJm (solverConnectedAugmented_size J hJn hJm hCap).1
  have hVGe : 16 ≤ V := by
    unfold V solverPenalty solverCapacityBound
    have h2 : 2 ≤ max 2 (J.m ^ 40) := le_max_left _ _
    have hsq : 4 ≤ (max 2 (J.m ^ 40)) ^ 2 := by nlinarith
    nlinarith
  have hIV : Real.exp 1 ≤ (I.m : ℝ) * (V : ℝ) := by
    have h1 : (1 : ℝ) ≤ (I.m : ℝ) := by exact_mod_cast hImGe
    have h2 : (16 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hVGe
    have he : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    nlinarith
  have hlog : (1 : ℝ) ≤ Real.log ((I.m : ℝ) * (V : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hIV
    rwa [Real.log_exp] at h
  have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hκpos : (0 : ℝ) < (1 / (2 : ℝ) ^ k) ^ 2 := by positivity
  have hκle : (1 / (2 : ℝ) ^ k) ^ 2 ≤ 1 := by
    have h1 : (1 : ℝ) / (2 : ℝ) ^ k ≤ 1 := div_le_one_of_le₀ h2k (by positivity)
    have h1nn : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ k := by positivity
    nlinarith
  unfold IPM.iterationLimit
  have hnum : (I.m : ℝ) ≤ 200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) := by
    have hm0 : (0 : ℝ) ≤ (I.m : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hdiv : 200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) ≤
      200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) / (1 / (2 : ℝ) ^ k) ^ 2 :=
    le_div_iff₀ hκpos |>.mpr (by
      have hnn : 0 ≤ 200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) := by positivity
      nlinarith)
  have hle : (I.m : ℝ) ≤ 200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) / (1 / (2 : ℝ) ^ k) ^ 2 :=
    hnum.trans hdiv
  have hceil : ⌈(I.m : ℝ)⌉₊ ≤ ⌈200000 * (I.m : ℝ) * Real.log ((I.m : ℝ) * (V : ℝ)) / (1 / (2 : ℝ) ^ k) ^ 2⌉₊ :=
    Nat.ceil_mono hle
  simpa using hceil

/-! ## 2. Linking `MinRatioDetectedWith.stages_le` to `alg2PreLoopState` rebuild counts -/

/-- `minRatioState` on `eraseFailure` of `Ordered.algorithm2_dsWithFailureWith` agrees identically
with `minRatioFailState` on `Ordered.algorithm2_dsWith`. -/
theorem minRatioState_eraseFailure_eq_failState (cfg : Alg2Config) (κ : ℝ)
    (D : DynamicInstance) (η : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ) :
    minRatioState (Ordered.algorithm2_dsWithFailureWith cfg κ).eraseFailure D η op T =
      minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T := by
  induction T with
  | zero => rfl
  | succ t ih =>
    rw [minRatioState, minRatioFailState.eq_2, ih]
    cases op (t + 1) <;> rfl

/-- One pre-loop chain refresh `alg2PreLoopState` increases `∑_{j ≤ d} rebuildCount j` by at most `1`. -/
theorem alg2PreLoopState_sum_rebuildCount_le (cfg : Alg2Config)
    (model : Alg2State cfg) (U : List Update) (gVec lVec : ℕ → ℝ) :
    ∑ j ∈ Finset.range (cfg.P.d + 1),
        (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount j ≤
      (∑ j ∈ Finset.range (cfg.P.d + 1), model.chain.rebuildCount j) + 1 := by
  set tb := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set ch1 := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tb.2.2.2.2
    (fun e' => gVec (tb.2.2.1 e')) (fun e' => lVec (tb.2.2.1 e'))).1
  change ∑ j ∈ Finset.range (cfg.P.d + 1), ch1.rebuildCount j ≤ _
  set G₀' := (model.chain.G 0).applyBatch tb.2.2.2.2
  set st0 : ChainState cfg.T cfg.P :=
    { model.chain with
      recUpdates := fun j => if j = 0 then model.chain.recUpdates 0 + tb.2.2.2.2.length else model.chain.recUpdates j }
  have hloopCases := Ordered.updateLoop_rebuildCount_cases cfg.T cfg.L cfg.TP cfg.P cfg.N₀
    (fun e' => lVec (tb.2.2.1 e')) (fun e' => gVec (tb.2.2.1 e')) cfg.P.d 0 st0 G₀'
    tb.2.2.2.2 ((model.chain.G 0).batchEnc tb.2.2.2.2) (by omega)
  have hch1Eq : ch1 = (Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀
      (fun e' => lVec (tb.2.2.1 e')) (fun e' => gVec (tb.2.2.1 e')) cfg.P.d 0 st0 G₀'
      tb.2.2.2.2 ((model.chain.G 0).batchEnc tb.2.2.2.2)).1 := rfl
  rcases hloopCases with heq | ⟨iStar, _, hiLt, heq⟩
  · have hrc : ch1.rebuildCount = model.chain.rebuildCount := by rw [hch1Eq]; exact heq
    rw [hrc]; omega
  · have hch1 : ch1.rebuildCount = fun j => if j = iStar then model.chain.rebuildCount iStar + 1
        else model.chain.rebuildCount j := by rw [hch1Eq]; exact heq
    rw [hch1]
    have hsumEq : ∑ j ∈ Finset.range (cfg.P.d + 1),
        (if j = iStar then model.chain.rebuildCount iStar + 1 else model.chain.rebuildCount j) =
        ∑ j ∈ Finset.range (cfg.P.d + 1),
          (model.chain.rebuildCount j + if j = iStar then 1 else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with h <;> [subst h; skip] <;> omega
    rw [hsumEq, Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (cfg.P.d + 1)) iStar]
    simp [Finset.mem_range.mpr (by omega : iStar < cfg.P.d + 1)]

/-- From `MinRatioDetectedWith` (which carries `T ≤ 2 * G.m` via `MinRatioDetectedWith.stages_le`),
the pre-loop state `alg2PreLoopState cfg model U gVec lVec` has total rebuild count at most
`2 * G.m + 1`. -/
theorem detectedWith_preLoop_sum_rebuildCount_le {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (hdet : MinRatioDetectedWith (Ordered.algorithm2_dsWithFailureWith cfg κ) G model changed g l)
    (U : List Update) (gVec lVec : ℕ → ℝ) :
    ∑ j ∈ Finset.range (cfg.P.d + 1),
        (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount j ≤ 2 * G.m + 1 := by
  obtain ⟨D, η, op, T, _, _, hmod, hT⟩ := hdet.stages_le
  have hchainEq : model.chain =
      (minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η op T).chain := by
    rw [hmod, minRatioState_eraseFailure_eq_failState]
    rfl
  have hsum0 : ∑ j ∈ Finset.range (cfg.P.d + 1), model.chain.rebuildCount j ≤ T := by
    rw [hchainEq]
    exact ordered_history_sum_rebuildCount_le cfg κ D η op T
  have hstep := alg2PreLoopState_sum_rebuildCount_le cfg model U gVec lVec
  omega

/-- From `MinRatioDetectedWith`, every pre-loop shift quota word is bounded by the static quantity
`(2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1)`. -/
theorem detectedWith_preLoop_shiftQuota_le {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} {changed : ℕ → Prop} {g l : ℕ → ℝ}
    (hdet : MinRatioDetectedWith (Ordered.algorithm2_dsWithFailureWith cfg κ) G model changed g l)
    (U : List Update) (gVec lVec : ℕ → ℝ) {i : ℕ} (hi : i ≤ cfg.P.d) :
    shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
        (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount i ≤
      (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) := by
  have hsum := detectedWith_preLoop_sum_rebuildCount_le hdet U gVec lVec
  calc shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
        (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount i
      ≤ (1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
          (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount j) *
          shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
        shiftQuotaWord_le_one_add_sum_rebuilds cfg _ hi
    _ ≤ (2 * G.m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) :=
        Nat.mul_le_mul_right _ (by omega)

/-- The static quota bound dominates the pass limit `⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊`. -/
theorem ceil_two_mul_alg2PsiGame_le_quotaBound (cfg : Alg2Config) (m : ℕ) :
    ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ ≤
      (2 * m + 2) * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) := by
  have h1 := ceil_two_mul_alg2PsiGame_le_basePow cfg
  exact h1.trans (Nat.le_mul_of_pos_left _ (by omega))

/-! ## 3. Word-size discharge for concrete circulations -/

/-- For every chain witness `W`, there is a constant `C_q` depending only on `W` such that
whenever `C_q ≤ allocationCoefficient`, the static quota bound
`(2 * (namedInstance I).m + 2) * shiftQuotaBase ^ (d + 1)` and the pass limit
`⌈2 * alg2PsiGame ...⌉₊` fit strictly below `2 ^ w` at the final solver word size. -/
theorem concrete_quotaBound_lt_two_pow_wordSize
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ C_q : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_q ≤ allocationCoefficient →
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let Ck := concreteQualityLinearCoeff threshold A
        let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        (2 * (namedInstance I).m + 2) *
            shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) < 2 ^ w ∧
        ⌈2 * alg2PsiGame cfg.Ψ cfg.P.M₀⌉₊ < 2 ^ w := by
  obtain ⟨a, ha⟩ := concrete_shiftQuotaBasePow_poly W
  refine ⟨14 * a, fun allocCoeff allocDeg hle source J hJn hJm hCap hw => ?_⟩
  set threshold := concreteEdgeThresholdWithLast W
  set A := concreteQualityBudgetWithLast W
  set Ck := concreteQualityLinearCoeff threshold A
  set deg := forestProgramsScratchDegree allocCoeff allocDeg Ck
  set I := solverConnectedAugmented J
  set V := solverPenalty J.m
  set k := cappedQualityExponent threshold A I.m
  set cfg := concreteCirculationCfgWithLast W J
  have hImLe : I.m ≤ 7 * J.m := (solverConnectedAugmented_size J hJn hJm hCap).2
  have h2m2 : 2 * (namedInstance I).m + 2 ≤ 14 * (J.m + 2) := by
    rw [namedInstance_m]; omega
  obtain ⟨hbase, _⟩ := ha J hJn hJm hCap
  have hpoly4 : (2 * (namedInstance I).m + 2) *
      shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1) ≤ (14 * a) * (J.m + 2) ^ 7 := by
    have h4 : (J.m + 2) ^ 4 ≤ (J.m + 2) ^ 7 := Nat.pow_le_pow_right (by omega) (by decide)
    calc (2 * (namedInstance I).m + 2) *
            shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (cfg.P.d + 1)
        ≤ (14 * (J.m + 2)) * (a * (J.m + 2) ^ 3) :=
          Nat.mul_le_mul h2m2 (hbase cfg.P.d le_rfl)
      _ = (14 * a) * (J.m + 2) ^ 4 := by ring
      _ ≤ (14 * a) * (J.m + 2) ^ 7 := Nat.mul_le_mul_left _ h4
  have hdeg7 := forestProgramsScratchDegree_covers_shiftQuota allocCoeff allocDeg Ck (14 * a) hle
  have hboundW := lt_two_pow_wordSize_of_poly_and_hw source J hJm (by decide) hw hpoly4 hdeg7
  exact ⟨hboundW, lt_of_le_of_lt (ceil_two_mul_alg2PsiGame_le_quotaBound cfg _) hboundW⟩

/-- Direct link from `MinRatioDetectedWith.stages_le` (`T ≤ 2 * G.m`) and
`concrete_m_le_iterationLimit` (`I.m ≤ iterationLimit`) to `concrete_shiftQuota_lt_two_pow_wordSize`:
every shift quota word of `alg2PreLoopState cfg model U gVec lVec` fits strictly below `2 ^ w`. -/
theorem concrete_detectedWith_shiftQuota_lt_two_pow_wordSize
    {lastTool : LastLevelTool} {lastConstant : ℝ}
    {lastSpec : lastTool.IsSpec (SparseCore.lastLevelParams lastConstant)}
    (W : ConcreteChainWitnessWithLast lastTool lastConstant lastSpec) :
    ∃ C_q : ℕ, ∀ (allocationCoefficient allocationDegree : ℕ),
      C_q ≤ allocationCoefficient →
      ∀ (source J : Circulation), J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) →
        let threshold := concreteEdgeThresholdWithLast W
        let A := concreteQualityBudgetWithLast W
        let Ck := concreteQualityLinearCoeff threshold A
        let deg := forestProgramsScratchDegree allocationCoefficient allocationDegree Ck
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent threshold A I.m
        let w := wordSize (scratchWordMultiplier 1 deg) source.solverWords
        let cfg := concreteCirculationCfgWithLast W J
        ipmQualityParameterWordBits I.m V k ≤ w →
        ∀ (model : Alg2State cfg) (changed : ℕ → Prop) (g l : ℕ → ℝ)
          (U : List Update) (gVec lVec : ℕ → ℝ),
          MinRatioDetectedWith (Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k))
            (namedInstance I) model changed g l →
          ∀ i ≤ cfg.P.d,
            shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount i < 2 ^ w := by
  obtain ⟨C_q, hCq⟩ := concrete_shiftQuota_lt_two_pow_wordSize W
  refine ⟨C_q, fun allocCoeff allocDeg hle source J hJn hJm hCap => ?_⟩
  dsimp only
  intro hw model changed g l U gVec lVec hdet i hi
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
  let cfg := concreteCirculationCfgWithLast W J
  obtain ⟨D, η, op, T, _, _, hmod, hT⟩ := hdet.stages_le
  have hIter := concrete_m_le_iterationLimit J hJn hJm hCap k
  have hT1 : T + 1 ≤ 2 * IPM.iterationLimit I V (1 / (2 : ℝ) ^ k) + 1 := by
    rw [namedInstance_m] at hT
    exact Nat.succ_le_succ (hT.trans (Nat.mul_le_mul_left 2 hIter))
  let D' := histSnoc D T (namedInstance I) U gVec lVec
  let η' := seqSnoc η T 0
  let op' := seqSnoc op T true
  have hqNext := (hCq allocCoeff allocDeg hle source J hJn hJm hCap hw).2.2
    D' η' op' (T + 1) (1 / (2 : ℝ) ^ k) hT1 i hi
  have hstateT1 :
      minRatioFailState (Ordered.algorithm2_dsWith cfg (1 / (2 : ℝ) ^ k)) D' η' op' (T + 1) =
        (Ordered.algorithm2_updateWith cfg (1 / (2 : ℝ) ^ k)
          (minRatioFailState (Ordered.algorithm2_dsWith cfg (1 / (2 : ℝ) ^ k)) D η op T)
          U gVec lVec 0).1 := by
    rw [minRatioFailState_snoc_succ]
    rfl
  -- `alg2PreLoopState` and `algorithm2_updateWith` have identical `chain.rebuildCount`
  have hrebEq :
      (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount =
        (minRatioFailState (Ordered.algorithm2_dsWith cfg (1 / (2 : ℝ) ^ k)) D' η' op' (T + 1)).chain.rebuildCount := by
    rw [hstateT1]
    set s0 := minRatioFailState (Ordered.algorithm2_dsWith cfg (1 / (2 : ℝ) ^ k)) D η op T
    have hmodEq : model = (algorithm2_detect cfg s0).2 := by
      rw [hmod, minRatioState_eraseFailure_eq_failState]; rfl
    have hsameFields : model.extG = s0.extG ∧ model.extToInt = s0.extToInt ∧
        model.intToExt = s0.intToExt ∧ model.nextFresh = s0.nextFresh ∧
        model.chain = s0.chain := by
      rw [hmodEq]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    set tb := translateBatch s0.extG s0.extToInt s0.intToExt s0.nextFresh U
    set ch1 := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ s0.chain tb.2.2.2.2
      (fun e' => gVec (tb.2.2.1 e')) (fun e' => lVec (tb.2.2.1 e'))).1
    have hpreEq : (alg2PreLoopState cfg model U gVec lVec).chain = ch1 := by
      dsimp only [alg2PreLoopState]
      rw [hsameFields.1, hsameFields.2.1, hsameFields.2.2.1, hsameFields.2.2.2.1, hsameFields.2.2.2.2]
    rw [hpreEq]
    set ren := Ordered.level0Rebuilt cfg.P.d s0.chain.rebuildCount ch1.rebuildCount
    set G₀' := (s0.chain.G 0).applyBatch tb.2.2.2.2
    set bp1 := match firstRebuiltLevel cfg.P.d s0.chain.rebuildCount ch1.rebuildCount with
      | none => (s0.branD, s0.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else s0.passes j)
    set lp := Ordered.algorithm2_loopWith cfg (1 / (2 : ℝ) ^ k) tb.1 (Ordered.level0E2I ren G₀' tb.2.1)
      gVec lVec ch1 bp1.1 bp1.2 (s0.lctUpdateOps + U.length)
    have hloopReb : lp.1.rebuildCount = ch1.rebuildCount :=
      (algorithm2_loopWith_updCount_le cfg (1 / (2 : ℝ) ^ k) tb.1
        (Ordered.level0E2I ren G₀' tb.2.1) gVec lVec
        (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1) ch1 bp1.1 bp1.2
        (s0.lctUpdateOps + U.length) le_rfl).1
    have hcases := Ordered.algorithm2_updateWith_eq_of_loop (1 / (2 : ℝ) ^ k) s0 U gVec lVec 0
    cases hlp : lp.2.2.2.2 with
    | none => rw [hcases.1 hlp]; exact hloopReb.symm
    | some Δ => rw [hcases.2 Δ hlp]; exact hloopReb.symm
  change shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
    (alg2PreLoopState cfg model U gVec lVec).chain.rebuildCount i < _
  rw [hrebEq]
  exact hqNext

end MinCostFlow.MinRatio
