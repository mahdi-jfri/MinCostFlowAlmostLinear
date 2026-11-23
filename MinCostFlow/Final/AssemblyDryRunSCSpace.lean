module

public import MinCostFlow.Final.AssemblyDryRunSCInitSpace
public import MinCostFlow.MinRatio.WireShiftDeepCostKFBL
import Mathlib.Tactic

/-!
# Polynomial size-parameter, op-1 restart, and op-0 update space bounds (`AssemblyDryRunSCSpace`)

Establishes the polynomial space bounds enabled by parameterizing `asmTopAlloc` by the logical size
parameter `drySCSizeParam J` (`Final/AssemblyDryRunSCSizeParam.lean`):

1. **`PolyNat` closure under `PolyBound.eval`** (`polyNat_pow`, `polyNat_comp_polyBound`).
2. **Polynomial bound on `drySCSizeParam J`** (`drySCSizeParamBound`, `drySCSizeParam_le_bound`,
   `drySCSizeParamBound_poly`): `drySCSizeParam J ≤ drySCSizeParamBound I.m` for every valid
   circulation `J`, with `PolyNat drySCSizeParamBound`.
3. **Heap-independent op-1 and op-0 bounds** (`drySCOp1Poly`, `drySCAlloc_op1_le_poly`,
   `drySCOp0Poly`, `drySCAlloc_op0_le_poly`) extracted from `drySCAllocAt_updateRestartBound`.
4. **Solver-side `DeepShiftOpsHypKFBL.restartSpaceDom` discharge** (`dryDeepRestartSpace`,
   `drySC_restartSpaceDom`, `dryDeepRestartSpaceBound`, `dryDeepRestartSpace_le_bound`,
   `dryDeepRestartSpaceBound_poly`): proves `DeepShiftOpsHypKFBL.restartSpaceDom` at
   `dryDeepRestartSpace Psc J`, bounded by `dryDeepRestartSpaceBound Psc I.m` with
   `PolyNat (dryDeepRestartSpaceBound Psc)`.
5. **Heap-free `PolyNat` op-0 (`update`) space bound for `OrdChainUpdateCoreSpecW`**
   (`drySCOp0Bound`, `drySCAlloc_op0_le_bound`, `drySCOp0Bound_mono`, `drySCOp0Bound_poly`):
   bounds op-0 allocation independently of `heap` and all pointer arguments by a monotone
   `PolyBound` evaluated at `drySCSizeParamBound I.m + words + editWords`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. `PolyNat` closure under powers and `PolyBound.eval` -/

/-- `PolyNat` is closed under fixed natural-number powers. -/
theorem polyNat_pow {f : ℕ → ℕ} (hf : PolyNat f) : ∀ d : ℕ, PolyNat (fun M => (f M) ^ d)
  | 0 => by simpa using PolyNat.const 1
  | d + 1 => by
      simpa [pow_succ] using (polyNat_pow hf d).mul hf

/-- Composing a fixed `PolyBound` with a `PolyNat` function remains `PolyNat`. -/
theorem polyNat_comp_polyBound {f : ℕ → ℕ} (hf : PolyNat f) (P : PolyBound) :
    PolyNat (fun M => P.eval (f M)) := by
  unfold PolyBound.eval
  exact (PolyNat.const P.coeff).mul (polyNat_pow (hf.add (PolyNat.const 2)) P.deg)

/-! ## 2. `drySCSizeParam J` is bounded by a `PolyNat` function of `I.m` -/

private lemma nat_size_le_self (n : ℕ) : n.size ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

private lemma two_pow_size_le_two_mul {n : ℕ} (hn : 1 ≤ n) : 2 ^ n.size ≤ 2 * n := by
  have hpos : 1 ≤ n.size := Nat.size_pos.mpr (by omega)
  have hprev : 2 ^ (n.size - 1) ≤ n := by
    by_contra h
    have hlt : n < 2 ^ (n.size - 1) := Nat.lt_of_not_ge h
    have hle := Nat.size_le.mpr hlt
    omega
  calc 2 ^ n.size = 2 ^ ((n.size - 1) + 1) := by congr 1; omega
    _ = 2 * 2 ^ (n.size - 1) := by rw [pow_succ, mul_comm]
    _ ≤ 2 * n := Nat.mul_le_mul_left 2 hprev

private lemma integerQualityExponent_le_poly (A M₀ : ℕ) :
    integerQualityExponent A M₀ ≤ 512 * (A + 1) * (M₀ + 1) ^ 2 := by
  unfold integerQualityExponent
  set b := (M₀.size + 1).size
  have hb_le : b ≤ M₀ + 1 := (nat_size_le_self _).trans (by have := nat_size_le_self M₀; omega)
  have h2b : 2 ^ b ≤ 2 * (M₀ + 1) :=
    (two_pow_size_le_two_mul (by omega)).trans (by have := nat_size_le_self M₀; omega)
  have hexp : (47 * b + 47) / 48 ≤ b + 1 := by omega
  have h2exp : 2 ^ ((47 * b + 47) / 48) ≤ 4 * (M₀ + 1) := by
    calc 2 ^ ((47 * b + 47) / 48) ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by decide) hexp
      _ = 2 * 2 ^ b := by rw [pow_succ, mul_comm]
      _ ≤ 4 * (M₀ + 1) := by omega
  calc 128 * (A + 1) * b * 2 ^ ((47 * b + 47) / 48)
      ≤ 128 * (A + 1) * (M₀ + 1) * (4 * (M₀ + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hb_le) h2exp
    _ = 512 * (A + 1) * (M₀ + 1) ^ 2 := by ring

private lemma solverPenalty_size_le {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    (solverPenalty m).size ≤ 5 + 81 * M := by
  have hp : solverPenalty m ≤ 16 * M ^ 81 :=
    (solverPenalty_le m hm).trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hmM 81))
  have hM : M ≤ 2 ^ M := Nat.lt_two_pow_self.le
  have hpow : M ^ 81 ≤ 2 ^ (81 * M) := by
    calc M ^ 81 ≤ (2 ^ M) ^ 81 := Nat.pow_le_pow_left hM 81
      _ = 2 ^ (81 * M) := by rw [← pow_mul, mul_comm]
  have h16 : 16 * M ^ 81 ≤ 2 ^ (4 + 81 * M) := by
    calc 16 * M ^ 81 ≤ 2 ^ 4 * 2 ^ (81 * M) := Nat.mul_le_mul_left 16 hpow
      _ = 2 ^ (4 + 81 * M) := (pow_add 2 4 (81 * M)).symm
  have hlt : 16 * M ^ 81 < 2 ^ (5 + 81 * M) :=
    lt_of_le_of_lt h16 (Nat.pow_lt_pow_right (by decide) (by omega))
  exact Nat.size_le.mpr (lt_of_le_of_lt hp hlt)

/-- Linear upper bound on `max M threshold` as a function of `M`. -/
def dryM0Bound (M : ℕ) : ℕ :=
  M + concreteEdgeThresholdWithLast dryWitnessUsed

theorem dryM0Bound_poly : PolyNat dryM0Bound :=
  PolyNat.id.add (PolyNat.const _)

/-- Explicit quadratic upper bound on `ipmQualityLimbs I.m (solverPenalty J.m) k` as a function
of `I.m`. -/
def dryLimbsBound (M : ℕ) : ℕ :=
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let S := 82 * M + 5
  25520000 * S ^ 2 + 4063 * S + 3675 + 116 * (512 * (A + 1) * (M + threshold + 1) ^ 2)

theorem dryLimbsBound_poly : PolyNat dryLimbsBound := by
  unfold dryLimbsBound
  dsimp only
  have hS : PolyNat (fun M => 82 * M + 5) :=
    ((PolyNat.const 82).mul PolyNat.id).add (PolyNat.const 5)
  have hM : PolyNat (fun M => M + concreteEdgeThresholdWithLast dryWitnessUsed + 1) :=
    (PolyNat.id.add (PolyNat.const _)).add (PolyNat.const 1)
  exact ((((PolyNat.const 25520000).mul (polyNat_pow hS 2)).add
    ((PolyNat.const 4063).mul hS)).add (PolyNat.const 3675)).add
    ((PolyNat.const 116).mul ((PolyNat.const _).mul (polyNat_pow hM 2)))

theorem ipmQualityLimbs_dry_le_bound (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    ipmQualityLimbs I.m V k ≤ dryLimbsBound I.m := by
  intro W I V k
  have hJm_le : J.m ≤ I.m := (solverConnectedAugmented_size J hJn hJm hCapPos).1
  have hVs : V.size ≤ 5 + 81 * I.m := solverPenalty_size_le hJm hJm_le
  have hMs : I.m.size ≤ I.m := nat_size_le_self I.m
  have hSum : I.m.size + V.size ≤ 82 * I.m + 5 := by omega
  have hSlack : slackRangeExponent I.m V ≤ 220000 * (82 * I.m + 5) ^ 2 := by
    unfold slackRangeExponent
    exact Nat.mul_le_mul_left 220000 (Nat.pow_le_pow_left hSum 2)
  have hLimbs : ipmLimbs I.m V ≤
      25520000 * (82 * I.m + 5) ^ 2 + 4063 * (82 * I.m + 5) + 3675 := by
    unfold ipmLimbs ipmPrecision ipmErrorBits ipmRangeExponent
      gradientCoefficientExponent Num.IPM.alphaScale
    omega
  have hM0_le : max I.m (concreteEdgeThresholdWithLast W) ≤
      I.m + concreteEdgeThresholdWithLast W := by omega
  have hk_le : k ≤ 512 * (concreteQualityBudgetWithLast W + 1) *
      (I.m + concreteEdgeThresholdWithLast W + 1) ^ 2 := by
    dsimp only [k, cappedQualityExponent, chainEdgeCap]
    exact (integerQualityExponent_le_poly _ _).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  exact (ipmQualityLimbs_le I.m V k).trans (Nat.add_le_add hLimbs (Nat.mul_le_mul_left 116 hk_le))

/-- Explicit polynomial upper bound on `drySCSizeParam J` as a function of `I.m`. -/
def drySCSizeParamBound (M : ℕ) : ℕ :=
  let M₀ := dryM0Bound M
  M₀ ^ 2 + 22 * M₀ + 5 + dryLimbsBound M

theorem drySCSizeParamBound_poly : PolyNat drySCSizeParamBound := by
  unfold drySCSizeParamBound
  dsimp only
  exact (((polyNat_pow dryM0Bound_poly 2).add ((PolyNat.const 22).mul dryM0Bound_poly)).add
    (PolyNat.const 5)).add dryLimbsBound_poly

private lemma chainParams_k_le_two_mul_M0 (P : ChainParams) : P.k ≤ 2 * P.M₀ := by
  have hM0 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hd1 : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast P.hd
  have hexp : (1 : ℝ) / (P.d : ℝ) ≤ 1 := div_le_one_of_le₀ hd1 (by positivity)
  have hrpow : (P.M₀ : ℝ) ^ ((1 : ℝ) / (P.d : ℝ)) ≤ (P.M₀ : ℝ) := by
    calc (P.M₀ : ℝ) ^ ((1 : ℝ) / (P.d : ℝ)) ≤ (P.M₀ : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM0 hexp
      _ = (P.M₀ : ℝ) := Real.rpow_one _
  have hkR : (P.k : ℝ) ≤ ((2 * P.M₀ : ℕ) : ℝ) := by
    push_cast
    linarith [P.hk_upper]
  exact_mod_cast hkR

/-- `drySCSizeParam J` is bounded by `drySCSizeParamBound I.m` on every valid circulation `J`. -/
theorem drySCSizeParam_le_bound (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e) :
    drySCSizeParam J ≤ drySCSizeParamBound (solverConnectedAugmented J).m := by
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast W J
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hM0_le : cfg.P.M₀ ≤ dryM0Bound I.m := by
    change max I.m (concreteEdgeThresholdWithLast W) ≤ I.m + concreteEdgeThresholdWithLast W
    omega
  have hLvl0 : levelM cfg.TP cfg.P 0 ≤ dryM0Bound I.m ^ 2 :=
    (Chain.levelM_le_sq hV.hTP hV.hγM₀ hV.hγk 0).trans (Nat.pow_le_pow_left hM0_le 2)
  have hN0 : cfg.N₀ ≤ 4 * dryM0Bound I.m := by
    change 4 * cfg.P.M₀ ≤ 4 * dryM0Bound I.m
    omega
  have hk : cfg.P.k ≤ 2 * dryM0Bound I.m := (chainParams_k_le_two_mul_M0 cfg.P).trans (by omega)
  have hCap : dryCapLimit W J ≤ 12 * dryM0Bound I.m + 4 := by
    change 12 * cfg.P.M₀ + 4 ≤ 12 * dryM0Bound I.m + 4
    omega
  have hLimbs := ipmQualityLimbs_dry_le_bound J hJn hJm hCapPos
  have hDepth : Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2) ≤
      4 * dryM0Bound I.m + 1 :=
    (chosenL_sq_le_four_mul_add_one cfg.P.hM₀).trans (by
      change 4 * cfg.P.M₀ + 1 ≤ 4 * dryM0Bound I.m + 1; omega)
  unfold drySCSizeParam drySCSizeParamBound
  dsimp only [W, I, cfg] at hLvl0 hN0 hk hCap hLimbs hDepth ⊢
  omega

/-! ## 3. Op-1 (`restart`) and op-0 (`update`) polynomial bounds extracted from the bridge -/

/-- Input-independent `PolyBound` dominating op `1` (`restart`) of `drySCAlloc Psc capExp limbMul J`,
evaluated at `drySCSizeParam J` (independent of `heap` and all pointer arguments). -/
def drySCOp1Poly (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) : PolyBound :=
  Classical.choose (drySCAllocAt_updateRestartBound Psc capExp limbMul).2.1

/-- On op `1` (`restart`), `drySCAlloc` is independent of `heap` and bounded by
`(drySCOp1Poly ...).eval (drySCSizeParam J)`. -/
theorem drySCAlloc_op1_le_poly (Psc : DrySparseCorePieces) (capExp limbMul : ℕ)
    (J : Circulation) (coreH b h : ℕ) :
    drySCAlloc Psc capExp limbMul J 1 [coreH, b, h] ≤
      (drySCOp1Poly Psc capExp limbMul).eval (drySCSizeParam J) :=
  Classical.choose_spec (drySCAllocAt_updateRestartBound Psc capExp limbMul).2.1
    (drySCSizeParam J) coreH b h

/-- Input-independent `PolyBound` dominating op `0` (`update`) of `drySCAlloc Psc capExp limbMul J`,
evaluated at `drySCSizeParam J + words + editWords` (independent of `heap` and all pointer
arguments). -/
def drySCOp0Poly (Psc : DrySparseCorePieces) (capExp limbMul : ℕ) : PolyBound :=
  Classical.choose (drySCAllocAt_updateRestartBound Psc capExp limbMul).2.2

/-- On op `0` (`update`), `drySCAlloc` is independent of `heap` and bounded by
`(drySCOp0Poly ...).eval (drySCSizeParam J + words + editWords)`. -/
theorem drySCAlloc_op0_le_poly (Psc : DrySparseCorePieces) (capExp limbMul : ℕ)
    (J : Circulation) (hndl g batch words edits editWords l gr h : ℕ) :
    drySCAlloc Psc capExp limbMul J 0 [hndl, g, batch, words, edits, editWords, l, gr, h] ≤
      (drySCOp0Poly Psc capExp limbMul).eval (drySCSizeParam J + words + editWords) :=
  Classical.choose_spec (drySCAllocAt_updateRestartBound Psc capExp limbMul).2.2
    (drySCSizeParam J) hndl g batch words edits editWords l gr h

/-! ## 4. Solver-side `DeepShiftOpsHypKFBL.restartSpaceDom` and `PolyNat` `restartSpace` -/

/-- Concrete `restartSpace` for `DeepShiftOpsHypKFBL` (and `DryOpenSizes.deepRestartSpace`) on
circulation `J`, using the heap-independent op-1 polynomial bound at `drySCSizeParam J`. -/
def dryDeepRestartSpace (Psc : DrySparseCorePieces) (J : Circulation) : ℕ :=
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
    (concreteQualityBudgetWithLast W) I.m
  let L := ipmQualityLimbs I.m V k
  let cfg := concreteCirculationCfgWithLast W J
  let limbMul := concreteReadout2LimbMul W
  ordLevelSpace L dryCapExp (dryCapLimit W J)
    ((drySCOp1Poly Psc dryCapExp limbMul).eval (drySCSizeParam J))
    (levelM cfg.TP cfg.P 0) cfg.N₀ (levelM cfg.TP cfg.P 0)

/-- Discharges `DeepShiftOpsHypKFBL.restartSpaceDom` unconditionally for `drySCAlloc` at
`dryDeepRestartSpace Psc J`. -/
theorem drySC_restartSpaceDom (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J))
    (i : Fin ((concreteCirculationCfgWithLast dryWitnessUsed J).P.d + 1))
    (coreH h : ℕ)
    (hiLt : i.val < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (hN0 : model.chain.N₀ = (concreteCirculationCfgWithLast dryWitnessUsed J).N₀)
    (hLvlM : ∀ j < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      model.chain.lvlM j = levelM (concreteCirculationCfgWithLast dryWitnessUsed J).TP
        (concreteCirculationCfgWithLast dryWitnessUsed J).P j)
    (hModelK : ShiftDeepModelInvKFBL model i) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let L := ipmQualityLimbs I.m V k
    let cfg := concreteCirculationCfgWithLast W J
    let limbMul := concreteReadout2LimbMul W
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let newBran := (model.chain.bran i.val + 1) % cfg.P.k
    ordLevelSpace L dryCapExp (dryCapLimit W J)
        (drySCAlloc Psc dryCapExp limbMul J 1 [coreH, newBran, h])
        (model.chain.lvlM i.val) model.chain.N₀ (next.G (i.val + 1)).m ≤
      dryDeepRestartSpace Psc J := by
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCapPos
  exact deepShift_restartSpaceDom hV.hTP hV.hγk
    (drySCAlloc_op1_le_poly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J)
    model i coreH h hiLt hN0 hLvlM hModelK

private lemma ordLevelSpace_mono_all
    {L₁ L₂ capExp capLimit₁ capLimit₂ initSp₁ initSp₂ M₁ M₂ N₁ N₂ nextM₁ nextM₂ : ℕ}
    (hL : L₁ ≤ L₂) (hCap : capLimit₁ ≤ capLimit₂) (hSp : initSp₁ ≤ initSp₂)
    (hM : M₁ ≤ M₂) (hN : N₁ ≤ N₂) (hNext : nextM₁ ≤ nextM₂) :
    ordLevelSpace L₁ capExp capLimit₁ initSp₁ M₁ N₁ nextM₁ ≤
      ordLevelSpace L₂ capExp capLimit₂ initSp₂ M₂ N₂ nextM₂ := by
  unfold ordLevelSpace
  dsimp only
  have hDG : dynGraphSize capLimit₁ capLimit₁ ≤ dynGraphSize capLimit₂ capLimit₂ := by
    unfold dynGraphSize; omega
  have hCL : capLimit₁ * L₁ ≤ capLimit₂ * L₂ := Nat.mul_le_mul hCap hL
  have hLw : ordLevelLwMax L₁ capExp M₁ N₁ ≤ ordLevelLwMax L₂ capExp M₂ N₂ := by
    unfold ordLevelLwMax
    have hlog : Nat.log 2 (M₁ + N₁ + 2) ≤ Nat.log 2 (M₂ + N₂ + 2) :=
      Nat.log_mono_right (by omega)
    exact Nat.add_le_add hL (Nat.mul_le_mul_left _ (by omega))
  have hEdgeSp : wireCoreLenEdgeSpace (ordLevelLwMax L₁ capExp M₁ N₁) ≤
      wireCoreLenEdgeSpace (ordLevelLwMax L₂ capExp M₂ N₂) := by
    unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
    have hmul : 5 * (2 * ordLevelLwMax L₁ capExp M₁ N₁) *
          (2 * ordLevelLwMax L₁ capExp M₁ N₁ + 1) ≤
        5 * (2 * ordLevelLwMax L₂ capExp M₂ N₂) *
          (2 * ordLevelLwMax L₂ capExp M₂ N₂ + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 5 (by omega)) (by omega)
    omega
  have hEdge := Nat.mul_le_mul hNext hEdgeSp
  omega

/-- Polynomial upper bound on `dryDeepRestartSpace Psc J` as a function of `I.m`. -/
def dryDeepRestartSpaceBound (Psc : DrySparseCorePieces) (M : ℕ) : ℕ :=
  let M₀ := dryM0Bound M
  let limbMul := concreteReadout2LimbMul dryWitnessUsed
  ordLevelSpace (dryLimbsBound M) dryCapExp (12 * M₀ + 4)
    ((drySCOp1Poly Psc dryCapExp limbMul).eval (drySCSizeParamBound M))
    (M₀ ^ 2) (4 * M₀) (M₀ ^ 2)

/-- `dryDeepRestartSpace Psc J` is bounded by `dryDeepRestartSpaceBound Psc I.m` on every valid
circulation `J`. -/
theorem dryDeepRestartSpace_le_bound (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e) :
    dryDeepRestartSpace Psc J ≤ dryDeepRestartSpaceBound Psc (solverConnectedAugmented J).m := by
  let W := dryWitnessUsed
  let I := solverConnectedAugmented J
  let cfg := concreteCirculationCfgWithLast W J
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hM0_le : cfg.P.M₀ ≤ dryM0Bound I.m := by
    change max I.m (concreteEdgeThresholdWithLast W) ≤ I.m + concreteEdgeThresholdWithLast W
    omega
  have hLvl0 : levelM cfg.TP cfg.P 0 ≤ dryM0Bound I.m ^ 2 :=
    (Chain.levelM_le_sq hV.hTP hV.hγM₀ hV.hγk 0).trans (Nat.pow_le_pow_left hM0_le 2)
  have hN0 : cfg.N₀ ≤ 4 * dryM0Bound I.m := by
    change 4 * cfg.P.M₀ ≤ 4 * dryM0Bound I.m
    omega
  have hCap : dryCapLimit W J ≤ 12 * dryM0Bound I.m + 4 := by
    change 12 * cfg.P.M₀ + 4 ≤ 12 * dryM0Bound I.m + 4
    omega
  exact ordLevelSpace_mono_all
    (ipmQualityLimbs_dry_le_bound J hJn hJm hCapPos)
    hCap
    (PolyBound.eval_mono _ (drySCSizeParam_le_bound J hJn hJm hCapPos))
    hLvl0 hN0 hLvl0

/-- `dryDeepRestartSpaceBound Psc` is `PolyNat` (a polynomial function of `I.m`). -/
theorem dryDeepRestartSpaceBound_poly (Psc : DrySparseCorePieces) :
    PolyNat (dryDeepRestartSpaceBound Psc) := by
  have hM0 : PolyNat dryM0Bound := dryM0Bound_poly
  have hM0Sq : PolyNat (fun M => dryM0Bound M ^ 2) := polyNat_pow hM0 2
  have hCap : PolyNat (fun M => 12 * dryM0Bound M + 4) :=
    ((PolyNat.const 12).mul hM0).add (PolyNat.const 4)
  have hOp1 : PolyNat (fun M =>
      (drySCOp1Poly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).eval
        (drySCSizeParamBound M)) :=
    polyNat_comp_polyBound drySCSizeParamBound_poly _
  have hDG : PolyNat (fun M => dynGraphSize (12 * dryM0Bound M + 4) (12 * dryM0Bound M + 4)) := by
    unfold dynGraphSize
    exact ((PolyNat.const 4).add ((PolyNat.const 7).mul hCap)).add ((PolyNat.const 9).mul hCap)
  have hLw : PolyNat (fun M =>
      ordLevelLwMax (dryLimbsBound M) dryCapExp (dryM0Bound M ^ 2) (4 * dryM0Bound M)) := by
    have hUpper : PolyNat (fun M =>
        dryLimbsBound M + (dryCapExp + sparseCoreReadout2LimbConst) *
          (dryM0Bound M ^ 2 + 4 * dryM0Bound M + 3)) :=
      dryLimbsBound_poly.add ((PolyNat.const _).mul
        ((hM0Sq.add ((PolyNat.const 4).mul hM0)).add (PolyNat.const 3)))
    refine PolyNat.mono (fun M => ?_) hUpper
    unfold ordLevelLwMax
    have hlog : Nat.log 2 (dryM0Bound M ^ 2 + 4 * dryM0Bound M + 2) ≤
        dryM0Bound M ^ 2 + 4 * dryM0Bound M + 2 := Nat.log_le_self 2 _
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have hEdgeSp : PolyNat (fun M =>
      wireCoreLenEdgeSpace
        (ordLevelLwMax (dryLimbsBound M) dryCapExp (dryM0Bound M ^ 2) (4 * dryM0Bound M))) := by
    unfold wireCoreLenEdgeSpace Num.integerDivideSpace Num.unsignedDivideSpace
    have h2K := (PolyNat.const 2).mul hLw
    exact ((PolyNat.const 10).mul hLw).add
      (((((PolyNat.const 3).mul h2K).add (PolyNat.const 2)).add
        (((PolyNat.const 5).mul h2K).mul (h2K.add (PolyNat.const 1)))).add
        ((PolyNat.const 3).mul h2K))
  unfold dryDeepRestartSpaceBound ordLevelSpace
  dsimp only
  exact (((((hOp1.add (PolyNat.const 1)).add hDG).add (PolyNat.const 5)).add
    (hCap.mul dryLimbsBound_poly)).add (hM0Sq.mul hEdgeSp)).add
    (((PolyNat.const 2).add ((PolyNat.const 2).mul ((PolyNat.const 4).mul hM0))).add
      ((PolyNat.const 2).mul hM0Sq))

/-- Full `DeepShiftOpsHypKFBL` witness for the dry run's sparse core `drySCAlloc`, using
`dryDeepRestartSpace Psc J` (bounded by `PolyNat` `dryDeepRestartSpaceBound Psc`),
`dryCoreInitSpace Psc J`, `deepShiftLevelCost`, `deepShiftFixedBound`, and
`deepShiftToolMulBound`. -/
theorem drySC_deepShiftOpsHypKFBL (Psc : DrySparseCorePieces)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    {fcap lastMul intCapMax forestEdgeCap deepSpace lastSpace : ℕ}
    {lastAlloc : ℕ → List ℕ → ℕ}
    (hLastSp : ∀ gB lB h,
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      lastAlloc 1 [gB, lB, F.limbs, F.fmt.precision, h] ≤ lastSpace)
    (hSpaceTot :
      let W := dryWitnessUsed
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
        (concreteQualityBudgetWithLast W) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast W J
      2 * (cfg.P.d + 1) + (5 + fcap + 5 * cfg.P.d) + dryDeepRestartSpace Psc J +
        (Finset.range cfg.P.d).sum (fun j =>
          ordLevelSpace F.limbs dryCapExp (dryCapLimit W J) (dryCoreInitSpace Psc J j)
            (levelM cfg.TP cfg.P j) cfg.N₀ (levelM cfg.TP cfg.P (j + 1))) +
        lastSpace + 5 * cfg.P.d +
        3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace F.limbs) ≤ deepSpace) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W)
      (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let limbMul := concreteReadout2LimbMul W
    let PscP := drySCParams Psc dryCapExp limbMul
    DeepShiftOpsHypKFBL
      (w := dryWordSize W allocationCoefficient allocationDegree source)
      (L := F.limbs) (capExp := dryCapExp) (capLimit := dryCapLimit W J)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace)
      (deepFixed := deepShiftFixedBound PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d lastMul)
      (toolMul := deepShiftToolMulBound F.limbs dryCapExp PscP (levelM cfg.TP cfg.P 0) cfg.N₀ cfg.P.d lastMul)
      (fmt := F.fmt) (cfg := cfg) (Psc := PscP)
      (allocation := drySCAlloc Psc dryCapExp limbMul J) (lastAlloc := lastAlloc)
      (dryDeepRestartSpace Psc J)
      (fun j => ordLevelSpace F.limbs dryCapExp (dryCapLimit W J) (dryCoreInitSpace Psc J j)
        (levelM cfg.TP cfg.P j) cfg.N₀ (levelM cfg.TP cfg.P (j + 1)))
      (deepShiftLevelCost F.limbs dryCapExp cfg PscP) lastSpace := by
  intro W I V k F cfg limbMul PscP
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden W J hJn hJm hCapPos
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed
      (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool W sparsifyImplUsed rfl rfl rfl J hw
  exact deepShiftOpsHypKFBL_of_mach
    (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed
    (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2))
    (fun _ => canonicalSparsify sparsifyImplUsed)
    (canonicalSparsifyParams sparsifyImplUsed)
    (dsAmortConst sparsifyImplUsed)
    (dryCoreInitSpace Psc J)
    hT hV.hTP hV.hγk
    (drySCAlloc_op1_le_poly Psc dryCapExp limbMul J)
    (fun j _ g l gr o h => le_of_eq (drySCAlloc_init_eq_dryCoreInitSpace Psc J j g l gr o _ _ h))
    hLastSp hSpaceTot

/-! ## 5. Heap-free `PolyNat` op-0 (`update`) bound for `OrdChainUpdateCoreSpecW` -/

/-- Heap-independent polynomial upper bound on op `0` (`update`) of `drySCAlloc` as a function of
`(I.m, words, editWords)`. -/
def drySCOp0Bound (Psc : DrySparseCorePieces) (M words editWords : ℕ) : ℕ :=
  (drySCOp0Poly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).eval
    (drySCSizeParamBound M + words + editWords)

/-- On op `0` (`update`), `drySCAlloc` is dominated by `drySCOp0Bound Psc I.m words editWords`
independently of `heap` and all pointer arguments. -/
theorem drySCAlloc_op0_le_bound (Psc : DrySparseCorePieces) (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hndl g batch words edits editWords l gr h : ℕ) :
    drySCAlloc Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J 0
        [hndl, g, batch, words, edits, editWords, l, gr, h] ≤
      drySCOp0Bound Psc (solverConnectedAugmented J).m words editWords := by
  have hsp := drySCSizeParam_le_bound J hJn hJm hCapPos
  exact (drySCAlloc_op0_le_poly Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed) J
    hndl g batch words edits editWords l gr h).trans
    (PolyBound.eval_mono _ (by omega))

/-- `drySCOp0Bound` is monotone in `words` and `editWords`. -/
theorem drySCOp0Bound_mono (Psc : DrySparseCorePieces) {M w₁ w₂ e₁ e₂ : ℕ}
    (hw : w₁ ≤ w₂) (he : e₁ ≤ e₂) :
    drySCOp0Bound Psc M w₁ e₁ ≤ drySCOp0Bound Psc M w₂ e₂ :=
  PolyBound.eval_mono _ (by omega)

/-- For any `PolyNat` batch-word and edit-word bounds `fWords, fEditWords`, `drySCOp0Bound` yields
a `PolyNat` bound in `I.m` (matching `DryOpenSizesIneqs.hSpacePoly` for `OrdChainUpdateCoreSpecW`). -/
theorem drySCOp0Bound_poly (Psc : DrySparseCorePieces) {fWords fEditWords : ℕ → ℕ}
    (hW : PolyNat fWords) (hE : PolyNat fEditWords) :
    PolyNat (fun M => drySCOp0Bound Psc M (fWords M) (fEditWords M)) :=
  polyNat_comp_polyBound ((drySCSizeParamBound_poly.add hW).add hE) _

end MinCostFlow.Final.DryRun

end
