module

public import MinCostFlow.Final.AssemblyDryRunSCCoreSelectCode
public import MinCostFlow.Final.WireCoreSelectSizes
public import MinCostFlow.Final.AssemblyDryRunSCCoreModelInv
public import MinCostFlow.MinRatio.WireChainCoreSelFromExtKFBL
import MinCostFlow.Final.AssemblyDryRunSCConnected
import Mathlib.Tactic

/-!
# Dry-run adapters for `ordChainUpdateCoreSpecWKFBLSel_of_parts` (`AssemblyDryRunSCCoreAdapters`)

Provides the concrete dry-run re-embedding function `dryReembFn`, reached-state gradient/length
helpers, and Adapters 1–4 of `ordChainUpdateCoreSpecWKFBLSel_of_parts`
(`MinRatio/WireChainCoreSelFromExtKFBL.lean`) at the dry-run values:

1. `dryCoreSel_hA1` (`UpdateCoreSelAdaptExtM`): unconditional proof of `model.extG.m = I.m`.
2. `dryCoreSel_hA3` (`UpdateCoreSelAdaptKFBLInv`): unconditional proof of `UpdateCoreModelInvKFBL`.
3. `dryCoreSel_hA4` (`UpdateCoreSelAdaptForest`): unconditional proof of the suffix forest edge
   sum bound `≤ forestEdgeCap`.
4. `CoreSelMissingHyps` and `dryCoreSel_hA2_of_missing`: proves Adapter 2 (`UpdateCoreModelInv`)
   from `UpdateCoreSelPremAt` together with the three further premises
   (`CoreSelMetaDisjInv`, `CoreSelVecValidInv`, `UpdateLoopModelInv`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- Concrete re-embedding list function `progReemb` on the dry-run sparse-core tool. -/
def dryReembFn (J : Circulation) :
    ToolReembFn (concreteCirculationCfgWithLast dryWitnessUsed J).T :=
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  let k := cappedQualityExponent threshold A I.m
  let L := ipmQualityLimbs I.m V k
  let P := ipmQualityPrecision I.m V k
  let depth := Expander.chosenL (max I.m threshold ^ 2)
  progReemb (dryLSFInitUsed L P) dryCLsstUsed depth sparsifyImplUsed

/-- The three premises between `OrdChainUpdateCoreSpecWKFBLSel`
(`MinRatio/OrdSelSpecs.lean`) and `UpdateCoreModelInv` (`MinRatio/WireChainSpecs.lean`):
* `hMetaDisj`: `mem0 (levelMeta + d + 0) = tok.rootGraph` (forcing
  `tok.rootECap = initTargetCap cfg G`) and pairwise disjointness of the level-graph and
  length-table blocks;
* `hVecValid`: `Num.Valid` on the external `g` and `l` arrays at every `U`-inserted edge;
* `hLoopModel`: `UpdateLoopModelInv` (including `rebuildCount i + 1 < 2 ^ w`). -/
structure CoreSelMissingHyps {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (w P wordExp stretchPrec vCap eCap g l : ℕ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
    (U : List Update) (mem0 : ℕ → ℕ) (gVec lVec : ℕ → ℝ) : Prop where
  hMetaDisj : CoreSelMetaDisjInv vCap eCap tok mem0
  hVecValid : CoreSelVecValidInv L g l U mem0
  hLoopModel :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap)
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j)
      (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) cfg.P.d 0
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + tr.2.2.2.2.length
          else model.chain.recUpdates j }
      ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.2
      ((model.chain.G 0).batchEnc tr.2.2.2.2) (model.chain.levelOrd 0)

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Pure reached-state & dry-parameter helpers -/

/-- Extracts `model.extG = G`, `model.chain.g = model.extg ∘ intToExt`, and
`model.chain.ℓ = model.extℓ ∘ intToExt` from `OrdSolverReached` at the dry parameters. -/
theorem dryReached_extG_g_ℓ (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap1 : ∀ e, 1 ≤ J.capacity e)
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (hReach : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J)
      (1 / (2 : ℝ) ^ cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)
      (namedInstance (solverConnectedAugmented J)) model) :
    let G := namedInstance (solverConnectedAugmented J)
    model.extG = G ∧
    (∀ ei ∈ (model.chain.G 0).E, model.chain.g ei = model.extg (model.intToExt ei)) ∧
    (∀ ei ∈ (model.chain.G 0).E, model.chain.ℓ ei = model.extℓ (model.intToExt ei)) := by
  intro G
  let I := solverConnectedAugmented J
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
    (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
    (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap1
  have hmG : G.m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
  have hnG : G.n ≤ cfg.N₀ := by
    have hInEq : G.n = I.n := Finset.card_range I.n
    rw [hInEq]; exact hIn
  obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := hReach
  have hUncond := (algorithm2_uncond_preserves_with (η := η) (1 / (2 : ℝ) ^ k) hV hHist hEdgeD
    hLenD (fun t ht => by rw [hGD t ht]; exact hmG) (fun t ht => by rw [hGD t ht]; exact hnG)).1
    T_step le_rfl
  rw [← hEq] at hUncond
  rcases hUncond with ⟨_, _, _, _, _, hEG, _, hCℓ, hCg, _, _, _, _, _, _⟩
  exact ⟨hEG.trans (hGD T_step le_rfl), fun ei _ => congrFun hCg ei, fun ei _ => congrFun hCℓ ei⟩

/-- Every edge `e ∈ (modelPre.chain.G 0).E` satisfies `modelPre.chain.g e = modelPre.extg
(modelPre.intToExt e)` in both Branch A (compacted) and Branch B (non-rebuilt). -/
theorem update_g_eq_extg_modelPre {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ} :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    ∀ e ∈ (modelPre.chain.G 0).E, modelPre.chain.g e = modelPre.extg (modelPre.intToExt e) := by
  intro modelPre e _
  dsimp only [modelPre, alg2PreResetState]
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
      (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
    ⟨h0, _, hgEq⟩ | ⟨hNe0, _, hgEq⟩
  · have hren : level0Rebuilt cfg.P.d model.chain.rebuildCount
        (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
          (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))).1.rebuildCount = true := by
      unfold level0Rebuilt; rw [h0]; simp
    rw [hren]
    exact congrFun hgEq e
  · have hren : level0Rebuilt cfg.P.d model.chain.rebuildCount
        (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
          (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))).1.rebuildCount = false := by
      unfold level0Rebuilt
      cases hfr : firstRebuiltLevel cfg.P.d model.chain.rebuildCount
          (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
            (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e'))).1.rebuildCount with
      | none => rfl
      | some j =>
        have hj0 : j ≠ 0 := fun hj => hNe0 (hj ▸ hfr)
        simp [hj0]
    rw [hren]
    exact congrFun hgEq e

/-- Any fixed-point integer `z` with `z / 2^P = g` and `|g| ≤ 2^E` satisfies both `Num.Fits 4 L z`
and `Num.Fits 4 L (-z)` whenever `P + E + 2 ≤ 4 * L`. -/
theorem update_g_fits_modelPre {L P E : ℕ} (hPE : P + E + 2 ≤ 4 * L) {g : ℝ}
    (hg : |g| ≤ (2 : ℝ) ^ E) (z : ℤ) (hz : (z : ℝ) / (2 : ℝ) ^ P = g) :
    Num.Fits 4 L z ∧ Num.Fits 4 L (-z) := by
  have hzAbs : (|z| : ℝ) ≤ (2 : ℝ) ^ (P + E) := by
    have h1 : (|z| : ℝ) / (2 : ℝ) ^ P = |g| := by
      rw [← hz, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ P)]
    have h2 : (|z| : ℝ) ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P := by
      have hp : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
      exact (div_le_iff₀ hp).mp (h1.trans_le hg)
    rw [pow_add]; linarith
  have hzInt : |z| ≤ (2 : ℤ) ^ (P + E) := by exact_mod_cast hzAbs
  have h2z : 2 * |z| ≤ (2 : ℤ) ^ (P + E + 1) := by
    rw [pow_succ]; linarith
  have hcap : (2 : ℤ) ^ (P + E + 1) < (Num.capacity 4 L : ℤ) := by
    unfold Num.capacity Num.base
    rw [← pow_mul]
    exact_mod_cast (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : P + E + 1 < 4 * L))
  have hle : |2 * z| < (Num.capacity 4 L : ℤ) := by
    rw [abs_mul, abs_of_pos (by decide : (0 : ℤ) < 2)]
    exact lt_of_le_of_lt h2z hcap
  rw [abs_lt] at hle
  constructor <;> (unfold Num.Fits; omega)

/-- `ordLevelLwMax` is bounded by `selectUpdatePostCoreSpaceBound` whenever `0 < eCap`. -/
theorem lwMax_le_postCoreSpace {d vCap eCap cap L capExp M₀ N₀ evalSpace coreSp : ℕ}
    (heCapPos : 0 < eCap) :
    ordLevelLwMax L capExp M₀ N₀ ≤
      selectUpdatePostCoreSpaceBound d vCap eCap cap L capExp M₀ N₀ evalSpace coreSp := by
  set Lw := ordLevelLwMax L capExp M₀ N₀
  have hLle : L ≤ Lw := Nat.le_add_right _ _
  have h1 : Lw ≤ selCoreLenEdgeSpace L Lw := by
    unfold selCoreLenEdgeSpace wireCoreLenEdgeSpace
    rw [max_eq_right hLle]; omega
  have h2 : Lw ≤ eCap * (6 + selCoreLenEdgeSpace L Lw) :=
    (h1.trans (Nat.le_add_left _ 6)).trans (Nat.le_mul_of_pos_left _ heCapPos)
  have h3 : Lw ≤ shiftDeepSelectSpaceBound d vCap eCap cap L capExp M₀ N₀ evalSpace := by
    unfold shiftDeepSelectSpaceBound; dsimp only [Lw] at h2 ⊢; omega
  unfold selectUpdatePostCoreSpaceBound; dsimp only [Lw] at h3 ⊢; omega

/-! ## 2. Unconditional dry-run Adapters 1, 3, 4 and conditional Adapter 2 -/

/-- **Unconditional Adapter 1 (`UpdateCoreSelAdaptExtM`)** at the dry values:
`OrdSolverReached` yields `model.extG = G`, and `namedInstance_m` yields `G.m = I.m`. -/
theorem dryCoreSel_hA1 (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e) {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w)
    (limbMul intCapMax forestEdgeCap : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T))
    (coreSpace : ℕ → ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    UpdateCoreSelAdaptExtM w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
      (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace := by
  intro I V k F cfg G root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  have hReach := hPrem.2.2.2.2.2.2.1
  have hExtG := (dryReached_extG_g_ℓ J hJn hJm hCap1 hReach).1
  rw [hExtG, namedInstance_m]

/-- **Unconditional Adapter 3 (`UpdateCoreSelAdaptKFBLInv`)** at the dry values. -/
theorem dryCoreSel_hA3 (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e) {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w)
    (limbMul intCapMax forestEdgeCap : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T))
    (coreSpace : ℕ → ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    UpdateCoreSelAdaptKFBLInv w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
      (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace := by
  intro I V k F cfg G root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hShift0, hShift1, _, hBr, _⟩ := hPrem
  exact dryCoreSel_updateCoreModelInvKFBL
    (concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1)
    hShift0 hShift1 hBr

/-- **Unconditional Adapter 4 (`UpdateCoreSelAdaptForest`)** at the dry values. -/
theorem dryCoreSel_hA4 (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e) {w : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w)
    (limbMul intCapMax forestEdgeCap : ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T))
    (coreSpace : ℕ → ℕ) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    UpdateCoreSelAdaptForest w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
      (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace := by
  intro I V k F cfg G root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R hPrem
  obtain ⟨hRep0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hForCap, _,
    hShift0, hShift1, _, _, _, _, _, _, _, _, _, _, _, _, hRef, _⟩ := hPrem
  exact (dryCoreSel_forestEdgeSum_le
    (concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1)
    hRep0.2.2.2.2.1 hRef hShift0 hShift1).trans hForCap

/-- **Adapter 2 (`UpdateCoreModelInv`) from `UpdateCoreSelPremAt` + `CoreSelMissingHyps`**:
reduces `UpdateCoreModelInv` to the three further premises `hMetaDisj`, `hVecValid` and `hLoopModel`. -/
theorem dryCoreSel_hA2_of_missing (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m)
    (hCap1 : ∀ e, 1 ≤ J.capacity e) {w wordExp stretchPrec : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w)
    {limbMul intCapMax forestEdgeCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs (concreteCirculationCfgWithLast dryWitnessUsed J).T)}
    {coreSpace : ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap : ℕ} {mem0 mem : ℕ → ℕ}
    {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    {tok : SolverToken (concreteCirculationCfgWithLast dryWitnessUsed J)
      (ipmQualityMinRatioFormat (solverConnectedAugmented J).m (solverPenalty J.m)
        (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) hw).limbs
      Rcore}
    {sg : SelectGhost} {U : List Update} {B R : ℤ} :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 F.limbs F.fmt.precision I.m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 F.limbs F.fmt.precision I.m) model.extℓ
    UpdateCoreSelPremAt w F.limbs F.fmt.precision F.rangeExponent I.m V ⌈cfg.Ψ⌉₊ k
      (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp limbMul
      (dryCapLimit dryWitnessUsed J) intCapMax forestEdgeCap G.n (initTargetCap cfg G) 4 2
      (dryLastStretchP J) (drySlot I.m) cfg G (dryPot J) (DryChainLenGridInv J) Rcore coreSpace
      root uIntBuf editsPtr editWords g l heap mem0 mem model tok sg U B R →
    CoreSelMissingHyps w F.fmt.precision wordExp stretchPrec G.n (initTargetCap cfg G) g l
      model tok U mem0 gVec lVec →
    UpdateCoreModelInv w F.limbs F.fmt.precision I.m (k + Num.IPM.alphaExponent I.m V + 10)
      wordExp stretchPrec model tok U mem0 g l B := by
  intro I V k F cfg G gVec lVec hPrem hMiss
  obtain ⟨hRep0, hMeta0, hCaps0, _, _, _, hReach, _, _, _, hTreeNum, _, _, hB0, hFitTree,
    hExtGLRng, _, hDet, hICap, _, _, _, hShift0, hShift1, _, _, hGLRng, _, _, _, hnfCap,
    _, _, _, _, _, hRef, _, _, _, hVecOff, _⟩ := hPrem
  exact dryCoreSel_updateCoreModelInv J hJn hJm hCap1 hw (Rcore := Rcore) (_uIntBuf := uIntBuf)
    (sg := sg) hRep0 hMeta0 hCaps0 hReach hTreeNum hB0 hFitTree hExtGLRng hDet hICap hShift0 hShift1
    hGLRng hnfCap hRef hVecOff hMiss.hMetaDisj hMiss.hVecValid hMiss.hLoopModel

end MinCostFlow.Final.DryRun

end
