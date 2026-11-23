module

public import MinCostFlow.MinRatio.WireChainCoreBranchBCostGoalKFBL
public import MinCostFlow.MinRatio.WireChainCoreCostBaseKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBCostProofModel
import MinCostFlow.MinRatio.WireChainCoreBranchBBatchOK
import MinCostFlow.MinRatio.WireChainCoreBranchBModelKFBL
import MinCostFlow.MinRatio.WireChainCoreSyncDefs
import MinCostFlow.MinRatio.WireShiftDeepCostKFBL
import Mathlib.Tactic

/-!
# Cost proof for Branch B of the chain core (`WireChainCoreBranchBCostProof`)

Proves `BranchBCostFieldsKFBL` (`costLe`) for every `H : BranchBRunKFBL …` under four
additional hypotheses:

1. `updateCoreTreeMulBound L drainUnit ≤ treeMul` (`treeMul` is unconstrained in
   `BranchBCostGoalKFBL` as stated);
2. `ToolCostMono cfg.T` (guards the runtime-growth clause of `H.loop`);
3. `cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k` (gives `levelM j ≤ levelM 0` via `levelM_le_levelM_zero`
   for `UpdateCoreOpsHypKFBL.costTotalBranchB`);
4. `H.ec0 = eCap` (links the `ec0` parameter of `H.pre`'s frame to level `0`'s length block tag
   `23 + d`).

* `branchB_ec0Tag_of_eq`: derives the level-`0` length block tag bound from `H.ec0 = eCap`.
* `branchB_phiCore_start_eq`: transports the initial core potential sum from `mem0` to `H.sF0.mem`.
* `branchB_phiCore_end_eq`: transports the final core potential sum from `H.sX.mem` to `H.out.mem`.
* `branchB_loopCost_split`: separates the loop cost bound of `H.loop` into the
  `updateCoreNoRebuildStepCost + 30` sum plus `20 * T + 20 * Rsum`.
* `branchBCostFieldsKFBL_of_hyps`: assembles `BranchBCostFieldsKFBL` across all three exit cases.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-! ### 1. Potential transports across the parts of Branch B -/

/-- When `H.ec0 = eCap`, every word of level `0`'s length block `[mem0 lm, mem0 lm + H.ec0 * L)`
carries tag `23 + cfg.P.d` in `tok`. -/
theorem branchB_ec0Tag_of_eq
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hEc0 : H.ec0 = eCap) :
    let lm := solverLevelMetaAddr tok.table cfg.P.d
    ∀ a, mem0 lm ≤ a → a < mem0 lm + H.ec0 * L → tok.tag a = 23 + cfg.P.d := by
  intro lm a ha1 ha2
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  obtain ⟨_, vcOf, ecOf, hLev, _, _⟩ := H.start.modelInv.2.2.2.2.2.2.2.2.1
  have hCap0 := dynGraphAt_caps_eq (hLev 0 hdPos).1 (H.start.caps0 0 hdPos)
  have hTag0 := (hLev 0 hdPos).2.2.2.1 a
  rw [add_zero] at hTag0
  rw [hEc0, ← hCap0.2] at ha2
  exact hTag0 ha1 ha2

/-- The initial sum of core potentials at `H.sF0.mem` (start of the Branch B loop) equals the sum
of core potentials at `mem0` (from the solver rep). -/
theorem branchB_phiCore_start_eq
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hEc0Tag :
      let lm := solverLevelMetaAddr tok.table cfg.P.d
      ∀ a, mem0 lm ≤ a → a < mem0 lm + H.ec0 * L → tok.tag a = 23 + cfg.P.d) :
    branchBPhiSum Rcore H.A tok.coreTok H.sF0.mem =
      (Finset.range cfg.P.d).sum
        (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
  unfold branchBPhiSum
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjLt : j < cfg.P.d := Finset.mem_range.mp hj
  have hCoreH : H.A.coreH j = tok.coreHandle j := by
    rw [H.A_eq]; simp [branchBAddrsOf, hjLt]
  rw [hCoreH]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, _, _, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, hh0S1, _, hS1H2, _, _, _, _, _, _, hFrS1, hFrSP, _⟩ := H.pre
  have hULeH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hLoc := H.envA.coreLocal (tok.coreHandle j) (chainLevelOrdAbs model.chain j)
    (tok.coreTok j) H.sF0.mem mem0 (fun a ha => ?_)
  · exact hLoc.2
  · have hTag : tok.tag a = 21 + j := hT21 j hjLt a ha
    have hLtU : a < uIntBuf := H.start.footLt a (Or.inl (hOwn a (by omega)))
    have hFrontEq : H.sF0.mem a = H.sP.mem a := H.front.2.2.2.1 a (by omega)
    have hNoNew : ∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E →
        a ≠ tok.slots + ei ∧ a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei := by
      intro ei hei _
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := hT9 ei hei; rw [← h] at this; omega
      · have := hT12 ei hei; rw [← h] at this; omega
      · have := hT13 ei hei; rw [← h] at this; omega
    have hLmOff : a < mem0 (solverLevelMetaAddr tok.table cfg.P.d) ∨
        mem0 (solverLevelMetaAddr tok.table cfg.P.d) + H.ec0 * L ≤ a := by
      by_contra hc
      push Not at hc
      have := hEc0Tag a hc.1 hc.2
      omega
    have hSPEq : H.sP.mem a = H.memS1 a := hFrSP a (by omega) hNoNew hLmOff
    have hNeR11 : a ≠ root + 11 := fun h => by
      have := hT1 11 (by decide); rw [← h] at this; omega
    have hS1Eq : H.memS1 a =
        Function.update mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) H.forestPtr a :=
      hFrS1 a (by omega) hNeR11 (fun _ => by omega)
    have hUpdEq : Function.update mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) H.forestPtr a = mem a :=
      Function.update_of_ne (by omega) H.forestPtr mem
    have hMemEq : mem a = mem0 a := H.start.memEq a hLtU (by omega) (by omega) (by omega)
    exact hFrontEq.trans (hSPEq.trans (hS1Eq.trans (hUpdEq.trans hMemEq)))

/-- The final sum of core potentials at `H.out.mem` equals the sum of core potentials at `H.sX.mem`
(right after the exit of the loop, before the suffix). -/
theorem branchB_phiCore_end_eq
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    (Finset.range cfg.P.d).sum
        (fun j => Rcore.phi (H.out.mem (tok.handle + 18 + j)) (H.tokN j) H.out.mem) =
      (Finset.range cfg.P.d).sum
        (fun j => Rcore.phi (H.sX.mem (H.A.handleBase + j)) (H.tokN j) H.sX.mem) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, _, hh0S1, _, hS1H2, _, _, _, hTreeFoot1, _⟩ := H.pre
  have hULeH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hSF0Le : H.heap2 ≤ H.sF0.regs 4 := by have := H.front.2.2.1; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hSELe, _, _, _, hLoopFootAll, _, _, _⟩ := H.loop
  have hSXLe : H.sE.regs 4 ≤ H.sX.regs 4 := H.exitOut.heapLo
  have hSufFr := H.suf.2.2.2.2.2.2.2.2.2.1
  have hHB : H.A.handleBase = tok.handle + 18 := by rw [H.A_eq]; rfl
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjLt : j < cfg.P.d := Finset.mem_range.mp hj
  have hTagHB : tok.tag (tok.handle + 18 + j) = 4 := hT4 j (by omega)
  have hHBLtU : tok.handle + 18 + j < uIntBuf :=
    H.start.footLt _ (Or.inl (hOwn _ (by omega)))
  have hHBNeR11 : tok.handle + 18 + j ≠ root + 11 := fun h => by
    have := hT1 11 (by decide); rw [← h] at this; omega
  have hHBEq : H.out.mem (tok.handle + 18 + j) = H.sX.mem (H.A.handleBase + j) := by
    rw [hHB]
    exact hSufFr (tok.handle + 18 + j) (by omega) hHBNeR11 (fun _ => by omega) (fun h => by omega)
  rw [hHBEq]
  have hLoc := H.envA.coreLocal (H.sX.mem (H.A.handleBase + j)) (chainLevelOrdAbs H.X j)
    (H.tokN j) H.out.mem H.sX.mem (fun a ha => ?_)
  · exact hLoc.2
  · have hLoopFoot := hLoopFootAll j hjLt a
    have hCoreH : H.A.coreH j = tok.coreHandle j := by rw [H.A_eq]; simp [branchBAddrsOf, hjLt]
    rcases (H.exitOut.reps j hjLt).2 a ha with hE | hNew
    · rcases hLoopFoot hE with h0 | hMid
      · rw [hCoreH] at h0
        have hTag : tok.tag a = 21 + j := hT21 j hjLt a h0
        have hLtU : a < uIntBuf := H.start.footLt a (Or.inl (hOwn a (by omega)))
        have hNeR11 : a ≠ root + 11 := fun h => by
          have := hT1 11 (by decide); rw [← h] at this; omega
        exact hSufFr a (by omega) hNeR11 (fun _ => by omega) (fun h => by omega)
      · have hR11Lt : root + 11 < uIntBuf :=
          H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by decide)]; decide)))
        refine hSufFr a (by omega) (by omega) (fun h => by omega) (fun _ hTree => ?_)
        rcases hTreeFoot1 a hTree with hT0 | hTNew
        · have hLtU : a < uIntBuf := H.start.footLt a (Or.inr (Or.inl hT0))
          omega
        · omega
    · have hR11Lt : root + 11 < uIntBuf :=
        H.start.footLt _ (Or.inl (hOwn _ (by rw [hT1 11 (by decide)]; decide)))
      refine hSufFr a hNew.2 (by omega) (fun h => by omega) (fun _ hTree => ?_)
      rcases hTreeFoot1 a hTree with hT0 | hTNew
      · have hLtU : a < uIntBuf := H.start.footLt a (Or.inr (Or.inl hT0))
        omega
      · omega

/-! ### 2. Loop cost splitting and `BranchBCostFieldsKFBL` assembly -/

/-- Splits the loop cost bound of `H.loop` into the `updateCoreNoRebuildStepCost + 30` sum plus
`20 * T + 20 * Rsum`, where `T = ∑ j < i₀, (D j).fDel.length` and
`Rsum = ∑ j < i₀, (D j).reemb.length`. -/
theorem branchB_loopCost_split
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    let Δc := fun j =>
      (branchBStepData cfg H.ℓ' H.g' cfg.P.d 0 H.st0 H.G1 H.Uint
        ((model.chain.G 0).batchEnc H.Uint) j).2.1
    H.cL + branchBPhiSum Rcore H.A H.tokE H.sE.mem ≤
      (Finset.range H.i₀).sum (fun j =>
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (H.C j).1 (H.C j).2.1 (H.C (j + 1)).2.2 (Δc j) + 30) +
      20 * (Finset.range H.i₀).sum (fun j => (H.D j).fDel.length) +
      20 * (Finset.range H.i₀).sum (fun j => (H.D j).reemb.length) +
      32 + branchBPhiSum Rcore H.A tok.coreTok H.sF0.mem := by
  intro Δc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLoopCost, hStepData, _⟩ := H.loop
  dsimp only at hLoopCost
  have hSumLe :
      (Finset.Ico 0 H.i₀).sum (fun j =>
        branchBStepCostKFBL L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀ (H.C j).1
          (H.C j).2.1 (cfg.T.cost (H.chE.scState j) - cfg.T.cost (H.st0.scState j))
          (H.levelUS j).length (H.D j).fDel.length (H.D j).reemb.length + 4) ≤
      (Finset.range H.i₀).sum (fun j =>
        updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
          (H.C j).1 (H.C j).2.1 (H.C (j + 1)).2.2 (Δc j) + 30) +
      20 * (Finset.range H.i₀).sum (fun j => (H.D j).fDel.length) +
      20 * (Finset.range H.i₀).sum (fun j => (H.D j).reemb.length) := by
    rw [← Finset.range_eq_Ico]
    calc (Finset.range H.i₀).sum (fun j =>
          branchBStepCostKFBL L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀ (H.C j).1
            (H.C j).2.1 (cfg.T.cost (H.chE.scState j) - cfg.T.cost (H.st0.scState j))
            (H.levelUS j).length (H.D j).fDel.length (H.D j).reemb.length + 4)
        ≤ (Finset.range H.i₀).sum (fun j =>
            (updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
              (H.C j).1 (H.C j).2.1 (H.C (j + 1)).2.2 (Δc j) + 30) +
            20 * (H.D j).fDel.length + 20 * (H.D j).reemb.length) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjLt : j < H.i₀ := Finset.mem_range.mp hj
          obtain ⟨hΔ, hUS⟩ := hStepData j (Nat.zero_le j) hjLt
          have hCnext : (H.C (j + 1)).2.2 = (H.levelUS j).length := by
            rw [H.C_eq, hUS]; rfl
          rw [hΔ, hCnext]
          exact branchB_stepCost_le_noRebuild L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j)
            cfg.N₀ (H.C j).1 (H.C j).2.1 (Δc j) (H.levelUS j).length (H.D j).fDel.length
            (H.D j).reemb.length
      _ = (Finset.range H.i₀).sum (fun j =>
            updateCoreNoRebuildStepCost L capExp Psc cfg.P.k (levelM cfg.TP cfg.P j) cfg.N₀
              (H.C j).1 (H.C j).2.1 (H.C (j + 1)).2.2 (Δc j) + 30) +
          20 * (Finset.range H.i₀).sum (fun j => (H.D j).fDel.length) +
          20 * (Finset.range H.i₀).sum (fun j => (H.D j).reemb.length) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  omega

set_option maxHeartbeats 800000 in
/-- **`BranchBCostFieldsKFBL` from `BranchBRunKFBL`.** Proves the `costLe` field of
`BranchBSufOutKFBL` from `H : BranchBRunKFBL …` together with the four hypotheses `hTreeMul`,
`hMono`, `hγk`, and `hEc0`. -/
theorem branchBCostFieldsKFBL_of_hyps
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hTreeMul : updateCoreTreeMulBound L drainUnit ≤ treeMul)
    (hMono : ToolCostMono cfg.T)
    (hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k)
    (hEc0 : H.ec0 = eCap) :
    BranchBCostFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost := by
  have hTreeMul' : wireTreeSyncEditCost L drainUnit + 62 ≤ treeMul := by
    unfold updateCoreTreeMulBound at hTreeMul; omega
  refine ⟨?_⟩
  -- Abbreviations matching `costTotalBranchB`
  set gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg with hgVec
  set lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ with hlVec
  set modelPre := alg2PreResetState cfg model U gVec lVec with hmodelPre
  set d := cfg.P.d with hd
  set Dstep := branchBStepData cfg H.ℓ' H.g' d 0 H.st0 H.G1 H.Uint
    ((model.chain.G 0).batchEnc H.Uint) with hDstep
  set Δc : ℕ → ℕ := fun j => (Dstep j).2.1 with hΔc
  set bW : ℕ → ℕ := fun j => (H.C j).1 with hbW
  set eW : ℕ → ℕ := fun j => (H.C j).2.1 with heW
  set nextULen : ℕ → ℕ := fun j => (H.C (j + 1)).2.2 with hnextULen
  have hXeq : H.X = modelPre.chain := by rw [H.modelEq, H.gVec_eq, H.lVec_eq]
  have hdPos : 0 < d := H.start.modelInv.1.1
  have hiLe : H.i₀ ≤ d := H.loop.2.2.1
  have hN0Eq : model.chain.N₀ = cfg.N₀ := H.start.modelInv.2.1.1
  -- Level-0 batch and edit bounds
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
    cases u with
    | insert _ _ _ | delete _ => trivial
    | split _ _ _ _ => exact H.start.refresh.2.2 _ hu
  have hULenEq : H.Uint.length = U.length := by
    rw [H.Uint_eq]
    exact translateBatch_length_eq U model.extG model.extToInt model.intToExt model.nextFresh hEdgeU
  have hEdgeInt : ∀ u ∈ H.Uint, IsEdgeUpdate u := by
    rw [H.Uint_eq]
    exact (refreshBatch_edge_dichotomy H.start.rep0.2.2.2.2.1 H.start.refresh).2.2.1
  have hbW0 : bW 0 ≤ 4 * U.length + 1 := by
    show (H.C 0).1 ≤ 4 * U.length + 1
    rw [H.C_eq, ← hULenEq]
    exact smallBatchAt_words_le_edgeOnly (H.Uint_eq ▸ H.start.small) hEdgeInt
  have heW0 : eW 0 ≤ 10 * U.length + 1 := by
    show (H.C 0).2.1 ≤ 10 * U.length + 1
    rw [H.C_eq]
    dsimp only [branchBTraceCaps]
    have h1 := (H.Uint_eq ▸ H.start.edits).2.2
    have h2 := ordEditsEnc_batchToOrdEdits_le H.Uint hEdgeInt
    omega
  -- Step premise for `costTotalBranchB`
  have hBatchOK := branchBStepBatch_ok H.tpValid H.start.shiftInv H.start.modelInv
    H.start.modelInvKFBL
  have hDle := branchBStepData_le (H.toolStep model.chain H.start.shiftInv) H.ℓ' H.g' d 0 H.st0
    H.G1 H.Uint ((model.chain.G 0).batchEnc H.Uint) (by omega)
    (fun j _ => by rw [H.st0_eq]) (by rw [H.st0_eq])
    (fun j _ hj => by
      simpa [H.Uint_eq, H.gVec_eq, H.lVec_eq, H.ℓ'_eq, H.g'_eq, H.G1_eq, H.st0_eq] using
        hBatchOK j (by omega))
  have hLogLe : ∀ j, SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀ ≤
      SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ := fun j =>
    bLog_mono (levelM_le_levelM_zero H.tpValid hγk j)
  have hStepPrem : ∀ j < H.i₀, nextULen j ≤ Δc j ∧ bW (j + 1) ≤ 6 * Δc j + 1 ∧
      eW (j + 1) ≤ edMul * (Δc j + (bW j + eW j + 1) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀) := fun j _ => by
    have hcp := branchBTraceCaps_costPremise (edMul := edMul)
      (bW0 := editsPtr - d - uIntBuf) (eW0 := editWords) (u0 := H.Uint.length) hLogLe
      (fun r => ⟨(hDle r).1, (hDle r).2.1⟩) j
    simpa [bW, eW, nextULen, Δc, Dstep, H.C_eq] using hcp
  have hNoFire' : ¬ intRebuildThreshold cfg.P model.chain.N₀ 0 <
      model.chain.updCount 0 +
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length := by
    rw [hN0Eq]; exact H.start.noFire
  -- `costTotalBranchB` in all three cases
  obtain ⟨hCostC1, hCostC2, hCostC3⟩ := H.envA.ops.costTotalBranchB model U gVec lVec bW eW
    nextULen Δc H.i₀ hdPos hiLe hNoFire' H.start.modelInvKFBL hbW0 heW0 hStepPrem
  -- Common potential equalities and cost bounds
  have hPhi0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem0 =
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem0 +
        (Finset.range d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) +
        tok.offReadyCount * drainUnit := by
    show _ + _ + _ = _
    rw [Fin.sum_univ_eq_sum_range (fun i => Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem0)]
  have hPhiCore0 := branchB_phiCore_start_eq H (branchB_ec0Tag_of_eq H hEc0)
  have hPhiCoreEnd := branchB_phiCore_end_eq H
  have hPhiTreeMid :
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap H.curTreeTok1 H.sX.mem =
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap H.curTreeTok1 H.memS1 :=
    rfl
  have hLoopCost := branchB_loopCost_split H
  obtain ⟨_, _, _, _, hLoopI, hLoopM, hFireLoop, hUpdLoopEq, _, _, _, _, _, _, _, _, _,
    hStepData, hLoopMono⟩ := H.loop
  have hLoopRt : H.st0.totalRuntime +
      (Finset.Ico 0 H.i₀).sum (fun j => cfg.T.cost (H.chE.scState j) - cfg.T.cost (H.st0.scState j)) ≤
      H.chE.totalRuntime :=
    hLoopMono hMono
  have hSt0Rt : H.st0.totalRuntime = model.chain.totalRuntime := by rw [H.st0_eq]; rfl
  have hSt0TU : H.st0.totalTreeUpdates = model.chain.totalTreeUpdates := by rw [H.st0_eq]; rfl
  have hIcoΔc : (Finset.range H.i₀).sum Δc =
      (Finset.Ico 0 H.i₀).sum (fun j => cfg.T.cost (H.chE.scState j) - cfg.T.cost (H.st0.scState j)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_congr rfl fun j hj =>
      (hStepData j (Nat.zero_le j) (Finset.mem_Ico.mp hj).2).1.symm
  have hc0 : H.c0 ≤ 210 := H.dispatch.2.1
  have hcP := H.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcF : H.cF ≤ 20 * bW 0 + 60 := by
    show H.cF ≤ 20 * (H.C 0).1 + 60
    rw [H.C_eq]; exact H.front.2.1
  have hcS := H.suf.2.2.2.2.2.2.2.2.2.2
  rw [hULenEq, hPhiTreeMid] at hcS
  have hOldFsSt0 : chainSuffixForests H.st0 = chainSuffixForests model.chain := by
    funext fr; rw [H.st0_eq]; rfl
  -- Split on the three exit cases
  rcases H.exitCase with hC1 | hC2 | hC3
  · -- Case 1: interior rebuild at `0 < i₀ < d`, `fr = i₀`
    obtain ⟨hiPos, hiLt, hfrEq, _, _, hXint, _, _, hcX⟩ := hC1
    have hFireI0 : intRebuildThreshold cfg.P cfg.N₀ H.i₀ < H.chE.updCount H.i₀ + H.curUE.length :=
      hFireLoop hiLt
    have hXupd : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        (d - H.i₀) H.i₀ H.chE H.curGE H.curUE H.curEncE).1 := by
      rw [hXint, ← branchBUpdateLoop_int hiLt hiPos hFireI0]
    have hXfull : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        d 0 H.st0 H.G1 H.Uint ((model.chain.G 0).batchEnc H.Uint)).1 := by
      rw [hXupd, hUpdLoopEq]
    have hEx := ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P
      { H.chE with ℓ := H.ℓ', g := H.g' } hiLt H.curGE H.curEncE
    rw [← hXint] at hEx
    -- Runtime bound for Case 1
    have hRt1 : (Finset.range H.i₀).sum Δc +
        (Finset.Ico H.i₀ d).sum (fun j => cfg.T.cost (modelPre.chain.scState j)) +
        cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime := by
      have hB := branchBRuntime_case_int cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' hiLt
        H.st0 H.chE H.curGE H.curUE H.curEncE hFireI0 hLoopRt
      dsimp only at hB
      rw [← hXupd, hXeq, hSt0Rt] at hB
      have hEqPre : (Finset.range H.i₀).sum Δc =
          (Finset.range H.i₀).sum
            (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (H.st0.scState j)) := by
        rw [hIcoΔc, Finset.range_eq_Ico]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjLt := (Finset.mem_Ico.mp hj).2
        rw [← hXeq, (hEx.1 j hjLt).2.1]
      rw [hEqPre]
      exact hB
    -- `initOrd` premise for Case 1
    have hInit1 : ∀ j, H.i₀ ≤ j → j < d → ∃ ℓj gj ordj,
        modelPre.chain.scState j = cfg.T.initOrd cfg.P.k (modelPre.chain.lvlM j) modelPre.chain.N₀
          (modelPre.chain.G j) ℓj gj ordj := fun j hj1 hj2 => by
      have hJ := (hEx.2.2.1 j hj1 hj2).1
      have hLvlEq : H.X.lvlM j = H.chE.lvlM j := congrFun hEx.2.2.2.2.2.2.2.2.1 j
      have hNEq : H.X.N₀ = H.chE.N₀ := hEx.2.2.2.2.2.2.2.2.2.1
      rw [← hXeq, hLvlEq, hNEq]
      exact ⟨_, _, _, hJ⟩
    -- `(model.chain.G i₀).m ≤ (modelPre.chain.G i₀).m + bW i₀`
    have hGm1 : (model.chain.G H.i₀).m ≤ (modelPre.chain.G H.i₀).m + bW H.i₀ := by
      obtain ⟨r, hr⟩ : ∃ r, d - H.i₀ = r + 1 := ⟨d - H.i₀ - 1, by omega⟩
      rw [hr] at hLoopM
      have hCurG : H.curGE = (H.chE.G H.i₀).applyBatch H.curUE := hLoopM.2.2.2.1
      have hChG : H.chE.G H.i₀ = model.chain.G H.i₀ := by
        rw [(hLoopI.modelFrame.1 H.i₀ le_rfl).1, H.st0_eq]
      have hXG : modelPre.chain.G H.i₀ = H.curGE := by rw [← hXeq]; exact hEx.2.1
      have hMle := mGraph_m_le_applyBatch_add_length (H.chE.G H.i₀) H.curUE
      rw [← hCurG, hChG, ← hXG] at hMle
      have hUleB : H.curUE.length ≤ bW H.i₀ := by
        obtain ⟨j, hj⟩ : ∃ j, H.i₀ = j + 1 := ⟨H.i₀ - 1, by omega⟩
        have hSzU : H.curUE.length ≤ (H.C H.i₀).2.2 := hLoopI.sizes.2.2
        have hC1 : bW H.i₀ = 5 * (Dstep j).1 + 1 := by
          show (H.C H.i₀).1 = 5 * (Dstep j).1 + 1
          rw [hj, H.C_eq]; rfl
        have hC2 : (H.C H.i₀).2.2 = (Dstep j).2.2 := by
          rw [hj, H.C_eq]; rfl
        have hLenEnc : (Dstep j).2.2 ≤ (Dstep j).1 := by
          have hStep := hStepData j (Nat.zero_le j) (by omega)
          -- `(Dstep j).1` is `GS.batchEnc nextU`, `(Dstep j).2.2` is `nextU.length`
          have h1 : ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph)
              (curU : List Update) (curEnc k : ℕ),
              (branchBStepData cfg H.ℓ' H.g' rem idx st curG curU curEnc k).2.2 ≤
              (branchBStepData cfg H.ℓ' H.g' rem idx st curG curU curEnc k).1 := by
            intro rem
            induction rem with
            | zero => intro _ _ _ _ _ _; simp [branchBStepData]
            | succ rem ih =>
              intro idx st curG curU curEnc k
              simp only [branchBStepData]
              split_ifs
              · exact le_rfl
              · exact list_length_le_batchEnc _ _
              · exact ih _ _ _ _ _ _
          exact h1 d 0 H.st0 H.G1 H.Uint ((model.chain.G 0).batchEnc H.Uint) j
        omega
      omega
    have hTotal1 := hCostC1 hiPos hiLt hInit1 hRt1 hGm1
    -- Bound `ordRotWords` and `bundleLogFactor` at `i₀ - 1`
    have hAbsPrev : chainLevelOrdAbs H.chE (H.i₀ - 1) = chainLevelOrdAbs modelPre.chain (H.i₀ - 1) := by
      have hp := hEx.1 (H.i₀ - 1) (by omega)
      have hOrd : H.X.levelOrd (H.i₀ - 1) = H.chE.levelOrd (H.i₀ - 1) := by
        unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
        by_cases h0 : H.i₀ - 1 = 0
        · simp [h0, (hEx.1 0 (by omega)).1]
        · have hp2 := hEx.1 (H.i₀ - 1 - 1) (by omega)
          simp [h0, hp2.2.1, hp2.2.2.1]
      rw [← hXeq]
      simp only [chainLevelOrdAbs, hp.1, hp.2.1, hp.2.2.2.1, hOrd]
    have hBrPrev : H.chE.bran (H.i₀ - 1) = modelPre.chain.bran (H.i₀ - 1) := by
      rw [← hXeq]; exact (hEx.1 (H.i₀ - 1) (by omega)).2.2.1.symm
    have hRot1 : ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1)) + 1 ≤
        2 * (modelPre.chain.G H.i₀).n + 2 * (modelPre.chain.G H.i₀).m + 2 := by
      rw [hAbsPrev, hBrPrev]
      have hR := H.start.modelInvKFBL.2.2.2.2.1 (H.i₀ - 1) (by omega)
      rw [show H.i₀ - 1 + 1 = H.i₀ by omega] at hR
      change ordRotWords (chainLevelOrdAbs modelPre.chain (H.i₀ - 1))
        (modelPre.chain.bran (H.i₀ - 1)) ≤
        1 + 2 * (modelPre.chain.G H.i₀).n + 2 * (modelPre.chain.G H.i₀).m at hR
      omega
    have hMul1 : Psc.mul * (ordRotWords (chainLevelOrdAbs H.chE (H.i₀ - 1)) (H.chE.bran (H.i₀ - 1)) + 1) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (H.i₀ - 1)) cfg.N₀ ≤
        Psc.mul * (2 * (modelPre.chain.G H.i₀).n + 2 * (modelPre.chain.G H.i₀).m + 2) *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ :=
      Nat.mul_le_mul (Nat.mul_le_mul_left Psc.mul hRot1) (hLogLe (H.i₀ - 1))
    -- Tree-update count bound for Case 1
    have hTU1 : (Finset.range H.i₀).sum (fun j => (H.D j).fDel.length) +
        ((graphListEdgeUnion H.oldFs \ graphListEdgeUnion H.newFs).card +
          (graphListEdgeUnion H.newFs \ graphListEdgeUnion H.oldFs).card) ≤
        modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates := by
      rw [H.oldFs_eq, H.newFs_eq, ← hXeq, ← hSt0TU]
      refine branchB_treeUpdates_ge_fDel_add_symmDiff hXfull hiLe
        (Or.inl ⟨hiLt, hfrEq,
          fun j hj => by rw [(hEx.1 j hj).2.2.2.2, hLoopI.modelFrame.2.2.2.2.2.2.2],
          by rw [hEx.2.2.2.2.2.1 H.i₀]; simp [hLoopI.modelFrame.2.2.2.2.2.2.2]⟩)
        (fun j hj => by
          have hs := hLoopI.slotModel j hj
          have hp := hEx.1 j hj
          rw [hp.2.1, hp.2.2.1]
          exact ⟨hs.2.2.1, by rw [hs.2.2.2.1, hLoopI.modelFrame.2.1]⟩)
        ⟨by rw [← H.Fp_eq, ← H.oldFs_eq]; exact H.split.2.2.1,
         by rw [← H.Fp_eq, ← H.newFs_eq]; exact H.split.2.2.2.1,
         by rw [← H.Fp_eq, ← H.newFs_eq]; exact H.split.2.2.2.2.1⟩
    -- Assemble Case 1
    have hS1 : graphListEdgeSum H.oldFs + graphListEdgeSum H.newFs =
        graphListEdgeSum (chainSuffixForests model.chain H.i₀) +
          graphListEdgeSum (chainSuffixForests modelPre.chain H.i₀) := by
      rw [H.oldFs_eq, H.newFs_eq, hfrEq, ite_eq_left hiLe, ite_eq_left hiLe, hOldFsSt0, hXeq]
    have hMin1 : min H.fr d = H.i₀ := by rw [hfrEq]; exact Nat.min_eq_left hiLe
    rw [hPhi0, hMin1]
    rw [hPhiCore0] at hLoopCost
    rw [← hPhiCoreEnd, hXeq, ← hd] at hcX
    rw [hfrEq, hS1, ← hd] at hcS
    have hcX' : H.cX + (Finset.range d).sum
          (fun j => Rcore.phi (H.out.mem (tok.handle + 18 + j)) (H.tokN j) H.out.mem) ≤
        2 * ((d - H.i₀) * (Psc.readout + 48)) + 670 * H.bWE +
          Psc.mul * (2 * (modelPre.chain.G H.i₀).n + 2 * (modelPre.chain.G H.i₀).m + 2) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ +
          (Finset.Ico H.i₀ d).sum (fun j => levelCost modelPre.chain j + 9) +
          lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) + Psc.readout + 15 * (d - H.i₀) + 413 +
          branchBPhiSum Rcore H.A H.tokE H.sE.mem :=
      hcX.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_left hMul1 _) _) _) _) _) _) _)
    exact branchB_cost_case1_arith H.costLe hc0 hcP hcF hbW0 hLoopCost hcX' hLoopI.sizes.1 hcS hiLe
      hTotal1 hTreeMul' hTU1
  · -- Case 2: non-empty terminal exit at `i₀ = d`, `curUE ≠ []`, `fr = d`
    obtain ⟨hiEq, hne, hfrEq, _, _, hXterm, _, _, _, hcX⟩ := hC2
    have hXupd : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        (d - H.i₀) H.i₀ H.chE H.curGE H.curUE H.curEncE).1 := by
      rw [hXterm, hiEq, Nat.sub_self]
    have hXfull : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        d 0 H.st0 H.G1 H.Uint ((model.chain.G 0).batchEnc H.Uint)).1 := by
      rw [hXupd, hUpdLoopEq]
    obtain ⟨_, hGdEq, hScPre⟩ := branchBRuntime_term cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
      H.chE H.curGE H.curUE H.curEncE
    rw [← hXterm, hXeq] at hGdEq hScPre
    have hRt2 : (Finset.range d).sum Δc + cfg.L.cost (modelPre.chain.G d) ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime := by
      have hB := branchBRuntime_case_term cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        H.st0 H.chE H.curGE H.curUE H.curEncE (hiEq ▸ hLoopRt)
      dsimp only at hB
      rw [← hXterm, hXeq, hSt0Rt, ite_eq_right hne] at hB
      have hEqPre : (Finset.range d).sum Δc =
          (Finset.range d).sum
            (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (H.st0.scState j)) := by
        have hiEq' : H.i₀ = d := hiEq
        rw [← hiEq', hIcoΔc, hiEq', Finset.range_eq_Ico]
        exact Finset.sum_congr rfl fun j hj => by rw [hScPre j (Finset.mem_Ico.mp hj).2]
      rw [hEqPre]
      exact hB
    have hTotal2 := hCostC2 hiEq hRt2
    rw [hiEq] at hTotal2
    -- Match `curGE = modelPre.chain.G d`, `ordRotWords`, `LwMax`, `bundleLogFactor`
    have hXbr : ∀ j < d, modelPre.chain.bran j = H.chE.bran j := fun j _ => by
      rw [← hXeq, hXterm]; simp [Chain.Ordered.updateLoop, hne]
    have hXGlt : ∀ j < d, modelPre.chain.G j = H.chE.G j := fun j hj => by
      rw [← hXeq, hXterm]; simp [Chain.Ordered.updateLoop, hne, show j ≠ cfg.P.d by omega]
    have hXuc : ∀ j < d, modelPre.chain.updCount j = H.chE.updCount j := fun j _ => by
      rw [← hXeq, hXterm]; simp [Chain.Ordered.updateLoop, hne]
    have hAbsPrev : chainLevelOrdAbs H.chE (d - 1) = chainLevelOrdAbs modelPre.chain (d - 1) := by
      have hOrd : modelPre.chain.levelOrd (d - 1) = H.chE.levelOrd (d - 1) := by
        unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
        by_cases h0 : d - 1 = 0
        · simp [h0, hXGlt 0 hdPos]
        · simp [h0, hScPre (d - 1 - 1) (by omega), hXbr (d - 1 - 1) (by omega)]
      simp only [chainLevelOrdAbs, hXGlt (d - 1) (by omega), hScPre (d - 1) (by omega),
        hXuc (d - 1) (by omega), hOrd]
    have hRot2 : ordRotWords (chainLevelOrdAbs H.chE (d - 1)) (H.chE.bran (d - 1)) + 1 ≤
        2 * (modelPre.chain.G d).n + 2 * (modelPre.chain.G d).m + 2 := by
      rw [hAbsPrev, ← hXbr (d - 1) (by omega)]
      have hR := H.start.modelInvKFBL.2.2.2.2.1 (d - 1) (by omega)
      rw [show d - 1 + 1 = d by omega] at hR
      change ordRotWords (chainLevelOrdAbs modelPre.chain (d - 1))
        (modelPre.chain.bran (d - 1)) ≤
        1 + 2 * (modelPre.chain.G d).n + 2 * (modelPre.chain.G d).m at hR
      omega
    have hMul2 : Psc.mul * (ordRotWords (chainLevelOrdAbs H.chE (d - 1)) (H.chE.bran (d - 1)) + 1) *
        SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (d - 1)) cfg.N₀ ≤
        Psc.mul * (2 * (modelPre.chain.G d).n + 2 * (modelPre.chain.G d).m + 2) *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ :=
      Nat.mul_le_mul (Nat.mul_le_mul_left Psc.mul hRot2) (hLogLe (d - 1))
    have hLen2 : (modelPre.chain.G d).m *
        (wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (d - 1)) cfg.N₀) + 30) ≤
        (modelPre.chain.G d).m *
        (wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 30) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (coreLenEdgeCost_mono (lwMax_mono (levelM_le_levelM_zero H.tpValid hγk (d - 1)))) 30)
    -- Match `branchBPhiSum Rcore H.A H.tokN H.sX.mem` with `H.out.mem` sum
    have hPhiXEq : branchBPhiSum Rcore H.A H.tokN H.sX.mem =
        (Finset.range d).sum
          (fun j => Rcore.phi (H.out.mem (tok.handle + 18 + j)) (H.tokN j) H.out.mem) := by
      rw [hPhiCoreEnd]; unfold branchBPhiSum
      exact Finset.sum_congr rfl fun j hj => by
        rw [H.exitOut.handlesLow j (by rw [hfrEq, Nat.min_self]; exact Finset.mem_range.mp hj)]
    -- Tree-update count bound for Case 2
    have hTU2 : (Finset.range d).sum (fun j => (H.D j).fDel.length) +
        ((graphListEdgeUnion H.oldFs \ graphListEdgeUnion H.newFs).card +
          (graphListEdgeUnion H.newFs \ graphListEdgeUnion H.oldFs).card) ≤
        modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates := by
      rw [H.oldFs_eq, H.newFs_eq, ← hXeq, ← hSt0TU]
      refine branchB_treeUpdates_ge_fDel_add_symmDiff hXfull le_rfl
        (Or.inr ⟨rfl, Or.inl hfrEq, fun j _ => by
          rw [hXterm]; simp [Chain.Ordered.updateLoop, hne, hLoopI.modelFrame.2.2.2.2.2.2.2]⟩)
        (fun j hj => by
          have hs := hLoopI.slotModel j (hiEq ▸ hj)
          rw [hXeq, hScPre j hj, hXbr j hj]
          exact ⟨hs.2.2.1, by rw [hs.2.2.2.1, hLoopI.modelFrame.2.1]⟩)
        ⟨by rw [← H.Fp_eq, ← H.oldFs_eq]; exact H.split.2.2.1,
         by rw [← H.Fp_eq, ← H.newFs_eq]; exact H.split.2.2.2.1,
         by rw [← H.Fp_eq, ← H.newFs_eq]; exact H.split.2.2.2.2.1⟩
    -- Suffix forest sum equals `oldLastF.m + newLastF.m`
    have hS2 : graphListEdgeSum H.oldFs + graphListEdgeSum H.newFs =
        (model.chain.lastLSFs model.chain.lastBran).F.F.m +
          (modelPre.chain.lastLSFs modelPre.chain.lastBran).F.F.m := by
      rw [H.oldFs_eq, H.newFs_eq, hfrEq, ite_eq_left le_rfl, ite_eq_left le_rfl, hOldFsSt0, hXeq]
      simp [chainSuffixForests, graphListEdgeSum]
    have hMin2 : min H.fr d = d := by rw [hfrEq, Nat.min_self]
    rw [hPhi0, hMin2]
    rw [hPhiCore0, hiEq, ← hd] at hLoopCost
    rw [hiEq, hfrEq, hS2, ← hd] at hcS
    rw [hPhiXEq, ← hGdEq, ← hd] at hcX
    have hcX' : H.cX + (Finset.range d).sum
          (fun j => Rcore.phi (H.out.mem (tok.handle + 18 + j)) (H.tokN j) H.out.mem) ≤
        3 * Psc.readout + copyGraphLiveCost (modelPre.chain.G d).n (modelPre.chain.G d).m +
          (modelPre.chain.G d).m *
            (wireCoreLenEdgeCost (ordLevelLwMax L capExp (levelM cfg.TP cfg.P 0) cfg.N₀) + 30) +
          Psc.mul * (2 * (modelPre.chain.G d).n + 2 * (modelPre.chain.G d).m + 2) *
            SparseCore.bundleLogFactor (levelM cfg.TP cfg.P 0) cfg.N₀ +
          lastMul * (cfg.L.cost (modelPre.chain.G d) + 1) + 360 + 36 +
          branchBPhiSum Rcore H.A H.tokE H.sE.mem :=
      (Nat.le_add_right _ _).trans (hcX.trans (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add (Nat.add_le_add_left hLen2 _) hMul2) _) _) _) _))
    exact branchB_cost_case2_arith H.costLe hc0 hcP hcF hbW0 hLoopCost hcX' hcS hTotal2 hTreeMul' hTU2
  · -- Case 3: empty terminal exit at `i₀ = d`, `curUE = []`, `fr = d + 1`
    obtain ⟨hiEq, hEmp, hfrEq, _, _, hXterm, hTokN, _, _, _, hcX, _, hPhiEq⟩ := hC3
    have hXupd : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        (d - H.i₀) H.i₀ H.chE H.curGE H.curUE H.curEncE).1 := by
      rw [hXterm, hiEq, Nat.sub_self]
    have hXfull : H.X = (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        d 0 H.st0 H.G1 H.Uint ((model.chain.G 0).batchEnc H.Uint)).1 := by
      rw [hXupd, hUpdLoopEq]
    obtain ⟨_, _, hScPre⟩ := branchBRuntime_term cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
      H.chE H.curGE H.curUE H.curEncE
    rw [← hXterm, hXeq] at hScPre
    have hRt3 : (Finset.range d).sum Δc ≤
        modelPre.chain.totalRuntime - model.chain.totalRuntime := by
      have hB := branchBRuntime_case_term cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g'
        H.st0 H.chE H.curGE H.curUE H.curEncE (hiEq ▸ hLoopRt)
      dsimp only at hB
      rw [← hXterm, hXeq, hSt0Rt, ite_eq_left hEmp, add_zero] at hB
      have hEqPre : (Finset.range d).sum Δc =
          (Finset.range d).sum
            (fun j => cfg.T.cost (modelPre.chain.scState j) - cfg.T.cost (H.st0.scState j)) := by
        have hiEq' : H.i₀ = d := hiEq
        rw [← hiEq', hIcoΔc, hiEq', Finset.range_eq_Ico]
        exact Finset.sum_congr rfl fun j hj => by rw [hScPre j (Finset.mem_Ico.mp hj).2]
      rw [hEqPre]
      exact hB
    have hTotal3 := hCostC3 hiEq hRt3
    rw [hiEq] at hTotal3
    have hXbr : ∀ j < d, modelPre.chain.bran j = H.chE.bran j := fun j _ => by
      rw [← hXeq, hXterm]; simp [Chain.Ordered.updateLoop, hEmp]
    have hPhiEndEq : (Finset.range d).sum
          (fun j => Rcore.phi (H.out.mem (tok.handle + 18 + j)) (H.tokN j) H.out.mem) =
        branchBPhiSum Rcore H.A H.tokE H.sE.mem := by
      rw [hPhiCoreEnd, hTokN, ← hPhiEq]; unfold branchBPhiSum
      exact Finset.sum_congr rfl fun j hj => by
        rw [H.exitOut.handlesLow j (by rw [hfrEq]; have := Finset.mem_range.mp hj; omega)]
    have hOldNil : H.oldFs = [] := by rw [H.oldFs_eq, hfrEq, ite_eq_right (by omega)]
    have hNewNil : H.newFs = [] := by rw [H.newFs_eq, hfrEq, ite_eq_right (by omega)]
    have hTU3 : (Finset.range d).sum (fun j => (H.D j).fDel.length) ≤
        modelPre.chain.totalTreeUpdates - model.chain.totalTreeUpdates := by
      have hT := branchB_treeUpdates_ge_fDel_add_symmDiff (fDel := fun j => (H.D j).fDel)
        hXfull le_rfl
        (Or.inr ⟨rfl, Or.inr hfrEq, fun j _ => by
          rw [hXterm]; simp [Chain.Ordered.updateLoop, hEmp, hLoopI.modelFrame.2.2.2.2.2.2.2]⟩)
        (fun j hj => by
          have hs := hLoopI.slotModel j (hiEq ▸ hj)
          rw [hXeq, hScPre j hj, hXbr j hj]
          exact ⟨hs.2.2.1, by rw [hs.2.2.2.1, hLoopI.modelFrame.2.1]⟩)
        ⟨by rw [← H.Fp_eq, ← H.oldFs_eq]; exact H.split.2.2.1,
         by rw [← H.Fp_eq, ← H.newFs_eq]; exact H.split.2.2.2.1,
         by rw [← H.Fp_eq, ← H.newFs_eq]; exact H.split.2.2.2.2.1⟩
      rw [hXeq, hSt0TU] at hT
      exact (Nat.le_add_right _ _).trans hT
    have hMin3 : min H.fr d = d := by rw [hfrEq]; omega
    rw [hPhi0, hMin3]
    rw [hPhiCore0, hiEq, ← hd] at hLoopCost
    rw [hiEq, hfrEq, hOldNil, hNewNil, ← hd] at hcS
    simp only [graphListEdgeUnion, graphListEdgeSum, List.foldl_nil, List.map_nil, List.sum_nil,
      Finset.sdiff_self, Finset.card_empty, add_zero] at hcS
    exact branchB_cost_case3_arith H.costLe hc0 hcP hcF hbW0 hLoopCost hcX hPhiEndEq hcS hTotal3
      hTreeMul' hTU3

end MinCostFlow.MinRatio
