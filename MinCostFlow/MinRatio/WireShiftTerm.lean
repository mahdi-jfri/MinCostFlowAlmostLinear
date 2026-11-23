module

public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.WireShiftTermPhases
import MinCostFlow.DynSpanner.Program.StateLayout
import MinCostFlow.LastLevelProgram.Readout
import MinCostFlow.MinRatio.SolverRep

/-!
# Terminal-level shift chain synchronization (`ShiftTermChainSyncSpecW`)

Proves `shiftTermChainBody_meets_spec`, establishing `ShiftTermChainSyncSpecW` for
`shiftTermChainBody` (Algorithm 2 terminal-level shift `i = d`, pages 20 and 29) with zero
sparse-core tool work (`toolMul = 0`) and per-tree-update cost `wireTreeSyncEditCost L drainUnit + 2`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program IPM.Machine

private theorem pathRep_foot_base_mem {L C b : ℕ} {s : PathTreeState}
    {x : (LinkCut.PathProg.pathRep 4 L C).τ} {mem : ℕ → ℕ}
    (_hrep : (LinkCut.PathProg.pathRep 4 L C).rep b s x mem) :
    (LinkCut.PathProg.pathRep 4 L C).foot b x b := by
  refine ⟨le_rfl, ?_⟩
  unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb LinkCut.PathProg.recW
  have h1 : 1 ≤ LinkCut.PathProg.recW (LinkCut.PathProg.treeLimbs L) := by
    unfold LinkCut.PathProg.recW; omega
  have h2 : 0 < (2 * x.1.n + 1) := by omega
  have h3 := Nat.mul_pos h1 h2
  unfold LinkCut.PathProg.recW at h3
  omega

/-- `shiftTermChainBody` satisfies `ShiftTermChainSyncSpecW` with zero sparse-core tool work
(`toolMul = 0`) and exact per-tree-update amortized cost `wireTreeSyncEditCost L drainUnit + 2`. -/
theorem shiftTermChainBody_meets_spec
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {fmt : Num.Format w}
    {shiftTermChainProc initTree : ℕ} {opTree : ℕ → ℕ} {bind canonCopy isNeg : ℕ}
    (hProc : p.procs[shiftTermChainProc]? =
      some (shiftTermChainBody (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg))
    (hCoreLocal : Rcore.Local)
    (hFmtBits : fmt.limbBits = 4) (hLpos : 0 < L) (hL4W : 4 * L + 2 < 2 ^ w)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hBindOk : MeetsContract w p bind (pathSlotBindContract w))
    (hCanonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4)) :
    ShiftTermChainSyncSpecWExt w L P m V psi k epsExp drainUnit capExp limbMul capLimit lastTreeCap
      cfg Rcore p shiftTermChainProc
      (lastTreeCap * (2 + wireTreeSyncEditSpace L))
      (41 * lastTreeCap + 320) 0 (wireTreeSyncEditCost L drainUnit + 2) := by
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  refine ⟨_, hProc, ?_⟩
  intro root heap pos ω mem0 mem model tok B R
  dsimp only
  set model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
  set oldLastF := (model.chain.lastLSFs model.chain.lastBran).F.F
  set newLastBran := (model.chain.lastBran + 1) % model.chain.lastK
  set newLastF := (model.chain.lastLSFs newLastBran).F.F
  intro hRep0 hMemEq hSched' hNum0 hOffInv0 hOffBd0 _hCapFacts _hBranLt
    hLastBranLt hLastKW hLogW hCapT hNewForest hOldSub hNewSub hDisjPref hLastCap
    hFootLt hzHeap hHeapRoom
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, hFreshInv, hFreshTab0, hExtLtM,
    ⟨hG0Cap, hIntCapPos, hNextFreshLe, hI2EId⟩, hSched0, hOffReady0, hTreeN0, hLct0,
    hTreeRep0, hAccounts0, hCores0, hTermPtr0, hTermBran0, hTermRep0, hWire0, hTags0⟩ := hRep0
  have hRep0Full : Rrep.rep root model tok mem0 :=
    ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, hFreshInv, hFreshTab0, hExtLtM,
      ⟨hG0Cap, hIntCapPos, hNextFreshLe, hI2EId⟩, hSched0, hOffReady0, hTreeN0, hLct0,
      hTreeRep0, hAccounts0, hCores0, hTermPtr0, hTermBran0, hTermRep0, hWire0, hTags0⟩
  obtain ⟨hOwnOfTag, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hT9, hT10, hT11, hT12, hT13, hT14,
    hT15, hT16, hT1718, hT19, hT20, hT21⟩ := hTags0
  obtain ⟨hTable0, hRootG0, ⟨hOldForest, hOldFInfo⟩, hNamed0, hOrient0⟩ := hWire0
  set G0 := model.chain.G 0
  set oldF := model.chain.toTreeChain.chainTree
  set newF := model'.chain.toTreeChain.chainTree
  set termBranAddr := tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < heap := hFootLt a (Or.inl (hOwnOfTag a h))
  have hmem0_of_tag {a : ℕ} (h : tok.tag a ≠ 5) : mem a = mem0 a := hMemEq a h
  have hG0nEq : G0.n = model.extG.n := by unfold MGraph.n; rw [← hFreshInv.hV]
  have hTermBranTag : tok.tag termBranAddr = 4 := by
    have h4 := hT4 (2 * cfg.P.d + 1) (by omega)
    have hadd : tok.handle + 18 + (2 * cfg.P.d + 1) = termBranAddr := by dsimp [termBranAddr]; omega
    rwa [hadd] at h4
  have hRootDir_m : ListAt mem root [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse,
      tok.freshCounter, tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds,
      tok.edgeRecords, tok.offReadyCount, tok.offReadyList, tok.inOffReady, tok.rootGraph,
      tok.intCap] := fun j hj => by
    rw [hmem0_of_tag (by rw [hT1 j (by simpa using hj)]; decide)]; exact hRootDir0 j hj
  have hInitPar_m : ListAt mem (tok.handle + 9)
      [m, V, cfg.P.d, cfg.P.k, psi, tok.alphaPtr, k, epsExp, Expander.chosenL (cfg.P.M₀ ^ 2)] :=
      fun j hj => by
    have hj8 : j < 9 := by simpa using hj
    have h9 : tok.tag (tok.handle + 9 + j) = 2 := by
      have := hT2 (9 + j) (by omega); simpa [Nat.add_assoc] using this
    rw [hmem0_of_tag (by rw [h9]; decide)]; exact hInitPar0 j hj
  have hLevelW : termBranAddr < heap := htagLt (by rw [hTermBranTag]; decide)
  have hRootW : root + 16 ≤ heap := by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleW : tok.handle + 18 ≤ heap := by have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hTermTokLe : tok.termTok ≤ heap := by
    by_cases hlt : tok.termHandle < tok.termTok
    · have := htagLt (by rw [hT19 (tok.termTok - 1) ⟨by omega, by omega⟩]; decide); omega
    · have := hTermRep0.1; omega
  have hRootGW : tok.rootGraph + dynGraphSize model.extG.n tok.rootECap ≤ heap := by
    have hpos : 0 < dynGraphSize model.extG.n tok.rootECap := by unfold dynGraphSize; omega
    have := htagLt (by rw [hT20 (tok.rootGraph + dynGraphSize model.extG.n tok.rootECap - 1)
      (by omega) (by omega)]; decide); omega
  have hTermPtr_m : mem (tok.handle + 18 + cfg.P.d) = tok.termHandle :=
    (hmem0_of_tag (by rw [hT4 cfg.P.d (by omega)]; decide)).trans hTermPtr0
  have hTermBran_m : mem termBranAddr = model.chain.lastBran :=
    (hmem0_of_tag (by rw [hTermBranTag]; decide)).trans hTermBran0
  have hLastK_m : mem tok.termHandle = model.chain.lastK := by
    have h19 : tok.tag tok.termHandle = 19 := hT19 tok.termHandle ⟨le_rfl, by have := hTermRep0.1; omega⟩
    exact (hmem0_of_tag (by rw [h19]; decide)).trans hTermRep0.2.2.1
  -- Phase 1: advance terminal branch pointer
  obtain ⟨st1, c1, r1, hc1, hmem1, h1_27, h1_28, h1_29, _, _, h1_32, h1_33, h1_2⟩ :=
    shiftTermSetupBranch_runs (w := w) (root := root) (heap := heap) (p := p) (ω := ω) (mem := mem) (pos := pos)
      (by simpa using hRootDir_m 0 (by simp))
      (by have := hInitPar_m 2 (by simp); simpa [Nat.add_assoc] using this)
      hTermPtr_m hLastK_m hTermBran_m hLastBranLt hLastKW
      (by omega) (by omega) (by omega) (by have := hTermRep0.1; omega)
  -- Phase 2: pack symmetric forest difference at `heap`
  have hNewBranLt : newLastBran < model.chain.lastK := Nat.mod_lt _ (by omega)
  have hMem1_term (a : ℕ) (ha1 : tok.termHandle ≤ a) (ha2 : a < tok.termTok) : st1.mem a = mem0 a := by
    have h19 : tok.tag a = 19 := hT19 a ⟨ha1, ha2⟩
    have hne : a ≠ termBranAddr := fun heq => by rw [heq, hTermBranTag] at h19; omega
    rw [hmem1, Function.update_of_ne hne, hmem0_of_tag (by rw [h19]; decide)]
  obtain ⟨hOldBW, hOldLSF⟩ := hTermRep0.2.2.2 model.chain.lastBran hLastBranLt
  obtain ⟨hNewBW, hNewLSF⟩ := hTermRep0.2.2.2 newLastBran hNewBranLt
  have hOldBrEq : st1.mem (tok.termHandle + 1 + model.chain.lastBran) =
      mem0 (tok.termHandle + 1 + model.chain.lastBran) :=
    hMem1_term _ (by omega) (by have := hTermRep0.1; omega)
  have hNewBrEq : st1.mem (tok.termHandle + 1 + newLastBran) =
      mem0 (tok.termHandle + 1 + newLastBran) :=
    hMem1_term _ (by omega) (by have := hTermRep0.1; omega)
  have hOldBaseEq : st1.mem (st1.mem (tok.termHandle + 1 + model.chain.lastBran) + 1) =
      mem0 (mem0 (tok.termHandle + 1 + model.chain.lastBran) + 1) := by
    rw [hOldBrEq]; exact hMem1_term _ (by have := hOldBW.1; have := hTermRep0.1; omega)
      (by have := hOldBW.2.1; omega)
  have hNewBaseEq : st1.mem (st1.mem (tok.termHandle + 1 + newLastBran) + 1) =
      mem0 (mem0 (tok.termHandle + 1 + newLastBran) + 1) := by
    rw [hNewBrEq]; exact hMem1_term _ (by have := hNewBW.1; have := hTermRep0.1; omega)
      (by have := hNewBW.2.1; omega)
  have hOldG1 : DynGraphAt st1.mem (st1.mem (st1.mem (tok.termHandle + 1 + model.chain.lastBran) + 1))
      tok.vcLast tok.ecLast oldLastF := by
    rw [hOldBaseEq]
    exact dynGraphAt_of_agree hOldLSF.2.1 (fun a ha1 ha2 =>
      hMem1_term a (by have := hOldBW.2.2.2.2.1; have := hTermRep0.1; omega)
        (by have := hOldBW.2.2.2.2.2.1; omega))
  have hNewG1 : DynGraphAt st1.mem (st1.mem (st1.mem (tok.termHandle + 1 + newLastBran) + 1))
      tok.vcLast tok.ecLast newLastF := by
    rw [hNewBaseEq]
    exact dynGraphAt_of_agree hNewLSF.2.1 (fun a ha1 ha2 =>
      hMem1_term a (by have := hNewBW.2.2.2.2.1; have := hTermRep0.1; omega)
        (by have := hNewBW.2.2.2.2.2.1; omega))
  have hPackRoom : heap + 2 * (oldLastF.m + newLastF.m) < 2 ^ w := by
    have hmul : 2 * (oldLastF.m + newLastF.m) ≤ lastTreeCap * (2 + wireTreeSyncEditSpace L) :=
      calc 2 * (oldLastF.m + newLastF.m) ≤ 2 * lastTreeCap := Nat.mul_le_mul_left 2 hLastCap
      _ = lastTreeCap * 2 := Nat.mul_comm _ _
      _ ≤ lastTreeCap * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨st2, c2, edits, r2, hc2, hDiffLast, hEditsAt2, h2_6, h2_18, h2_27, h2_29, hFrame2⟩ :=
    shiftTermPackEdits_runs (w := w) (heap := heap) (termTok := tok.termTok) h1_27 h1_28 h1_29 h1_32 h1_33 h1_2
      hTermTokLe (by have := hTermRep0.1; omega) (by have := hTermRep0.1; omega)
      (by rw [hOldBrEq]; exact hOldBW.2.1) (by rw [hNewBrEq]; exact hNewBW.2.1)
      (by rw [hOldBaseEq]; exact hOldBW.2.2.2.2.2.1) (by rw [hNewBaseEq]; exact hNewBW.2.2.2.2.2.1)
      hOldG1 hNewG1 hPackRoom (by omega)
  -- Relate `edits` to full chain tree difference `oldF.E` vs `newF.E`
  obtain ⟨hOldFEq, hNewFEq⟩ := termShift_chainTree_eq model
  have hDiffFull : TreeEditDifference oldF.E newF.E edits := by
    rw [hOldFEq, hNewFEq]; exact treeEditDiff_union_disjoint hDisjPref hDiffLast
  have hEditsLenEq : edits.length = model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates :=
    (treeEditDiff_len_eq hDiffFull).trans (termShift_totalTreeUpdates model).symm
  have hEditsLeCap : edits.length ≤ lastTreeCap :=
    (treeEditDiff_len_le hDiffLast).trans hLastCap
  have hMem2_eq_mem0 {a : ℕ} (ha : a < heap) (ht4 : tok.tag a ≠ 4) (ht5 : tok.tag a ≠ 5) :
      st2.mem a = mem0 a := by
    have hne : a ≠ termBranAddr := fun heq => ht4 (heq ▸ hTermBranTag)
    rw [hFrame2 a (Or.inl ha), hmem1, Function.update_of_ne hne, hmem0_of_tag ht5]
  -- Phase 3: set up loop registers
  have hRootG_m2 : DynGraphAt st2.mem tok.rootGraph model.extG.n tok.rootECap G0 :=
    dynGraphAt_of_agree hRootG0 (fun a ha1 ha2 =>
      hMem2_eq_mem0 (by omega) (by rw [hT20 a ha1 ha2]; decide) (by rw [hT20 a ha1 ha2]; decide))
  have hLoadRoot (j : ℕ) (hj : j < 16) : st2.mem (root + j) = mem0 (root + j) :=
    hMem2_eq_mem0 (by omega) (by rw [hT1 j hj]; decide) (by rw [hT1 j hj]; decide)
  have hLoadHdr (j : ℕ) (hj : j < 18) : st2.mem (tok.handle + j) = mem0 (tok.handle + j) :=
    hMem2_eq_mem0 (by omega) (by rw [hT2 j hj]; decide) (by rw [hT2 j hj]; decide)
  obtain ⟨st3, c3, r3, hc3, hmem3, h3_0, h3_1, h3_2, h3_3, h3_6, h3_18, h3_9, h3_10, h3_11,
      h3_19, h3_20, h3_22, h3_23, h3_24, h3_25, h3_26⟩ :=
    shiftTermSetupLoop_runs (w := w) h2_6 h2_18 h2_27 h2_29
      ((hLoadHdr 0 (by omega)).trans (by simpa using hDetHdr0 0 (by simp)))
      ((hLoadHdr 5 (by omega)).trans (by simpa using hDetHdr0 5 (by simp)))
      ((hLoadRoot 14 (by omega)).trans (by simpa using hRootDir0 14 (by simp)))
      (by simpa [dgVCapOff] using hRootG_m2.2.2.2.1)
      (by simpa [dgECapOff] using hRootG_m2.2.2.2.2.1)
      ((hLoadRoot 6 (by omega)).trans (by simpa using hRootDir0 6 (by simp)))
      ((hLoadRoot 7 (by omega)).trans (by simpa using hRootDir0 7 (by simp)))
      ((hLoadRoot 8 (by omega)).trans (by simpa using hRootDir0 8 (by simp)))
      ((hLoadRoot 9 (by omega)).trans (by simpa using hRootDir0 9 (by simp)))
      ((hLoadRoot 10 (by omega)).trans (by simpa using hRootDir0 10 (by simp)))
      ((hLoadRoot 12 (by omega)).trans (by simpa using hRootDir0 12 (by simp)))
      ((hLoadRoot 13 (by omega)).trans (by simpa using hRootDir0 13 (by simp)))
      (by omega) (by omega)
      (by have hle : edits.length ≤ oldLastF.m + newLastF.m := treeEditDiff_len_le hDiffLast; omega)
      (by omega)
  -- Phase 4: build `WireSyncCtx` and `WireSyncInv`, run `wireTreeSyncLoop`
  set heap0 := heap + 2 * edits.length
  obtain ⟨canonVal, hLive0, hCanonExt⟩ :=
    liveAccounts_of_solverStateRep hRep0Full hNum0 hOffInv0 hOffBd0 hOldSub
  have hCanonProp : ∀ ei ∈ G0.E, (canonVal ei).forward = true ∧
      |(canonVal ei).gradient| ≤ B ∧ |(canonVal ei).length| ≤ B ∧
      |(canonVal ei).flow| ≤ B ∧ |(canonVal ei).detector| ≤ B := fun ei heiG => by
    obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
    obtain ⟨hf, hg, hl, hfl, hd, _⟩ := hCanonExt (model.intToExt ei) heExt
    rw [heMap] at hf hg hl hfl hd
    exact ⟨hf, hg, hl, hfl, hd⟩
  have hOffAt0 : ∀ ei ∈ G0.E, ei ∉ oldF.E →
      PathEdgeAt mem0 (mem0 (tok.edgeRecords + ei)) 4 L (some (canonVal ei)) := fun ei heiG hnot => by
    obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
    have hrec := (hCanonExt (model.intToExt ei) heExt).2.2.2.2.2.2.2.2.2 (heMap.symm ▸ hnot)
    rwa [heMap] at hrec
  have hAgree3 : ∀ a, tok.tag a ≠ 0 → tok.tag a ≠ 4 → tok.tag a ≠ 5 → st3.mem a = mem0 a :=
    fun a h0 h4 h5 => hmem3.symm ▸ hMem2_eq_mem0 (htagLt h0) h4 h5
  have h2nW : 2 * G0.n + 1 < 2 ^ w := by
    rw [hG0nEq]
    by_cases hn0 : model.extG.n = 0
    · omega
    · have hEnd : tok.names + 2 * tok.tree.n ≤ heap := by
        have := htagLt (by rw [hT10 (2 * tok.tree.n - 1) (by omega)]; decide); omega
      by_cases hlt : root < tok.names
      · omega
      · have hge : tok.names + 2 * tok.tree.n ≤ root := by
          by_contra hcon
          have h10 := hT10 (root - tok.names) (by omega)
          have hsub : tok.names + (root - tok.names) = root := by omega
          have h0 := hT1 0 (by omega); simp only [Nat.add_zero] at h0
          rw [hsub, h0] at h10; omega
        omega
  have hTreeHeapLt : tok.treeHeap < 2 ^ w := by
    have hft := pathRep_foot_base_mem hTreeRep0
    have := htagLt (by rw [hT16 tok.treeHeap hft]; decide)
    omega
  have hSyncRoom : heap0 + edits.length * wireTreeSyncEditSpace L < 2 ^ w := by
    have h1 : 2 * edits.length + edits.length * wireTreeSyncEditSpace L =
        edits.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits.length * (2 + wireTreeSyncEditSpace L) ≤
        lastTreeCap * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_right _ hEditsLeCap
    omega
  let ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root heap heap0 st3.mem G0 oldF newF edits tok canonVal B R :=
    { fmtBits := hFmtBits
      hw11 := by omega
      treeImpl := hTreeImpl
      bindOk := hBindOk
      canonOk := hCanonOk
      isNegOk := hIsNegOk
      treeHeapLt := hTreeHeapLt
      nW := h2nW
      logW := hG0nEq.symm ▸ hLogW
      capT := hG0nEq.symm ▸ hCapT
      diff := hDiffFull
      oldSub := hOldSub
      newSub := hNewSub
      newForest := hNewForest
      oldEnds := fun _ _ => ⟨rfl, rfl⟩
      newEnds := fun _ _ => by
        simp [newF, model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift,
          TreeChain.chainTree, ChainState.toTreeChain, G0]
      vtxE := fun ei hei => by
        obtain ⟨h1, h2⟩ := hRootG0.1 ei hei
        exact ⟨hG0nEq.symm ▸ hRootG0.2.1 _ h1, hG0nEq.symm ▸ hRootG0.2.1 _ h2⟩
      capE := hG0Cap
      rootGraph := hG0nEq.symm ▸ (hmem3.symm ▸ hRootG_m2)
      editsAt := hmem3.symm ▸ hEditsAt2
      editsEnd := le_rfl
      editsTag0 := fun a ha1 _ =>
        ⟨by by_contra hne; have := htagLt hne; omega, by omega⟩
      tags := by
        refine ⟨fun a h => lt_of_lt_of_le (htagLt h) (by omega), hT1, hT9,
          fun sl hsl => hT10 sl (by omega), fun sl hsl => hT11 sl (by omega),
          hT12, hT13, hT14, hT15, hT16, fun ei hei hnot j hj => ?_, fun a ha1 ha2 =>
            hT20 a ha1 (by rwa [← hG0nEq])⟩
        obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei hei
        have hrecEq : st3.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei) :=
          hAgree3 _ (by rw [hT13 ei (hG0Cap ei hei)]; decide)
            (by rw [hT13 ei (hG0Cap ei hei)]; decide) (by rw [hT13 ei (hG0Cap ei hei)]; decide)
        rw [hrecEq]
        have ht18 := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) j hj
        rwa [heMap] at ht18
      canonProp := hCanonProp
      room := hSyncRoom }
  have hSlotEq3 (ei : ℕ) (hei : ei ∈ oldF.E) : st3.mem (tok.slots + ei) = mem0 (tok.slots + ei) :=
    hAgree3 _ (by rw [hT9 ei (hG0Cap ei (hOldSub hei))]; decide)
      (by rw [hT9 ei (hG0Cap ei (hOldSub hei))]; decide) (by rw [hT9 ei (hG0Cap ei (hOldSub hei))]; decide)
  have hNameEq3 (sl : ℕ) (hsl : isEdgeSlot tok.tree.n sl) : st3.mem (tok.names + sl) = mem0 (tok.names + sl) := by
    have hlt : sl < 2 * tok.tree.n := by unfold isEdgeSlot at hsl; omega
    exact hAgree3 _ (by rw [hT10 sl hlt]; decide) (by rw [hT10 sl hlt]; decide) (by rw [hT10 sl hlt]; decide)
  obtain ⟨hTreeRep3_iff, hTreePhi3_eq⟩ := hTreeImpl.1 tok.treeHeap tok.tree tok.treeTok mem0 st3.mem
    (fun a ha => (hAgree3 a (by rw [hT16 a ha]; decide) (by rw [hT16 a ha]; decide)
      (by rw [hT16 a ha]; decide)).symm)
  have hInvInit : WireSyncInv root heap heap0 st3.mem G0 oldF newF edits tok canonVal B R
      [] edits tok.tree tok.treeTok heap0 tok.offReadyCount st3 := by
    refine ⟨rfl, h3_0, h3_1, h3_2, h3_3, by simpa using h3_6, h3_18, hG0nEq.symm ▸ h3_9,
      hG0nEq.symm ▸ h3_10, hG0nEq.symm ▸ h3_11, h3_19, h3_20, h3_22, h3_23, h3_24, h3_25, h3_26,
      le_rfl, by simp,
      fun a ha => by
        rw [hmem3, hFrame2 a (Or.inr ha), hmem1, Function.update_of_ne (by omega)]
        exact hzHeap a (by omega),
      fun a ha => Or.inl ha, fun _ _ _ _ _ _ _ _ _ _ => rfl, hTreeN0.trans hG0nEq.symm,
      ⟨tok.trees, tok.free, tok.depth, hLct0, hNum0,
        namedSlots_congr_slot hNamed0 hSlotEq3 (fun sl _ hsl => hNameEq3 sl hsl),
        liveAccounts_congr_slot hLive0 hSlotEq3⟩,
      hTreeRep3_iff hTreeRep0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ei hei; change ei ∈ oldF.E at hei
      have hcap := hG0Cap ei (hOldSub hei)
      have hsl : isEdgeSlot tok.tree.n (mem0 (tok.slots + ei)) := (hNamed0.forward ei hei).2.1
      have hslLt : mem0 (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hsl; omega
      rw [hSlotEq3 ei hei,
        hAgree3 _ (by rw [hT11 _ hslLt]; decide) (by rw [hT11 _ hslLt]; decide) (by rw [hT11 _ hslLt]; decide),
        hAgree3 _ (by rw [hT12 ei hcap]; decide) (by rw [hT12 ei hcap]; decide) (by rw [hT12 ei hcap]; decide)]
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei (hOldSub hei)
      have hacc := (hAccounts0.1 (model.intToExt ei) heExt).2.2
      rw [heMap] at hacc; split_ifs at hacc with hmem
      · exact hacc.2.2.2.1
      · exact (hmem hei).elim
    · intro ei heiG hnot; change ei ∉ oldF.E at hnot
      have hcap := hG0Cap ei heiG
      rw [hAgree3 _ (by rw [hT9 ei hcap]; decide) (by rw [hT9 ei hcap]; decide) (by rw [hT9 ei hcap]; decide)]
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
      have hacc := (hAccounts0.1 (model.intToExt ei) heExt).2.2
      rw [heMap] at hacc; split_ifs at hacc with hmem
      · exact (hnot hmem).elim
      · exact hacc.1
    · intro ei heiG hnot; change ei ∉ oldF.E at hnot
      have hcap := hG0Cap ei heiG
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
      rw [hAgree3 _ (by rw [hT13 ei hcap]; decide) (by rw [hT13 ei hcap]; decide) (by rw [hT13 ei hcap]; decide)]
      refine (hOffAt0 ei heiG hnot).congr fun a ha1 ha2 => ?_
      have ht18 := (hT1718 (model.intToExt ei) heExt).2 (heMap.symm ▸ hnot) (a - mem0 (tok.edgeRecords + ei)) (by omega)
      have hsub : mem0 (tok.edgeRecords + ei) + (a - mem0 (tok.edgeRecords + ei)) = a := by omega
      rw [heMap, hsub] at ht18
      exact hAgree3 a (by rw [ht18]; decide) (by rw [ht18]; decide) (by rw [ht18]; decide)
    · intro ei heiG hnot hdet; change ei ∉ oldF.E at hnot
      have hcap := hG0Cap ei heiG
      rw [hAgree3 _ (by rw [hT15 ei hcap]; decide) (by rw [hT15 ei hcap]; decide) (by rw [hT15 ei hcap]; decide)]
      obtain ⟨heMap, heExt⟩ := hFreshInv.hRight ei heiG
      have hacc := (hAccounts0.1 (model.intToExt ei) heExt).2.2
      rw [heMap] at hacc; split_ifs at hacc with hmem
      · exact (hnot hmem).elim
      · obtain ⟨_, val, _, hAt, _, _, _, hPush⟩ := hacc
        have hEq := (readPathEdge_eq hAt).symm.trans (readPathEdge_eq (hOffAt0 ei heiG hnot))
        exact hPush (Option.some.inj hEq ▸ hdet)
    · intro ei _ hnot; change ei ∉ oldF.E at hnot; exact ⟨fun h => (hnot h).elim, fun _ => rfl⟩
    · intro e1 he1 e2 he2 hne hnot1 hnot2; change e1 ∉ oldF.E at hnot1; change e2 ∉ oldF.E at hnot2
      rw [hAgree3 _ (by rw [hT13 e1 (hG0Cap e1 he1)]; decide) (by rw [hT13 e1 (hG0Cap e1 he1)]; decide)
          (by rw [hT13 e1 (hG0Cap e1 he1)]; decide),
        hAgree3 _ (by rw [hT13 e2 (hG0Cap e2 he2)]; decide) (by rw [hT13 e2 (hG0Cap e2 he2)]; decide)
          (by rw [hT13 e2 (hG0Cap e2 he2)]; decide)]
      obtain ⟨hm1, hx1⟩ := hFreshInv.hRight e1 he1
      obtain ⟨hm2, hx2⟩ := hFreshInv.hRight e2 he2
      have hxe : model.intToExt e1 ≠ model.intToExt e2 := fun h => hne (hm1.symm.trans (h ▸ hm2))
      have hd := hOffInv0.2 (model.intToExt e1) hx1 (model.intToExt e2) hx2 hxe
        (hm1.symm ▸ hnot1) (hm2.symm ▸ hnot2)
      simpa [hm1, hm2] using hd
    · exact hmem3.symm ▸ (hLoadRoot 11 (by omega)).trans (by simpa using hRootDir0 11 (by simp))
    · have hAL (j : ℕ) (hj : j < tok.intCap) : st3.mem (tok.offReadyList + j) = mem0 (tok.offReadyList + j) :=
        hAgree3 _ (by rw [hT14 j hj]; decide) (by rw [hT14 j hj]; decide) (by rw [hT14 j hj]; decide)
      have hAI (j : ℕ) (hj : j < tok.intCap) : st3.mem (tok.inOffReady + j) = mem0 (tok.inOffReady + j) :=
        hAgree3 _ (by rw [hT15 j hj]; decide) (by rw [hT15 j hj]; decide) (by rw [hT15 j hj]; decide)
      obtain ⟨hc, h1', h2', h3', h4'⟩ := hOffReady0
      refine ⟨hc, fun j hj => ?_, fun j1 hj1 j2 hj2 hne => ?_, fun k hk => ?_, fun k hk h1'' => ?_⟩
      · rw [hAL j (by omega)]; exact ⟨(h1' j hj).1, (hAI _ (h1' j hj).1).trans (h1' j hj).2⟩
      · rw [hAL j1 (by omega), hAL j2 (by omega)]; exact h2' j1 hj1 j2 hj2 hne
      · rw [hAI k hk]; exact h3' k hk
      · rw [hAI k hk] at h1''; obtain ⟨j, hj, hje⟩ := h4' k hk h1''
        exact ⟨j, hj, (hAL j (by omega)).trans hje⟩
  obtain ⟨st4, cLoop, curTree', curTreeTok', nextHeap, curOffCnt', rLoop, hInvEnd, hcLoop⟩ :=
    wireTreeSyncLoop_runs ctx hInvInit
  obtain ⟨_, _, _, _, h4_3, _, _, _, _, _, _, _, _, _, _, _, _,
    hNextGe0, hNextLe0, hzNext, hFootEnd, hFrameEnd, hTreeNEnd,
    ⟨curTrees', curFree', curDepth', hLctEnd, hNumEnd, hNamedEnd, hLiveEnd⟩,
    hTreeRepEnd, hSlotThrEnd, hOffSlotEnd, hOffRecEnd, hOffPushEnd,
    hOffWhereEnd, hOffDisjEnd, hOffCntEnd, hOffReadyEnd⟩ := hInvEnd
  have hApplyEq : applyTreeChanges oldF.E edits = newF.E := hDiffFull.result.2
  rw [hApplyEq] at hNamedEnd hLiveEnd hSlotThrEnd hOffSlotEnd hOffRecEnd hOffPushEnd hOffWhereEnd hOffDisjEnd
  have rRet : Runs w p ω (.ret (.reg 3)) st4 (.returned nextHeap) st4 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, h4_3], rfl, rfl, rfl⟩
  have rAll : Runs w p ω (shiftTermChainBody (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
      (startState [root, heap] mem pos) (.returned nextHeap) st4
      (c1 + (c2 + (c3 + (cLoop + 2 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨st3, c3, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨st4, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hOut_eq_mem (a : ℕ) (ha : a < heap) (hne11 : a ≠ root + 11) (hneBr : a ≠ termBranAddr)
      (h9 : tok.tag a ≠ 9) (h10 : tok.tag a ≠ 10) (h11 : tok.tag a ≠ 11) (h13 : tok.tag a ≠ 13)
      (h14 : tok.tag a ≠ 14) (h15 : tok.tag a ≠ 15) (h16 : tok.tag a ≠ 16) : st4.mem a = mem a := by
    have h1 := hFrameEnd a (lt_of_lt_of_le ha (by omega)) hne11 h9 h10 h11 h13 h14 h15 h16
    rw [h1, hmem3, hFrame2 a (Or.inl ha), hmem1, Function.update_of_ne hneBr]
  have hOut_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (h0 : v ≠ 0) (h1 : v ≠ 1) (h4 : v ≠ 4)
      (h5 : v ≠ 5) (h9 : v ≠ 9) (h10 : v ≠ 10) (h11 : v ≠ 11) (h13 : v ≠ 13)
      (h14 : v ≠ 14) (h15 : v ≠ 15) (h16 : v ≠ 16) : st4.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ h0)
    have hne11 : a ≠ root + 11 := fun h => h1 (ht.symm.trans (h ▸ hT1 11 (by omega)))
    have hneBr : a ≠ termBranAddr := fun h => h4 (ht.symm.trans (h ▸ hTermBranTag))
    rw [hOut_eq_mem a hlt hne11 hneBr (ht ▸ h9) (ht ▸ h10) (ht ▸ h11) (ht ▸ h13)
      (ht ▸ h14) (ht ▸ h15) (ht ▸ h16), hmem0_of_tag (ht ▸ h5)]
  -- `model'` algebraic equalities with `model`
  have hM'_G0 : model'.chain.G 0 = G0 := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, G0]
  have hM'_Gd : model'.chain.G cfg.P.d = model.chain.G cfg.P.d := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hM'_lastK : model'.chain.lastK = model.chain.lastK := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hM'_lastLSFs : model'.chain.lastLSFs = model.chain.lastLSFs := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hM'_lastBran : model'.chain.lastBran = newLastBran := by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift, newLastBran]
  have hM'_bran : ∀ i < cfg.P.d, model'.chain.bran i = model.chain.bran i := fun i _ => by
    simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
  have hFreshInv' : FreshInv model'.extG (model'.chain.G 0) model'.extToInt model'.intToExt model'.nextFresh :=
    hM'_G0.symm ▸ hFreshInv
  have hG0Cap' : ∀ e ∈ (model'.chain.G 0).E, e < tok.intCap := hM'_G0.symm ▸ hG0Cap
  let tok' : SolverToken cfg L Rcore :=
    { tok with
      offReadyCount := curOffCnt'
      tree := curTree'
      trees := curTrees'
      free := curFree'
      depth := curDepth'
      treeTok := curTreeTok'
      owned := fun a => tok.owned a ∨ (heap ≤ a ∧ a < nextHeap)
      tag := fun a =>
        if a < heap then tok.tag a
        else if tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L then 16
        else if a < nextHeap then 18
        else 0 }
  have hThrSame (e : ℕ) (he : e ∈ model.extG.E) :
      let ei := model.extToInt e
      st4.mem (tok.edgeThresholds + ei) = mem0 (tok.edgeThresholds + ei) ∧
      ∀ j < L, st4.mem (mem0 (tok.edgeThresholds + ei) + j) = mem0 (mem0 (tok.edgeThresholds + ei) + j) := by
    intro ei
    have hcap := hG0Cap ei (hFreshInv.hE ▸ Finset.mem_image_of_mem model.extToInt he)
    exact ⟨hOut_eq_mem0 (hT12 ei hcap) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      fun j hj => hOut_eq_mem0 ((hT1718 e he).1 j hj) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  have hGraphEq : ({ G0 with E := newF.E } : MGraph) = newF := by
    have hV : G0.V = newF.V := by
      simp [newF, model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift,
        TreeChain.chainTree, ChainState.toTreeChain, G0]
    have hT : G0.tail = newF.tail := by
      simp [newF, model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift,
        TreeChain.chainTree, ChainState.toTreeChain, G0]
    have hH : G0.head = newF.head := by
      simp [newF, model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift,
        TreeChain.chainTree, ChainState.toTreeChain, G0]
    show ({ V := G0.V, E := newF.E, tail := G0.tail, head := G0.head } : MGraph) =
      { V := newF.V, E := newF.E, tail := newF.tail, head := newF.head }
    rw [hV, hT, hH]
  have hNamedEnd' : TreeEditNamedSlots curTree' curTrees' newF
      (fun ei => st4.mem (tok.slots + ei)) (fun sl => st4.mem (tok.names + sl)) :=
    hGraphEq ▸ hNamedEnd
  have hLiveEnd' : TreeEditLiveAccounts curTree' curTrees' newF
      (fun ei => st4.mem (tok.slots + ei)) canonVal :=
    hGraphEq ▸ hLiveEnd
  obtain ⟨hAccountsEnd, hOrientEnd, hOffInvEnd, hOffBdEnd⟩ :=
    solverEdgeAccounts_of_treeSync (model := model') (P := P) (B := B) hFreshInv' hLctEnd
      hNamedEnd' hLiveEnd' (hM'_G0.symm ▸ hNewSub) hG0Cap'
      (fun e he => by
        obtain ⟨hptr, hlimbs⟩ := hThrSame e he
        change PathIntAt st4.mem (st4.mem (tok.edgeThresholds + model.extToInt e)) 4 L _
        rw [hptr]
        exact (hAccounts0.1 e he).2.1.congr (fun i hi => hlimbs i hi))
      (fun e he => by
        obtain ⟨hf, hg, hl, hfl, hd, h1, h2, h3, h4, _⟩ := hCanonExt e he
        exact ⟨hf, hg, hl, hfl, hd, h1, h2, h3, h4⟩)
      hSlotThrEnd
      (fun e he hnot => hOffSlotEnd (model.extToInt e) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he) hnot)
      (fun e he hnot => hOffRecEnd (model.extToInt e) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he) hnot)
      (fun e he hnot hdet => hOffPushEnd (model.extToInt e) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he) hnot hdet)
      (fun e1 he1 e2 he2 hne hnot1 hnot2 =>
        hOffDisjEnd (model.extToInt e1) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he1)
          (model.extToInt e2) (hFreshInv.hE ▸ Finset.mem_image_of_mem _ he2)
          (fun h => hne ((hFreshInv.hLeft e1 he1).symm.trans (h ▸ hFreshInv.hLeft e2 he2)))
          hnot1 hnot2)
  have hCoreEq (i : ℕ) (hi : i < cfg.P.d) :
      Rcore.rep (tok.coreHandle i) (chainLevelOrdAbs model'.chain i) (tok.coreTok i) st4.mem ∧
      Rcore.phi (tok.coreHandle i) (tok.coreTok i) st4.mem =
        Rcore.phi (tok.coreHandle i) (tok.coreTok i) mem0 := by
    have hAbsEq : chainLevelOrdAbs model'.chain i = chainLevelOrdAbs model.chain i := by
      unfold chainLevelOrdAbs ChainState.levelOrd
      simp [model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift]
    obtain ⟨himp, hphi⟩ := hCoreLocal (tok.coreHandle i) (chainLevelOrdAbs model.chain i)
      (tok.coreTok i) mem0 st4.mem (fun a ha =>
        (hOut_eq_mem0 (hT21 i hi a ha) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm)
    exact ⟨hAbsEq ▸ himp (hCores0 i hi).2.2, hphi.symm⟩
  have hRepEnd : Rrep.rep root model' tok' st4.mem := by
    refine ⟨?_, ?_, ?_, ?_, hFreshInv', ?_, hExtLtM,
      ⟨hG0Cap', hIntCapPos, hNextFreshLe, hI2EId⟩, ?_, hOffReadyEnd,
      hTreeNEnd.trans hG0nEq, hLctEnd, hTreeRepEnd, hAccountsEnd, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have hj16 : j < 16 := by simpa using hj
      by_cases h11 : j = 11
      · subst h11; simpa [tok'] using hOffCntEnd
      · have hne11 : root + j ≠ root + 11 := by omega
        have hneBr : root + j ≠ termBranAddr := fun h => by
          have h1 := hT1 j hj16; rw [h, hTermBranTag] at h1; omega
        rw [hOut_eq_mem (root + j) (by omega) hne11 hneBr (by rw [hT1 j hj16]; decide)
          (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide)
          (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide) (by rw [hT1 j hj16]; decide),
          hmem0_of_tag (by rw [hT1 j hj16]; decide)]
        have h0 := hRootDir0 j hj
        have : [tok'.handle, tok'.table, tok'.levelsEnd, tok'.forward, tok'.inverse,
            tok'.freshCounter, tok'.slots, tok'.names, tok'.slotThresholds, tok'.edgeThresholds,
            tok'.edgeRecords, tok'.offReadyCount, tok'.offReadyList, tok'.inOffReady,
            tok'.rootGraph, tok'.intCap][j] =
          [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse,
            tok.freshCounter, tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds,
            tok.edgeRecords, tok.offReadyCount, tok.offReadyList, tok.inOffReady,
            tok.rootGraph, tok.intCap][j] := by
          interval_cases j <;> first | rfl | contradiction
        exact h0.trans this.symm
    · intro j hj
      have hj8 : j < 8 := by simpa using hj
      rw [hOut_eq_mem0 (hT2 j (by omega)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hDetHdr0 j hj
    · intro j hj
      have hj4 : j < 4 := by simpa using hj
      have h2 : tok.tag (tok.handle + 5 + j) = 2 := by
        have := hT2 (5 + j) (by omega); simpa [Nat.add_assoc] using this
      rw [hOut_eq_mem0 h2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hNumHdr0 j hj
    · intro j hj
      have hj8 : j < 9 := by simpa using hj
      have h2 : tok.tag (tok.handle + 9 + j) = 2 := by
        have := hT2 (9 + j) (by omega); simpa [Nat.add_assoc] using this
      rw [hOut_eq_mem0 h2 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hInitPar0 j hj
    · refine ⟨?_, fun e he => ?_, fun j hj => ?_⟩
      · rw [hOut_eq_mem0 hT6 (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hFreshTab0.1
      · rw [hOut_eq_mem0 (hT7 e he) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hFreshTab0.2.1 e he
      · rw [hOut_eq_mem0 (hT8 j hj) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hFreshTab0.2.2 j hj
    · have hS5 (j : ℕ) (hj : j < 4 * (cfg.P.d + 1) + 1) : st4.mem (tok.levelsEnd + j) = mem (tok.levelsEnd + j) :=
        hOut_eq_mem (tok.levelsEnd + j) (htagLt (by rw [hT5 j hj]; decide))
          (fun h => by have := hT5 j hj; rw [h, hT1 11 (by omega)] at this; omega)
          (fun h => by have := hT5 j hj; rw [h, hTermBranTag] at this; omega)
          (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide)
          (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide) (by rw [hT5 j hj]; decide)
          (by rw [hT5 j hj]; decide)
      refine ⟨fun i => (hS5 i.val (by omega)).trans (hSched'.1 i),
        fun i hi => by
          rw [Nat.add_assoc]
          exact (hS5 ((cfg.P.d + 1) + i) (by omega)).trans
            (by simpa [Nat.add_assoc] using hSched'.2.1 i hi),
        fun i hi => by
          rw [Nat.add_assoc]
          exact (hS5 (2 * (cfg.P.d + 1) + i) (by omega)).trans
            (by simpa [Nat.add_assoc] using hSched'.2.2.1 i hi),
        fun i hi => by
          rw [Nat.add_assoc]
          exact (hS5 (3 * (cfg.P.d + 1) + i) (by omega)).trans
            (by simpa [Nat.add_assoc] using hSched'.2.2.2.1 i hi),
        (hS5 (4 * (cfg.P.d + 1)) (by omega)).trans hSched'.2.2.2.2⟩
    · intro i hi
      have hneBr1 : tok.handle + 18 + i ≠ termBranAddr := by dsimp [termBranAddr]; omega
      have hneBr2 : tok.handle + 18 + (cfg.P.d + 1) + i ≠ termBranAddr := by dsimp [termBranAddr]; omega
      have h4a := hT4 i (by omega)
      have h4b : tok.tag (tok.handle + 18 + (cfg.P.d + 1) + i) = 4 := by
        have := hT4 ((cfg.P.d + 1) + i) (by omega); simpa [Nat.add_assoc] using this
      refine ⟨?_, ?_, (hCoreEq i hi).1⟩
      · rw [hOut_eq_mem _ (htagLt (by rw [h4a]; decide))
          (fun h => by rw [h, hT1 11 (by omega)] at h4a; omega) hneBr1
          (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide)
          (by rw [h4a]; decide) (by rw [h4a]; decide) (by rw [h4a]; decide),
          hmem0_of_tag (by rw [h4a]; decide)]
        exact (hCores0 i hi).1
      · rw [hOut_eq_mem _ (htagLt (by rw [h4b]; decide))
          (fun h => by rw [h, hT1 11 (by omega)] at h4b; omega) hneBr2
          (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide)
          (by rw [h4b]; decide) (by rw [h4b]; decide) (by rw [h4b]; decide),
          hmem0_of_tag (by rw [h4b]; decide), hM'_bran i hi]
        exact (hCores0 i hi).2.1
    · change st4.mem (tok.handle + 18 + cfg.P.d) = tok.termHandle
      have h4d := hT4 cfg.P.d (by omega)
      rw [hOut_eq_mem _ (htagLt (by rw [h4d]; decide))
        (fun h => by rw [h, hT1 11 (by omega)] at h4d; omega) (by dsimp [termBranAddr]; omega)
        (by rw [h4d]; decide) (by rw [h4d]; decide) (by rw [h4d]; decide) (by rw [h4d]; decide)
        (by rw [h4d]; decide) (by rw [h4d]; decide) (by rw [h4d]; decide),
        hmem0_of_tag (by rw [h4d]; decide)]
      exact hTermPtr0
    · have h1 := hFrameEnd termBranAddr (lt_of_lt_of_le hLevelW (by omega))
        (fun h => by rw [h, hT1 11 (by omega)] at hTermBranTag; omega)
        (by rw [hTermBranTag]; decide) (by rw [hTermBranTag]; decide) (by rw [hTermBranTag]; decide)
        (by rw [hTermBranTag]; decide) (by rw [hTermBranTag]; decide) (by rw [hTermBranTag]; decide)
        (by rw [hTermBranTag]; decide)
      rw [h1, hmem3, hFrame2 termBranAddr (Or.inl hLevelW), hmem1, Function.update_self, hM'_lastBran]
    · rw [hM'_Gd, hM'_lastK, hM'_lastLSFs]
      exact (LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E tok.termHandle (model.chain.lastK, model.chain.lastLSFs)
        tok.termTok mem0 st4.mem (fun a ha =>
          (hOut_eq_mem0 (hT19 a ha) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm)).1
        hTermRep0
    · refine ⟨fun j hj => ?_, ?_, ⟨hNewForest, fun ei hei => ?_⟩, hNamedEnd', hOrientEnd⟩
      · rw [hOut_eq_mem0 (hT3 j hj) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hTable0 j hj
      · rw [hM'_G0]
        exact dynGraphAt_of_agree hRootG0 (fun a ha1 ha2 =>
          hOut_eq_mem0 (hT20 a ha1 ha2) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      · have heiG0 := hNewSub hei
        obtain ⟨h1, h2⟩ := hRootG0.1 ei heiG0
        have hEndN : newF.tail ei = G0.tail ei ∧ newF.head ei = G0.head ei := by
          simp [newF, model', alg2LoopShiftStep, Chain.Ordered.algorithm1_shift,
            TreeChain.chainTree, ChainState.toTreeChain, G0]
        have hne := named_account_endpoints_ne (G := newF) hLctEnd hNamedEnd' hei
          (by rw [hTreeNEnd, hG0nEq, hEndN.1]; exact hRootG0.2.1 _ h1)
        exact ⟨hG0Cap ei heiG0, hEndN.1.symm ▸ hRootG0.2.1 _ h1, hEndN.2.symm ▸ hRootG0.2.1 _ h2, hne⟩
    · have hOldTag {a : ℕ} (h : tok.tag a ≠ 0) : tok'.tag a = tok.tag a := by
        dsimp only [tok']; simp only [htagLt h, ↓reduceIte]
      have hTreeNEq : tok'.tree.n = tok.tree.n := by dsimp [tok']; omega
      refine ⟨fun a ha => ?_, fun j hj => (hOldTag (by rw [hT1 j hj]; decide)).trans (hT1 j hj),
        fun j hj => (hOldTag (by rw [hT2 j hj]; decide)).trans (hT2 j hj),
        fun j hj => (hOldTag (by rw [hT3 j hj]; decide)).trans (hT3 j hj),
        fun j hj => (hOldTag (by rw [hT4 j hj]; decide)).trans (hT4 j hj),
        fun j hj => (hOldTag (by rw [hT5 j hj]; decide)).trans (hT5 j hj),
        (hOldTag (by rw [hT6]; decide)).trans hT6,
        fun j hj => (hOldTag (by rw [hT7 j hj]; decide)).trans (hT7 j hj),
        fun j hj => (hOldTag (by rw [hT8 j hj]; decide)).trans (hT8 j hj),
        fun j hj => (hOldTag (by rw [hT9 j hj]; decide)).trans (hT9 j hj),
        fun j hj => (hOldTag (by rw [hT10 j (by omega)]; decide)).trans (hT10 j (by omega)),
        fun j hj => (hOldTag (by rw [hT11 j (by omega)]; decide)).trans (hT11 j (by omega)),
        fun j hj => (hOldTag (by rw [hT12 j hj]; decide)).trans (hT12 j hj),
        fun j hj => (hOldTag (by rw [hT13 j hj]; decide)).trans (hT13 j hj),
        fun j hj => (hOldTag (by rw [hT14 j hj]; decide)).trans (hT14 j hj),
        fun j hj => (hOldTag (by rw [hT15 j hj]; decide)).trans (hT15 j hj),
        fun a ha => ?_, fun e he => ?_,
        fun a ha => (hOldTag (by rw [hT19 a ha]; decide)).trans (hT19 a ha),
        fun a ha1 ha2 => (hOldTag (by rw [hT20 a ha1 ha2]; decide)).trans (hT20 a ha1 ha2),
        fun i hi a ha => (hOldTag (by rw [hT21 i hi a ha]; omega)).trans (hT21 i hi a ha)⟩
      · dsimp only [tok'] at ha ⊢
        split_ifs at ha with hlt hft hhi
        · exact Or.inl (hOwnOfTag a ha)
        · rcases hFootEnd a hft with h0 | ⟨_, hhi'⟩
          · exact Or.inl (hOwnOfTag a (by rw [hT16 a h0]; decide))
          · exact Or.inr ⟨by omega, hhi'⟩
        · exact Or.inr ⟨by omega, hhi⟩
        · exact (ha rfl).elim
      · rcases hFootEnd a ha with h0 | ⟨hlo, _⟩
        · exact (hOldTag (by rw [hT16 a h0]; decide)).trans (hT16 a h0)
        · have ha' : tok.treeHeap ≤ a ∧ a < LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L := ha
          dsimp only [tok']; simp [show ¬ a < heap by omega, ha']
      · refine ⟨fun j hj => ?_, fun hnot j hj => ?_⟩
        · change tok'.tag (st4.mem (tok.edgeThresholds + model.extToInt e) + j) = 17
          rw [(hThrSame e he).1]
          exact (hOldTag (by rw [(hT1718 e he).1 j hj]; decide)).trans ((hT1718 e he).1 j hj)
        · set ei := model.extToInt e
          change tok'.tag (st4.mem (tok.edgeRecords + ei) + j) = 18
          have heiG0 := hFreshInv.hE ▸ Finset.mem_image_of_mem model.extToInt he
          by_cases hOld : ei ∈ oldF.E
          · obtain ⟨hlo, hhi, hnf⟩ := (hOffWhereEnd ei heiG0 hnot).1 hOld
            have hnf' : ¬ (tok.treeHeap ≤ st4.mem (tok.edgeRecords + ei) + j ∧
                st4.mem (tok.edgeRecords + ei) + j <
                LinkCut.PathProg.arenaEnd tok.treeHeap curTreeTok'.1.n L) :=
              hnf _ (by omega) (by omega)
            dsimp only [tok']
            simp only [show ¬ st4.mem (tok.edgeRecords + ei) + j < heap by omega, ↓reduceIte, hnf',
              show st4.mem (tok.edgeRecords + ei) + j < nextHeap by omega]
          · have hrecEq : st4.mem (tok.edgeRecords + ei) = mem0 (tok.edgeRecords + ei) :=
              ((hOffWhereEnd ei heiG0 hnot).2 hOld).trans
                (hAgree3 _ (by rw [hT13 ei (hG0Cap ei heiG0)]; decide)
                  (by rw [hT13 ei (hG0Cap ei heiG0)]; decide)
                  (by rw [hT13 ei (hG0Cap ei heiG0)]; decide))
            rw [hrecEq]
            exact (hOldTag (by rw [(hT1718 e he).2 hOld j hj]; decide)).trans ((hT1718 e he).2 hOld j hj)
  have hPhiCores : (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) st4.mem) =
      (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem0) :=
    Finset.sum_congr rfl (fun i _ => (hCoreEq i.val i.isLt).2)
  have hNextBound : nextHeap ≤ heap + lastTreeCap * (2 + wireTreeSyncEditSpace L) := by
    have h1 : 2 * edits.length + edits.length * wireTreeSyncEditSpace L =
        edits.length * (2 + wireTreeSyncEditSpace L) := by ring
    have h2 : edits.length * (2 + wireTreeSyncEditSpace L) ≤
        lastTreeCap * (2 + wireTreeSyncEditSpace L) := Nat.mul_le_mul_right _ hEditsLeCap
    omega
  have hPresMeta : PreservesLevelMeta tok tok' mem0 st4.mem := by
    refine ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, fun a ht => ?_⟩
    have hge : 20 ≤ tok.tag a := by rcases ht with h | h | h | h <;> omega
    have hlt : a < heap := htagLt (by omega)
    exact ⟨by dsimp only [tok']; exact ite_eq_left hlt,
      hOut_eq_mem0 rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  refine ⟨nextHeap, _, st4, tok', rAll, by omega, hNextBound, rfl, rfl,
    hRepEnd, hPresMeta, hNumEnd, hOffInvEnd, hOffBdEnd, hzNext, ?_, ?_, ?_⟩
  · intro a ha hnf
    have htag0 : tok.tag a = 0 := by
      by_contra hne; exact hnf (Or.inl (hOwnOfTag a hne))
    have hne11 : a ≠ root + 11 := fun h => by rw [h, hT1 11 (by omega)] at htag0; omega
    have hneBr : a ≠ termBranAddr := fun h => by rw [h, hTermBranTag] at htag0; omega
    exact hOut_eq_mem a ha hne11 hneBr (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · intro a ha
    rcases ha with hown | hft | hcore
    · rcases hown with h0 | hnew
      · exact Or.inl (Or.inl h0)
      · exact Or.inr hnew
    · rcases hFootEnd a hft with h0 | ⟨hlo, hhi⟩
      · exact Or.inl (Or.inr (Or.inl h0))
      · exact Or.inr ⟨by omega, hhi⟩
    · exact Or.inl (Or.inr (Or.inr hcore))
  · change _ + (Rtree.phi tok.treeHeap curTreeTok' st4.mem +
      (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) st4.mem) +
      curOffCnt' * drainUnit) ≤
      (41 * lastTreeCap + 320) + 0 * _ +
      (wireTreeSyncEditCost L drainUnit + 2) * (model'.chain.totalTreeUpdates - model.chain.totalTreeUpdates) +
      (Rtree.phi tok.treeHeap tok.treeTok mem0 +
        (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem0) +
        tok.offReadyCount * drainUnit)
    rw [hPhiCores, ← hEditsLenEq, hTreePhi3_eq]
    dsimp only [Rtree] at hcLoop ⊢
    have hcLoop' : cLoop + ((LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap curTreeTok' st4.mem + curOffCnt' * drainUnit) ≤
        edits.length * (wireTreeSyncEditCost L drainUnit + 2) + 2 +
          ((LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok st3.mem + tok.offReadyCount * drainUnit) := hcLoop
    have hc2' : c2 ≤ 41 * lastTreeCap + 120 := by omega
    have hmul : edits.length * (wireTreeSyncEditCost L drainUnit + 2) =
        (wireTreeSyncEditCost L drainUnit + 2) * edits.length := Nat.mul_comm _ _
    clear hRepEnd hAccountsEnd hOrientEnd hOffInvEnd hOffBdEnd hCoreEq hInvInit rAll rLoop r3 r2 r1
      hRep0Full
    omega

end MinCostFlow.MinRatio
