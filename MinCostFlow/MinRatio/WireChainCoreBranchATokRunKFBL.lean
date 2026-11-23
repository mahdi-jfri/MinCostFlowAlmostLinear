module

public import MinCostFlow.MinRatio.WireChainCoreBranchATokHypKFBL
import WordRAM.Tactic

/-!
# Branch A Step 5b: the run (`WireChainCoreBranchATokRunKFBL`)

Step 5b runs `wireBranchAReadyRetStmt` from the state `s5g`. It saves the return value
`nextHeap + 1` in `reg 4`, loads the edge count `mNew` of the new level 0 from the new root graph,
calls the off-ready rebuild `wireRebuildOffReadyBody`, and returns `reg 4`.

The off-ready rebuild reads, for each edge off the new forest, the detector word of its edge
record. So the main work here is to show that these records are where the rebuild expects them
(`hDet`): they lie below `heap2`, and their words below `uIntBuf` carry tag 18, so they are off
the two off-ready arrays.

The result `readyRet_runs` gives the memory after the run only through what the rebuild changes:
the count word `root + 11` and the two off-ready arrays.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

namespace WireBranchATokHypKFBL

variable {w L P m V psi k epsExp drainUnit vCap eCap root uIntBuf heap heap1 heapSync heap2
  newLen0 newRootGraph heap3 heap4 nextHeap termTok4 : ℕ} {cfg : Alg2Config}
  {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 mem : ℕ → ℕ} {s4 s5g : State}
  {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
  {gVec lVec : ℕ → ℝ} {curTree2 : PathTreeState} {curTrees2 : List AuxTree}
  {curFree2 : List ℕ} {curDepth2 : ℕ → ℕ}
  {curTreeTok1 curTreeTok2 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
  {newCanonVal : ℕ → PathEdgeValue} {coreTok4 : ℕ → Rcore.τ}

variable (H : WireBranchATokHypKFBL w L P m V psi k epsExp drainUnit vCap eCap root uIntBuf heap
  heap1 heapSync heap2 newLen0 newRootGraph heap3 heap4 nextHeap termTok4 cfg Rcore mem0 mem s4
  s5g model tok U B R gVec lVec curTree2 curTrees2 curFree2 curDepth2 curTreeTok1 curTreeTok2
  newCanonVal coreTok4)
include H

set_option maxHeartbeats 400000 in
/-- The run of Branch A Step 5b (`wireBranchAReadyRetStmt`) from `s5g`. It returns
`nextHeap + 1`, costs at most `80 * mNew + 120`, and changes only the count word `root + 11` and
the two off-ready arrays, which it fills from the detectors of the edges off the new forest. -/
theorem readyRet_runs {isNeg rebuildOffReadyProc : ℕ} {p : Program} {ω : ℕ → Bool}
    (hRebuildProc : p.procs[rebuildOffReadyProc]? = some (wireRebuildOffReadyBody isNeg))
    (hIsNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4)) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    let mNew := (modelPre.chain.G 0).m
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let G0' := (model.chain.G 0).applyBatch tr.2.2.2.2
    ∃ (newOffCnt cost : ℕ) (out : State),
      Runs w p ω (wireBranchAReadyRetStmt rebuildOffReadyProc) s5g (.returned (nextHeap + 1))
        out cost ∧
      cost ≤ 80 * mNew + 120 ∧
      newOffCnt ≤ mNew ∧
      out.mem (root + 11) = newOffCnt ∧
      OffReadyInv out.mem newOffCnt tok.offReadyList tok.inOffReady tok.intCap ∧
      (∀ j < mNew, out.mem (tok.inOffReady + j) =
        if s5g.mem (tok.slots + j) = 0 ∧
            0 ≤ (newCanonVal (compactUnrank G0'.E j)).detector then 1 else 0) ∧
      ∀ a, a ≠ root + 11 → (a < tok.offReadyList ∨ tok.offReadyList + tok.intCap ≤ a) →
        (a < tok.inOffReady ∨ tok.inOffReady + tok.intCap ≤ a) → out.mem a = s5g.mem a := by
  intro modelPre mNew tr G0'
  classical
  obtain ⟨hRootDir0, hDetHdr0, _, _, _, _, _, ⟨_, hIntCapPos, _, _⟩, _, _, _, _, _, _, _, _, _,
    _, _, hTags0⟩ := H.rep0
  obtain ⟨_, hT1, hT2, _, _, _, _, _, _, hT9, _, _, _, hT13, hT14, hT15, _⟩ := hTags0
  obtain ⟨hH1Lo, hSyncLo, hH2Lo, hNL0Lo, hNRGLo, hH3Lo, hH4Lo, hNextLo, hNextW⟩ := H.heaps
  have hU := H.uLeHeap
  have hw18 := H.w18
  have hLpos := H.lpos
  have hr3_5g := H.r3_5g
  have hr70_5g := H.r70_5g
  let newF := modelPre.chain.toTreeChain.chainTree
  let canonC : ℕ → PathEdgeValue := fun j => newCanonVal (compactUnrank G0'.E j)
  have hPreG0m : mNew = G0'.m := H.preG0m
  have hPreE2I : modelPre.extToInt = level0E2I true G0' tr.2.1 := H.preE2I
  have hPreG0 : modelPre.chain.G 0 = G0'.compact := H.preG0
  have hFreshPre : FreshInv modelPre.extG (modelPre.chain.G 0) modelPre.extToInt
      modelPre.intToExt modelPre.nextFresh := H.freshPre
  have hR14_5g : s5g.mem (root + 14) = newRootGraph :=
    (H.s5g_eq4_root 14 (by omega) (by omega)).trans H.r14_4
  -- the three assignments before the call
  let s5h := { s5g with regs := Function.update s5g.regs 4 (nextHeap + 1) }
  let s5i := { s5h with regs := Function.update s5h.regs 10 newRootGraph }
  let s5j := { s5i with regs := Function.update s5i.regs 11 mNew }
  have hr5h : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.const 1))) s5g .normal s5h 4 :=
    runs_assign_iff.mpr ⟨nextHeap + 1, by
      simp [Expr.eval, BinOp.eval, hr3_5g, show 1 < 2 ^ w by omega,
        show nextHeap + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr5i : Runs w p ω (.assign 10 (.load (.bin .add (.reg 70) (.const 14)))) s5h .normal s5i
      5 :=
    runs_assign_iff.mpr ⟨newRootGraph, by
      simp [Expr.eval, BinOp.eval, s5h, hr70_5g, show 14 < 2 ^ w by omega,
        show root + 14 < 2 ^ w by have := H.tagLt (by rw [hT1 14 (by omega)]; decide); omega,
        hR14_5g],
      rfl, rfl, rfl⟩
  have hRG5g : DynGraphAt s5g.mem newRootGraph vCap eCap (modelPre.chain.G 0) :=
    dynGraphAt_of_agree H.rg4 (fun a ha1 ha2 => H.s5g_eq4_hi a (by omega) (by omega))
  have hr5j : Runs w p ω (.assign 11 (.load (.bin .add (.reg 10) (.const 3)))) s5i .normal s5j
      5 :=
    runs_assign_iff.mpr ⟨mNew, by
      simp [Expr.eval, BinOp.eval, s5i, s5h, show 3 < 2 ^ w by omega,
        show newRootGraph + 3 < 2 ^ w by unfold dynGraphSize at hH3Lo; omega,
        show s5g.mem (newRootGraph + 3) = mNew by simpa [dgMOff] using hRG5g.2.2.2.2.2.2.1],
      rfl, rfl, rfl⟩
  -- the root directory that the rebuild reads
  have hRoot5j : SolverRootDirAt s5j.mem root tok.handle tok.table tok.levelsEnd tok.forward
      tok.inverse tok.freshCounter tok.slots tok.names tok.slotThresholds tok.edgeThresholds
      tok.edgeRecords 0 tok.offReadyList tok.inOffReady newRootGraph tok.intCap := fun j hj => by
    have hj16 : j < 16 := by simpa using hj
    change s5g.mem (root + j) = _
    by_cases h11 : j = 11
    · subst h11; simpa using H.r11_5g
    · by_cases h14 : j = 14
      · subst h14; simpa using hR14_5g
      · rw [H.s5g_eq4_root j hj16 h11, H.s4_root j hj16 h11 h14]
        have h0 := hRootDir0 j hj
        have : [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse, tok.freshCounter,
            tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds, tok.edgeRecords,
            0, tok.offReadyList, tok.inOffReady, newRootGraph, tok.intCap][j] =
          [tok.handle, tok.table, tok.levelsEnd, tok.forward, tok.inverse, tok.freshCounter,
            tok.slots, tok.names, tok.slotThresholds, tok.edgeThresholds, tok.edgeRecords,
            tok.offReadyCount, tok.offReadyList, tok.inOffReady, tok.rootGraph, tok.intCap][j] := by
          interval_cases j <;> first | rfl | contradiction
        exact h0.trans this.symm
  -- the detector words of the edges off the new forest
  have hDet5j : ∀ j < mNew, s5j.mem (tok.slots + j) = 0 →
      PathIntAt s5j.mem (s5j.mem (tok.edgeRecords + j) + 2 + 3 * L) 4 L (canonC j).detector ∧
      s5j.mem (tok.edgeRecords + j) + 2 + 4 * L < 2 ^ w ∧
      (∀ t < L, (s5j.mem (tok.edgeRecords + j) + 2 + 3 * L + t < tok.inOffReady ∨
          tok.inOffReady + tok.intCap ≤ s5j.mem (tok.edgeRecords + j) + 2 + 3 * L + t) ∧
        (s5j.mem (tok.edgeRecords + j) + 2 + 3 * L + t < tok.offReadyList ∨
          tok.offReadyList + tok.intCap ≤ s5j.mem (tok.edgeRecords + j) + 2 + 3 * L + t)) := by
    intro j hj hSl0
    simp only [show s5j.mem = s5g.mem from rfl] at hSl0 ⊢
    have hjG0 : j ∈ (modelPre.chain.G 0).E := by
      rw [hPreG0]; simp [MGraph.compact]; rwa [hPreG0m] at hj
    have hjNotNew : j ∉ newF.E := fun hm => by
      have hSl := (H.namedEnd.forward j hm).2.1
      unfold isEdgeSlot at hSl; change s5g.mem (tok.slots + j) = 0 at hSl0; omega
    obtain ⟨hPA, hRecEq⟩ := H.offRecEnd j hjG0 hjNotNew
    obtain ⟨heMap, heExt⟩ := hFreshPre.hRight j hjG0
    have hLoc (k : ℕ) (hk : k < 2 + 4 * L) :
        s5g.mem (tok.edgeRecords + j) + k < heap2 ∧
        (s5g.mem (tok.edgeRecords + j) + k < uIntBuf →
          tok.tag (s5g.mem (tok.edgeRecords + j) + k) = 18) := by
      rw [hRecEq]
      have h := H.recLoc (modelPre.intToExt j) (H.preExtG ▸ heExt)
        (s4.mem (tok.edgeRecords + j) + k)
      rw [← hPreE2I, heMap] at h; exact h (by omega) (by omega)
    refine ⟨by simpa [Nat.add_assoc] using hPA.2.2.2.2.2,
      by have := (hLoc (2 + 4 * L - 1) (by omega)).1; omega,
      fun t ht => ⟨?_, ?_⟩⟩
    · by_contra h; push Not at h
      have h15 := tag_of_block tok.tag hT15 (s5g.mem (tok.edgeRecords + j) + (2 + 3 * L + t))
        (by omega) (by omega)
      have h18 := (hLoc (2 + 3 * L + t) (by omega)).2 (H.tagLt (by rw [h15]; decide))
      omega
    · by_contra h; push Not at h
      have h14 := tag_of_block tok.tag hT14 (s5g.mem (tok.edgeRecords + j) + (2 + 3 * L + t))
        (by omega) (by omega)
      have h18 := (hLoc (2 + 3 * L + t) (by omega)).2 (H.tagLt (by rw [h14]; decide))
      omega
  have hR11a : tok.tag (root + 11) = 1 := hT1 11 (by omega)
  obtain ⟨newOffCnt, outRdy, cRdy, rRdyBody, hcRdy, hNewOffLe, hR11End, hOffInvEnd,
      hInOffDone, _, hFrRdy⟩ :=
    wireRebuildOffReadyBody_runs (w := w) (isNeg := isNeg) (root := root) (mNew := mNew)
      (handle := tok.handle) (table := tok.table) (levelsEnd := tok.levelsEnd)
      (forward := tok.forward) (inverse := tok.inverse) (freshCounter := tok.freshCounter)
      (slots := tok.slots) (names := tok.names) (slotThresholds := tok.slotThresholds)
      (edgeThresholds := tok.edgeThresholds) (edgeRecords := tok.edgeRecords)
      (offReadyCount := 0) (offReadyList := tok.offReadyList) (inOffReady := tok.inOffReady)
      (rootGraph := newRootGraph) (intCap := tok.intCap) (L := L) (pos := s5j.pos)
      (det := fun j => (canonC j).detector) (p := p) (ω := ω) (mem := s5j.mem)
      hIsNegOk hRoot5j
      ((H.s5g_eq4_tag (hT2 5 (by omega)) (by decide)).trans
        ((H.s4_tag (hT2 5 (by omega)) (by decide) (by omega) (by omega)
          (fun _ _ => by omega)).trans (by simpa using hDetHdr0 5 (by simp))))
      (by rw [hPreG0m]; exact H.g0'mLeR.2) hLpos (offReadyInv_zero_inOffReady H.offReady5g)
      hDet5j
      (tagBlocksDisj tok.tag _ _ 14 _ _ 15 hIntCapPos hIntCapPos hT14 hT15 (by decide))
      (tagBlocksDisj tok.tag _ _ 13 _ _ 14 hIntCapPos hIntCapPos hT13 hT14 (by decide))
      (tagBlocksDisj tok.tag _ _ 13 _ _ 15 hIntCapPos hIntCapPos hT13 hT15 (by decide))
      (tagBlocksDisj tok.tag _ _ 9 _ _ 14 hIntCapPos hIntCapPos hT9 hT14 (by decide))
      (tagBlocksDisj tok.tag _ _ 9 _ _ 15 hIntCapPos hIntCapPos hT9 hT15 (by decide))
      (by
        by_contra h; push Not at h
        have := tag_of_block tok.tag hT14 (root + 11) h.1 h.2; omega)
      (by
        by_contra h; push Not at h
        have := tag_of_block tok.tag hT15 (root + 11) h.1 h.2; omega)
      (by have := H.tagLt (by rw [hT1 15 (by omega)]; decide); omega)
      (by have := H.tagLt (by rw [hT2 5 (by omega)]; decide); omega)
      (by have := H.tagLt (by rw [hT9 (tok.intCap - 1) (by omega)]; decide); omega)
      (by have := H.tagLt (by rw [hT13 (tok.intCap - 1) (by omega)]; decide); omega)
      (by have := H.tagLt (by rw [hT14 (tok.intCap - 1) (by omega)]; decide); omega)
      (by have := H.tagLt (by rw [hT15 (tok.intCap - 1) (by omega)]; decide); omega)
      (by omega) (by omega)
  -- the call and the return
  let s5k : State :=
    { regs := Function.update s5j.regs 12 newOffCnt, mem := outRdy.mem, pos := outRdy.pos }
  have hr5k : Runs w p ω (.call 12 rebuildOffReadyProc [.reg 70, .reg 11]) s5j .normal s5k
      (2 + cRdy + 1) :=
    runs_call_iff.mpr ⟨[root, mNew], wireRebuildOffReadyBody isNeg, .returned newOffCnt, outRdy,
      cRdy, by simp [evalArgs, Expr.eval, s5j, s5i, s5h, hr70_5g], hRebuildProc, rRdyBody, rfl,
      rfl, by simp [argsSize, Expr.size]⟩
  have hrRet : Runs w p ω (.ret (.reg 4)) s5k (.returned (nextHeap + 1)) s5k 2 :=
    runs_ret_iff.mpr ⟨nextHeap + 1, by simp [Expr.eval, s5k, s5j, s5i, s5h], rfl, rfl, rfl⟩
  have rReadyRet : Runs w p ω (wireBranchAReadyRetStmt rebuildOffReadyProc) s5g
      (.returned (nextHeap + 1)) s5k
      (4 + (5 + (5 + ((2 + cRdy + 1) + 2 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s5h, 4, _, hr5h,
    runs_seq_iff.mpr (Or.inr ⟨s5i, 5, _, hr5i,
    runs_seq_iff.mpr (Or.inr ⟨s5j, 5, _, hr5j,
    runs_seq_iff.mpr (Or.inr ⟨s5k, 2 + cRdy + 1, 2, hr5k, hrRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  exact ⟨newOffCnt, _, s5k, rReadyRet, by omega, hNewOffLe, hR11End, hOffInvEnd, hInOffDone,
    hFrRdy⟩

end WireBranchATokHypKFBL

end MinCostFlow.MinRatio
