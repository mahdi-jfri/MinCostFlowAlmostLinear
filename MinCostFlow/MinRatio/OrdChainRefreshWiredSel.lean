module

public import MinCostFlow.MinRatio.OrdSelSpecs
public import MinCostFlow.MinRatio.OrdChainRefreshWiredBase
public import MinCostFlow.MinRatio.SolverSelectPreserve
import WordRAM.Tactic

/-!
# Select-aware wired chain refresh (`OrdChainRefreshWiredSel`)

Proves `chainRefreshStepSpecWKFBLSel_wired`: `ordChainRefreshWiredBody` implements
`ChainRefreshStepSpecWKFBLSel` given `OrdChainUpdateCoreSpecWKFBLSel` and `ShiftQuotaWriterSpec`.
Threads `SolverLevelCapsInv`, `SolverSelectInv`, `SolverSelectRegionInv`,
`sg.reembPot = chainReembPot pot`, footprint
`Rrep.foot ∨ sg.owned`, and combined potential `Rrep.phi + K * sg.reembPot` cleanly across the
pre-core edit encoder, the chain core, the post-core pass reset (tag `5` only), and the quota
writer (`quotaBase .. quotaBase + d + 1`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program MinCostFlow.Bundle

private theorem offTreeRecBound_preReset_to_preLoop_sel {cfg : Alg2Config} {model : Alg2State cfg}
    {U : List Update} {gVec lVec : ℕ → ℝ} {L : ℕ} {mem : ℕ → ℕ} {edgeRecords : ℕ} {B : ℤ}
    (h : OffTreeRecBound (alg2PreResetState cfg model U gVec lVec) L mem edgeRecords B) :
    OffTreeRecBound (alg2PreLoopState cfg model U gVec lVec) L mem edgeRecords B := h

/-- Discharges `ChainRefreshStepSpecWKFBLSel` for `ordChainRefreshWiredBody` from
`OrdChainUpdateCoreSpecWKFBLSel` and `ShiftQuotaWriterSpec`. -/
theorem chainRefreshStepSpecWKFBLSel_wired
    {w L P E m V psi k epsExp drainUnit capExp limbMul capLimit intCapMax forestEdgeCap
      vCap eCap dMul kOff K pLast slot chainRefreshProc ordEditsProc ordChainCoreProc shiftQuotaWriterProc
      quotaBudget toolMul treeMul : ℕ}
    {coreSpace coreFixed : ℕ → ℕ}
    {cfg : Alg2Config} {G : MGraph} {pot : cfg.T.State → ℕ}
    {DeepInv : ChainState cfg.T cfg.P → Prop}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program}
    (hlocal : Rcore.Local)
    (hAt : p.procs[chainRefreshProc]? =
      some (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc))
    (hEditsAt : p.procs[ordEditsProc]? = some level0BatchToOrdEditsBody)
    (hCore : OrdChainUpdateCoreSpecWKFBLSel w L P E m V psi k epsExp drainUnit capExp limbMul
      capLimit intCapMax forestEdgeCap vCap eCap dMul kOff K pLast slot cfg G pot DeepInv Rcore p
      ordChainCoreProc coreSpace coreFixed toolMul treeMul)
    (hQuota : ShiftQuotaWriterSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      shiftQuotaWriterProc quotaBudget)
    (hw11 : 11 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w) :
    ChainRefreshStepSpecWKFBLSel w L P E m V psi k epsExp drainUnit capExp limbMul capLimit
      intCapMax forestEdgeCap vCap eCap dMul kOff K pLast slot cfg G pot DeepInv Rcore p
      chainRefreshProc
      (fun uLen => cfg.P.d + (8 * uLen + 1) + coreSpace uLen)
      (fun uLen => coreFixed uLen + quotaBudget + 120 * uLen + 62 * (cfg.P.d + 1) + 240)
      toolMul treeMul := by
  obtain ⟨bCore, hbCore, hCoreRun⟩ := hCore
  obtain ⟨bQuota, hbQuota, hQuotaRun⟩ := hQuota
  refine ⟨ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc, hAt, ?_⟩
  intro root uIntBuf g l quotaBase heap pos ω mem0 mem model tok sg U B R
  dsimp only
  intro hrep0 hMeta0 hCaps0 hSel0 hPot0 hReg0 hReach hDeep hFits hTreeNum hnumB hoffB hbdB hB0
    hfitB hrangeM hflowM haccM hICap hICapMax
    hFEdge hLogW hLoopBefore hLoopAfter hCap hBr hglB hglAg htags0 hfreshTab hnfCap hbatchInt
    hsmallInt hRefreshU hwordsU hKeyW hQuotaW hfootLt hgEnd hlEnd hglOff hqEnd hqOut huLeH hz hroom
    hglValid hLay0
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hlocR := solverStateRep_local cfg L P m V psi k epsExp drainUnit hlocal
  let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  let U_int := tr.2.2.2.2
  let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  let modelPre := alg2PreResetState cfg model U gVec lVec
  let model1 := alg2PreLoopState cfg model U gVec lVec
  have hrep0' := hrep0
  obtain ⟨hroot0, _, _, hchP0, hfrInv0, _, _, _, hsched0, _, _, _, _, _, _, _, _, _, _, htagsM0⟩ := hrep0
  obtain ⟨hOwn0, t1_0, t2_0, _, _, t5_0, t6_0, t7_0, t8_0, _⟩ := htagsM0
  have hheapW : heap < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw8 : 8 < 2 ^ w := by omega
  have hltU {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < uIntBuf :=
    hfootLt a (Or.inl (Or.inl (hOwn0 a (ht ▸ hv))))
  have hmemEqOfTag {a v : ℕ} (ht : tok.tag a = v) (h6 : v ≠ 6) (h7 : v ≠ 7) (h8 : v ≠ 8) (hv : v ≠ 0) :
      mem a = mem0 a :=
    htags0 a (hltU ht hv) (fun h => h6 (ht.symm.trans h)) (fun h => h7 (ht.symm.trans h))
      (fun h => h8 (ht.symm.trans h))
  have hroot0M : mem root = tok.handle :=
    (hmemEqOfTag (t1_0 0 (by omega)) (by decide) (by decide) (by decide) (by decide)).trans
      (by simpa using hroot0 0 (by simp))
  have hroot2M : mem (root + 2) = tok.levelsEnd :=
    (hmemEqOfTag (t1_0 2 (by omega)) (by decide) (by decide) (by decide) (by decide)).trans
      (by simpa using hroot0 2 (by simp))
  have hdM : mem (tok.handle + 11) = cfg.P.d :=
    (hmemEqOfTag (t2_0 11 (by omega)) (by decide) (by decide) (by decide) (by decide)).trans
      (by simpa [Nat.add_assoc] using hchP0 2 (by simp))
  have hrc0M : ∀ j < cfg.P.d, mem (tok.levelsEnd + 2 * (cfg.P.d + 1) + j) = model.chain.rebuildCount j := by
    intro j hj
    have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + j = tok.levelsEnd + (2 * (cfg.P.d + 1) + j) := by omega
    rw [h1]
    exact (hmemEqOfTag (t5_0 (2 * (cfg.P.d + 1) + j) (by omega)) (by decide) (by decide) (by decide) (by decide)).trans
      (by rw [← h1]; exact hsched0.2.2.1 j (by omega))
  have hlvEndLt : tok.levelsEnd + 4 * (cfg.P.d + 1) < uIntBuf :=
    hltU (t5_0 (4 * (cfg.P.d + 1)) (by omega)) (by decide)
  -- Prefix loads (`reg 20..30`)
  let s0 := startState [root, uIntBuf, g, l, quotaBase, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 20 root }
  let s2 : State := { s1 with regs := Function.update s1.regs 21 uIntBuf }
  let s3 : State := { s2 with regs := Function.update s2.regs 22 g }
  let s4 : State := { s3 with regs := Function.update s3.regs 23 l }
  let s5 : State := { s4 with regs := Function.update s4.regs 24 quotaBase }
  let s6 : State := { s5 with regs := Function.update s5.regs 25 heap }
  let s7 : State := { s6 with regs := Function.update s6.regs 26 tok.handle }
  let s8 : State := { s7 with regs := Function.update s7.regs 27 tok.levelsEnd }
  let s9 : State := { s8 with regs := Function.update s8.regs 28 cfg.P.d }
  let s10 : State := { s9 with regs := Function.update s9.regs 29 (cfg.P.d + 1) }
  let s11 : State := { s10 with regs := Function.update s10.regs 30 (tok.levelsEnd + 2 * (cfg.P.d + 1)) }
  have r1 : Runs w p ω (.assign 20 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 21 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨uIntBuf, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 22 (.reg 2)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨g, by simp [Expr.eval, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 23 (.reg 3)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨l, by simp [Expr.eval, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 24 (.reg 4)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨quotaBase, by simp [Expr.eval, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 25 (.reg 5)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s5, s4, s3, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 26 (.load (.reg 20))) s6 .normal s7 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s6, s5, s4, s3, s2, s1, s0, startState, hroot0M], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 20) (.const 2)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd, by
      have hr2Lt : root + 2 < 2 ^ w := lt_trans (hltU (t1_0 2 (by omega)) (by decide)) (by omega)
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState, hw2, hr2Lt, hroot2M], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 28 (.load (.bin .add (.reg 26) (.const 11)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨cfg.P.d, by
      have hh11Lt : tok.handle + 11 < 2 ^ w := lt_trans (hltU (t2_0 11 (by omega)) (by decide)) (by omega)
      simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState, hw11, hh11Lt, hdM], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 29 (.bin .add (.reg 28) (.const 1))) s9 .normal s10 4 :=
    runs_assign_iff.mpr ⟨cfg.P.d + 1, by simp [Expr.eval, BinOp.eval, s9, hw1, hdW], rfl, rfl, rfl⟩
  have r11 : Runs w p ω (.assign 30 (.bin .add (.reg 27) (.bin .mul (.const 2) (.reg 29)))) s10 .normal s11 6 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd + 2 * (cfg.P.d + 1), by
      simp [Expr.eval, BinOp.eval, s10, s9, s8, hw2, show 2 * (cfg.P.d + 1) < 2 ^ w by omega,
        show tok.levelsEnd + 2 * (cfg.P.d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Step 1: snapshot old `rebuildCount[0..d-1]` at `[heap, heap + d)`
  obtain ⟨s12, cSnap, rSnap, hcSnap, hsnapMem, hsnapFr, hsnapRegs⟩ :=
    snapshotRebuildCounts_runs (w := w) (dstBase := heap)
      (srcBase := tok.levelsEnd + 2 * (cfg.P.d + 1)) (d := cfg.P.d) (ω := ω) (st := s11)
      (by simp [s11, s10, s9, s8, s7, s6]) (by simp [s11, s10, s9]) (by simp [s11])
      (by omega) (by omega) hw1
  let editsPtr := heap + cfg.P.d
  let s12b : State := { s12 with regs := Function.update s12.regs 36 editsPtr }
  have r12b : Runs w p ω (.assign 36 (.bin .add (.reg 25) (.reg 28))) s12 .normal s12b 4 :=
    runs_assign_iff.mpr ⟨editsPtr, by
      simp [Expr.eval, BinOp.eval, hsnapRegs 25 (by decide), hsnapRegs 28 (by decide),
        s11, s10, s9, s8, s7, s6, show editsPtr < 2 ^ w by omega, editsPtr], rfl, rfl, rfl⟩
  have hs12_snap (j : ℕ) (hj : j < cfg.P.d) : s12.mem (heap + j) = model.chain.rebuildCount j :=
    (hsnapMem j hj).trans (hrc0M j hj)
  -- Step 2: run `level0BatchToOrdEditsBody` at `editsPtr = heap + d`
  have hEdgeU : ∀ u ∈ U, IsEdgeUpdate u := refreshBatch_isEdgeUpdate hRefreshU
  have hEdgeInt : ∀ u ∈ U_int, IsEdgeUpdate u :=
    (translateBatch_freshIdsAlongBatch hfrInv0 hRefreshU.1 hEdgeU).1
  have hIntLenEq : U_int.length = U.length :=
    (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
      model.nextFresh hfrInv0 hRefreshU.1).2.2.2.2.1
  have hIntWordsLen : heap - uIntBuf = (batchWords U_int).length :=
    smallBatchAt_len_eq_of_edgeOnly hEdgeInt hsmallInt
  obtain ⟨hIntWordsLt, hIntKeysLt⟩ :=
    translateBatch_words_lt hfrInv0 hRefreshU.1 hEdgeU hwordsU hKeyW hw1
  have hbatch12 : BatchAt s12.mem uIntBuf U_int := fun j hj =>
    (hsnapFr (uIntBuf + j) (Or.inl (by omega))).trans (hbatchInt j hj)
  obtain ⟨cEd, sEd, rEd, hcEd, hEdLe, hOrdAt, hEdW, hEdFr⟩ :=
    level0BatchToOrdEditsBody_runs (w := w) (uIntBuf := uIntBuf) (outEdits := editsPtr)
      (pos := s12b.pos) (p := p) (ω := ω) (mem := s12.mem) (U := U_int)
      hbatch12 hEdgeInt (by omega)
      (fun j hj => by rw [hbatch12 j hj]; exact hIntWordsLt _ (List.getElem_mem hj))
      hIntKeysLt (by rw [hIntLenEq]; omega) hw8
  let editWords := 1 + batchOrdPayloadWords U_int
  let afterEdits := editsPtr + editWords
  have hEdLeU : editWords ≤ 8 * U.length + 1 := by rw [← hIntLenEq]; exact hEdLe
  let s13 : State := { regs := Function.update s12b.regs 31 editWords, mem := sEd.mem, pos := sEd.pos }
  let s14 : State := { s13 with regs := Function.update s13.regs 32 afterEdits }
  have r12 : Runs w p ω (.call 31 ordEditsProc [.reg 21, .reg 36]) s12b .normal s13 (cEd + 3) :=
    runs_call_iff.mpr ⟨[uIntBuf, editsPtr], level0BatchToOrdEditsBody, .returned editWords, sEd, cEd,
      by simp [evalArgs, Expr.eval, s12b, hsnapRegs 21 (by decide), s11, s10, s9, s8, s7, s6, s5, s4, s3, s2],
      hEditsAt, rEd, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have r13 : Runs w p ω (.assign 32 (.bin .add (.reg 36) (.reg 31))) s13 .normal s14 4 :=
    runs_assign_iff.mpr ⟨afterEdits, by
      simp [Expr.eval, BinOp.eval, s13, s12b, show afterEdits < 2 ^ w by omega, afterEdits], rfl, rfl, rfl⟩
  have hs14_ltHeap (a : ℕ) (ha : a < heap) : s14.mem a = mem a :=
    (hEdFr a (Or.inl (by omega))).trans (hsnapFr a (Or.inl ha))
  have hs14_snap (j : ℕ) (hj : j < cfg.P.d) : s14.mem (heap + j) = model.chain.rebuildCount j :=
    (hEdFr (heap + j) (Or.inl (by omega))).trans (hs12_snap j hj)
  have hs14_fresh : FreshTablesAt s14.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 :=
    ⟨(hs14_ltHeap _ (lt_of_lt_of_le (hltU t6_0 (by decide)) huLeH)).trans hfreshTab.1,
      fun e he => (hs14_ltHeap _ (lt_of_lt_of_le (hltU (t7_0 e he) (by decide)) huLeH)).trans (hfreshTab.2.1 e he),
      fun e he => (hs14_ltHeap _ (lt_of_lt_of_le (hltU (t8_0 e he) (by decide)) huLeH)).trans (hfreshTab.2.2 e he)⟩
  have hs14_batch : BatchAt s14.mem uIntBuf U_int := fun j hj =>
    (hs14_ltHeap (uIntBuf + j) (by omega)).trans (hbatchInt j hj)
  have hs14_small : DynSpanner.Program.SmallBatchAt s14.mem uIntBuf (model.chain.G 0) U_int
      (editsPtr - cfg.P.d - uIntBuf) := by
    rw [show editsPtr - cfg.P.d - uIntBuf = heap - uIntBuf by omega]
    exact smallBatchAt_congr hsmallInt (fun x h1 h2 => hs14_ltHeap x (by omega))
  have hs14_hz : ZeroFrom s14.mem afterEdits := fun a ha =>
    (hEdFr a (Or.inr ha)).trans ((hsnapFr a (Or.inr (by omega))).trans (hz a (by omega)))
  -- Step 3: call select-aware `ordChainCoreProc`
  obtain ⟨nextHeap, cCore, stCore, tokC, sg', hrCore, hnhLo, hnhHi, hlevC, hintCapC,
      hrcapC, htblC, hrepC, hMetaC, hCapsC, hLayC, hSelC, hPotC, hRegC, hnumC, hoffC, hbdC,
      hzC, hfrC, hftC, hcCore⟩ :=
    hCoreRun root uIntBuf editsPtr editWords g l afterEdits s14.pos ω mem0 s14.mem model tok sg U
      B R hrep0' hMeta0 hCaps0 hSel0 hPot0 hReg0 hReach hDeep hFits hTreeNum hnumB hoffB hbdB hB0
      hfitB hrangeM hflowM haccM hICap hICapMax hFEdge
      hLogW hLoopBefore hLoopAfter hCap hBr hglB hglAg
      (fun a ha h6 h7 h8 => (hs14_ltHeap a (lt_of_lt_of_le ha huLeH)).trans (htags0 a ha h6 h7 h8))
      hs14_fresh hnfCap hs14_batch hs14_small hOrdAt hEdW rfl hRefreshU hfootLt hgEnd hlEnd hglOff
      (by omega) hs14_hz (by omega) hglValid (fun i hi => by
        have hqW : shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model1.chain.rebuildCount i < 2 ^ w :=
          hQuotaW i (Nat.le_of_lt hi)
        rw [shiftQuotaWord_eq_gameShiftBoundNat] at hqW
        have hB10 : 10 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k :=
          shiftQuotaBase_ge_ten ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.hk
        have hrcLe : model.chain.rebuildCount i ≤ model1.chain.rebuildCount i := by
          dsimp only [model1, alg2PreLoopState]
          have hcases := Chain.Ordered.updateLoop_rebuildCount_cases cfg.T cfg.L cfg.TP cfg.P cfg.N₀
            (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) cfg.P.d 0
            { model.chain with
              recUpdates := fun j =>
                if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
            ((model.chain.G 0).applyBatch U_int) U_int ((model.chain.G 0).batchEnc U_int) (by omega)
          rcases hcases with heq | ⟨iStar, _, _, heq⟩
          · change model.chain.rebuildCount i ≤
              (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀
                (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) cfg.P.d 0 _ _ _ _).1.rebuildCount i
            rw [heq]
          · change model.chain.rebuildCount i ≤
              (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀
                (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) cfg.P.d 0 _ _ _ _).1.rebuildCount i
            rw [heq]; dsimp only; split_ifs with h <;> [subst h; skip] <;> omega
        have hterm : model1.chain.rebuildCount i * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ≤
            ∑ j ∈ Finset.range (i + 1),
              model1.chain.rebuildCount j * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1 - j) := by
          have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (Nat.lt_succ_self i)
          have h1 := Finset.single_le_sum (f := fun j =>
            model1.chain.rebuildCount j * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1 - j))
            (fun _ _ => Nat.zero_le _) hmem
          simpa [Nat.add_sub_cancel_left] using h1
        have hpow : 10 ≤ shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k ^ (i + 1) :=
          hB10.trans (Nat.le_self_pow (Nat.succ_ne_zero i) _)
        have hmul : model1.chain.rebuildCount i ≤
            model1.chain.rebuildCount i * shiftQuotaBase ⌈cfg.Ψ⌉₊ cfg.P.M₀ cfg.P.k :=
          Nat.le_mul_of_pos_right _ (by omega)
        dsimp only [gameShiftBoundNat] at hqW
        omega) hLay0
  let s15 : State := { regs := Function.update s14.regs 33 nextHeap, mem := stCore.mem, pos := stCore.pos }
  have r14 : Runs w p ω (.call 33 ordChainCoreProc [.reg 20, .reg 21, .reg 36, .reg 31, .reg 22, .reg 23, .reg 32])
      s14 .normal s15 (cCore + 8) :=
    runs_call_iff.mpr ⟨[root, uIntBuf, editsPtr, editWords, g, l, afterEdits], bCore, .returned nextHeap,
      stCore, cCore,
      by simp [evalArgs, Expr.eval, s14, s13, s12b, hsnapRegs 20 (by decide), hsnapRegs 21 (by decide),
           hsnapRegs 22 (by decide), hsnapRegs 23 (by decide), s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1],
      hbCore, hrCore, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Step 4: reload `tokC.levelsEnd` and run deterministic `firstRebuiltLevel` scan
  have hrepC0 := hrepC
  obtain ⟨hrootC, _, _, _, _, _, _, _, hschedC, _, _, _, _, _, _, _, _, _, _, htagsC⟩ := hrepC
  obtain ⟨hOwnC, t1_C, _, _, _, t5_C, _⟩ := htagsC
  have hfootC_lt (a : ℕ) (ha : Rrep.foot root tokC a ∨ sg'.owned a) : a < nextHeap := by
    rcases hftC a ha with h0 | ⟨_, hhi⟩
    · have := hfootLt a h0; omega
    · exact hhi
  have hroot2C : stCore.mem (root + 2) = tokC.levelsEnd := by simpa using hrootC 2 (by simp)
  have hr2CLt : root + 2 < 2 ^ w :=
    lt_trans (hfootC_lt _ (Or.inl (Or.inl (hOwnC _ (by rw [t1_C 2 (by omega)]; decide))))) (by omega)
  have hlvCLt : tokC.levelsEnd + 4 * (cfg.P.d + 1) < nextHeap :=
    hfootC_lt _ (Or.inl (Or.inl (hOwnC _ (by rw [t5_C (4 * (cfg.P.d + 1)) (by omega)]; decide))))
  let s16 : State := { s15 with regs := Function.update s15.regs 27 tokC.levelsEnd }
  let s17 : State := { s16 with regs := Function.update s16.regs 30 (tokC.levelsEnd + 2 * (cfg.P.d + 1)) }
  let s18 : State := { s17 with regs := Function.update s17.regs 34 cfg.P.d }
  have r15 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 20) (.const 2)))) s15 .normal s16 5 :=
    runs_assign_iff.mpr ⟨tokC.levelsEnd, by
      simp [Expr.eval, BinOp.eval, s15, s14, s13, s12b, hsnapRegs 20 (by decide),
        s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, hw2, hr2CLt, hroot2C], rfl, rfl, rfl⟩
  have r16 : Runs w p ω (.assign 30 (.bin .add (.reg 27) (.bin .mul (.const 2) (.reg 29)))) s16 .normal s17 6 :=
    runs_assign_iff.mpr ⟨tokC.levelsEnd + 2 * (cfg.P.d + 1), by
      simp [Expr.eval, BinOp.eval, s16, s15, s14, s13, s12b, hsnapRegs 29 (by decide),
        s11, s10, hw2, show 2 * (cfg.P.d + 1) < 2 ^ w by omega,
        show tokC.levelsEnd + 2 * (cfg.P.d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r17 : Runs w p ω (.assign 34 (.reg 28)) s17 .normal s18 2 :=
    runs_assign_iff.mpr ⟨cfg.P.d, by
      simp [Expr.eval, s17, s16, s15, s14, s13, s12b, hsnapRegs 28 (by decide), s11, s10, s9],
      rfl, rfl, rfl⟩
  have hsnapPres (j : ℕ) (hj : j < cfg.P.d) : stCore.mem (heap + j) = model.chain.rebuildCount j := by
    have hnf : ¬ (Rrep.foot root tok (heap + j) ∨ sg.owned (heap + j)) := fun hf => by
      have := hfootLt _ hf; omega
    exact (hfrC (heap + j) (by omega) hnf).trans (hs14_snap j hj)
  have hnewRC (j : ℕ) (hj : j < cfg.P.d) :
      stCore.mem (tokC.levelsEnd + 2 * (cfg.P.d + 1) + j) = modelPre.chain.rebuildCount j :=
    hschedC.2.2.1 j (by omega)
  obtain ⟨s19, cScan, rScan, hcScan, hscan34, hscanMem, hscanRegs⟩ :=
    scanFirstRebuiltLevel_runs (w := w) (oldBase := heap)
      (newBase := tokC.levelsEnd + 2 * (cfg.P.d + 1)) (d := cfg.P.d)
      (oldRC := model.chain.rebuildCount) (newRC := modelPre.chain.rebuildCount)
      (p := p) (ω := ω) (st := s18)
      (by simp [s18, s17, s16, s15, s14, s13, s12b, hsnapRegs 25 (by decide), s11, s10, s9, s8, s7, s6])
      (by simp [s18, s17, s16, s15, s14, s13, s12b, hsnapRegs 28 (by decide), s11, s10, s9])
      (by simp [s18, s17]) (by simp [s18]) hsnapPres hnewRC (by omega) (by omega) hw1
  -- Step 5: conditional `resetPassSuffix` + `branD := 0` (mutates tag `5` only)
  let condResetStmt : Stmt :=
    .cond (.bin .lt (.reg 34) (.reg 28))
      (.assign 0 (.reg 27) ;; .assign 1 (.reg 34) ;; .assign 2 (.reg 29) ;;
       resetPassSuffix ;;
       .store (.bin .add (.reg 27) (.bin .mul (.const 4) (.reg 29))) (.const 0))
      .nop
  have hCondReset : ∃ s20 cRes,
      Runs w p ω condResetStmt s19 .normal s20 cRes ∧
      cRes ≤ 14 * (cfg.P.d + 1) + 40 ∧
      Rrep.rep root model1 tokC s20.mem ∧
      Rrep.phi root tokC s20.mem = Rrep.phi root tokC stCore.mem ∧
      OffTreeRecInv model1 L s20.mem tokC.edgeRecords B ∧
      (∀ a, tokC.tag a ≠ 5 → s20.mem a = stCore.mem a) ∧
      s20.regs 20 = root ∧ s20.regs 24 = quotaBase ∧ s20.regs 33 = nextHeap := by
    have h20_19 : s19.regs 20 = root :=
      (hscanRegs 20 (by decide) (by decide)).trans
        (by simp [s18, s17, s16, s15, s14, s13, s12b, hsnapRegs 20 (by decide),
             s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1])
    have h24_19 : s19.regs 24 = quotaBase :=
      (hscanRegs 24 (by decide) (by decide)).trans
        (by simp [s18, s17, s16, s15, s14, s13, s12b, hsnapRegs 24 (by decide),
             s11, s10, s9, s8, s7, s6, s5])
    have h27_19 : s19.regs 27 = tokC.levelsEnd :=
      (hscanRegs 27 (by decide) (by decide)).trans (by simp [s18, s17, s16])
    have h28_19 : s19.regs 28 = cfg.P.d :=
      (hscanRegs 28 (by decide) (by decide)).trans
        (by simp [s18, s17, s16, s15, s14, s13, s12b, hsnapRegs 28 (by decide), s11, s10, s9])
    have h29_19 : s19.regs 29 = cfg.P.d + 1 :=
      (hscanRegs 29 (by decide) (by decide)).trans
        (by simp [s18, s17, s16, s15, s14, s13, s12b, hsnapRegs 29 (by decide), s11, s10])
    have h33_19 : s19.regs 33 = nextHeap :=
      (hscanRegs 33 (by decide) (by decide)).trans (by simp [s18, s17, s16, s15])
    cases hfl : firstRebuiltLevel cfg.P.d model.chain.rebuildCount modelPre.chain.rebuildCount with
    | none =>
      have h34d : s19.regs 34 = cfg.P.d := by simpa [hfl] using hscan34
      have hm1Eq : model1 = modelPre := by
        dsimp only [model1, alg2PreLoopState, modelPre, alg2PreResetState]
        dsimp only [modelPre, alg2PreResetState] at hfl
        rw [hfl]
      have rNo : Runs w p ω condResetStmt s19 .normal s19 5 :=
        runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, h34d, h28_19, show 0 < 2 ^ w by omega],
          by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
      refine ⟨s19, 5, rNo, by omega, by rw [hm1Eq, hscanMem]; exact hrepC0,
        by rw [hscanMem], by rw [hm1Eq, hscanMem]; exact hoffC,
        fun _ _ => congrFun hscanMem _, h20_19, h24_19, h33_19⟩
    | some iStar =>
      have hiLt : iStar < cfg.P.d := List.mem_range.mp (List.mem_of_find?_eq_some hfl)
      have h34i : s19.regs 34 = iStar := by simpa [hfl] using hscan34
      let t1 : State := { s19 with regs := Function.update s19.regs 0 tokC.levelsEnd }
      let t2 : State := { t1 with regs := Function.update t1.regs 1 iStar }
      let t3 : State := { t2 with regs := Function.update t2.regs 2 (cfg.P.d + 1) }
      have rt1 : Runs w p ω (.assign 0 (.reg 27)) s19 .normal t1 2 :=
        runs_assign_iff.mpr ⟨tokC.levelsEnd, by simp [Expr.eval, h27_19], rfl, rfl, rfl⟩
      have rt2 : Runs w p ω (.assign 1 (.reg 34)) t1 .normal t2 2 :=
        runs_assign_iff.mpr ⟨iStar, by simp [Expr.eval, t1, h34i], rfl, rfl, rfl⟩
      have rt3 : Runs w p ω (.assign 2 (.reg 29)) t2 .normal t3 2 :=
        runs_assign_iff.mpr ⟨cfg.P.d + 1, by simp [Expr.eval, t2, t1, h29_19], rfl, rfl, rfl⟩
      obtain ⟨t4, cRP, rt4, hcRP, hmemRP, hregsRP, _⟩ :=
        resetPassSuffix_runs (w := w) (base := tokC.levelsEnd) (first := iStar) (stop := cfg.P.d + 1)
          (ω := ω) (st := t3) (by simp [t3, t2, t1]) (by simp [t3, t2]) (by simp [t3])
          (by omega) (by omega) hw1
      let t5 : State := { t4 with mem := Function.update t4.mem (tokC.levelsEnd + 4 * (cfg.P.d + 1)) 0 }
      have h27_t4 : t4.regs 27 = tokC.levelsEnd := (hregsRP 27 (by decide)).trans (by simp [t3, t2, t1, h27_19])
      have h29_t4 : t4.regs 29 = cfg.P.d + 1 := (hregsRP 29 (by decide)).trans (by simp [t3, t2, t1, h29_19])
      have rt5 : Runs w p ω (.store (.bin .add (.reg 27) (.bin .mul (.const 4) (.reg 29))) (.const 0))
          t4 .normal t5 7 :=
        runs_store_iff.mpr ⟨tokC.levelsEnd + 4 * (cfg.P.d + 1), 0, by
          simp [Expr.eval, BinOp.eval, h27_t4, h29_t4, hw4,
            show 4 * (cfg.P.d + 1) < 2 ^ w by omega,
            show tokC.levelsEnd + 4 * (cfg.P.d + 1) < 2 ^ w by omega],
          by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have rBody : Runs w p ω
          (.assign 0 (.reg 27) ;; .assign 1 (.reg 34) ;; .assign 2 (.reg 29) ;;
           resetPassSuffix ;;
           .store (.bin .add (.reg 27) (.bin .mul (.const 4) (.reg 29))) (.const 0))
          s19 .normal t5 (2 + (2 + (2 + (cRP + 7 + 1) + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨t1, 2, _, rt1,
        runs_seq_iff.mpr (Or.inr ⟨t2, 2, _, rt2,
        runs_seq_iff.mpr (Or.inr ⟨t3, 2, _, rt3,
        runs_seq_iff.mpr (Or.inr ⟨t4, cRP, 7, rt4, rt5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have rYes : Runs w p ω condResetStmt s19 .normal t5 (3 + (2 + (2 + (2 + (cRP + 7 + 1) + 1) + 1) + 1) + 1) :=
        runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, h34i, h28_19, hiLt, hw1],
          by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact rBody, by simp [Expr.size]⟩
      have ht5_ne5 (a : ℕ) (hne : tokC.tag a ≠ 5) : t5.mem a = stCore.mem a := by
        have hneB : a ≠ tokC.levelsEnd + 4 * (cfg.P.d + 1) := fun h => hne (h ▸ t5_C (4 * (cfg.P.d + 1)) (by omega))
        have hnotP : ¬ (tokC.levelsEnd + iStar ≤ a ∧ a < tokC.levelsEnd + (cfg.P.d + 1)) := by
          rintro ⟨hlo, hhi⟩
          have heq : tokC.levelsEnd + (a - tokC.levelsEnd) = a := by omega
          exact hne (heq ▸ t5_C (a - tokC.levelsEnd) (by omega))
        change Function.update t4.mem _ 0 a = _
        rw [Function.update_of_ne hneB, hmemRP a, ite_eq_right hnotP, hscanMem]
      have hm1Eq : model1 = { modelPre with
          branD := 0, passes := fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else modelPre.passes j } := by
        dsimp only [model1, alg2PreLoopState, modelPre, alg2PreResetState]
        dsimp only [modelPre, alg2PreResetState] at hfl
        rw [hfl]
      have hsched1 : SolverScheduleAt t5.mem tokC.levelsEnd
          { modelPre with branD := 0, passes := fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else modelPre.passes j } := by
        refine ⟨fun j => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, by simp [t5]⟩
        · change Function.update t4.mem _ 0 _ = _
          dsimp only
          rw [Function.update_of_ne (by have := j.isLt; omega), hmemRP, hscanMem]
          by_cases hle : iStar ≤ j.val
          · rw [ite_eq_left ⟨by omega, by have := j.isLt; omega⟩, ite_eq_left hle]
          · rw [ite_eq_right (by omega), ite_eq_right hle]; exact hschedC.1 j
        · change Function.update t4.mem _ 0 _ = _
          rw [Function.update_of_ne (by omega), hmemRP, ite_eq_right (by omega), hscanMem]
          exact hschedC.2.1 i hi
        · change Function.update t4.mem _ 0 _ = _
          rw [Function.update_of_ne (by omega), hmemRP, ite_eq_right (by omega), hscanMem]
          exact hschedC.2.2.1 i hi
        · change Function.update t4.mem _ 0 _ = _
          rw [Function.update_of_ne (by omega), hmemRP, ite_eq_right (by omega), hscanMem]
          exact hschedC.2.2.2.1 i hi
      obtain ⟨hrep1, hphi1⟩ := solverStateRep_update_passes_branD hlocal hrepC0 hsched1 ht5_ne5
      have hoff1' : OffTreeRecInv modelPre L t5.mem tokC.edgeRecords B :=
        offTreeRecInv_of_agree hrepC0 hoffC (fun a ha => ht5_ne5 a (by rcases ha with h | h <;> omega))
      have hoff1 : OffTreeRecInv model1 L t5.mem tokC.edgeRecords B := by rw [hm1Eq]; exact hoff1'
      refine ⟨t5, _, rYes, by omega, by rw [hm1Eq]; exact hrep1, hphi1, hoff1, ht5_ne5,
        (hregsRP 20 (by decide)).trans (by simp [t3, t2, t1, h20_19]),
        (hregsRP 24 (by decide)).trans (by simp [t3, t2, t1, h24_19]),
        (hregsRP 33 (by decide)).trans (by simp [t3, t2, t1, h33_19])⟩
  obtain ⟨s20, cRes, rRes, hcRes, hrep20, hphi20, hoff20, hfr20, h20_20, h24_20, h33_20⟩ := hCondReset
  -- Step 6: call `shiftQuotaWriterProc`
  have hqOutC (i : ℕ) (hi : i ≤ cfg.P.d + 1) : ¬ (Rrep.foot root tokC (quotaBase + i) ∨ sg'.owned (quotaBase + i)) :=
    fun hf => by
      rcases hftC _ hf with h0 | ⟨hlo, _⟩
      · exact hqOut i hi h0
      · omega
  obtain ⟨cQ, stQ, rQ, hcQ, hquotasQ, hpsiQ, hfrQ⟩ :=
    hQuotaRun root quotaBase s20.pos ω s20.mem model1 tokC hrep20
      (fun a ha => lt_trans (hfootC_lt a (Or.inl ha)) (by omega))
      hQuotaW (fun i hi hf => hqOutC i hi (Or.inl hf)) (by omega)
  let s21 : State := { regs := Function.update s20.regs 35 0, mem := stQ.mem, pos := stQ.pos }
  have r18 : Runs w p ω (.call 35 shiftQuotaWriterProc [.reg 20, .reg 24]) s20 .normal s21 (cQ + 3) :=
    runs_call_iff.mpr ⟨[root, quotaBase], bQuota, .returned 0, stQ, cQ,
      by simp [evalArgs, Expr.eval, h20_20, h24_20], hbQuota, rQ, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have r19 : Runs w p ω (.ret (.reg 33)) s21 (.returned nextHeap) s21 2 :=
    runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, s21, h33_20], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (ordChainRefreshWiredBody ordEditsProc ordChainCoreProc shiftQuotaWriterProc)
      s0 (.returned nextHeap) s21 _ :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 2, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 2, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 3, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 4, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 6, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, cSnap, _, rSnap,
    runs_seq_iff.mpr (Or.inr ⟨s12b, 4, _, r12b,
    runs_seq_iff.mpr (Or.inr ⟨s13, cEd + 3, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s14, 4, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s15, cCore + 8, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s16, 5, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s17, 6, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s18, 2, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s19, cScan, _, rScan,
    runs_seq_iff.mpr (Or.inr ⟨s20, cRes, _, rRes,
    runs_seq_iff.mpr (Or.inr ⟨s21, cQ + 3, 2, r18, r19, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hfootQ_eq : ∀ a, Rrep.foot root tokC a ∨ sg'.owned a → s20.mem a = stQ.mem a := fun a ha => by
    have hnotQ : a < quotaBase ∨ quotaBase + cfg.P.d + 1 < a := by
      by_contra hIn; push Not at hIn
      have heq : quotaBase + (a - quotaBase) = a := by omega
      exact hqOutC (a - quotaBase) (by omega) (by rw [heq]; exact ha)
    exact (hfrQ a hnotQ).symm
  have hlocQ := hlocR root model1 tokC s20.mem stQ.mem (fun a ha => hfootQ_eq a (Or.inl ha))
  have hrepFin : Rrep.rep root model1 tokC s21.mem := hlocQ.1 hrep20
  have hphiFin : Rrep.phi root tokC s21.mem = Rrep.phi root tokC stCore.mem :=
    hlocQ.2.symm.trans hphi20
  have hoffFin : OffTreeRecInv model1 L s21.mem tokC.edgeRecords B := by
    refine offTreeRecInv_of_agree hrep20 hoff20 (fun a ha => ?_)
    have hfootA : Rrep.foot root tokC a :=
      Or.inl (hOwnC a (by rcases ha with h | h <;> rw [h] <;> decide))
    exact (hfootQ_eq a (Or.inl hfootA)).symm
  have hbdOut : OffTreeRecBound model1 L s21.mem tokC.edgeRecords B := by
    refine offTreeRecBound_preReset_to_preLoop_sel (offTreeRecBound_of_agree hrepC0 hbdC fun a ha => ?_)
    have hfootA : Rrep.foot root tokC a :=
      Or.inl (hOwnC a (by rcases ha with h | h <;> rw [h] <;> decide))
    exact (hfootQ_eq a (Or.inl hfootA)).symm.trans (hfr20 a (by rcases ha with h | h <;> omega))
  -- Both `LevelMetaFoot tokC` and `sg'.owned` are untouched by `condResetStmt` (tag `5`) and `shiftQuotaWriterProc` (`quotaBase..`)
  have hPresC : PreservesLevelMeta tokC tokC stCore.mem s21.mem :=
    (PreservesLevelMeta.refl tokC stCore.mem).congr_mem_right fun a ht =>
      (hfootQ_eq a (Or.inl (LevelMetaFoot.mem_foot hrepC0 ht))).symm.trans
        (hfr20 a (by rcases ht with h | h | h | h <;> omega))
  have hCapsInvOut : SolverLevelCapsInv P V vCap eCap model1 tokC s21.mem :=
    hPresC.to_capsInv ⟨hMetaC, hCapsC⟩ rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) rfl
  have hSelOut : SolverSelectInv G L P m dMul kOff tokC.table model1 (Rrep.foot root tokC)
      (LevelMetaFoot tokC) sg' s21.mem := by
    refine ⟨fun mem' hag => ?_, hSelC.2.1, ?_⟩
    · have hagCore : ∀ a, LevelMetaFoot tokC a ∨ sg'.owned a → mem' a = stCore.mem a := by
        intro a ha
        rcases ha with hm | hs
        · exact (hag a (Or.inl hm)).trans (hPresC.metaEq a hm).2
        · have hne5 : tokC.tag a ≠ 5 := fun h5 =>
            hSelC.2.1 a hs (Or.inl (hOwnC a (by rw [h5]; decide)))
          exact (hag a (Or.inr hs)).trans ((hfootQ_eq a (Or.inr hs)).symm.trans (hfr20 a hne5))
      exact hSelC.1 mem' hagCore
    · exact hSelC.2.2
  have hRegOut : SolverSelectRegionInv G L P m E pLast slot vCap eCap model1 (Rrep.foot root tokC)
      tokC sg' s21.mem := by
    refine hRegC.congr hMetaC hPresC hRegC.owned_not_foot (fun a hs => ?_) rfl rfl rfl
    have hne5 : tokC.tag a ≠ 5 := fun h5 =>
      hSelC.2.1 a hs (Or.inl (hOwnC a (by rw [h5]; decide)))
    exact (hfootQ_eq a (Or.inr hs)).symm.trans (hfr20 a hne5)
  refine ⟨nextHeap, _, s21, tokC, sg', rFull, by omega, by omega, hlevC, hintCapC, hrcapC,
    htblC, hrepFin, hCapsInvOut.1, hCapsInvOut.2, hPresC.to_levelLayout hMetaC hLayC, hSelOut, hPotC, hRegOut, hnumC,
    hoffFin,
    hbdOut, hquotasQ, hpsiQ, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have hne5 : tokC.tag a ≠ 5 := fun h =>
      absurd (hfootC_lt a (Or.inl (Or.inl (hOwnC a (by rw [h]; decide))))) (by omega)
    exact (hfrQ a (Or.inr (by omega))).trans ((hfr20 a hne5).trans (hzC a ha))
  · intro a ha hnf hnotQ
    have hne5 : tokC.tag a ≠ 5 := fun h => by
      rcases hftC a (Or.inl (Or.inl (hOwnC a (by rw [h]; decide)))) with h0 | ⟨hlo, _⟩
      · exact hnf h0
      · omega
    exact (hfrQ a hnotQ).trans ((hfr20 a hne5).trans ((hfrC a (by omega) hnf).trans (hs14_ltHeap a ha)))
  · intro a ha
    rcases hftC a ha with h0 | ⟨hlo, hhi⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, hhi⟩
  · have hphiFin' : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tokC stQ.mem =
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tokC stCore.mem := hphiFin
    rw [hphiFin']
    rw [hIntLenEq] at hcEd
    dsimp only [model1, modelPre, gVec, lVec, alg2PreLoopState, alg2PreResetState] at hcCore ⊢
    omega

end MinCostFlow.MinRatio
