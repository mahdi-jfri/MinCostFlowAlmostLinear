module

public import MinCostFlow.MinRatio.WireChainCoreBranchBExitOutKFBL
import WordRAM.Tactic

/-!
# The terminal exit of Branch B with a batch (`WireChainCoreBranchBTermOutKFBL`)

When the loop of Branch B reaches `d` and the batch of level `d` is not empty, the terminal step
builds the new last level (`wireBranchBTermKFBL_runs_exit`), and the copy of the last forest
(`collectTermForestStmt 81`) stores the pointer of its forest at `newPtrs + d`. This file gives
the facts `BranchBExitBaseKFBL` at `firstReb = d` after both (`wireBranchBTermNonEmpty_exitOut`).
The old last forest is at `oldPtrs + d`, where the prefix of Branch B stored it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 4000000 in
/-- **The terminal exit with a batch.** The loop exits at `i₀ = d` with the invariant `I` at
`sE` and a non-empty batch for level `d`. The premises of the terminal step are those of
`wireBranchBTermKFBL_runs_exit`, with the new last level at the caps `(vCap, eCap)`. The old last
forest is at `sE.mem (oldPtrs + d)`, inside the footprint of the old last level (`hOldLast`), and
the new last forest has its edges below `intCap`. Then `BranchBExitBaseKFBL` holds at
`firstReb = d`, with the new token `y` of core `d - 1` and the token `termTokN` of the new last
level. -/
theorem wireBranchBTermNonEmpty_exitOut
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy wordExp stretchPrec N0 capLimit coreLenProc lastInit
      lastMul lastSpace nextM vcL ecL oldPtrs newPtrs intCap : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {E0 : Finset ℕ} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : ℕ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hd : 0 < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt)
      (RL := LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P E0) reembFn A origLen ℓ' N0
      BWc EWc ULc ch0 termTok cfg.P.d ch curG curU curEditsList oldOrd sE tok curBatch
      curBatchWords curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' 0 cfg.P.d ch curG curU curEnc oldOrd)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (hNonEmpty : curU ≠ [])
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).Implements w p
      lastInit opLast
      (lastLevelRuntimeMachineContract fmt L cfg.L curG vCap eCap lastMul stretchPrec lastAlloc))
    (hLastSp : ∀ g l h, lastAlloc 1 [g, l, L, fmt.precision, h] ≤ lastSpace)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L)
    (hHm : curG.m ≤ nextM)
    (hRotW : ordRotWords (chainLevelOrdAbs ch (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * nextM)
    (hRoom : sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      nextM * wireCoreLenEdgeSpace
        (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * nextM)) + lastSpace + 7 < 2 ^ w)
    (h71 : sE.regs 71 = 0) (h81 : sE.regs 81 = newPtrs)
    (hOldLast : ∃ vc ec, DynGraphAt sE.mem (sE.mem (oldPtrs + cfg.P.d)) vc ec
        (ch0.lastLSFs ch0.lastBran).F.F ∧
      ∀ a, sE.mem (oldPtrs + cfg.P.d) ≤ a →
        a < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec →
        (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P E0).foot (A.coreH cfg.P.d)
          termTok a)
    (hOldLastFCap : ∀ e ∈ (ch0.lastLSFs ch0.lastBran).F.F.E, e < intCap) :
    let X := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' 0 cfg.P.d ch curG curU
      curEnc).1
    (0 < X.lastK) → (∀ e ∈ (X.lastLSFs X.lastBran).F.F.E, e < intCap) →
    ∃ (out : State) (cost h1 : ℕ) (y : Rcore.τ) (termTokN : ℕ),
      let tokN : ℕ → Rcore.τ := fun j => if j = cfg.P.d - 1 then y else tok j
      Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
        collectTermForestStmt 81) st .normal out cost ∧
      sE.regs 4 ≤ h1 ∧
      h1 ≤ sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
        nextM * wireCoreLenEdgeSpace
          (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
        (2 + 2 * cfg.N₀ + 2 * nextM)) + lastSpace ∧
      out.regs 4 = h1 + 7 ∧
      BranchBExitBaseKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vCap eCap oldPtrs newPtrs intCap cfg.P.d ch0 ch X levelU D sE out
        tok tokN termTokN ∧
      cost + branchBPhiSum Rcore A tokN out.mem +
          (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).phi
            (out.mem (A.handleBase + cfg.P.d)) termTokN out.mem ≤
        3 * Psc.readout + copyGraphLiveCost curG.n curG.m +
          curG.m * (wireCoreLenEdgeCost
            (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) + 30) +
          Psc.mul * (ordRotWords (chainLevelOrdAbs ch (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) +
            1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀ +
          lastMul * (cfg.L.cost curG + 1) + 360 + 36 + branchBPhiSum Rcore A tok sE.mem := by
  intro X hKPos hNewFCap
  have hRLLoc := LastLevelProgram.lastLevelRepresentation_local vcL ecL 4 L P E0
  have hRLnLoc := LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P curG.E
  obtain ⟨hFloor, _, _, _, _, _, _, _, hr75, _, hr77, hr78, _, _, _, _, _, _, _, _, _, _⟩ :=
    I.regs
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  obtain ⟨out1, c1, h1, y, termTokN, r1, hh1lo, hh1hi, hR4, hz1, hReg1, hReps1, hDisj1, hSlots1,
      hSel1, hLB1, hTH1, hCurGS, hLRep1, hLFoot1, _, hG1, hL1, hFr1, hc1⟩ :=
    wireBranchBTermKFBL_runs_exit E hRLLoc S hSlotLe hN0 hLvlM hd I hM hstMem hstRegs hNonEmpty
      hcapLim hCoreLenProc hLastImpl hLastSp hLWord hPWord hWidth hHm hRotW hRoom
  set tokN : ℕ → Rcore.τ := fun j => if j = cfg.P.d - 1 then y else tok j with htokN
  have hHB := S.hbLt
  have hBB := S.bbLt
  have hW : h1 + 7 < 2 ^ w := by omega
  -- the frame of the terminal step on the words below the select base
  have hFrLow : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
      a ≠ A.handleBase + cfg.P.d → a ≠ A.branchBase + cfg.P.d → out1.mem a = sE.mem a :=
    fun a ha hc h1' h2' => hFr1 a (by omega) hc h1' h2' (by omega) (by omega) (by omega)
  -- the words of the new last level
  set termH := out1.mem (A.handleBase + cfg.P.d) with htermH
  have hXl : X = { ch with
      G := (fun j => if j = cfg.P.d then curG else ch.G j)
      lastK := (cfg.L.build curG (({ ch.toTreeChain with
        G := fun j => if j = cfg.P.d then curG else ch.G j } : TreeChain).chainLen ℓ' cfg.P.d)).1
      lastLSFs := (cfg.L.build curG (({ ch.toTreeChain with
        G := fun j => if j = cfg.P.d then curG else ch.G j } : TreeChain).chainLen ℓ'
          cfg.P.d)).2
      lastBran := 0
      ℓ := ℓ'
      g := g'
      curLastRebuilds := ch.curLastRebuilds + 1
      curLastCost := ch.curLastCost + cfg.L.cost curG
      curLastTreeUpdates := ch.curLastTreeUpdates + (diffTreeChanges
        (ch.lastLSFs ch.lastBran).F.F.E ((cfg.L.build curG (({ ch.toTreeChain with
          G := fun j => if j = cfg.P.d then curG else ch.G j } : TreeChain).chainLen ℓ'
            cfg.P.d)).2 0).F.F.E).length } := by
    simp only [X, Chain.Ordered.updateLoop, hNonEmpty, ↓reduceIte]
  have hXBuild : (X.lastK, X.lastLSFs) = cfg.L.build curG
      (coreLen (cfg.T.lsfs (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)))
        (ch.toTreeChain.chainLen ℓ' (cfg.P.d - 1))) := by
    rw [hXl]; dsimp only; rw [chainLen_last_eq ch curG ℓ' hd]
  have hXB0 : X.lastBran = 0 := by rw [hXl]
  have hXGd : X.G cfg.P.d = curG := by rw [hXl]; simp
  have hXG : ∀ i < cfg.P.d, X.G i = ch.G i := fun i hi => by rw [hXl]; simp [hi.ne]
  have hLRepX : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).rep termH
      (X.lastK, X.lastLSFs) termTokN out1.mem := by rw [hXBuild]; exact hLRep1
  have hLRepX' := hLRepX
  obtain ⟨hTLo, _, _, hTBr⟩ := hLRepX'
  obtain ⟨hTBrHdr, hTLSF⟩ := hTBr X.lastBran (by rw [hXB0]; exact hKPos)
  obtain ⟨_, _, _, _, hB5, hB6, _⟩ := hTBrHdr
  set lsfHdr := out1.mem (termH + 1 + X.lastBran) with hlsfHdr
  set forestPtr := out1.mem (lsfHdr + 1) with hforestPtr
  set tN : ℕ := termTokN with htN
  have hInT : ∀ a, termH ≤ a → a < tN → sE.regs 4 ≤ a ∧ a < h1 := fun a h1' h2' =>
    ⟨(hLFoot1 a ⟨h1', h2'⟩).1, (hLFoot1 a ⟨h1', h2'⟩).2.1⟩
  have hTLo' : termH + 1 + X.lastK ≤ tN := hTLo
  have hTermEnd : tN ≤ h1 := by
    have := (hInT (tN - 1) (by omega) (by omega)).2; omega
  -- the copy of the new last forest
  have hO1 : ∀ (r v : ℕ), 70 ≤ r → r ≠ 99 → sE.regs r = v → out1.regs r = v :=
    fun r v hr h99 hv => by
    rw [hReg1 r hr, hstRegs r (by omega) (by omega) (by omega) h99]; exact hv
  obtain ⟨out, c2, r2, hc2, hOutMem, hOutRegs⟩ :=
    collectTermForestStmt_runs (w := w) (p := p) (ω := ω) (st := out1) (dstReg := 81)
      (dstPtrs := newPtrs) (baseIdx := 0) (d := cfg.P.d) (handleBase := A.handleBase)
      (branchBase := A.branchBase) (termHandle := termH) (lastBran := X.lastBran)
      (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (hO1 81 _ (by decide) (by decide) h81) (hO1 71 _ (by decide) (by decide) h71) (hO1 75 _ (by decide) (by decide) hr75)
      (hO1 77 _ (by decide) (by decide) hr77) (hO1 78 _ (by decide) (by decide) hr78)
      (by decide) (Nat.zero_le _) rfl (by rw [hXB0]; exact hLB1) rfl rfl
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hOut : ∀ a, a ≠ newPtrs + cfg.P.d → out.mem a = out1.mem a := fun a h =>
    by rw [hOutMem, Function.update_of_ne (by omega)]
  have hOutLow : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
      a ≠ A.handleBase + cfg.P.d → a ≠ A.branchBase + cfg.P.d → out.mem a = sE.mem a :=
    fun a ha hc h1' h2' => (hOut a (by omega)).trans (hFrLow a ha hc h1' h2')
  have hOR4 : out.regs 4 = h1 + 7 := by
    rw [hOutRegs 4 (by decide) (by decide) (by decide), hR4]
  have hHandle : ∀ j < cfg.P.d, out.mem (A.handleBase + j) = A.coreH j := fun j hj => by
    rw [hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.1 j hj.le).1) (by omega)
      (by rcases S.sepHB with h | h <;> omega)]
    exact (I.cells j hj).2.2.1
  have hHandleD : out.mem (A.handleBase + cfg.P.d) = termH := hOut _ (by omega)
  -- the footprints of the cores lie below the select base or above the heap floor
  have hFootN : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tokN j) a →
      a < A.selBase ∨ A.heapFloor ≤ a := fun j hj a ha => by
    rcases (hReps1 j hj).2 a ha with h | h
    · exact I.footLoc j hj a h
    · exact Or.inr (by omega)
  have hFootKeep : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tokN j) a →
      out.mem a = out1.mem a := fun j hj a ha => hOut a (by
        rcases hFootN j hj a ha with h | h <;> omega)
  have hXabs : ∀ j < cfg.P.d, chainLevelOrdAbs X j = chainLevelOrdAbs ch j := fun j hj => by
    have hSc : X.scState = ch.scState := by rw [hXl]
    have hBr : X.bran = ch.bran := by rw [hXl]
    have hUc : X.updCount = ch.updCount := by rw [hXl]
    simp only [chainLevelOrdAbs, ChainState.levelOrd, chainLevelOrd, hXG j hj, hXG 0 (by omega),
      hSc, hBr, hUc]
  have hRepJ : ∀ j < cfg.P.d, Rcore.rep (A.coreH j) (chainLevelOrdAbs X j) (tokN j) out.mem ∧
      Rcore.phi (A.coreH j) (tokN j) out.mem = Rcore.phi (A.coreH j) (tokN j) out1.mem := by
    intro j hj
    have hL := E.loc (A.coreH j) (chainLevelOrdAbs ch j) (tokN j) out1.mem out.mem
      (fun a ha => (hFootKeep j hj a ha).symm)
    rw [hXabs j hj]
    exact ⟨hL.1 (hReps1 j hj).1, hL.2.symm⟩
  have hPhiT : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).phi termH
      termTokN out.mem =
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).phi termH termTokN
        out1.mem :=
    (hRLnLoc _ (X.lastK, X.lastLSFs) _ _ _ (fun a ha => (hOut a (by
      have := hInT a ha.1 ha.2; omega)).symm)).2.symm
  refine ⟨out, c1 + c2 + 1, h1, y, termTokN,
    runs_seq_iff.mpr (Or.inr ⟨out1, c1, c2, r1, r2, rfl⟩), hh1lo, hh1hi, hOR4, ?_, ?_⟩
  rotate_left
  · rw [hHandleD, hPhiT]
    have hPS : branchBPhiSum Rcore A tokN out.mem = branchBPhiSum Rcore A tokN out1.mem := by
      unfold branchBPhiSum
      exact Finset.sum_congr rfl fun j hj => (hRepJ j (Finset.mem_range.mp hj)).2
    have hPhi0 : ∀ b t (mm : ℕ → ℕ),
        (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).phi b t mm = 0 :=
      fun _ _ _ => rfl
    rw [hPS]; simp only [hPhi0] at hc1 ⊢; omega
  have hmin : min cfg.P.d cfg.P.d = cfg.P.d := min_self _
  have hOldF : chainSuffixForests ch0 cfg.P.d = [(ch0.lastLSFs ch0.lastBran).F.F] := by
    simp [chainSuffixForests]
  have hNewF : chainSuffixForests X cfg.P.d = [(X.lastLSFs X.lastBran).F.F] := by
    simp [chainSuffixForests]
  refine
    { frLe := by omega
      heapLo := by rw [hOR4]; omega
      zero := fun a ha => by
        rw [hOR4] at ha
        rw [hOut a (by omega)]; exact hz1 a ha
      regs := fun r hr _ h99 => by
        rw [hOutRegs r (by omega) (by omega) (by omega), hReg1 r hr,
          hstRegs r (by omega) (by omega) (by omega) h99]
      handlesLow := fun j hj => hHandle j (by omega)
      reps := fun j hj => by
        rw [hHandle j hj]
        refine ⟨(hRepJ j hj).1, fun a ha => ?_⟩
        rcases (hReps1 j hj).2 a ha with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by rw [hOR4]; omega⟩
      disj := fun j₁ hj₁ j₂ hj₂ hne a => by
        rw [hHandle j₁ hj₁, hHandle j₂ hj₂]; exact hDisj1 j₁ hj₁ j₂ hj₂ hne a
      slots := by
        rw [hmin, hOR4]
        refine hSlots1.frame le_rfl (fun j hj x => by rw [hHandle j hj])
          (fun r hr x _ _ hf => by rw [hHandle r hr] at hf; exact hf) (fun a ha => ?_)
          (fun j hj i hi => hOut _ (by omega))
        rcases ha with ⟨j, hj, hf⟩ | ⟨h1', h2', _⟩
        · exact hFootKeep j hj a hf
        · exact hOut a (by omega)
      sel := by rw [hOut _ (by omega)]; exact hSel1
      cells := fun j hj => by
        have hc := I.cells j hj
        have hRC := S.rcLt
        have hUC := S.ucLt
        rw [hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.1 j hj.le).2)
            (by rcases S.sepHB with h | h <;> omega) (by omega),
          hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).2.2.2.1)
            (by rcases S.sepUCHB with h | h <;> omega) (by rcases S.sepUCBB with h | h <;> omega),
          hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).2.2.2.2)
            (by rcases S.sepRCHB with h | h <;> omega) (by rcases S.sepRCBB with h | h <;> omega)]
        have hBr : X.bran = ch.bran := by rw [hXl]
        have hUc : X.updCount = ch.updCount := by rw [hXl]
        have hRc : X.rebuildCount = ch.rebuildCount := by rw [hXl]
        rw [hBr, hUc, hRc]
        exact ⟨hc.2.2.2.1, hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2⟩
      lastB := by rw [hOut _ (by omega), hXB0]; exact hLB1
      graphs := fun j hj => by
        have hMeta := S.metaLt
        rw [hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).2.2.1)
          (by rcases S.sepHL with h | h <;> omega) (by rcases S.sepBL with h | h <;> omega),
          (I.cells j hj).2.2.2.2.2.2.1, hXG j hj]
        refine dynGraphAt_of_agree (hG1 j hj) (fun x _ hx2 => hOut x ?_)
        have := S.gLt j hj; omega
      lens := fun j hj => by
        have hMeta := S.metaLt
        rw [hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).2.1)
          (by rcases S.sepHL with h | h <;> omega) (by rcases S.sepBL with h | h <;> omega),
          (I.cells j hj).2.2.2.2.2.2.2.1]
        have hGX : (X.G j).E = (ch.G j).E := by rw [hXG j hj]
        have hLX : X.toTreeChain.chainLen X.ℓ j = ch.toTreeChain.chainLen ℓ' j := by
          rw [hXl]
          refine chainLen_congr_lt _ _ _ _ fun m hm => ?_
          have hm' : m < cfg.P.d := by omega
          simp only [TreeChain.activeLSF, ChainState.toTreeChain, hm', ↓reduceIte]
        rw [hGX, hLX]
        refine (hL1 j hj).congr (fun e he t ht => hOut _ ?_)
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using
            Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((I.graphs j hj).2.2.1 e he))
        have := S.lLt j hj; omega
      lastRep := by
        rw [hXGd, hHandleD]
        exact (hRLnLoc _ _ _ _ _ (fun a ha => (hOut a (by
          have := hInT a ha.1 ha.2; omega)).symm)).1 hLRepX
      lastFoot := fun a ha => by
        rw [hXGd, hHandleD] at ha
        obtain ⟨h1', h2', h3'⟩ := hLFoot1 a ha
        exact ⟨Or.inr ⟨h1', by rw [hOR4]; omega⟩, fun j hj => by
          rw [hHandle j hj]; exact h3' j hj⟩
      oldF := by
        rw [if_pos le_rfl, hOldF, hOR4]
        obtain ⟨vc, ec, hDG, hInF⟩ := hOldLast
        have hSz : 0 < dynGraphSize vc ec := by unfold dynGraphSize; omega
        have hTm := I.term.2
        have hBlk : ∀ x, sE.mem (oldPtrs + cfg.P.d) ≤ x →
            x < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec → out.mem x = sE.mem x :=
          fun x hx1 hx2 => by
            obtain ⟨hx3, hx4, _, hx5, hx6, _⟩ := hTm x (hInF x hx1 hx2)
            exact hOutLow x hx3 hx4 (by omega) (by omega)
        have hEnd := (hTm (sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc ec - 1)
          (hInF _ (by omega) (by omega))).1
        have hPtr : out.mem (oldPtrs + cfg.P.d) = sE.mem (oldPtrs + cfg.P.d) := by
          rw [hOut _ (by omega)]
          refine hFr1 _ (by omega) (fun j hj hf => ?_) (by omega) (by omega) (by omega)
            (by omega) (by omega)
          rcases I.footLoc j hj _ hf with h | h <;> omega
        refine ⟨by simp only [List.length_singleton]; omega, fun t ht => ?_⟩
        obtain rfl : t = 0 := by simpa using ht
        simp only [Nat.add_zero, List.getElem_singleton]
        refine ⟨vc, ec, ?_, ?_, ?_⟩
        · rw [hPtr]
          exact dynGraphAt_of_agree hDG hBlk
        · rw [hPtr]; omega
        · exact hOldLastFCap
      newF := by
        rw [if_pos le_rfl, hNewF, hOR4]
        have hPtr : out.mem (newPtrs + cfg.P.d) = forestPtr := by
          rw [hOutMem]; simp
        have hF := hTLSF.2.1
        refine ⟨by simp only [List.length_singleton]; omega, fun t ht => ?_⟩
        obtain rfl : t = 0 := by simpa using ht
        simp only [Nat.add_zero, List.getElem_singleton]
        refine ⟨vCap, eCap, ?_, ?_, ?_⟩
        · rw [hPtr]
          refine dynGraphAt_of_agree hF (fun x hx1 hx2 => hOut x ?_)
          have := (hInT x (by omega) (by omega)).1; omega
        · rw [hPtr]; omega
        · exact hNewFCap
      frame := fun a ha hc h1 h2 _ _ _ _ => by
        rw [hOut a (by omega)]
        exact hFrLow a ha hc (by omega) (by omega)
      frameHeap := fun a h1 h2 _ hn => by
        rw [hOut a (by omega)]
        refine hFr1 a (by omega) (fun j hj hf => ?_) (by omega) (by omega) (by omega)
          (by omega) (by omega)
        rcases I.footLoc j hj a hf with h | h <;> omega }

end MinCostFlow.MinRatio
