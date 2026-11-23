module

public import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayGoalKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayZone
import WordRAM.Tactic

/-!
# The places of the data at the terminal non-empty exit of Branch B (`WireChainCoreBranchBExitLayTerm`)

This file proves `BranchBTermExitLayGoalKFBL`
(`WireChainCoreBranchBExitLayGoalKFBL.lean`): when the Branch B loop exits at `i₀ = d` with a
non-empty batch for level `d`, the run of `wireBranchBTermKFBL ;; collectTermForestStmt 81`
produces `BranchBExitBaseKFBL` and `BranchBExitLayKFBL` at `fr = d` and cut `hT = h1` (the heap
pointer right after the last-level rebuild, with `out.regs 4 = h1 + 7`).

* `wireBranchBTermKFBL_runs_exit_zone`: refines `wireBranchBTermKFBL_runs_exit` by also applying
  `BranchBDoneSlots.refreshZone` to the same run of `wireBranchBTermKFBL_runs_nonEmpty`, placing
  the select data of all `d` finished levels in `BranchBSelZone A.heapFloor (sE.regs 4) h1 (h1 + 7)`
  off all core footprints.
* `branchBTermExitLayGoalKFBL_proved`: proves `BranchBTermExitLayGoalKFBL`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 4000000 in
/-- Like `wireBranchBTermKFBL_runs_exit`, additionally recording the zone placement of all `d`
finished select slots from `BranchBDoneSlots.refreshZone`. -/
private theorem wireBranchBTermKFBL_runs_exit_zone
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy wordExp stretchPrec N0 capLimit coreLenProc lastInit
      lastMul lastSpace nextM : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL RLn : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
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
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
    (hN0 : N0 = cfg.N₀) (hLvlM : ∀ j < cfg.P.d, ch0.lvlM j = levelM cfg.TP cfg.P j)
    (hd : 0 < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok cfg.P.d ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' 0 cfg.P.d ch curG curU curEnc oldOrd)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (hNonEmpty : curU ≠ [])
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl : RLn.Implements w p lastInit opLast
      (lastLevelRuntimeMachineContract fmt L cfg.L curG vCap eCap lastMul stretchPrec lastAlloc))
    (hLastSp : ∀ g l h, lastAlloc 1 [g, l, L, fmt.precision, h] ≤ lastSpace)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L)
    (hHm : curG.m ≤ nextM)
    (hRotW : ordRotWords (chainLevelOrdAbs ch (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * nextM)
    (hRoom : sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      nextM * wireCoreLenEdgeSpace
        (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * nextM)) + lastSpace + 7 < 2 ^ w) :
    ∃ (out : State) (cost h1 : ℕ) (y : Rcore.τ) (termTokN : RLn.τ),
      let tokN : ℕ → Rcore.τ := fun j => if j = cfg.P.d - 1 then y else tok j
      Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        st .normal out cost ∧
      sE.regs 4 ≤ h1 ∧
      h1 ≤ sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
        nextM * wireCoreLenEdgeSpace
          (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
        (2 + 2 * cfg.N₀ + 2 * nextM)) + lastSpace ∧
      out.regs 4 = h1 + 7 ∧ ZeroFrom out.mem (h1 + 7) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      (∀ j < cfg.P.d, Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tokN j) out.mem ∧
        ∀ a, Rcore.foot (A.coreH j) (tokN j) a →
          Rcore.foot (A.coreH j) (tok j) a ∨ (sE.regs 4 ≤ a ∧ a < h1 + 5)) ∧
      (∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
        ∀ a, Rcore.foot (A.coreH j₁) (tokN j₁) a → ¬ Rcore.foot (A.coreH j₂) (tokN j₂) a) ∧
      BranchBDoneSlots w P cfg.P.d
        (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
        (fun r => Rcore.foot (A.coreH r) (tokN r)) A.heapFloor (h1 + 7) A.selBase out.mem
        cfg.P.d D ch0.G levelU (fun j => (ch.G j).E)
        (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr) ∧
      (∀ j < cfg.P.d,
        SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
          (fun x => BranchBSelZone A.heapFloor (sE.regs 4) h1 (h1 + 7) x ∧
            ∀ r < cfg.P.d, ¬ Rcore.foot (A.coreH r) (tokN r) x)
          (fun x => Rcore.foot (A.coreH j) (tokN j) x ∨ (A.heapFloor ≤ x ∧ x < h1 + 7))
          A.heapFloor (h1 + 7) out.mem (A.selBase + 1 + 12 * j) (D j) (ch0.G j) (levelU j)
          (ch.G j).E (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr) ∧
      out.mem A.selBase = cfg.P.d ∧
      out.mem (A.branchBase + cfg.P.d) = 0 ∧ sE.regs 4 ≤ out.mem (A.handleBase + cfg.P.d) ∧
      curG = cfg.T.S (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) ∧
      RLn.rep (out.mem (A.handleBase + cfg.P.d))
        (cfg.L.build curG (coreLen (cfg.T.lsfs (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)))
          (ch.toTreeChain.chainLen ℓ' (cfg.P.d - 1)))) termTokN out.mem ∧
      (∀ z, RLn.foot (out.mem (A.handleBase + cfg.P.d)) termTokN z →
        sE.regs 4 ≤ z ∧ z < h1 ∧ ∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tokN j) z) ∧
      (∀ j < cfg.P.d, DynGraphAt out.mem (A.gPtr0 j) vCap eCap (ch.G j)) ∧
      (∀ j < cfg.P.d,
        EdgeValuesAt out.mem (A.lPtr0 j) 4 L P (ch.G j).E (ch.toTreeChain.chainLen ℓ' j)) ∧
      (∀ a < sE.regs 4, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
        a ≠ A.handleBase + cfg.P.d → a ≠ A.branchBase + cfg.P.d → a ≠ A.selBase →
        a ≠ A.selBase + 1 + 12 * (cfg.P.d - 1) + 8 →
        a ≠ A.selBase + 1 + 12 * (cfg.P.d - 1) + 9 → out.mem a = sE.mem a) ∧
      cost + branchBPhiSum Rcore A tokN out.mem +
          RLn.phi (out.mem (A.handleBase + cfg.P.d)) termTokN out.mem ≤
        3 * Psc.readout + copyGraphLiveCost curG.n curG.m +
          curG.m * (wireCoreLenEdgeCost
            (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) + 30) +
          Psc.mul * (ordRotWords (chainLevelOrdAbs ch (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) +
            1) * SparseCore.bundleLogFactor (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀ +
          lastMul * (cfg.L.cost curG + 1) + 360 + branchBPhiSum Rcore A tok sE.mem := by
  obtain ⟨_, hMne⟩ := hM
  obtain ⟨_, hAgree, hPos, hStr, hRest⟩ := hMne hNonEmpty
  obtain ⟨hIn, hCurGEq, hHE, hFits⟩ := hRest hd
  have hℓd := chainLen_last_eq ch curG ℓ' hd
  rw [hℓd] at hAgree hPos hStr hFits
  subst hCurGEq
  set dm := cfg.P.d - 1 with hdmEq
  have hdm : dm < cfg.P.d := by omega
  have hdmne : dm ≠ cfg.P.d := by omega
  obtain ⟨hFloor, hr10, _, _, _, hr72, _, _, hr75, _, hr77, hr78, _, hr83, _, _, hr94, hr95,
    hr96, _, _, _⟩ := I.regs
  have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hLvl : ch.lvlM dm = levelM cfg.TP cfg.P dm := by
    rw [I.modelFrame.2.2.2.2.2.2.1]; exact hLvlM dm hdm
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hSepHB := S.sepHB
  have hSepHL := S.sepHL
  have hSepBL := S.sepBL
  have hw0 : sE.regs 4 < 2 ^ w := by omega
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := I.cells dm hdm
  have hRepDm := (I.reps dm hdm).1
  rw [ite_eq_right hdmne] at hRepDm
  have hFootDm := (I.reps dm hdm).2
  obtain ⟨sH, sT, sHB, sM, sG, sL⟩ := I.static dm hdm
  have sGdm := S.gSep dm hdm
  have hFootSel : ∀ r < cfg.P.d, ∀ a, Rcore.foot (A.coreH r) (tok r) a →
      a < A.selBase ∨ A.heapFloor ≤ a := I.footLoc
  have hT := wireBranchBTermKFBL_runs_nonEmpty (ω := ω) (st := st) (nextM := nextM)
    (lastTool := cfg.L) (RL := RLn) (curBatch := curBatch) (selBase := A.selBase)
    (k := cfg.P.k) (M := levelM cfg.TP cfg.P dm) (N := cfg.N₀) (d := cfg.P.d)
    (cur := sE.regs 4) (handleBase := A.handleBase) (branchBase := A.branchBase)
    (levelMeta := A.levelMeta) (handle := A.coreH dm) (branch := ch.bran dm)
    (graph := A.gPtr0 dm) (lens := A.lPtr0 dm)
    (a := ⟨ch.scState dm, ch.G dm, ch.levelOrd dm, ch.updCount dm⟩) (x := tok dm)
    (ch.toTreeChain.chainLen ℓ' dm) E.four (dsRep_implements_kfbl_of_kfrbl (E.impl dm hdm))
    (E.footAt dm hdm) hcapLim hCoreLenProc E.edgeP E.signC E.mulC E.divC E.copyC
    hLastImpl hLastSp
    ⟨hstRegs 4 (by decide) (by decide) (by decide) (by decide),
      (hstRegs 75 (by decide) (by decide) (by decide) (by decide)).trans hr75,
      (hstRegs 77 (by decide) (by decide) (by decide) (by decide)).trans hr77,
      (hstRegs 78 (by decide) (by decide) (by decide) (by decide)).trans hr78,
      (hstRegs 83 (by decide) (by decide) (by decide) (by decide)).trans hr83,
      (hstRegs 94 (by decide) (by decide) (by decide) (by decide)).trans hr94,
      (hstRegs 95 (by decide) (by decide) (by decide) (by decide)).trans (hr95.trans E.prec.symm)⟩
    ⟨(hstRegs 10 (by decide) (by decide) (by decide) (by decide)).trans hr10,
      (hstRegs 72 (by decide) (by decide) (by decide) (by decide)).trans hr72⟩
    (by rw [hstMem, I.batchLen]; exact fun h => hNonEmpty (List.length_eq_zero_iff.mp h)) hd
    ⟨by rw [hstMem]; exact c3, by rw [hstMem]; exact c4, by rw [hstMem]; exact c7,
      by rw [hstMem]; exact c8⟩
    ⟨by omega, by omega, by omega⟩ c5 E.kW c6 (by have := E.w16; omega) hLWord
    (by rw [E.prec]; exact hPWord) (by rw [E.prec]; exact hWidth)
    (by rw [hstMem]; exact I.graphs dm hdm) (by have := S.gLt dm hdm; omega)
    (fun z h1 h2 => sG dm hdm z h1 h2)
    (by rw [hstMem, E.prec]; exact I.lensLt dm (by omega)) (by have := S.lLt dm hdm; omega)
    (fun z h1 h2 => sL dm hdm z h1 h2) (by rw [hstMem]; exact hRepDm)
    (by rw [hLvl, hN, hN0] at hIn; exact hIn) hFootDm (by rw [hstMem]; exact I.zero) hHE hHm
    hRotW (by rw [E.prec]; exact hFits) (by rw [E.four]; exact hStr) hPos hAgree
    ⟨by omega, by omega, by omega, (sHB cfg.P.d le_rfl).1, (sHB cfg.P.d le_rfl).2⟩
    (fun z hz => by
      rcases hz with rfl | rfl | rfl | ⟨hz1, hz2⟩
      · exact ⟨by omega, (sHB dm (by omega)).1, by omega, by omega, by omega⟩
      · exact ⟨by omega, (sHB dm (by omega)).2, by omega, by omega, by omega⟩
      · exact ⟨by omega, (sM dm hdm).2.2.1, by omega, by omega, by omega⟩
      · obtain ⟨_, _, g3, g4, _, _, _, _, _⟩ := sGdm z hz1 hz2
        exact ⟨by have := S.gLt dm hdm; omega, sG dm hdm z hz1 hz2, by omega, by omega,
          by have := S.gLt dm hdm; omega⟩)
    ⟨by omega, fun hf => by rcases hFootSel dm hdm _ hf with h | h <;> omega⟩
    (fun z hz => by rcases hz with rfl | rfl <;> exact ⟨by omega, by omega, by omega⟩)
    (by omega)
    ⟨fun hf => by rcases hFootSel dm hdm _ hf with h | h <;> omega,
      fun hf => by rcases hFootSel dm hdm _ hf with h | h <;> omega⟩
    hRoom
  dsimp only at hT
  obtain ⟨out, cost, h1, ret, y, termTokN, rT, hh1lo, hh1hi, hretlo, hrethi, hout4, hzout,
    hregs, hRepY, hFootY, hBd, hHd, hRLn, hRLnFoot, hSel, hFr, h8, h9, hSV, hT0, hT1,
    hcost⟩ := hT
  have hFr' : ∀ z < sE.regs 4, ¬ Rcore.foot (A.coreH dm) (tok dm) z →
      z ≠ A.handleBase + cfg.P.d → z ≠ A.branchBase + cfg.P.d → z ≠ A.selBase →
      z ≠ A.selBase + 1 + 12 * dm + 8 → z ≠ A.selBase + 1 + 12 * dm + 9 →
      out.mem z = sE.mem z := fun z a b c d e f g => by
    rw [hFr z a b c d e f g, hstMem]
  have hKeepFoot : ∀ r < cfg.P.d, r ≠ dm → ∀ z, Rcore.foot (A.coreH r) (tok r) z →
      out.mem z = sE.mem z := fun r hr hne z hz => by
    obtain ⟨_, _, sHBr, _, _, _⟩ := I.static r hr
    refine hFr' z ((I.reps r hr).2 z hz) (I.disj r hr dm hdm hne z hz)
      (fun h => (sHBr cfg.P.d le_rfl).1 (h ▸ hz)) (fun h => (sHBr cfg.P.d le_rfl).2 (h ▸ hz))
      ?_ ?_ ?_
    · rintro rfl; rcases hFootSel r hr _ hz with h | h <;> omega
    · rintro rfl; rcases hFootSel r hr _ hz with h | h <;> omega
    · rintro rfl; rcases hFootSel r hr _ hz with h | h <;> omega
  have hLocJ : ∀ j < cfg.P.d, j ≠ dm →
      (Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) sE.mem →
        Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) out.mem) ∧
      Rcore.phi (A.coreH j) (tok j) sE.mem = Rcore.phi (A.coreH j) (tok j) out.mem :=
    fun j hj hne => E.loc _ _ _ _ _ (fun a ha => (hKeepFoot j hj hne a ha).symm)
  -- Shared hypotheses for `BranchBDoneSlots.refresh` and `BranchBDoneSlots.refreshZone`
  have hDone := I.slots.of_le (n' := dm) (by omega)
  have hLists := (I.slots dm hdm).lists
  have hKeepR : ∀ x < sE.regs 4, ¬ Rcore.foot (A.coreH dm) (tok dm) x →
      x ≠ A.selBase + 1 + 12 * dm + 8 → x ≠ A.selBase + 1 + 12 * dm + 9 →
      (A.heapFloor ≤ x ∨ (∃ r < dm, Rcore.foot (A.coreH r) (tok r) x) ∨
        (A.selBase + 1 ≤ x ∧ x < A.selBase + 1 + 12 * cfg.P.d)) →
      out.mem x = sE.mem x := fun x hx hnf h8x h9x hcase => by
    refine hFr' x hx hnf ?_ ?_ ?_ h8x h9x
    · rintro rfl
      rcases hcase with h | ⟨r, hr, hf⟩ | h
      · omega
      · exact ((I.static r (by omega)).2.2.1 cfg.P.d le_rfl).1 hf
      · omega
    · rintro rfl
      rcases hcase with h | ⟨r, hr, hf⟩ | h
      · omega
      · exact ((I.static r (by omega)).2.2.1 cfg.P.d le_rfl).2 hf
      · omega
    · rintro rfl
      rcases hcase with h | ⟨r, hr, hf⟩ | h
      · omega
      · rcases hFootSel r (by omega) _ hf with h | h <;> omega
      · omega
  have hSV' : StretchValuesAt out.mem (h1 + 5) 4 (out.mem (A.selBase + 1 + 12 * dm + 9)) P
      (ch.G dm).E (cfg.T.lsfs (ch.scState dm) (ch.bran dm)).wstr := by
    have h := hSV; rw [E.four, E.prec] at h; exact h
  have hFootNewR : ∀ x, Rcore.foot (A.coreH dm) ((fun j => if j = dm then y else tok j) dm) x →
      Rcore.foot (A.coreH dm) (tok dm) x ∨ (sE.regs 4 ≤ x ∧ x < h1 + 5) := fun x hx => by
    simp only [↓reduceIte] at hx
    exact (hFootY x hx).imp id fun h => ⟨h.1, by omega⟩
  have hSlotsOut : BranchBDoneSlots w P cfg.P.d
      (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
      (fun r => Rcore.foot (A.coreH r) ((fun j => if j = dm then y else tok j) r))
      A.heapFloor (h1 + 7) A.selBase out.mem cfg.P.d D ch0.G levelU (fun j => (ch.G j).E)
      (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr) := by
    have hR := BranchBDoneSlots.refresh
      (foot' := fun r => Rcore.foot (A.coreH r) ((fun j => if j = dm then y else tok j) r))
      (mem' := out.mem) (cur := h1) (Lw := out.mem (A.selBase + 1 + 12 * dm + 9)) hDone hLists
      hdm hFloor hh1lo (fun r hr x => by simp only [show r ≠ dm by omega, ↓reduceIte])
      (fun r _ hne x hx => by simp only [hne, ↓reduceIte] at hx; exact Or.inl hx)
      hFootNewR (fun r hr x hx => (I.reps r hr).2 x hx)
      (fun r hr hne x hx => I.disj r hr dm hdm hne x hx) hSlotLe
      (fun r hr i hi hf => by rcases hFootSel r hr _ hf with h | h <;> omega)
      hKeepR h8 rfl h9 hSV' (by simp only [↓reduceIte]; exact hT0)
      (by simp only [↓reduceIte]; exact hT1)
    rwa [show dm + 1 = cfg.P.d by omega] at hR
  have hZoneOut : ∀ j < cfg.P.d,
      SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
        (fun x => BranchBSelZone A.heapFloor (sE.regs 4) h1 (h1 + 7) x ∧
          ∀ r < cfg.P.d,
            ¬ Rcore.foot (A.coreH r) ((fun j => if j = dm then y else tok j) r) x)
        (fun x => Rcore.foot (A.coreH j) ((fun j => if j = dm then y else tok j) j) x ∨
          (A.heapFloor ≤ x ∧ x < h1 + 7))
        A.heapFloor (h1 + 7) out.mem (A.selBase + 1 + 12 * j) (D j) (ch0.G j) (levelU j)
        (ch.G j).E (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr := by
    have hR := BranchBDoneSlots.refreshZone
      (foot' := fun r => Rcore.foot (A.coreH r) ((fun j => if j = dm then y else tok j) r))
      (mem' := out.mem) (cur := h1) (Lw := out.mem (A.selBase + 1 + 12 * dm + 9)) hDone hLists
      hdm hFloor hh1lo (fun r hr x => by simp only [show r ≠ dm by omega, ↓reduceIte])
      (fun r _ hne x hx => by simp only [hne, ↓reduceIte] at hx; exact Or.inl hx)
      hFootNewR (fun r hr x hx => (I.reps r hr).2 x hx)
      (fun r hr hne x hx => I.disj r hr dm hdm hne x hx) hSlotLe
      (fun r hr i hi hf => by rcases hFootSel r hr _ hf with h | h <;> omega)
      hKeepR h8 rfl h9 hSV' (by simp only [↓reduceIte]; exact hT0)
      (by simp only [↓reduceIte]; exact hT1)
    rwa [show dm + 1 = cfg.P.d by omega] at hR
  refine ⟨out, _, h1, y, termTokN, rT, hh1lo, hh1hi, hout4, hzout, hregs, fun j hj => ?_,
    fun j₁ hj₁ j₂ hj₂ hne a ha1 ha2 => ?_, hSlotsOut, hZoneOut, hSel, hBd, hHd, rfl, hRLn,
    fun z hz => ?_, fun j hj => ?_, fun j hj => ?_, fun a ha h0 => ?_, ?_⟩
  · by_cases hje : j = dm
    · subst hje
      simp only [↓reduceIte]
      exact ⟨hRepY, fun a ha => (hFootY a ha).imp id fun h => ⟨h.1, by omega⟩⟩
    · simp only [hje, ↓reduceIte]
      have hR := (I.reps j hj).1
      rw [ite_eq_right (show j ≠ cfg.P.d by omega)] at hR
      exact ⟨(hLocJ j hj hje).1 hR, fun a ha => Or.inl ha⟩
  · by_cases h1' : j₁ = dm
    · have h2 : j₂ ≠ dm := fun h => hne (h1'.trans h.symm)
      simp only [h1', ↓reduceIte] at ha1
      simp only [h2, ↓reduceIte] at ha2
      rcases hFootY a ha1 with h0 | ⟨hlo, _⟩
      · exact I.disj dm hdm j₂ hj₂ (Ne.symm h2) a h0 ha2
      · have := (I.reps j₂ hj₂).2 a ha2; omega
    · by_cases h2 : j₂ = dm
      · simp only [h2, ↓reduceIte] at ha2
        simp only [h1', ↓reduceIte] at ha1
        rcases hFootY a ha2 with h0 | ⟨hlo, _⟩
        · exact I.disj j₁ hj₁ dm hdm h1' a ha1 h0
        · have := (I.reps j₁ hj₁).2 a ha1; omega
      · simp only [h1', h2, ↓reduceIte] at ha1 ha2
        exact I.disj j₁ hj₁ j₂ hj₂ hne a ha1 ha2
  · obtain ⟨hz1, hz2, hz3⟩ := hRLnFoot z hz
    refine ⟨hz1, hz2, fun j hj hf => ?_⟩
    by_cases hje : j = dm
    · simp only [hje, ↓reduceIte] at hf; exact hz3 hf
    · simp only [hje, ↓reduceIte] at hf
      have := (I.reps j hj).2 z hf; omega
  · refine dynGraphAt_of_agree (I.graphs j hj) (fun x hx1 hx2 => ?_)
    obtain ⟨_, _, g3, g4, _, _, _, _, _⟩ := S.gSep j hj x hx1 hx2
    have := S.gLt j hj
    exact hFr' x (by omega) (sG j hj x hx1 hx2) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  · refine (I.lensLt j (by omega)).congr (fun e he t ht => ?_)
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((I.graphs j hj).2.2.1 e he))
    have hlo : A.lPtr0 j ≤ A.lPtr0 j + e * L + t := by omega
    have hhi : A.lPtr0 j + e * L + t < A.lPtr0 j + eCap * L := by omega
    obtain ⟨_, _, l3, l4, _, _, _, _⟩ := S.lSep j hj _ hlo hhi
    have := S.lLt j hj
    exact hFr' _ (by omega) (sL j hj _ hlo hhi) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  · exact fun a1 a2 a3 a4 a5 => hFr' a ha (h0 dm hdm) a1 a2 a3 a4 a5
  · have hmem : dm ∈ Finset.range cfg.P.d := Finset.mem_range.mpr hdm
    have hPhi : branchBPhiSum Rcore A (fun j => if j = dm then y else tok j) out.mem +
        Rcore.phi (A.coreH dm) (tok dm) sE.mem =
        branchBPhiSum Rcore A tok sE.mem + Rcore.phi (A.coreH dm) y out.mem := by
      unfold branchBPhiSum
      rw [← Finset.add_sum_erase _ _ hmem,
        ← Finset.add_sum_erase _ (fun j => Rcore.phi (A.coreH j) (tok j) sE.mem) hmem]
      have hRest : ((Finset.range cfg.P.d).erase dm).sum
          (fun j => Rcore.phi (A.coreH j) ((fun j => if j = dm then y else tok j) j) out.mem) =
          ((Finset.range cfg.P.d).erase dm).sum
            (fun j => Rcore.phi (A.coreH j) (tok j) sE.mem) :=
        Finset.sum_congr rfl (fun j hj => by
          obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hj
          simp only [hne, ↓reduceIte]
          exact (hLocJ j (Finset.mem_range.mp hlt) hne).2.symm)
      rw [hRest]
      simp only [↓reduceIte]
      omega
    have hcost' : cost + Rcore.phi (A.coreH dm) y out.mem +
        RLn.phi (out.mem (A.handleBase + cfg.P.d)) termTokN out.mem ≤
        3 * Psc.readout + copyGraphLiveCost (cfg.T.S (ch.scState dm) (ch.bran dm)).n
          (cfg.T.S (ch.scState dm) (ch.bran dm)).m +
        (cfg.T.S (ch.scState dm) (ch.bran dm)).m * (wireCoreLenEdgeCost
          (ordLevelLwMax L capExp (levelM cfg.TP cfg.P dm) cfg.N₀) + 30) +
        Psc.mul * (ordRotWords (chainLevelOrdAbs ch dm) (ch.bran dm) + 1) *
          SparseCore.bundleLogFactor (levelM cfg.TP cfg.P dm) cfg.N₀ +
        lastMul * (cfg.L.cost (cfg.T.S (ch.scState dm) (ch.bran dm)) + 1) +
        Rcore.phi (A.coreH dm) (tok dm) sE.mem + 360 := by
      rw [hstMem] at hcost; exact hcost
    omega

set_option maxHeartbeats 4000000 in
/-- **Proof of `BranchBTermExitLayGoalKFBL`.** Runs the terminal non-empty exit with the zone
refresh (`wireBranchBTermKFBL_runs_exit_zone`) followed by `collectTermForestStmt 81`, giving both
`BranchBExitBaseKFBL` and `BranchBExitLayKFBL` at `fr = cfg.P.d` and `hT = h1`. -/
theorem branchBTermExitLayGoalKFBL_proved : BranchBTermExitLayGoalKFBL := by
  intro w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
    edgeProc signExt mul intDiv copy wordExp stretchPrec N0 capLimit coreLenProc lastInit
    lastMul lastSpace nextM vcL ecL oldPtrs newPtrs intCap
    fmt cfg Psc alloc lastAlloc Ginit reembFn Rcore E0 p opCore opLast ω A origLen ℓ' g'
    BWc EWc ULc ch0 termTok ch curG curU curEditsList curEnc oldOrd sE st tok
    curBatch curBatchWords curEdits curEditsWords levelU levelUS D
    E S hOldLo hOldNew hNewHi hN0 hLvlM hd I hM hstMem hstRegs hNonEmpty hcapLim hCoreLenProc
    hLastImpl hLastSp hLWord hPWord hWidth hHm hRotW hRoom h71 h81 hOldLast hOldLastFCap
    X hKPos hNewFCap
  have hRLnLoc := LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P curG.E
  obtain ⟨hFloor, _, _, _, _, _, _, _, hr75, _, hr77, hr78, _, _, _, _, _, _, _, _, _, _⟩ :=
    I.regs
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  obtain ⟨out1, c1, h1, y, termTokN, r1, hh1lo, hh1hi, hR4, hz1, hReg1, hReps1, hDisj1, hSlots1,
      hZone1, hSel1, hLB1, hTH1, hCurGS, hLRep1, hLFoot1, hG1, hL1, hFr1, hc1⟩ :=
    wireBranchBTermKFBL_runs_exit_zone E S hSlotLe hN0 hLvlM hd I hM hstMem hstRegs hNonEmpty
      hcapLim hCoreLenProc hLastImpl hLastSp hLWord hPWord hWidth hHm hRotW hRoom
  set tokN : ℕ → Rcore.τ := fun j => if j = cfg.P.d - 1 then y else tok j with htokN
  have hHB := S.hbLt
  have hBB := S.bbLt
  have hW : h1 + 7 < 2 ^ w := by omega
  have hFrLow : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
      a ≠ A.handleBase + cfg.P.d → a ≠ A.branchBase + cfg.P.d → out1.mem a = sE.mem a :=
    fun a ha hc h1' h2' => hFr1 a (by omega) hc h1' h2' (by omega) (by omega) (by omega)
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
  have hO1 : ∀ (r v : ℕ), 70 ≤ r → r ≠ 99 → sE.regs r = v → out1.regs r = v :=
    fun r v hr h99 hv => by
      rw [hReg1 r hr, hstRegs r (by omega) (by omega) (by omega) h99]; exact hv
  obtain ⟨out, c2, r2, hc2, hOutMem, hOutRegs⟩ :=
    collectTermForestStmt_runs (w := w) (p := p) (ω := ω) (st := out1) (dstReg := 81)
      (dstPtrs := newPtrs) (baseIdx := 0) (d := cfg.P.d) (handleBase := A.handleBase)
      (branchBase := A.branchBase) (termHandle := termH) (lastBran := X.lastBran)
      (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (hO1 81 _ (by decide) (by decide) h81) (hO1 71 _ (by decide) (by decide) h71)
      (hO1 75 _ (by decide) (by decide) hr75) (hO1 77 _ (by decide) (by decide) hr77)
      (hO1 78 _ (by decide) (by decide) hr78) (by decide) (Nat.zero_le _) rfl
      (by rw [hXB0]; exact hLB1) rfl rfl
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hOut : ∀ a, a ≠ newPtrs + cfg.P.d → out.mem a = out1.mem a := fun a h => by
    rw [hOutMem, Function.update_of_ne (by omega)]
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
  have hmin : min cfg.P.d cfg.P.d = cfg.P.d := min_self _
  have hOldF : chainSuffixForests ch0 cfg.P.d = [(ch0.lastLSFs ch0.lastBran).F.F] := by
    simp [chainSuffixForests]
  have hNewF : chainSuffixForests X cfg.P.d = [(X.lastLSFs X.lastBran).F.F] := by
    simp [chainSuffixForests]
  have hMetaKeep : ∀ j < cfg.P.d,
      out.mem (A.levelMeta + j) = sE.mem (A.levelMeta + j) ∧
      out.mem (A.levelMeta + cfg.P.d + j) = sE.mem (A.levelMeta + cfg.P.d + j) := fun j hj => by
    have hMeta := S.metaLt
    exact ⟨hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).2.1)
        (by rcases S.sepHL with h | h <;> omega) (by rcases S.sepBL with h | h <;> omega),
      hOutLow _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).2.2.1)
        (by rcases S.sepHL with h | h <;> omega) (by rcases S.sepBL with h | h <;> omega)⟩
  have hZoneOut : ∀ j < cfg.P.d,
      SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
        (fun x => BranchBSelZone A.heapFloor (sE.regs 4) h1 (h1 + 7) x ∧
          ∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (A.handleBase + r)) (tokN r) x)
        (fun x => Rcore.foot (out.mem (A.handleBase + j)) (tokN j) x ∨
          (A.heapFloor ≤ x ∧ x < h1 + 7))
        A.heapFloor (h1 + 7) out.mem (A.selBase + 1 + 12 * j) (D j) (ch0.G j) (levelU j)
        (ch.G j).E (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr := by
    refine branchBExitZone_frame hZone1 le_rfl (fun r hr x => by rw [hHandle r hr])
      (fun a ha => ?_) (fun j hj i hi => hOut _ (by omega))
    rcases ha with ⟨j, hj, hf⟩ | ⟨h1', _⟩
    · exact hFootKeep j hj a hf
    · exact hOut a (by omega)
  refine ⟨out, c1 + c2 + 1, h1, y, termTokN,
    runs_seq_iff.mpr (Or.inr ⟨out1, c1, c2, r1, r2, rfl⟩), hh1lo, hh1hi, hOR4, ?_, ?_, ?_⟩
  · refine
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
          rcases ha with ⟨j, hj, hf⟩ | ⟨h1', _, _⟩
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
          rw [(hMetaKeep j hj).2, (I.cells j hj).2.2.2.2.2.2.1, hXG j hj]
          refine dynGraphAt_of_agree (hG1 j hj) (fun x _ hx2 => hOut x ?_)
          have := S.gLt j hj; omega
        lens := fun j hj => by
          rw [(hMetaKeep j hj).1, (I.cells j hj).2.2.2.2.2.2.2.1]
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
          rw [ite_eq_left le_rfl, hOldF, hOR4]
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
          · rw [hPtr]; exact dynGraphAt_of_agree hDG hBlk
          · rw [hPtr]; omega
          · exact hOldLastFCap
        newF := by
          rw [ite_eq_left le_rfl, hNewF, hOR4]
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
  · rw [hHandleD, hPhiT]
    have hPS : branchBPhiSum Rcore A tokN out.mem = branchBPhiSum Rcore A tokN out1.mem := by
      unfold branchBPhiSum
      exact Finset.sum_congr rfl fun j hj => (hRepJ j (Finset.mem_range.mp hj)).2
    have hPhi0 : ∀ b t (mm : ℕ → ℕ),
        (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).phi b t mm = 0 :=
      fun _ _ _ => rfl
    rw [hPS]; simp only [hPhi0] at hc1 ⊢; omega
  · refine ⟨h1,
      { hTle := ⟨hh1lo, by rw [hOR4]; omega⟩
        zone := by rw [hmin, hOR4]; exact hZoneOut
        newCores := fun j hj1 hj2 => absurd hj2 (by omega)
        lastLoc := fun a ha => by
          rw [hXGd, hHandleD] at ha
          exact Or.inr ⟨(hLFoot1 a ha).1, (hLFoot1 a ha).2.1⟩
        metaKeep := fun j hj => hMetaKeep j (by omega)
        metaNew := fun j hj1 hj2 => absurd hj2 (by omega) }⟩

end MinCostFlow.MinRatio
