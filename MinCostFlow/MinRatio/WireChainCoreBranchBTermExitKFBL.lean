module

public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBTermKFBL
import WordRAM.Tactic

/-!
# The terminal step after the Branch B loop under `KFBL` (`WireChainCoreBranchBTermExitKFBL`)

When the plain-step loop of Branch B (`wireBranchBLoopKFBL_runs`) exits at `i₀ = d`, every level
`j < d` took its plain step, and the batch `curU` of level `d` is at `reg 10`. This file runs the
terminal step `wireBranchBTermKFBL` from the exit state when `curU` is not empty, and moves the
facts of the loop invariant across it: the cores, the finished slots (the slot of level `d - 1`
gets its descriptor again, `BranchBDoneSlots.refresh`), the graphs and lengths of the levels, and
the old last level. The model facts that the step needs come from `UpdateLoopModelInv` at
`rem = 0`.

* `chainLen_last_eq`: the length vector of the last level, from the one of level `d - 1`.
* `wireBranchBTermKFBL_runs_exit`: the run and its post when the batch of level `d` is not empty.
* `wireBranchBTermKFBL_runs_exit_empty`: the run when the batch is empty. The step only stores
  `firstReb = d + 1`, and the invariant moves across it by the frame.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The length vector of level `d`, in the chain whose graph of level `d` is replaced by `curG`,
is the core length of the active forest of level `d - 1` on the lengths of level `d - 1`. -/
theorem chainLen_last_eq {cfg : Alg2Config} (ch : ChainState cfg.T cfg.P) (curG : MGraph)
    (ℓ' : ℕ → ℝ) (hd : 0 < cfg.P.d) :
    ({ ch.toTreeChain with G := fun j => if j = cfg.P.d then curG else ch.G j } :
      TreeChain).chainLen ℓ' cfg.P.d =
    coreLen (cfg.T.lsfs (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)))
      (ch.toTreeChain.chainLen ℓ' (cfg.P.d - 1)) := by
  have key : ∀ n, n + 1 = cfg.P.d →
      ({ ch.toTreeChain with G := fun j => if j = cfg.P.d then curG else ch.G j } :
        TreeChain).chainLen ℓ' (n + 1) =
      coreLen (cfg.T.lsfs (ch.scState n) (ch.bran n)) (ch.toTreeChain.chainLen ℓ' n) := by
    intro n hn
    simp only [TreeChain.chainLen]
    have h1 : ({ ch.toTreeChain with G := fun j => if j = cfg.P.d then curG else ch.G j } :
        TreeChain).activeLSF n = cfg.T.lsfs (ch.scState n) (ch.bran n) := by
      simp [TreeChain.activeLSF, ChainState.toTreeChain, show n < cfg.P.d by omega]
    rw [h1, chainLen_congr_lt _ ch.toTreeChain ℓ' n (fun m _ => by
      simp [TreeChain.activeLSF, ChainState.toTreeChain])]
  have := key (cfg.P.d - 1) (by omega)
  rwa [Nat.sub_add_cancel hd] at this

set_option maxHeartbeats 4000000 in
/-- The terminal step of Branch B after the loop exits at `i₀ = d` with a non-empty batch for
level `d`. The exit state `sE` satisfies the loop invariant at `d` and the model invariant at
`rem = 0`, and the run starts at `st`, which differs from `sE` only in `regs 16, 17, 18, 99`.
With `y` the new token of core `d - 1`, the step keeps the reps of all cores (core `d - 1` at
`y`), builds the last level at the new handle `mem (handleBase + d)`, stores `firstReb = d` at
`selBase`, and makes all `d` slots finished in the region `[heapFloor, h1 + 7)`. It keeps the old
last level, the graphs and the lengths. Below `sE.regs 4` it changes only the footprint of core
`d - 1`, the cells `handleBase + d`, `branchBase + d`, the select base, and the descriptor words
`8`, `9` of slot `d - 1`. -/
theorem wireBranchBTermKFBL_runs_exit
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
    (hRLLoc : RL.Local)
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
      out.mem A.selBase = cfg.P.d ∧
      out.mem (A.branchBase + cfg.P.d) = 0 ∧ sE.regs 4 ≤ out.mem (A.handleBase + cfg.P.d) ∧
      curG = cfg.T.S (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) ∧
      RLn.rep (out.mem (A.handleBase + cfg.P.d))
        (cfg.L.build curG (coreLen (cfg.T.lsfs (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)))
          (ch.toTreeChain.chainLen ℓ' (cfg.P.d - 1)))) termTokN out.mem ∧
      (∀ z, RLn.foot (out.mem (A.handleBase + cfg.P.d)) termTokN z →
        sE.regs 4 ≤ z ∧ z < h1 ∧ ∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tokN j) z) ∧
      RL.rep (A.coreH cfg.P.d) (ch.lastK, ch.lastLSFs) termTok out.mem ∧
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
  -- the model facts at `rem = 0`
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
  -- the layout facts
  have hTabLt := S.tableLt
  have hLvlMLt := S.lvlMLt
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hUCLt := S.ucLt
  have hRCLt := S.rcLt
  have hHLt := S.handleLt
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
  -- the terminal step
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
      · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := sGdm z hz1 hz2
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
  -- the frame below `sE.regs 4`
  have hFr' : ∀ z < sE.regs 4, ¬ Rcore.foot (A.coreH dm) (tok dm) z →
      z ≠ A.handleBase + cfg.P.d → z ≠ A.branchBase + cfg.P.d → z ≠ A.selBase →
      z ≠ A.selBase + 1 + 12 * dm + 8 → z ≠ A.selBase + 1 + 12 * dm + 9 →
      out.mem z = sE.mem z := fun z a b c d e f g => by
    rw [hFr z a b c d e f g, hstMem]
  -- a word of a footprint of another core is kept
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
  refine ⟨out, _, h1, y, termTokN, rT, hh1lo, hh1hi, hout4, hzout, hregs, fun j hj => ?_,
    fun j₁ hj₁ j₂ hj₂ hne a ha1 ha2 => ?_, ?_, hSel, hBd, hHd, rfl, hRLn,
    fun z hz => ?_, ?_, fun j hj => ?_, fun j hj => ?_, fun a ha h0 => ?_, ?_⟩
  -- cores
  · by_cases hje : j = dm
    · subst hje
      simp only [↓reduceIte]
      exact ⟨hRepY, fun a ha => (hFootY a ha).imp id fun h => ⟨h.1, by omega⟩⟩
    · simp only [hje, ↓reduceIte]
      have hR := (I.reps j hj).1
      rw [ite_eq_right (show j ≠ cfg.P.d by omega)] at hR
      exact ⟨(hLocJ j hj hje).1 hR, fun a ha => Or.inl ha⟩
  -- disjointness
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
  -- the finished slots
  · have hDone := I.slots.of_le (n' := dm) (by omega)
    have hLists := (I.slots dm hdm).lists
    have hR := BranchBDoneSlots.refresh (foot' := fun r => Rcore.foot (A.coreH r)
        ((fun j => if j = dm then y else tok j) r)) (mem' := out.mem) (cur := h1)
      (Lw := out.mem (A.selBase + 1 + 12 * dm + 9)) hDone hLists hdm hFloor hh1lo
      (fun r hr x => by simp only [show r ≠ dm by omega, ↓reduceIte])
      (fun r _ hne x hx => by simp only [hne, ↓reduceIte] at hx; exact Or.inl hx)
      (fun x hx => by
        simp only [↓reduceIte] at hx
        exact (hFootY x hx).imp id fun h => ⟨h.1, by omega⟩)
      (fun r hr x hx => (I.reps r hr).2 x hx) (fun r hr hne x hx => I.disj r hr dm hdm hne x hx)
      hSlotLe
      (fun r hr i hi hf => by rcases hFootSel r hr _ hf with h | h <;> omega)
      (fun x hx hnf h8x h9x hcase => by
        refine hFr' x hx hnf ?_ ?_ ?_ h8x h9x
        · rintro rfl
          rcases hcase with h | ⟨r, hr, hf⟩ | h
          · omega
          · obtain ⟨_, _, sHBr, _, _, _⟩ := I.static r (by omega)
            exact (sHBr cfg.P.d le_rfl).1 hf
          · omega
        · rintro rfl
          rcases hcase with h | ⟨r, hr, hf⟩ | h
          · omega
          · obtain ⟨_, _, sHBr, _, _, _⟩ := I.static r (by omega)
            exact (sHBr cfg.P.d le_rfl).2 hf
          · omega
        · rintro rfl
          rcases hcase with h | ⟨r, hr, hf⟩ | h
          · omega
          · rcases hFootSel r (by omega) _ hf with h | h <;> omega
          · omega)
      h8 rfl h9 (by have h := hSV; rw [E.four, E.prec] at h; exact h)
      (by simp only [↓reduceIte]; exact hT0) (by simp only [↓reduceIte]; exact hT1)
    rwa [show dm + 1 = cfg.P.d by omega] at hR
  -- the new last level is off every core
  · obtain ⟨hz1, hz2, hz3⟩ := hRLnFoot z hz
    refine ⟨hz1, hz2, fun j hj hf => ?_⟩
    by_cases hje : j = dm
    · simp only [hje, ↓reduceIte] at hf; exact hz3 hf
    · simp only [hje, ↓reduceIte] at hf
      have := (I.reps j hj).2 z hf; omega
  -- the old last level
  · refine (hRLLoc _ _ _ _ _ (fun a ha => ?_)).1 I.term.1
    obtain ⟨t1, t2, _, t4, t5, _⟩ := I.term.2 a ha
    exact (hFr' a (by omega) (t2 dm hdm) (by omega) (by omega) (by omega) (by omega)
      (by omega)).symm
  -- graphs
  · refine dynGraphAt_of_agree (I.graphs j hj) (fun x hx1 hx2 => ?_)
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, _⟩ := S.gSep j hj x hx1 hx2
    have := S.gLt j hj
    exact hFr' x (by omega) (sG j hj x hx1 hx2) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  -- lengths
  · refine (I.lensLt j (by omega)).congr (fun e he t ht => ?_)
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((I.graphs j hj).2.2.1 e he))
    have hlo : A.lPtr0 j ≤ A.lPtr0 j + e * L + t := by omega
    have hhi : A.lPtr0 j + e * L + t < A.lPtr0 j + eCap * L := by omega
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := S.lSep j hj _ hlo hhi
    have := S.lLt j hj
    exact hFr' _ (by omega) (sL j hj _ hlo hhi) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  -- the frame
  · exact fun a1 a2 a3 a4 a5 => hFr' a ha (h0 dm hdm) a1 a2 a3 a4 a5
  -- cost
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

/-- The terminal step of Branch B after the loop exits at `i₀ = d` with an empty batch for
level `d`: it only stores `firstReb = d + 1` at `selBase`. The select base lies off every
footprint, every graph and length block, the old last level and the slots, so the cores, the
finished slots and the rest of the invariant stay. -/
theorem wireBranchBTermKFBL_runs_exit_empty
    {w L P depth vCap eCap capExp wordExp stretchPrec N0 readGraph readLSF coreLenProc readOrd
      lastInit : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
    (hLoc : Rcore.Local) (hRLLoc : RL.Local)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok cfg.P.d ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' 0 cfg.P.d ch curG curU curEnc oldOrd)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (hEmpty : curU = []) (hRoom : sE.regs 4 < 2 ^ w) :
    ∃ out : State,
      Runs w p ω (wireBranchBTermKFBL readGraph readLSF coreLenProc readOrd lastInit) st
        .normal out 8 ∧
      out.regs = st.regs ∧ out.mem A.selBase = cfg.P.d + 1 ∧
      (∀ a, a ≠ A.selBase → out.mem a = sE.mem a) ∧
      curG.E = (ch.G cfg.P.d).E ∧
      (∀ j < cfg.P.d, Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) out.mem) ∧
      BranchBDoneSlots w P cfg.P.d
        (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
        (fun r => Rcore.foot (A.coreH r) (tok r)) A.heapFloor (sE.regs 4) A.selBase out.mem
        cfg.P.d D ch0.G levelU (fun j => (ch.G j).E)
        (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr) ∧
      RL.rep (A.coreH cfg.P.d) (ch.lastK, ch.lastLSFs) termTok out.mem ∧
      (∀ j < cfg.P.d, DynGraphAt out.mem (A.gPtr0 j) vCap eCap (ch.G j)) ∧
      (∀ j < cfg.P.d,
        EdgeValuesAt out.mem (A.lPtr0 j) 4 L P (ch.G j).E (ch.toTreeChain.chainLen ℓ' j)) ∧
      branchBPhiSum Rcore A tok out.mem = branchBPhiSum Rcore A tok sE.mem := by
  obtain ⟨hFloor, hr10, _, _, _, hr72, _, _, hr75, _⟩ := I.regs
  have hdW : cfg.P.d + 1 < 2 ^ w := by have := S.hbLt; omega
  have rE := wireBranchBTermKFBL_runs_empty (p := p) (ω := ω) (st := st) readGraph readLSF
    coreLenProc readOrd lastInit
    ⟨(hstRegs 10 (by decide) (by decide) (by decide) (by decide)).trans hr10,
      (hstRegs 72 (by decide) (by decide) (by decide) (by decide)).trans hr72,
      (hstRegs 75 (by decide) (by decide) (by decide) (by decide)).trans hr75⟩
    (by rw [hstMem, I.batchLen, hEmpty]; rfl) hdW
  have hAg : ∀ a, a ≠ A.selBase →
      Function.update st.mem A.selBase (cfg.P.d + 1) a = sE.mem a := fun a ha => by
    rw [Function.update_of_ne ha, hstMem]
  have hFootNe : ∀ r < cfg.P.d, ∀ a, Rcore.foot (A.coreH r) (tok r) a → a ≠ A.selBase :=
    fun r hr a ha h => by
      subst h; rcases I.footLoc r hr _ ha with h | h <;> omega
  have hLocJ : ∀ j < cfg.P.d,
      (Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j) sE.mem →
        Rcore.rep (A.coreH j) (chainLevelOrdAbs ch j) (tok j)
          (Function.update st.mem A.selBase (cfg.P.d + 1))) ∧
      Rcore.phi (A.coreH j) (tok j) sE.mem =
        Rcore.phi (A.coreH j) (tok j) (Function.update st.mem A.selBase (cfg.P.d + 1)) :=
    fun j hj => hLoc _ _ _ _ _ (fun a ha => (hAg a (hFootNe j hj a ha)).symm)
  have hMetaLt := S.metaLt
  refine ⟨_, rE, rfl, by simp, hAg, ?_, fun j hj => ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_,
    ?_⟩
  · exact hM.1 hEmpty
  · have hR := (I.reps j hj).1
    rw [ite_eq_right (show j ≠ cfg.P.d by omega)] at hR
    exact (hLocJ j hj).1 hR
  · refine I.slots.frame le_rfl (fun _ _ _ => Iff.rfl) (fun _ _ _ _ _ h => h)
      (fun a ha => hAg a ?_) (fun j hj i hi => hAg _ (by omega))
    rintro rfl
    rcases ha with ⟨r, hr, hf⟩ | ⟨h1, _, _⟩
    · exact hFootNe r (by omega) _ hf rfl
    · omega
  · refine (hRLLoc _ _ _ _ _ (fun a ha => (hAg a ?_).symm)).1 I.term.1
    have := (I.term.2 a ha).1; omega
  · refine dynGraphAt_of_agree (I.graphs j hj) (fun x hx1 hx2 => hAg x ?_)
    have := S.gLt j hj; omega
  · refine (I.lensLt j (by omega)).congr (fun e he t ht => hAg _ ?_)
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using
        Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((I.graphs j hj).2.2.1 e he))
    have := S.lLt j hj; omega
  · unfold branchBPhiSum
    exact Finset.sum_congr rfl (fun j hj => (hLocJ j (Finset.mem_range.mp hj)).2.symm)

end MinCostFlow.MinRatio
