module

public import MinCostFlow.MinRatio.WireChainCoreBranchBForestLocGoalKFBL
import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
import WordRAM.Tactic

/-!
# Where the forests lie at the terminal non-empty exit of Branch B (`WireChainCoreBranchBExitLocTerm`)

This file proves `BranchBTermExitForestLocGoalKFBL`
(`WireChainCoreBranchBForestLocGoalKFBL.lean`): at every run of the terminal non-empty exit
`wireBranchBTermKFBL … ;; collectTermForestStmt 81`, the old last forest at `oldPtrs + d` lies in
the footprint of the old last level (`hOldLast`), and the new last forest at `newPtrs + d` lies in
the fresh heap `[A.heapFloor, out.regs 4)`.

The proof constructs the run from `wireBranchBTermKFBL_runs_exit` and `collectTermForestStmt_runs`,
identifies any run with it by `Runs.det`, and uses `dynGraphAt_caps_eq` to fix the graph caps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 1600000 in
/-- **Proof of `BranchBTermExitForestLocGoalKFBL`.** At every run of the terminal non-empty exit,
the words of the old last forest lie in the footprint of the old last level and the words of the
new last forest lie in `[A.heapFloor, out.regs 4)`. -/
theorem branchBTermExitForestLocGoalKFBL_proved : BranchBTermExitForestLocGoalKFBL := by
  intro w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
    edgeProc signExt mul intDiv copy wordExp stretchPrec N0 capLimit coreLenProc lastInit
    lastMul lastSpace nextM vcL ecL oldPtrs newPtrs intCap
    fmt cfg Psc alloc lastAlloc Ginit reembFn Rcore E0 p opCore opLast ω A origLen ℓ' g'
    BWc EWc ULc ch0 termTok ch curG curU curEditsList curEnc oldOrd sE st tok
    curBatch curBatchWords curEdits curEditsWords levelU levelUS D
    E S hOldLo hOldNew hNewHi hN0 hLvlM hd I hM hstMem hstRegs hNonEmpty hcapLim hCoreLenProc
    hLastImpl hLastSp hLWord hPWord hWidth hHm hRotW hRoom h71 h81 hOldLast _
    X hKPos _ out cost hRun
  have hRLLoc := LastLevelProgram.lastLevelRepresentation_local vcL ecL 4 L P E0
  obtain ⟨hFloor, _, _, _, _, _, _, _, hr75, _, hr77, hr78, _, _, _, _, _, _, _, _, _, _⟩ :=
    I.regs
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  obtain ⟨out1, c1, h1, _, termTokN, r1, hh1lo, hh1hi, hR4, _, hReg1, _, _, _,
      _, hLB1, _, _, hLRep1, hLFoot1, _, _, _, hFr1, _⟩ :=
    wireBranchBTermKFBL_runs_exit E hRLLoc S hSlotLe hN0 hLvlM hd I hM hstMem hstRegs hNonEmpty
      hcapLim hCoreLenProc hLastImpl hLastSp hLWord hPWord hWidth hHm hRotW hRoom
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
  have hLRepX : (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P curG.E).rep termH
      (X.lastK, X.lastLSFs) termTokN out1.mem := by rw [hXBuild]; exact hLRep1
  obtain ⟨hTLo, _, _, hTBr⟩ := hLRepX
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
  obtain ⟨out', c2, r2, _, hOutMem, hOutRegs⟩ :=
    collectTermForestStmt_runs (w := w) (p := p) (ω := ω) (st := out1) (dstReg := 81)
      (dstPtrs := newPtrs) (baseIdx := 0) (d := cfg.P.d) (handleBase := A.handleBase)
      (branchBase := A.branchBase) (termHandle := termH) (lastBran := X.lastBran)
      (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (hO1 81 _ (by decide) (by decide) h81) (hO1 71 _ (by decide) (by decide) h71)
      (hO1 75 _ (by decide) (by decide) hr75) (hO1 77 _ (by decide) (by decide) hr77)
      (hO1 78 _ (by decide) (by decide) hr78) (by decide) (Nat.zero_le _) rfl
      (by rw [hXB0]; exact hLB1) rfl rfl
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hRun' : Runs w p ω (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5)
      lastInit ;; collectTermForestStmt 81) st .normal out' (c1 + c2 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨out1, c1, c2, r1, r2, rfl⟩)
  obtain ⟨_, rfl, _⟩ := Runs.det hRun' hRun
  have hOut : ∀ a, a ≠ newPtrs + cfg.P.d → out'.mem a = out1.mem a := fun a h => by
    rw [hOutMem, Function.update_of_ne (by omega)]
  have hOutLow : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
      a ≠ A.handleBase + cfg.P.d → a ≠ A.branchBase + cfg.P.d → out'.mem a = sE.mem a :=
    fun a ha hc h1' h2' => (hOut a (by omega)).trans (hFrLow a ha hc h1' h2')
  have hOR4 : out'.regs 4 = h1 + 7 := by
    rw [hOutRegs 4 (by decide) (by decide) (by decide), hR4]
  have hOldF : chainSuffixForests ch0 cfg.P.d = [(ch0.lastLSFs ch0.lastBran).F.F] := by
    simp [chainSuffixForests]
  have hNewF : chainSuffixForests X cfg.P.d = [(X.lastLSFs X.lastBran).F.F] := by
    simp [chainSuffixForests]
  refine ⟨?_, ?_⟩
  · intro t ht vc ec hDG x hx1 hx2
    have ht0 : t = 0 := by rw [hOldF] at ht; simp at ht; exact ht
    subst ht0
    simp only [Nat.add_zero] at hDG hx1 hx2
    obtain ⟨vc0, ec0, hDG0, hInF⟩ := hOldLast
    have hBlk : ∀ y, sE.mem (oldPtrs + cfg.P.d) ≤ y →
        y < sE.mem (oldPtrs + cfg.P.d) + dynGraphSize vc0 ec0 → out'.mem y = sE.mem y :=
      fun y hy1 hy2 => by
        obtain ⟨hy3, hy4, _, hy5, hy6, _⟩ := I.term.2 y (hInF y hy1 hy2)
        exact hOutLow y hy3 hy4 (by omega) (by omega)
    have hPtr : out'.mem (oldPtrs + cfg.P.d) = sE.mem (oldPtrs + cfg.P.d) := by
      rw [hOut _ (by omega)]
      refine hFr1 _ (by omega) (fun j hj hf => ?_) (by omega) (by omega) (by omega)
        (by omega) (by omega)
      rcases I.footLoc j hj _ hf with h | h <;> omega
    have hDG0' : DynGraphAt out'.mem (out'.mem (oldPtrs + cfg.P.d)) vc0 ec0
        (ch0.lastLSFs ch0.lastBran).F.F := by
      rw [hPtr]; exact dynGraphAt_of_agree hDG0 hBlk
    obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hDG hDG0'
    subst hvc hec
    rw [hPtr] at hx1 hx2
    exact Or.inr (Or.inl (hInF x hx1 hx2))
  · intro t ht vc ec hDG x hx1 hx2
    have ht0 : t = 0 := by rw [hNewF] at ht; simp at ht; exact ht
    subst ht0
    simp only [Nat.add_zero] at hDG hx1 hx2
    have hPtr : out'.mem (newPtrs + cfg.P.d) = forestPtr := by
      rw [hOutMem]; simp
    have hDG0' : DynGraphAt out'.mem (out'.mem (newPtrs + cfg.P.d)) vCap eCap
        (X.lastLSFs X.lastBran).F.F := by
      rw [hPtr]
      refine dynGraphAt_of_agree hTLSF.2.1 (fun y hy1 hy2 => hOut y ?_)
      have := (hInT y (by omega) (by omega)).1; omega
    obtain ⟨hvc, hec⟩ := dynGraphAt_caps_eq hDG hDG0'
    subst hvc hec
    rw [hPtr] at hx1 hx2
    have hxIn := hInT x (by omega) (by omega)
    exact Or.inr (Or.inr ⟨by omega, by rw [hOR4]; omega⟩)

end MinCostFlow.MinRatio
