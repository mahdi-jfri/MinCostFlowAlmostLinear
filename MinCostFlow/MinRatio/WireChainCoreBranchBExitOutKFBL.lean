module

public import MinCostFlow.MinRatio.WireChainCoreBranchBIntExitKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBTermExitKFBL
public import MinCostFlow.MinRatio.WireShiftDeepSteps
import WordRAM.Tactic

/-!
# The state after the exits of the loop of Branch B (`WireChainCoreBranchBExitBaseKFBL`)

After its loop, Branch B runs one of three exits:
* the interior rebuild, when the test fires at a level `i₀ < d` (`wireBranchBIntKFBL`);
* the terminal step and the copy of the new last forest, when the loop reaches `d` and the batch
  of level `d` is not empty;
* the same code when the batch of level `d` is empty, where the terminal step only stores
  `firstReb = d + 1`.

The suffix of Branch B (the two tree syncs and the push) and its post read the same facts after
each exit. The structure `BranchBExitBaseKFBL` holds them, with the number `firstReb` that the
select region gets (`i₀`, `d` or `d + 1`) and the model `X` after the update. This file gives the
structure from the interior exit (`BranchBExitBaseKFBL.of_int`) and from the terminal step with an
empty batch (`wireBranchBTermEmpty_exitOut`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The facts after an exit of the loop of Branch B, at the state `out`, from the state `sE` at
the top of the last pass of the loop. The select base holds `firstReb = fr`, the levels below
`min fr d` keep their handles and have finished slots, all cores hold the levels of the model `X`
after the update at the handles in `mem (handleBase + j)`, the last level is at the handle in
`mem (handleBase + d)` with caps `(vcL, ecL)`, and the old and new forests of the levels from
`fr` on are listed at `oldPtrs + fr` and `newPtrs + fr` (no forests when `fr = d + 1`). Between
the select slots and the heap floor, the exit writes only the two arrays of forest pointers. -/
structure BranchBExitBaseKFBL {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (A : BranchBAddrs)
    (vcL ecL oldPtrs newPtrs intCap fr : ℕ) (ch0 ch X : ChainState cfg.T cfg.P)
    (levelU : ℕ → List Update) (D : ℕ → LevelDiffLists) (sE out : State) (tok tokN : ℕ → Rcore.τ)
    (termTokN : ℕ) : Prop where
  frLe : fr ≤ cfg.P.d + 1
  heapLo : sE.regs 4 ≤ out.regs 4
  zero : ZeroFrom out.mem (out.regs 4)
  regs : ∀ r, 70 ≤ r → r ≠ 97 → r ≠ 99 → out.regs r = sE.regs r
  handlesLow : ∀ j < min fr cfg.P.d, out.mem (A.handleBase + j) = A.coreH j
  reps : ∀ j < cfg.P.d,
    Rcore.rep (out.mem (A.handleBase + j)) (chainLevelOrdAbs X j) (tokN j) out.mem ∧
    ∀ a, Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a →
      Rcore.foot (A.coreH j) (tok j) a ∨ (sE.regs 4 ≤ a ∧ a < out.regs 4)
  disj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
    Rcore.foot (out.mem (A.handleBase + j₁)) (tokN j₁) a →
      ¬ Rcore.foot (out.mem (A.handleBase + j₂)) (tokN j₂) a
  slots : BranchBDoneSlots w P cfg.P.d
    (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
    (fun r => Rcore.foot (out.mem (A.handleBase + r)) (tokN r)) A.heapFloor (out.regs 4)
    A.selBase out.mem (min fr cfg.P.d) D ch0.G levelU (fun j => (ch.G j).E)
    (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr)
  sel : out.mem A.selBase = fr
  cells : ∀ j < cfg.P.d, out.mem (A.branchBase + j) = X.bran j ∧
    out.mem (A.ucBase + j) = X.updCount j ∧ out.mem (A.rcBase + j) = X.rebuildCount j
  lastB : out.mem (A.branchBase + cfg.P.d) = X.lastBran
  graphs : ∀ j < cfg.P.d,
    DynGraphAt out.mem (out.mem (A.levelMeta + cfg.P.d + j)) vCap eCap (X.G j)
  lens : ∀ j < cfg.P.d, EdgeValuesAt out.mem (out.mem (A.levelMeta + j)) 4 L P (X.G j).E
    (X.toTreeChain.chainLen X.ℓ j)
  lastRep : (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P (X.G cfg.P.d).E).rep
    (out.mem (A.handleBase + cfg.P.d)) (X.lastK, X.lastLSFs) termTokN out.mem
  lastFoot : ∀ a, (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
      (X.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a →
    (a < A.selBase ∨ (sE.regs 4 ≤ a ∧ a < out.regs 4)) ∧
    ∀ j < cfg.P.d, ¬ Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a
  oldF : ForestPtrListAt out.mem (oldPtrs + fr)
    (if fr ≤ cfg.P.d then chainSuffixForests ch0 fr else []) intCap (out.regs 4)
  newF : ForestPtrListAt out.mem (newPtrs + fr)
    (if fr ≤ cfg.P.d then chainSuffixForests X fr else []) intCap (out.regs 4)
  frame : ∀ a < A.selBase, (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) →
    (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) →
    (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) →
    (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) → (a < A.rcBase ∨ A.rcBase + cfg.P.d ≤ a) →
    (∀ j < cfg.P.d, a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) →
    (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) → out.mem a = sE.mem a
  frameHeap : ∀ a, A.selBase + 1 + 12 * cfg.P.d ≤ a → a < A.heapFloor →
    (a < oldPtrs ∨ oldPtrs + (cfg.P.d + 1) ≤ a) → (a < newPtrs ∨ newPtrs + (cfg.P.d + 1) ≤ a) →
    out.mem a = sE.mem a

/-- The zone of the select data of the finished levels in the heap of Branch B: `[lo, hS)`,
below the rebuilt blocks, and `[hT, hX)`, above them. -/
@[expose] def BranchBSelZone (lo hS hT hX x : ℕ) : Prop :=
  (lo ≤ x ∧ x < hS) ∨ (hT ≤ x ∧ x < hX)

/-- Where an exit of the loop of Branch B puts its words, at the cut `hT` with
`sE.regs 4 ≤ hT ≤ out.regs 4`. The new cores (the levels from `fr` on), the new last level and the
new level blocks (the levels from `fr + 1` on) lie in `[sE.regs 4, hT)`. The select data of the
finished levels lies in the zone `[heapFloor, sE.regs 4) ∪ [hT, out.regs 4)`: the interior and
the terminal exits write the descriptor of level `fr - 1` again at `hT`, above the rebuilt blocks.
The meta words of the levels below `fr + 1` keep their values. -/
structure BranchBExitLayKFBL {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (A : BranchBAddrs) (vcL ecL fr : ℕ)
    (ch0 ch X : ChainState cfg.T cfg.P) (levelU : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (sE out : State) (tokN : ℕ → Rcore.τ) (termTokN hT : ℕ) : Prop where
  hTle : sE.regs 4 ≤ hT ∧ hT ≤ out.regs 4
  zone : ∀ j < min fr cfg.P.d,
    SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
      (fun x => BranchBSelZone A.heapFloor (sE.regs 4) hT (out.regs 4) x ∧
        ∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (A.handleBase + r)) (tokN r) x)
      (fun x => Rcore.foot (out.mem (A.handleBase + j)) (tokN j) x ∨
        (A.heapFloor ≤ x ∧ x < out.regs 4))
      A.heapFloor (out.regs 4) out.mem (A.selBase + 1 + 12 * j) (D j) (ch0.G j) (levelU j)
      (ch.G j).E (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr
  newCores : ∀ j, fr ≤ j → j < cfg.P.d →
    sE.regs 4 ≤ out.mem (A.handleBase + j) ∧ out.mem (A.handleBase + j) ≤ hT ∧
    ∀ a, Rcore.foot (out.mem (A.handleBase + j)) (tokN j) a → sE.regs 4 ≤ a ∧ a < hT
  lastLoc : ∀ a, (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
      (X.G cfg.P.d).E).foot (out.mem (A.handleBase + cfg.P.d)) termTokN a →
    a < A.selBase ∨ (sE.regs 4 ≤ a ∧ a < hT)
  metaKeep : ∀ j < min (fr + 1) cfg.P.d,
    out.mem (A.levelMeta + j) = sE.mem (A.levelMeta + j) ∧
    out.mem (A.levelMeta + cfg.P.d + j) = sE.mem (A.levelMeta + cfg.P.d + j)
  metaNew : ∀ j, fr + 1 ≤ j → j < cfg.P.d →
    let gp := out.mem (A.levelMeta + cfg.P.d + j)
    let lp := out.mem (A.levelMeta + j)
    sE.regs 4 ≤ gp ∧ gp + dynGraphSize vCap eCap ≤ hT ∧ sE.regs 4 ≤ lp ∧ lp + eCap * L ≤ hT ∧
    ∀ a, ((gp ≤ a ∧ a < gp + dynGraphSize vCap eCap) ∨ (lp ≤ a ∧ a < lp + eCap * L)) →
      (∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (A.handleBase + r)) (tokN r) a) ∧
      ¬ (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P (X.G cfg.P.d).E).foot
        (out.mem (A.handleBase + cfg.P.d)) termTokN a

/-- The facts after an exit of the loop of Branch B: those of `BranchBExitBaseKFBL` and the places
of `BranchBExitLayKFBL` at the cut `hT`. -/
structure BranchBExitOutKFBL {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (A : BranchBAddrs)
    (vcL ecL oldPtrs newPtrs intCap fr : ℕ) (ch0 ch X : ChainState cfg.T cfg.P)
    (levelU : ℕ → List Update) (D : ℕ → LevelDiffLists) (sE out : State) (tok tokN : ℕ → Rcore.τ)
    (termTokN hT : ℕ) : Prop
    extends BranchBExitBaseKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vcL ecL oldPtrs newPtrs intCap fr ch0 ch X levelU D sE out tok tokN
        termTokN,
      BranchBExitLayKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vcL ecL fr ch0 ch X levelU D sE out tokN termTokN hT

/-- The facts of the interior exit are those of `BranchBExitBaseKFBL` at `firstReb = i₀ < d`,
with the new last level at the caps `(vCap, eCap)`. -/
theorem BranchBExitBaseKFBL.of_int {w L P vCap eCap capExp : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {A : BranchBAddrs}
    {oldPtrs newPtrs intCap i₀ : ℕ} {ch0 ch next : ChainState cfg.T cfg.P}
    {levelU : ℕ → List Update} {D : ℕ → LevelDiffLists} {sE out : State}
    {tok tokN : ℕ → Rcore.τ} {termTokN : ℕ} (hi : i₀ < cfg.P.d)
    (O : BranchBIntOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A oldPtrs newPtrs intCap i₀ ch0 ch next levelU D sE out tok tokN
      termTokN) :
    BranchBExitBaseKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) A vCap eCap oldPtrs newPtrs intCap i₀ ch0 ch next levelU D sE out tok
      tokN termTokN := by
  have hmin : min i₀ cfg.P.d = i₀ := Nat.min_eq_left hi.le
  refine
    { frLe := by omega
      heapLo := O.heapLo
      zero := O.zero
      regs := O.regs
      handlesLow := fun j hj => O.handlesLow j (by omega)
      reps := O.reps
      disj := O.disj
      slots := by rw [hmin]; exact O.slots
      sel := O.sel
      cells := O.cells
      lastB := O.lastB
      graphs := O.graphs
      lens := O.lens
      lastRep := O.lastRep
      lastFoot := fun a ha =>
        ⟨Or.inr ⟨(O.lastFoot a ha).1, (O.lastFoot a ha).2.1⟩, (O.lastFoot a ha).2.2⟩
      oldF := by rw [if_pos hi.le]; exact O.oldF
      newF := by rw [if_pos hi.le]; exact O.newF
      frame := O.frame
      frameHeap := O.frameHeap }

set_option maxHeartbeats 1600000 in
/-- **The terminal exit with an empty batch.** The loop exits at `i₀ = d` with the invariant `I`
at `sE`, and the batch of level `d` is empty. The run starts at `st`, which differs from `sE`
only in `regs 16, 17, 18, 99`. The terminal step stores `firstReb = d + 1`, and the copy of the
last forest writes the pointer of the old last forest to `newPtrs + d`, a word of the reserved
part of the heap. The model `X` is the rest of `Chain.Ordered.updateLoop` at level `d`, which
only puts the graph `curG` (with the edges of the old one) at level `d`. Then
`BranchBExitBaseKFBL` holds at `firstReb = d + 1`, with the old tokens and the old last level. -/
theorem wireBranchBTermEmpty_exitOut
    {w L P depth vCap eCap capExp wordExp stretchPrec N0 readGraph readLSF coreLenProc readOrd
      lastInit vcL ecL oldPtrs newPtrs intCap lsfHdr forestPtr : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {E0 : Finset ℕ} {p : Program}
    {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P}
    {termTok : ℕ} {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE st : State}
    {tok : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists}
    (hLoc : Rcore.Local)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldNew : oldPtrs + (cfg.P.d + 1) ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt)
      (RL := LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P E0) reembFn A origLen ℓ' N0
      BWc EWc ULc ch0 termTok cfg.P.d ch curG curU curEditsList oldOrd sE tok curBatch
      curBatchWords curEdits curEditsWords levelU levelUS D)
    (hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap) origLen
      ℓ' g' 0 cfg.P.d ch curG curU curEnc oldOrd)
    (hstMem : st.mem = sE.mem)
    (hstRegs : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → r ≠ 99 → st.regs r = sE.regs r)
    (hEmpty : curU = []) (hE0 : (ch0.G cfg.P.d).E = E0)
    (h71 : sE.regs 71 = 0) (h81 : sE.regs 81 = newPtrs)
    (hLsfHdr : sE.mem (A.coreH cfg.P.d + 1 + ch.lastBran) = lsfHdr)
    (hForestPtr : sE.mem (lsfHdr + 1) = forestPtr)
    (hTW : A.coreH cfg.P.d + 1 + ch.lastBran < A.selBase) (hLW : lsfHdr + 1 < A.selBase)
    (hRoom : sE.regs 4 < 2 ^ w) :
    let X := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P N0 ℓ' g' 0 cfg.P.d ch curG curU
      curEnc).1
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBTermKFBL readGraph readLSF coreLenProc readOrd lastInit ;;
        collectTermForestStmt 81) st .normal out cost ∧
      cost ≤ 44 ∧ out.regs 4 = sE.regs 4 ∧
      branchBPhiSum Rcore A tok out.mem = branchBPhiSum Rcore A tok sE.mem ∧
      BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) A vcL ecL oldPtrs newPtrs intCap (cfg.P.d + 1) ch0 ch X levelU D sE
        out tok tok termTok (sE.regs 4) := by
  intro X
  have hRLLoc := LastLevelProgram.lastLevelRepresentation_local vcL ecL 4 L P E0
  obtain ⟨hFloor, _, _, _, _, _, _, _, hr75, _, hr77, hr78, _, _, _, _, _, _, _, _, _, _⟩ :=
    I.regs
  have hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor := by omega
  obtain ⟨out1, r1, hReg1, hSel1, hMem1, hCurGE, _, _, _, _, _, _⟩ :=
    wireBranchBTermKFBL_runs_exit_empty (readGraph := readGraph) (readLSF := readLSF)
      (coreLenProc := coreLenProc) (readOrd := readOrd) (lastInit := lastInit) (p := p) (ω := ω)
      (st := st) (wordExp := wordExp) (stretchPrec := stretchPrec) (g' := g') (curEnc := curEnc)
      hLoc hRLLoc S hSlotLe I hM hstMem hstRegs hEmpty hRoom
  have hHB := S.hbLt
  have hBB := S.bbLt
  have hW : A.selBase < 2 ^ w := by omega
  -- the copy of the last forest
  have hM1 : ∀ a, a < A.selBase → out1.mem a = sE.mem a := fun a ha => hMem1 a (by omega)
  obtain ⟨out, c2, r2, hc2, hOutMem, hOutRegs⟩ :=
    collectTermForestStmt_runs (w := w) (p := p) (ω := ω) (st := out1) (dstReg := 81)
      (dstPtrs := newPtrs) (baseIdx := 0) (d := cfg.P.d) (handleBase := A.handleBase)
      (branchBase := A.branchBase) (termHandle := A.coreH cfg.P.d) (lastBran := ch.lastBran)
      (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (by rw [hReg1, hstRegs 81 (by decide) (by decide) (by decide) (by decide)]; exact h81)
      (by rw [hReg1, hstRegs 71 (by decide) (by decide) (by decide) (by decide)]; exact h71)
      (by rw [hReg1, hstRegs 75 (by decide) (by decide) (by decide) (by decide)]; exact hr75)
      (by rw [hReg1, hstRegs 77 (by decide) (by decide) (by decide) (by decide)]; exact hr77)
      (by rw [hReg1, hstRegs 78 (by decide) (by decide) (by decide) (by decide)]; exact hr78)
      (by decide) (Nat.zero_le _)
      (by rw [hM1 _ (by omega)]; exact I.termCells.1)
      (by rw [hM1 _ (by omega)]; exact I.termCells.2)
      (by rw [hM1 _ hTW]; exact hLsfHdr) (by rw [hM1 _ hLW]; exact hForestPtr)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hOut : ∀ a, a ≠ A.selBase → a ≠ newPtrs + cfg.P.d → out.mem a = sE.mem a :=
    fun a h1 h2 => by
      rw [hOutMem, Function.update_of_ne (by omega)]; exact hMem1 a h1
  have hOutLow : ∀ a, a < A.selBase → out.mem a = sE.mem a := fun a ha =>
    hOut a (by omega) (by omega)
  have hR4 : out.regs 4 = sE.regs 4 := by
    rw [hOutRegs 4 (by decide) (by decide) (by decide), hReg1,
      hstRegs 4 (by decide) (by decide) (by decide) (by decide)]
  -- the model after the update
  have hX : X = { ch with
      G := (fun j => if j = cfg.P.d then curG else ch.G j)
      ℓ := ℓ'
      g := g' } := by
    simp only [X, Chain.Ordered.updateLoop, hEmpty, ↓reduceIte]
  have hXE : (X.G cfg.P.d).E = E0 := by
    rw [hX]; simp only [↓reduceIte]
    rw [hCurGE, (I.modelFrame.1 cfg.P.d le_rfl).1, hE0]
  have hXG : ∀ i < cfg.P.d, X.G i = ch.G i := fun i hi => by rw [hX]; simp [hi.ne]
  have hXabs : ∀ j < cfg.P.d, chainLevelOrdAbs X j = chainLevelOrdAbs ch j := fun j hj => by
    have hSc : X.scState = ch.scState := by rw [hX]
    have hBr : X.bran = ch.bran := by rw [hX]
    have hUc : X.updCount = ch.updCount := by rw [hX]
    simp only [chainLevelOrdAbs, ChainState.levelOrd, chainLevelOrd, hXG j hj, hXG 0 (by omega),
      hSc, hBr, hUc]
  have hHandle : ∀ j < cfg.P.d, out.mem (A.handleBase + j) = A.coreH j := fun j hj => by
    rw [hOutLow _ (by omega)]; exact (I.cells j hj).2.2.1
  have hHandleD : out.mem (A.handleBase + cfg.P.d) = A.coreH cfg.P.d := by
    rw [hOutLow _ (by omega)]; exact I.termCells.1
  -- the reps of the cores
  have hFootKeep : ∀ j < cfg.P.d, ∀ a, Rcore.foot (A.coreH j) (tok j) a → out.mem a = sE.mem a :=
    fun j hj a ha => by
      rcases I.footLoc j hj a ha with h | h
      · exact hOutLow a h
      · exact hOut a (by omega) (by omega)
  have hRepJ : ∀ j < cfg.P.d, Rcore.rep (A.coreH j) (chainLevelOrdAbs X j) (tok j) out.mem ∧
      Rcore.phi (A.coreH j) (tok j) out.mem = Rcore.phi (A.coreH j) (tok j) sE.mem := by
    intro j hj
    have hL := hLoc (A.coreH j) (chainLevelOrdAbs ch j) (tok j) sE.mem out.mem
      (fun a ha => (hFootKeep j hj a ha).symm)
    have hR := (I.reps j hj).1
    rw [if_neg hj.ne] at hR
    rw [hXabs j hj]
    exact ⟨hL.1 hR, hL.2.symm⟩
  refine ⟨out, 8 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨out1, 8, c2, r1, r2, rfl⟩), by omega, hR4,
    ?_, ?_⟩
  · unfold branchBPhiSum
    exact Finset.sum_congr rfl fun j hj => (hRepJ j (Finset.mem_range.mp hj)).2
  have hmin : min (cfg.P.d + 1) cfg.P.d = cfg.P.d := by omega
  have hSlotsB : BranchBDoneSlots w P cfg.P.d
      (fun j => ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
      (fun r => Rcore.foot (out.mem (A.handleBase + r)) (tok r)) A.heapFloor (sE.regs 4)
      A.selBase out.mem cfg.P.d D ch0.G levelU (fun j => (ch.G j).E)
      (fun j => (cfg.T.lsfs (ch.scState j) (ch.bran j)).wstr) := by
    refine I.slots.frame le_rfl (fun j hj x => by rw [hHandle j hj])
      (fun r hr x _ _ hf => by rw [hHandle r hr] at hf; exact hf) (fun a ha => ?_)
      (fun j hj i hi => hOut _ (by omega) (by omega))
    rcases ha with ⟨j, hj, hf⟩ | ⟨h1, _, _⟩
    · exact hFootKeep j hj a hf
    · exact hOut a (by omega) (by omega)
  refine
    { frLe := le_rfl
      heapLo := hR4.ge
      zero := fun a ha => by
        rw [hR4] at ha
        rw [hOut a (by omega) (by omega)]; exact I.zero a ha
      regs := fun r hr h97 h99 => by
        rw [hOutRegs r (by omega) (by omega) (by omega), hReg1,
          hstRegs r (by omega) (by omega) (by omega) h99]
      handlesLow := fun j hj => hHandle j (by omega)
      reps := fun j hj => by
        rw [hHandle j hj]
        exact ⟨(hRepJ j hj).1, fun a ha => Or.inl ha⟩
      disj := fun j₁ hj₁ j₂ hj₂ hne a => by
        rw [hHandle j₁ hj₁, hHandle j₂ hj₂]; exact I.disj j₁ hj₁ j₂ hj₂ hne a
      slots := by rw [hmin, hR4]; exact hSlotsB
      hTle := ⟨le_rfl, hR4.ge⟩
      zone := fun j hj => by
        rw [hmin] at hj
        refine (hSlotsB j hj).transfer (fun _ _ => rfl) (fun _ _ => rfl)
          (fun a h1 h2 hg => ⟨Or.inl ⟨h1, by omega⟩, hg⟩)
          (fun a ha => ha.imp id fun h => ⟨h.1, by omega⟩) le_rfl hR4.ge
      newCores := fun j hj1 hj2 => absurd hj2 (by omega)
      lastLoc := fun a ha => by
        rw [hXE, hHandleD] at ha
        exact Or.inl (I.term.2 a ha).1
      metaKeep := fun j hj => by
        have hMeta := S.metaLt
        have hj' : j < cfg.P.d := by omega
        exact ⟨hOutLow _ (by omega), hOutLow _ (by omega)⟩
      metaNew := fun j hj1 hj2 => absurd hj2 (by omega)
      sel := by
        rw [hOutMem, Function.update_of_ne (by omega)]; exact hSel1
      cells := fun j hj => by
        have hc := I.cells j hj
        have hRC := S.rcLt
        have hUC := S.ucLt
        rw [hOutLow _ (by omega), hOutLow _ (by omega), hOutLow _ (by omega), hX]
        exact ⟨hc.2.2.2.1, hc.2.2.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2.2.2⟩
      lastB := by
        rw [hOutLow _ (by omega), hX]; exact I.termCells.2
      graphs := fun j hj => by
        have hMeta := S.metaLt
        rw [hOutLow _ (by omega), (I.cells j hj).2.2.2.2.2.2.1, hXG j hj]
        refine dynGraphAt_of_agree (I.graphs j hj) (fun x _ hx2 => hOutLow x ?_)
        have := S.gLt j hj; omega
      lens := fun j hj => by
        have hMeta := S.metaLt
        rw [hOutLow _ (by omega), (I.cells j hj).2.2.2.2.2.2.2.1]
        have hGX : (X.G j).E = (ch.G j).E := by rw [hXG j hj]
        have hLX : X.toTreeChain.chainLen X.ℓ j = ch.toTreeChain.chainLen ℓ' j := by
          rw [hX]; exact chainLen_congr_lt _ _ _ _ fun _ _ => rfl
        rw [hGX, hLX]
        refine (I.lensLt j hj).congr (fun e he t ht => hOutLow _ ?_)
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using
            Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((I.graphs j hj).2.2.1 e he))
        have := S.lLt j hj; omega
      lastRep := by
        rw [hXE, hHandleD]
        have hXl : (X.lastK, X.lastLSFs) = (ch.lastK, ch.lastLSFs) := by rw [hX]
        rw [hXl]
        exact (hRLLoc _ _ _ _ _ (fun a ha => (hOutLow a (I.term.2 a ha).1).symm)).1 I.term.1
      lastFoot := fun a ha => by
        rw [hXE, hHandleD] at ha
        obtain ⟨h1, h2, _⟩ := I.term.2 a ha
        exact ⟨Or.inl h1, fun j hj => by rw [hHandle j hj]; exact h2 j hj⟩
      oldF := by
        rw [if_neg (by omega), hR4]
        exact ⟨by simp only [List.length_nil]; omega, fun t ht => absurd ht (by simp)⟩
      newF := by
        rw [if_neg (by omega), hR4]
        exact ⟨by simp only [List.length_nil]; omega, fun t ht => absurd ht (by simp)⟩
      frame := fun a ha _ _ _ _ _ _ _ => hOutLow a ha
      frameHeap := fun a h1 _ _ hn => hOut a (by omega) (by omega) }

end MinCostFlow.MinRatio
