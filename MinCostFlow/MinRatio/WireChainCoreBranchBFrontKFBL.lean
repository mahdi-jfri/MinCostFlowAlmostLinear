module

public import MinCostFlow.MinRatio.WireChainCoreBranchBLoopKFBL
import WordRAM.Tactic

/-!
# The start of the Branch B loop under `KFBL` (`WireChainCoreBranchBFrontKFBL`)

Before the plain-step loop of Branch B (`wireBranchBLoopKFBL`) runs, the core sets the loop
registers for level `0` and copies the level-`0` batch from the caller's buffer `uIntBuf` to the
fresh heap (`wireBranchBCopyBatch0Stmt`). After the copy, the batch of every level lies in the
region of the loop, so the finished slots can use one set of good words for all levels.

`wireBranchBFrontKFBL_runs` gives the run of these steps and the loop invariant
`BranchBLoopInvKFBL` at level `0`, so that `wireBranchBLoopKFBL_runs` applies right after it.
No level is finished yet, so the slot part of the invariant holds by `branchBDoneSlots_zero`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The loop registers for level `0` (`reg 96 := 0`, the flag `reg 97 := 0`, the end register
`reg 99 := d`, the batch of level `0` and its edit list), and the copy of the batch to the fresh
heap. -/
@[expose] def wireBranchBFrontKFBL (copyProc : ℕ) : Stmt :=
  .assign 96 (.const 0) ;;
  .assign 97 (.const 0) ;;
  .assign 99 (.reg 75) ;;
  .assign 10 (.reg 87) ;;
  .assign 11 (.bin .sub (.bin .sub (.reg 88) (.reg 75)) (.reg 87)) ;;
  .assign 12 (.reg 88) ;;
  .assign 13 (.reg 89) ;;
  wireBranchBCopyBatch0Stmt copyProc

theorem wireBranchBFrontKFBL_noRand (copyProc : ℕ) :
    (wireBranchBFrontKFBL copyProc).NoRand := by
  simp [wireBranchBFrontKFBL, wireBranchBCopyBatch0Stmt_noRand, Stmt.NoRand]

private theorem runs_assign_seq_front {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {st sOut : State} {v c : ℕ} (he : e.eval w st = some v)
    (hr : Runs w p ω s { st with regs := Function.update st.regs r v } .normal sOut c) :
    Runs w p ω (.assign r e ;; s) st .normal sOut (e.size + 1 + c + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c, runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr,
    rfl⟩)

set_option maxHeartbeats 1600000 in
/-- The run of `wireBranchBFrontKFBL` at the entry of Branch B, with the heap pointer
`heap = reg 4` and the level-`0` batch at `uIntBuf` in `bW = editsPtr - d - uIntBuf` words.
Afterwards the batch lies at `heap`, the heap pointer is `heap + bW`, no word below `heap`
changes, and the loop invariant holds at level `0` for the start state `ch0` of the model, with
`curG` the graph of level `0` after the batch. Every fact of the invariant lies below `selBase`,
so it moves from the entry memory by the frame of the copy. -/
theorem wireBranchBFrontKFBL_runs
    {w L P depth vCap eCap capExp copyProc N0 heap uIntBuf editsPtr editWords : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program} {ω : ℕ → Bool} {reembFn : ToolReembFn cfg.T}
    {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ} {ℓ' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ}
    {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ} {curG : MGraph} {U : List Update}
    {edits : List OrdEdit} {tok : ℕ → Rcore.τ} {levelU levelUS : ℕ → List Update}
    {D : ℕ → LevelDiffLists} {st : State}
    (hLoc : Rcore.Local) (hRLLoc : RL.Local)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hSlotLe : A.selBase + 1 + 12 * cfg.P.d ≤ A.heapFloor)
    (hw : 6 < 2 ^ w) (hCopy : p.procs[copyProc]? = some wireRawCopyBody)
    (hRegs : st.regs 4 = heap ∧ st.regs 72 = A.selBase ∧ st.regs 73 = A.handle ∧
      st.regs 74 = A.table ∧ st.regs 75 = cfg.P.d ∧ st.regs 76 = cfg.P.k ∧
      st.regs 77 = A.handleBase ∧ st.regs 78 = A.branchBase ∧ st.regs 82 = A.lvlMTable ∧
      st.regs 83 = A.levelMeta ∧ st.regs 85 = A.ucBase ∧ st.regs 86 = A.rcBase ∧
      st.regs 87 = uIntBuf ∧ st.regs 88 = editsPtr ∧ st.regs 89 = editWords ∧ st.regs 94 = L ∧
      st.regs 95 = P ∧ st.regs 98 = depth)
    (hFloor : A.heapFloor ≤ heap)
    (hdrCell : st.mem (A.lvlMTable - 1) = N0)
    (hN0Word : 0 < A.lvlMTable ∧
      (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) (A.lvlMTable - 1)) ∧
      (∀ j < cfg.P.d,
        (A.lvlMTable - 1 < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ A.lvlMTable - 1) ∧
        (A.lvlMTable - 1 < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ A.lvlMTable - 1) ∧
        A.lvlMTable - 1 ≠ A.ucBase + j ∧ A.lvlMTable - 1 ≠ A.rcBase + j))
    (hCells : ∀ j < cfg.P.d,
      st.mem (A.table + j) = intRebuildThreshold cfg.P N0 j ∧
      st.mem (A.lvlMTable + j) = ch0.lvlM j ∧
      st.mem (A.handleBase + j) = A.coreH j ∧
      st.mem (A.branchBase + j) = ch0.bran j ∧
      ch0.bran j < cfg.P.k ∧ A.coreH j < 2 ^ w ∧
      st.mem (A.levelMeta + cfg.P.d + j) = A.gPtr0 j ∧
      st.mem (A.levelMeta + j) = A.lPtr0 j ∧
      st.mem (A.ucBase + j) = ch0.updCount j ∧
      st.mem (A.rcBase + j) = ch0.rebuildCount j)
    (hTermCells : st.mem (A.handleBase + cfg.P.d) = A.coreH cfg.P.d ∧
      st.mem (A.branchBase + cfg.P.d) = ch0.lastBran)
    (hReps : ∀ j < cfg.P.d,
      Rcore.rep (A.coreH j) (chainLevelOrdAbs ch0 j) (tok j) st.mem ∧
      (∀ a, Rcore.foot (A.coreH j) (tok j) a → a < A.selBase))
    (hDisj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ →
      ∀ a, Rcore.foot (A.coreH j₁) (tok j₁) a → ¬ Rcore.foot (A.coreH j₂) (tok j₂) a)
    (hStatic : BranchBCoresDisjStatic (cfg := cfg) (Rcore := Rcore) L A.handle A.table
      A.handleBase A.branchBase A.lvlMTable A.levelMeta A.rcBase A.ucBase (fun _ => vCap)
      (fun _ => eCap) A.gPtr0 A.lPtr0 A.coreH tok)
    (hGraphs : ∀ j < cfg.P.d, DynGraphAt st.mem (A.gPtr0 j) vCap eCap (ch0.G j))
    (hCurGCap : ∀ e ∈ curG.E, e < eCap)
    (hLen0 : 0 < cfg.P.d →
      EdgeValuesAt st.mem (A.lPtr0 0) 4 L P curG.E
        (({ ch0.toTreeChain with G := fun j => if j = 0 then curG else ch0.G j } :
          TreeChain).chainLen ℓ' 0))
    (hLenGt : ∀ j, 0 < j → j < cfg.P.d →
      EdgeValuesAt st.mem (A.lPtr0 j) 4 L P (ch0.G j).E (origLen j))
    (hTerm : RL.rep (A.coreH cfg.P.d) (ch0.lastK, ch0.lastLSFs) termTok st.mem ∧
      (∀ a, RL.foot (A.coreH cfg.P.d) termTok a →
        a < A.selBase ∧
        (∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) a) ∧
        (∀ j < cfg.P.d, (a < A.gPtr0 j ∨ A.gPtr0 j + dynGraphSize vCap eCap ≤ a) ∧
          (a < A.lPtr0 j ∨ A.lPtr0 j + eCap * L ≤ a)) ∧
        (a < A.handleBase ∨ A.handleBase + cfg.P.d < a) ∧
        (a < A.branchBase ∨ A.branchBase + cfg.P.d < a) ∧
        (a < A.levelMeta ∨ A.levelMeta + 2 * cfg.P.d ≤ a) ∧
        (a < A.ucBase ∨ A.ucBase + cfg.P.d ≤ a) ∧
        (a < A.rcBase ∨ A.rcBase + cfg.P.d < a)))
    (hBatch : SmallBatchAt st.mem uIntBuf (ch0.G 0) U (editsPtr - cfg.P.d - uIntBuf) ∧
      (∀ t < editsPtr - cfg.P.d - uIntBuf, st.mem (uIntBuf + t) < 2 ^ w) ∧
      uIntBuf + cfg.P.d ≤ editsPtr ∧ editsPtr + editWords ≤ heap)
    (hEdgeOnly : ∀ u ∈ U, IsEdgeUpdate u)
    (hEdits : OrdEditsAt st.mem editsPtr edits editWords ∧
      (∀ t < editWords, st.mem (editsPtr + t) < 2 ^ w))
    (hOrd0 : applyOrdEdits (ch0.levelOrd 0) edits =
      chainLevelOrd cfg.T (fun j => if j = 0 then curG else ch0.G j) ch0.scState ch0.bran 0)
    (hValid : OrdEditsValidFor vCap eCap (ch0.levelOrd 0) edits)
    (hFor : OrdEditsForBatch (ch0.G 0) U edits)
    (hSizes : editsPtr - cfg.P.d - uIntBuf ≤ BWc 0 ∧ editWords ≤ EWc 0 ∧ U.length ≤ ULc 0)
    (hLU : levelU 0 = U) (hN : ch0.N₀ = N0)
    (hz : ZeroFrom st.mem heap)
    (hRoom : heap + (editsPtr - cfg.P.d - uIntBuf) < 2 ^ w) :
    ∃ (s : State) (cost : ℕ),
      Runs w p ω (wireBranchBFrontKFBL copyProc) st .normal s cost ∧
      cost ≤ 20 * (editsPtr - cfg.P.d - uIntBuf) + 60 ∧
      s.regs 4 = heap + (editsPtr - cfg.P.d - uIntBuf) ∧
      (∀ a < heap, s.mem a = st.mem a) ∧
      (∀ r, r ≠ 4 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 30 → r ≠ 96 → r ≠ 97 → r ≠ 99 →
        s.regs r = st.regs r) ∧
      BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
        (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
        EWc ULc ch0 termTok 0 ch0 curG U edits (ch0.levelOrd 0) s tok heap
        (editsPtr - cfg.P.d - uIntBuf) editsPtr editWords levelU levelUS D := by
  obtain ⟨hr4, hr72, hr73, hr74, hr75, hr76, hr77, hr78, hr82, hr83, hr85, hr86, hr87, hr88,
    hr89, hr94, hr95, hr98⟩ := hRegs
  obtain ⟨hSB, hBW, hUE, hEE⟩ := hBatch
  have hSelHeap : A.selBase ≤ heap := by omega
  have hdW : cfg.P.d < 2 ^ w := by
    have := S.hbLt; omega
  -- the seven register assignments
  let r7 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update st.regs 96 0) 97 0) 99 cfg.P.d) 10 uIntBuf) 11
      (editsPtr - cfg.P.d - uIntBuf)) 12 editsPtr) 13 editWords
  let s7 : State := { st with regs := r7 }
  have h7 : ∀ r, r ≠ 96 → r ≠ 97 → r ≠ 99 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 →
      s7.regs r = st.regs r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    simp [s7, r7, Function.update_of_ne, h1, h2, h3, h4, h5, h6, h7]
  obtain ⟨s, cC, rC, hs10, hs4, hsR, hSB', hW', hfr, hcC⟩ :=
    wireBranchBCopyBatch0Stmt_runs (s := s7) (heap := heap) hw hCopy
      (by rw [h7 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]; exact hr4)
      (by simp [s7, r7]) (by simp [s7, r7]) hSB hBW (by omega) hRoom
  have hw0 : 0 < 2 ^ w := by omega
  have rAll : Runs w p ω (wireBranchBFrontKFBL copyProc) st .normal s
      ((Expr.const 0).size + 1 + ((Expr.const 0).size + 1 + ((Expr.reg 75).size + 1 +
        ((Expr.reg 87).size + 1 +
        ((Expr.bin .sub (.bin .sub (.reg 88) (.reg 75)) (.reg 87)).size + 1 +
        ((Expr.reg 88).size + 1 + ((Expr.reg 89).size + 1 + cC + 1) + 1) + 1) + 1) + 1) + 1) +
        1) :=
    runs_assign_seq_front (v := 0) (by simp [Expr.eval, hw0]) <|
    runs_assign_seq_front (v := 0) (by simp [Expr.eval, hw0]) <|
    runs_assign_seq_front (v := cfg.P.d) (by simp [Expr.eval, hr75]) <|
    runs_assign_seq_front (v := uIntBuf) (by simp [Expr.eval, hr87]) <|
    runs_assign_seq_front (v := editsPtr - cfg.P.d - uIntBuf) (by
      simp [Expr.eval, BinOp.eval, hr88, hr75, hr87, show editsPtr - cfg.P.d < 2 ^ w by omega,
        show editsPtr - cfg.P.d - uIntBuf < 2 ^ w by omega]) <|
    runs_assign_seq_front (v := editsPtr) (by simp [Expr.eval, hr88]) <|
    runs_assign_seq_front (v := editWords) (by simp [Expr.eval, hr89]) rC
  have hAg : ∀ a < heap, s.mem a = st.mem a := fun a ha => hfr a (Or.inl ha)
  have hsr : ∀ r, r ≠ 4 → r ≠ 10 → r ≠ 30 → r ≠ 96 → r ≠ 97 → r ≠ 99 → r ≠ 11 → r ≠ 12 →
      r ≠ 13 → s.regs r = st.regs r := fun r a b c d e f g h i =>
    (hsR r a b c).trans (h7 r d e f b g h i)
  refine ⟨s, _, rAll, by simp only [Expr.size]; omega, hs4, hAg,
    fun r a b c d e f g h i => hsr r a b f g h i c d e, ?_⟩
  have hu : ∀ r, r ≠ 4 → r ≠ 10 → r ≠ 30 → s.regs r = s7.regs r := hsR
  have hu' : ∀ r, 70 ≤ r → r ≠ 96 → r ≠ 97 → r ≠ 99 → s.regs r = st.regs r :=
    fun r hr a b c => hsr r (by omega) (by omega) (by omega) a b c (by omega) (by omega)
      (by omega)
  have hTabLt := S.tableLt
  have hLvlMLt := S.lvlMLt
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hUCLt := S.ucLt
  have hRCLt := S.rcLt
  have hHLt := S.handleLt
  refine
    { idxLe := Nat.zero_le _
      regs := ⟨by omega, hs10,
        by rw [hu 11 (by decide) (by decide) (by decide)]; simp [s7, r7],
        by rw [hu 12 (by decide) (by decide) (by decide)]; simp [s7, r7],
        by rw [hu 13 (by decide) (by decide) (by decide)]; simp [s7, r7],
        (hu' 72 (by decide) (by decide) (by decide) (by decide)).trans hr72,
        (hu' 73 (by decide) (by decide) (by decide) (by decide)).trans hr73,
        (hu' 74 (by decide) (by decide) (by decide) (by decide)).trans hr74,
        (hu' 75 (by decide) (by decide) (by decide) (by decide)).trans hr75,
        (hu' 76 (by decide) (by decide) (by decide) (by decide)).trans hr76,
        (hu' 77 (by decide) (by decide) (by decide) (by decide)).trans hr77,
        (hu' 78 (by decide) (by decide) (by decide) (by decide)).trans hr78,
        (hu' 82 (by decide) (by decide) (by decide) (by decide)).trans hr82,
        (hu' 83 (by decide) (by decide) (by decide) (by decide)).trans hr83,
        (hu' 85 (by decide) (by decide) (by decide) (by decide)).trans hr85,
        (hu' 86 (by decide) (by decide) (by decide) (by decide)).trans hr86,
        (hu' 94 (by decide) (by decide) (by decide) (by decide)).trans hr94,
        (hu' 95 (by decide) (by decide) (by decide) (by decide)).trans hr95,
        by rw [hu 96 (by decide) (by decide) (by decide)]; simp [s7, r7],
        by rw [hu 97 (by decide) (by decide) (by decide)]; simp [s7, r7],
        (hu' 98 (by decide) (by decide) (by decide) (by decide)).trans hr98,
        by rw [hu 99 (by decide) (by decide) (by decide)]; simp [s7, r7]⟩
      hdrCell := (hAg _ (by omega)).trans hdrCell
      n0Word := hN0Word
      cells := fun j hj => ?_
      termCells := ⟨(hAg _ (by omega)).trans hTermCells.1, (hAg _ (by omega)).trans hTermCells.2⟩
      reps := fun j hj => ?_
      footLoc := fun j hj a ha => Or.inl ((hReps j hj).2 a ha)
      footOld := fun j _ hj a ha => (hReps j hj).2 a ha
      disj := hDisj
      static := hStatic
      graphs := fun j hj => dynGraphAt_of_agree (hGraphs j hj) (fun x _ h2 =>
        hAg x (by have := S.gLt j hj; omega))
      lensLt := fun j hj => absurd hj (Nat.not_lt_zero _)
      lensEq := fun h => (hLen0 h).congr (fun e he t ht => by
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hCurGCap e he))
        have := S.lLt 0 h
        exact hAg _ (by omega))
      lensGt := fun j hj1 hj2 => (hLenGt j hj1 hj2).congr (fun e he t ht => by
        have heL : e * L + L ≤ eCap * L := by
          simpa [Nat.succ_mul] using
            Nat.mul_le_mul_right L (Nat.succ_le_of_lt ((hGraphs j hj2).2.2.1 e he))
        have := S.lLt j hj2
        exact hAg _ (by omega))
      term := ⟨(hRLLoc _ _ _ _ _ (fun a ha =>
        (hAg a (by have := (hTerm.2 a ha).1; omega)).symm)).1 hTerm.1, hTerm.2⟩
      batchLen := hSB'.1.2.1
      batch := fun _ => ⟨hSB', decodeBatch_eq_of_noSplit hSB'.1 (fun u hu => by
          have h := hEdgeOnly u hu
          cases u with
          | split _ _ _ _ => exact h.elim
          | _ => trivial),
        fun t ht => ⟨hW' t ht, fun j hj hf => by have := (hReps j hj).2 _ hf; omega⟩, hFloor,
        by omega, ordEditsAt_of_agree hEdits.1 (fun x _ h2 => hAg x (by omega)),
        fun t ht => by rw [hAg _ (by omega)]; exact hEdits.2 t ht, by omega, hOrd0, hValid,
        hFor⟩
      sizes := hSizes
      slots := branchBDoneSlots_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _
      slotModel := fun j hj => absurd hj (Nat.not_lt_zero _)
      curULink := hLU
      modelFrame := ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, hN, rfl, rfl⟩
      zero := fun a ha => by
        rw [hfr a (Or.inr (by omega))]; exact hz a (by omega)
      oldOrdEq := rfl
      updFrame := fun _ _ => rfl }
  -- cells
  · obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hCells j hj
    exact ⟨(hAg _ (by omega)).trans c1, (hAg _ (by omega)).trans c2, (hAg _ (by omega)).trans c3,
      (hAg _ (by omega)).trans c4, c5, c6, (hAg _ (by omega)).trans c7,
      (hAg _ (by omega)).trans c8, (hAg _ (by omega)).trans c9, (hAg _ (by omega)).trans c10⟩
  -- reps
  · have e : (if j = 0 then (⟨ch0.scState j, ch0.G j, ch0.levelOrd 0, ch0.updCount j⟩ :
        SparseCoreOrdAbs cfg.T) else chainLevelOrdAbs ch0 j) = chainLevelOrdAbs ch0 j := by
      split_ifs with h0
      · subst h0; rfl
      · rfl
    rw [e]
    refine ⟨(hLoc _ _ _ _ _ (fun a ha => (hAg a (by have := (hReps j hj).2 a ha; omega)).symm)).1
      (hReps j hj).1, fun a ha => ?_⟩
    have := (hReps j hj).2 a ha
    omega

end MinCostFlow.MinRatio
