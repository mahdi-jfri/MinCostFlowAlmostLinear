module

public import MinCostFlow.MinRatio.WireShiftDeepSelectCost
public import MinCostFlow.MinRatio.SelectMetaTableWrite
public import MinCostFlow.MinRatio.SolverSelectBlocks
import WordRAM.Tactic

/-!
# Deep-shift select-refresh program and stitching helpers (`WireShiftDeepSelectAux`)

Defines the fixed deterministic deep-shift select-refresh wrapper `shiftDeepSelectBody` together
with the prefix-preservation and Word-RAM execution-stitching helpers used by
`shiftDeepSelectBody_runs` (`WireShiftDeepSelect.lean`):

* `shiftDeepSelectBody` & `shiftDeepSelectBody_noRand`: runs `deepProc`, recovers `slot` directly
  from the select metadata table via `((B.fPtr 1 - B.embPtr 0) - eCap) / eCap`, refreshes the
  metadata table (`selTableWrite`), interior blocks (`selectInitInteriorLoop`), terminal `G_d`
  readout (`op 3`) and fill (`selectFillLastLevel`), and suffix potentials/heap
  (`selectRefreshFinalizeBody`).
* `shiftDeep_prefix_agree`: prefix levels `j < i` of `alg2LoopShiftStep` retain `G`, `activeLSF`,
  `activeS`, `activeEmb`, `activeCore`, `g`, `ℓ`, `chainLen`, and `SelectPotInvAt`.
* `slot_div_formula`, `levelCandCount_congr_eq`, `selectRefreshFinalize_congr_mem`.
* `shiftDeepSelectBody_stitch`: stitches the 6 sub-call `Runs` witnesses into a single `Runs`
  witness for `shiftDeepSelectBody` with at most `400` glue steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered IPM.Machine Num DynSpanner.Program SparseCore.Program

/-- Fixed deterministic deep-shift wrapper with in-place select-region refresh.
Arguments (`reg 0..2`): `[root, i, heap]` (matching `shiftDeepChainBodyKFBL`).
Returns the new heap pointer `nextHeap`. -/
def shiftDeepSelectBody
    (deepProc tableWriteProc intLoopProc op3Proc fillLastProc finalizeProc : ℕ) : Stmt :=
  .call 3 deepProc [.reg 0, .reg 1, .reg 2] ;;
  .assign 4 (.load (.reg 0)) ;; -- handle
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;; -- table
  .assign 6 (.load (.bin .add (.reg 4) (.const 11))) ;; -- d
  .assign 7 (.bin .add (.reg 4) (.const 18)) ;; -- levelTable
  .assign 8 (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.const 2)) ;; -- lvlMeta
  .assign 9 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 6))) (.const 2))) ;; -- sb
  .assign 10 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 6))) (.const 3))) ;; -- blkBase
  .assign 11 (.load (.bin .add (.reg 9) (.const 13))) ;; -- metaBase
  .assign 12 (.load (.bin .add (.reg 9) (.const 3))) ;; -- L
  .assign 13 (.bin .add (.reg 6) (.const 1)) ;; -- d + 1
  .assign 14 (.load (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 13))) ;; -- vCap
  .assign 15 (.load (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 2) (.reg 13)))) ;; -- eCap
  .assign 16 (.load (.bin .add (.bin .add (.bin .add (.reg 11) (.const 2))
    (.bin .mul (.const 7) (.reg 13))) (.reg 6))) ;; -- pLast
  .assign 17 (.load (.bin .add (.bin .add (.reg 11) (.const 2)) (.bin .mul (.const 5) (.reg 13)))) ;; -- embPtr 0
  .assign 18 (.load (.bin .add (.bin .add (.bin .add (.reg 11) (.const 2))
    (.bin .mul (.const 6) (.reg 13))) (.const 1))) ;; -- fPtr 1
  .assign 19 (.bin .div (.bin .sub (.bin .sub (.reg 18) (.reg 17)) (.reg 15)) (.reg 15)) ;; -- slot
  .call 20 tableWriteProc
    [.reg 11, .reg 10, .reg 6, .reg 14, .reg 15, .reg 12, .reg 19, .reg 8, .reg 16] ;;
  .call 21 intLoopProc
    [.reg 11, .reg 1, .reg 6, .reg 7, .reg 8, .reg 12, .reg 19, .reg 3] ;;
  .assign 22 (.load (.bin .add (.reg 7) (.bin .sub (.reg 6) (.const 1)))) ;; -- coreHandle (d - 1)
  .assign 23 (.load (.bin .add (.bin .add (.reg 7) (.reg 13)) (.bin .sub (.reg 6) (.const 1)))) ;; -- bran' (d - 1)
  .call 24 op3Proc [.reg 22, .reg 23, .reg 21] ;;
  .assign 25 (.load (.reg 21)) ;; -- srcGd
  .assign 26 (.load (.bin .add (.reg 7) (.reg 6))) ;; -- termHandle'
  .assign 27 (.load (.bin .add (.bin .add (.reg 7) (.reg 13)) (.reg 6))) ;; -- termBran'
  .assign 28 (.load (.bin .add (.bin .add (.bin .add (.reg 11) (.const 2))
    (.bin .mul (.const 4) (.reg 13))) (.bin .sub (.reg 6) (.const 1)))) ;; -- B.lenPtr (d - 1)
  .call 29 fillLastProc
    [.reg 11, .reg 6, .reg 26, .reg 27, .reg 28, .reg 12, .reg 16, .reg 25, .reg 24] ;;
  .call 30 finalizeProc [.reg 9, .reg 11, .reg 1, .reg 6, .reg 12, .reg 29] ;;
  .ret (.reg 30)

theorem shiftDeepSelectBody_noRand (a b c d e f : ℕ) :
    (shiftDeepSelectBody a b c d e f).NoRand := by
  simp [shiftDeepSelectBody, Stmt.NoRand]

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered IPM.Machine Num DynSpanner.Program SparseCore.Program

/-- Under `alg2LoopShiftStep` at level `i < d`, all prefix levels `j < i` retain `G`, `activeLSF`,
`activeS`, `activeEmb`, `activeCore`, `g`, `ℓ`, `chainLen` (for `j ≤ i`), and `SelectPotInvAt`. -/
theorem shiftDeep_prefix_agree {cfg : Alg2Config} (model : Alg2State cfg)
    (i : Fin (cfg.P.d + 1)) (hiLt : i.val < cfg.P.d) :
    let C := model.chain.toTreeChain
    let C' := (alg2LoopShiftStep cfg model i).chain.toTreeChain
    let g := model.chain.g
    let g' := (alg2LoopShiftStep cfg model i).chain.g
    let ℓ := model.chain.ℓ
    let ℓ' := (alg2LoopShiftStep cfg model i).chain.ℓ
    (∀ j ≤ i.val, C'.G j = C.G j) ∧
    (∀ j < i.val, C'.activeLSF j = C.activeLSF j) ∧
    (∀ j < i.val, C'.activeS j = C.activeS j) ∧
    (∀ j < i.val, C'.activeEmb j = C.activeEmb j) ∧
    (∀ j < i.val, C'.activeCore j = C.activeCore j) ∧
    (∀ e, g' e = g e) ∧
    (∀ e, ℓ' e = ℓ e) ∧
    (∀ j ≤ i.val, C'.chainLen ℓ' j = C.chainLen ℓ j) ∧
    (∀ φ, ∀ j < i.val, SelectPotInvAt C g φ j → SelectPotInvAt C' g' φ j) := by
  intro C C' g g' ℓ ℓ'
  obtain ⟨hG', hPre, _, _, _, _, _, _, _, _, _, _, _, hℓEq', hgEq', _, _⟩ :=
    ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P model.chain hiLt
  have hG : ∀ j ≤ i.val, C'.G j = C.G j := fun j hj => hG' j hj
  have hLSF : ∀ j < i.val, C'.activeLSF j = C.activeLSF j := fun j hj => by
    have hjD : j < cfg.P.d := by omega
    have hsc := (hPre j hj).1
    have hbr := (hPre j hj).2.1
    simp only [C', C, alg2LoopShiftStep, ChainState.toTreeChain, TreeChain.activeLSF, hjD, ↓reduceIte]
    rw [hsc, hbr]
  have hS : ∀ j < i.val, C'.activeS j = C.activeS j := fun j hj => by
    have hjD : j < cfg.P.d := by omega
    have hsc := (hPre j hj).1
    have hbr := (hPre j hj).2.1
    simp only [C', C, alg2LoopShiftStep, ChainState.toTreeChain, TreeChain.activeS, hjD, ↓reduceIte]
    rw [hsc, hbr]
  have hEmb : ∀ j < i.val, C'.activeEmb j = C.activeEmb j := fun j hj => by
    have hjD : j < cfg.P.d := by omega
    have hsc := (hPre j hj).1
    have hbr := (hPre j hj).2.1
    simp only [C', C, alg2LoopShiftStep, ChainState.toTreeChain, TreeChain.activeEmb, hjD, ↓reduceIte]
    rw [hsc, hbr]
  have hCore : ∀ j < i.val, C'.activeCore j = C.activeCore j := fun j hj => by
    unfold TreeChain.activeCore
    rw [hG j (le_of_lt hj), hLSF j hj]
  have hgEq : g' = g := hgEq'
  have hℓEq : ℓ' = ℓ := hℓEq'
  have hLen : ∀ j ≤ i.val, C'.chainLen ℓ' j = C.chainLen ℓ j := by
    intro j hj
    induction j with
    | zero => rw [hℓEq]; rfl
    | succ k ih =>
      funext e
      simp only [TreeChain.chainLen]
      rw [hLSF k (by omega), ih (by omega)]
  have hPot : ∀ φ, ∀ j < i.val, SelectPotInvAt C g φ j → SelectPotInvAt C' g' φ j := by
    intro φ j hj hP
    have hgrad : ∀ k ≤ j, potGrad C' g' φ k = potGrad C g φ k := by
      intro k hk
      induction k with
      | zero => funext e; simp [potGrad, hgEq]
      | succ r ih =>
        funext e
        simp only [potGrad]
        rw [ih (by omega), hG r (by omega)]
    unfold SelectPotInvAt at hP ⊢
    rw [hLSF j hj, hgrad j le_rfl]
    exact hP
  exact ⟨hG, hLSF, hS, hEmb, hCore, fun e => congrFun hgEq e, fun e => congrFun hℓEq e, hLen, hPot⟩

/-- Recovers `B.slot` directly from `B.fPtr 1`, `B.embPtr 0`, and `B.eCap` whenever `0 < B.eCap`. -/
theorem slot_div_formula {B : SelectBlocksLoc} (hePos : 0 < B.eCap) :
    ((B.fPtr 1 - B.embPtr 0) - B.eCap) / B.eCap = B.slot := by
  have h1 : B.fPtr 1 = B.embPtr 0 + B.eCap + B.eCap * B.slot := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr
      SelectBlocksLoc.fPtr SelectBlocksLoc.levelSize
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]
    omega
  rw [h1]
  have h2 : B.embPtr 0 + B.eCap + B.eCap * B.slot - B.embPtr 0 - B.eCap = B.eCap * B.slot := by omega
  rw [h2, Nat.mul_div_cancel_left B.slot hePos]

theorem levelCandCount_congr_eq {mem₁ mem₂ : ℕ → ℕ} {loc : SelectHeapLoc} {j : ℕ}
    (h : ∀ a, loc.hb ≤ a → a < loc.endAddr → mem₁ a = mem₂ a) :
    levelCandCount mem₁ loc j = levelCandCount mem₂ loc j := by
  unfold levelCandCount
  congr 1; ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  refine and_congr_right fun he => ?_
  have h1 : loc.hb ≤ loc.posPtr + e ∧ loc.posPtr + e < loc.endAddr := by
    rw [loc.endAddr_eq]; unfold SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega
  have h2 : loc.hb ≤ loc.lvlPtr + e ∧ loc.lvlPtr + e < loc.endAddr := by
    rw [loc.endAddr_eq]; unfold SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr SelectHeapLoc.arrPtr selectHeapSize shHdrSize; omega
  rw [h _ h1.1 h1.2, h _ h2.1 h2.2]

theorem selectRefreshFinalize_congr_mem {mem₁ mem₂ : ℕ → ℕ} {loc : SelectHeapLoc}
    {C : TreeChain} {cur L evalSpace evalCost : ℕ}
    (h : ∀ a, loc.hb ≤ a → a < loc.endAddr → mem₁ a = mem₂ a) :
    selectRefreshFinalizeSpace mem₁ loc C cur L evalSpace =
      selectRefreshFinalizeSpace mem₂ loc C cur L evalSpace ∧
    selectRefreshFinalizeCost mem₁ loc C cur L evalCost =
      selectRefreshFinalizeCost mem₂ loc C cur L evalCost := by
  have hc : ∀ j, levelCandCount mem₁ loc j = levelCandCount mem₂ loc j :=
    fun j => levelCandCount_congr_eq h
  constructor
  · unfold selectRefreshFinalizeSpace selectRebuildSuffixSpace
    congr 1; exact Finset.sum_congr rfl fun j _ => by rw [hc j]
  · unfold selectRefreshFinalizeCost selectRebuildSuffixCost
    have hsum : (Finset.Icc cur C.d).sum (fun j => selectRebuildLevelCost (levelCandCount mem₁ loc j)
          (C.G j).E.card loc.cap loc.Lk evalCost + 40) =
        (Finset.Icc cur C.d).sum (fun j => selectRebuildLevelCost (levelCandCount mem₂ loc j)
          (C.G j).E.card loc.cap loc.Lk evalCost + 40) :=
      Finset.sum_congr rfl fun j _ => by rw [hc j]
    rw [hsum]

private theorem runs_seq_call_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r f : ℕ} {args : List Expr} {s body : Stmt} {st st₁ : State} {vs : List ℕ}
    {o₁ : Outcome} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (hb : p.procs[f]? = some body)
    (hr : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hargs : evalArgs w st args = some vs)
    (hrest : ∃ o st' c, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c ∧ Q o st' ∧ (k + (argsSize args + c₁ + 1) + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  have hcall : Runs w p ω (.call r f args) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (argsSize args + c₁ + 1) :=
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, hr, rfl, rfl, rfl⟩
  rcases hrest with ⟨o, st', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall, hr₂, rfl⟩), hq, by omega⟩

/-- Stitches the six sub-call `Runs` witnesses (`deepProc`, `tableWriteProc`, `intLoopProc`,
`op3Proc`, `fillLastProc`, `finalizeProc`) into a single `Runs` witness for `shiftDeepSelectBody`
with at most `400` glue steps. -/
theorem shiftDeepSelectBody_stitch
    {w deepProc tableWriteProc intLoopProc op3Proc fillLastProc finalizeProc
      root i0 heap pos handle table d sb blkBase metaBase L vCap eCap pLast emb0 f1 slot
      coreLast branLast termH termB prevLenD sc0 sc1 sc2 sc3 sc4
      cDeep cTW cInt cOp3 cLast cFin : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {bDeep bTW bInt b3 bLast bFin : Stmt}
    {oTW o3 : Outcome}
    {st0 stTW st1 st2 st3 st4 : State}
    (hw16 : 16 < 2 ^ w) (hdPos : 0 < d) (heCapPos : 0 < eCap)
    (hrootW : root + 1 < 2 ^ w) (_hiW : i0 < 2 ^ w) (_hheapW : heap < 2 ^ w)
    (hHndW : handle + 18 + 2 * (d + 1) < 2 ^ w) (hTabW : table + 4 * d + 3 < 2 ^ w)
    (hdW : d + 1 < 2 ^ w) (hSbW : sb + 13 < 2 ^ w) (_hBlkW : blkBase < 2 ^ w)
    (hMetaW : metaBase + 2 + 8 * (d + 1) < 2 ^ w) (_hLW : L < 2 ^ w)
    (_hvCapW : vCap < 2 ^ w) (_heCapW : eCap < 2 ^ w) (hpLastW : pLast < 2 ^ w)
    (hEmb0LeF1 : emb0 + eCap ≤ f1) (hF1W : f1 < 2 ^ w) (hSlotW : slot < 2 ^ w)
    (hSlotEq : ((f1 - emb0) - eCap) / eCap = slot)
    (ho3Val : o3.value = sc2)
    (hReadHnd : st0.mem root = handle)
    (hReadTab : st0.mem (root + 1) = table)
    (hReadD : st0.mem (handle + 11) = d)
    (hReadSb : st0.mem (table + 4 * d + 2) = sb)
    (hReadBlk : st0.mem (table + 4 * d + 3) = blkBase)
    (hReadMeta : st0.mem (sb + 13) = metaBase)
    (hReadL : st0.mem (sb + 3) = L)
    (hReadVCap : st0.mem (metaBase + 2 + (d + 1)) = vCap)
    (hReadECap : st0.mem (metaBase + 2 + 2 * (d + 1)) = eCap)
    (hReadPLast : st0.mem (metaBase + 2 + 7 * (d + 1) + d) = pLast)
    (hReadEmb0 : st0.mem (metaBase + 2 + 5 * (d + 1)) = emb0)
    (hReadF1 : st0.mem (metaBase + 2 + 6 * (d + 1) + 1) = f1)
    (hReadCoreLast : st1.mem (handle + 18 + (d - 1)) = coreLast)
    (hReadBranLast : st1.mem (handle + 18 + (d + 1) + (d - 1)) = branLast)
    (hReadTermH : st2.mem (handle + 18 + d) = termH)
    (hReadTermB : st2.mem (handle + 18 + (d + 1) + d) = termB)
    (hReadPrevLenD : st2.mem (metaBase + 2 + 4 * (d + 1) + (d - 1)) = prevLenD)
    (hbDeep : p.procs[deepProc]? = some bDeep)
    (hrDeep : Runs w p ω bDeep (startState [root, i0, heap] mem pos) (.returned sc0) st0 cDeep)
    (hbTW : p.procs[tableWriteProc]? = some bTW)
    (hrTW : Runs w p ω bTW
      (startState [metaBase, blkBase, d, vCap, eCap, L, slot, table + 2 * d + 2, pLast]
        st0.mem st0.pos) oTW stTW cTW)
    (hbInt : p.procs[intLoopProc]? = some bInt)
    (hrInt : Runs w p ω bInt
      (startState [metaBase, i0, d, handle + 18, table + 2 * d + 2, L, slot, sc0]
        stTW.mem stTW.pos) (.returned sc1) st1 cInt)
    (hb3 : p.procs[op3Proc]? = some b3)
    (hr3 : Runs w p ω b3 (startState [coreLast, branLast, sc1] st1.mem st1.pos) o3 st2 cOp3)
    (hbLast : p.procs[fillLastProc]? = some bLast)
    (hrLast : Runs w p ω bLast
      (startState [metaBase, d, termH, termB, prevLenD, L, pLast, st2.mem sc1, sc2]
        st2.mem st2.pos) (.returned sc3) st3 cLast)
    (hbFin : p.procs[finalizeProc]? = some bFin)
    (hrFin : Runs w p ω bFin
      (startState [sb, metaBase, i0, d, L, sc3] st3.mem st3.pos) (.returned sc4) st4 cFin) :
    ∃ outF cBody,
      Runs w p ω
        (shiftDeepSelectBody deepProc tableWriteProc intLoopProc op3Proc fillLastProc finalizeProc)
        (startState [root, i0, heap] mem pos) (.returned sc4) outF cBody ∧
      outF.mem = st4.mem ∧
      cBody ≤ cDeep + cTW + cInt + cOp3 + cLast + cFin + 400 := by
  let Q_goal (o : Outcome) (out : State) : Prop := o = .returned sc4 ∧ out.mem = st4.mem
  suffices h : ∃ o out c,
      Runs w p ω
        (shiftDeepSelectBody deepProc tableWriteProc intLoopProc op3Proc fillLastProc finalizeProc)
        (startState [root, i0, heap] mem pos) o out c ∧ Q_goal o out ∧
        c ≤ cDeep + cTW + cInt + cOp3 + cLast + cFin + 400 by
    obtain ⟨_, out, c, hr, ⟨rfl, hm⟩, hc⟩ := h; exact ⟨out, c, hr, hm, hc⟩
  refine runs_start_le (T := cDeep + cTW + cInt + cOp3 + cLast + cFin + 400) (Q := Q_goal) ?_
  dsimp only [startState]
  unfold shiftDeepSelectBody
  have h1 : Runs w p ω bDeep (startState [root, i0, heap] mem pos) (.returned sc0) st0 cDeep := hrDeep
  refine runs_seq_call_runs (hb := hbDeep) (hr := h1) (vs := [root, i0, heap])
    (by eval_expr) ?_
  refine runs_seq_assign_flat (v := handle) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := table) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := d) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := handle + 18) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := table + 2 * d + 2) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := sb) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := blkBase) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := metaBase) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := L) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := d + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := vCap) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := eCap) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := pLast) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := emb0) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := f1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := slot) (by
    have hsub1 : f1 - emb0 < 2 ^ w := by omega
    have hsub2 : (f1 - emb0) - eCap < 2 ^ w := by omega
    simp [Expr.eval, BinOp.eval, hsub1, hsub2, hSlotEq, hSlotW]) ?_
  refine runs_seq_call_runs (hb := hbTW) (hr := hrTW)
    (vs := [metaBase, blkBase, d, vCap, eCap, L, slot, table + 2 * d + 2, pLast])
    (by eval_expr) ?_
  refine runs_seq_call_runs (hb := hbInt) (hr := hrInt)
    (vs := [metaBase, i0, d, handle + 18, table + 2 * d + 2, L, slot, sc0])
    (by eval_expr) ?_
  refine runs_seq_assign_flat (v := coreLast) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := branLast) (by eval_expr) ?_
  refine runs_seq_call_runs (hb := hb3) (hr := hr3)
    (vs := [coreLast, branLast, sc1]) (by eval_expr) ?_
  rw [ho3Val]
  refine runs_seq_assign_flat (v := st2.mem sc1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := termH) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := termB) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := prevLenD) (by eval_expr) ?_
  refine runs_seq_call_runs (hb := hbLast) (hr := hrLast)
    (vs := [metaBase, d, termH, termB, prevLenD, L, pLast, st2.mem sc1, sc2])
    (by eval_expr) ?_
  refine runs_seq_call_runs (hb := hbFin) (hr := hrFin)
    (vs := [sb, metaBase, i0, d, L, sc3]) (by eval_expr) ?_
  exact WordRAM.runs_ret_le (v := sc4) (by eval_expr) ⟨rfl, rfl⟩
    (by simp only [argsSize, Expr.size]; omega)

/-- Preserves `OffTreeRecInv` and `OffTreeRecBound` across any memory transformation that leaves
every non-core solver-owned cell (`tok.tag a ≠ 0` and `∀ j < d, tok.tag a ≠ 21 + j`) unchanged. -/
theorem offTreeRec_preserve_nonCore
    {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B_t : ℤ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hRep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₁)
    (hInv : OffTreeRecInv model L mem₁ tok.edgeRecords B_t)
    (hBd : OffTreeRecBound model L mem₁ tok.edgeRecords B_t)
    (hAg : ∀ a, tok.tag a ≠ 0 → (∀ j < cfg.P.d, tok.tag a ≠ 21 + j) → mem₂ a = mem₁ a) :
    OffTreeRecInv model L mem₂ tok.edgeRecords B_t ∧
    OffTreeRecBound model L mem₂ tok.edgeRecords B_t := by
  have hag1318 : ∀ a, (tok.tag a = 13 ∨ tok.tag a = 18) → mem₂ a = mem₁ a := fun a ha =>
    hAg a (by rcases ha with h | h <;> omega) (fun j _ => by rcases ha with h | h <;> omega)
  exact ⟨offTreeRecInv_of_agree hRep hInv hag1318, offTreeRecBound_of_agree hRep hBd hag1318⟩

/-- Equivalence from `SolverSelectBlocksInv` (`SolverSelectBlocks.lean`) to `SelectRegionAt` plus
disjointness of `[sg.loc.hb, B.endAddr)` from `foot`. -/
theorem SelectRegionAt.of_solverSelectBlocksInv
    {cfg : Alg2Config} {G : MGraph} {L P m vCap eCap pLast : ℕ} {B : SelectBlocksLoc}
    {model : Alg2State cfg} {foot : ℕ → Prop} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tok : SolverToken cfg L Rcore} {sg : SelectGhost} {mem : ℕ → ℕ}
    (h : SolverSelectBlocksInv G L P m vCap eCap pLast B model foot tok sg mem) :
    SelectRegionAt G P m vCap eCap pLast sg.loc.hb sg.loc.metaPtr B model tok sg mem ∧
    (∀ a, sg.loc.hb ≤ a → a < B.endAddr → ¬ foot a) := by
  obtain ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown, hoff, hhb, hblk, hmloc, hclen,
    htab, hblocks, hpot, hmatch, hmod⟩ := h
  refine ⟨⟨hreg, hcap, hBd, hBv, hBe, hBLk, hown, hhb, hblk, hmloc,
    hmloc ▸ htab, hblocks, hmatch, hpot, hclen, hmod⟩, fun a h1 h2 => hoff a (by rw [hown]; exact ⟨h1, h2⟩)⟩

/-- Equivalence from `SelectRegionAt` plus disjointness of `[sb, B.endAddr)` from `foot` to
`SolverSelectBlocksInv` (`SolverSelectBlocks.lean`). -/
theorem SelectRegionAt.to_solverSelectBlocksInv
    {cfg : Alg2Config} {G : MGraph} {L P m vCap eCap pLast sb metaBase : ℕ} {B : SelectBlocksLoc}
    {model : Alg2State cfg} {foot : ℕ → Prop} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {tok : SolverToken cfg L Rcore} {sg : SelectGhost} {mem : ℕ → ℕ}
    (h : SelectRegionAt G P m vCap eCap pLast sb metaBase B model tok sg mem)
    (hdisj : ∀ a, sb ≤ a → a < B.endAddr → ¬ foot a) :
    SolverSelectBlocksInv G L P m vCap eCap pLast B model foot tok sg mem := by
  obtain ⟨hreg, hcap, hBd, hBv, hBe, hBLk, hown, hhb, hblk, hmloc,
    htab, hblocks, hmatch, hpot, hclen, hmod⟩ := h
  have hsb : sb = sg.loc.hb := hreg.1.symm
  have hmeta : metaBase = sg.loc.metaPtr := hreg.2.2.1
  subst hsb hmeta
  exact ⟨hBd, hBv, hBe, hBLk, hcap, hreg, hown,
    fun a ha => by rw [hown] at ha; exact hdisj a ha.1 ha.2,
    hhb, hblk, hmloc, hclen, hmloc.symm ▸ htab, hblocks, hpot, hmatch, hmod⟩

end MinCostFlow.MinRatio
