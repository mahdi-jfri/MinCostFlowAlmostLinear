module

public import MinCostFlow.MinRatio.SelectUpdateG0
public import MinCostFlow.MinRatio.SelectUpdateFPhiLenLoop
public import MinCostFlow.MinRatio.SelectUpdateEmbLoop
public import MinCostFlow.MinRatio.SelectUpdateSuffixBlocks
public import MinCostFlow.MinRatio.SelectUpdateHeapPhase
public import MinCostFlow.MinRatio.WireShiftDeepSelectAux
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Post-core select-update program and stitching helpers (`SelectUpdatePostCoreAux`)

Defines the fixed 3-argument post-core select-maintenance wrapper `selectUpdatePostCoreBody`
(`[root, selOutBase, scratch]`) together with its raw space/cost formulas and Word-RAM execution
stitching theorem `selectUpdatePostCoreBody_stitch`.

`selectUpdatePostCoreBody` loads all solver and select-region layout pointers from `root`,
recovers `slot` from the metadata table, computes `limit := min firstReb d`, and executes the
six phases in order:
1. `tableWriteProc` (`selTableWriteBody`)
2. `g0Proc` (`selUpdateG0Body`)
3. `fPhiLenLoopProc` (`selectUpdateFPhiLenLoopBody`)
4. `embLoopProc` (`selectUpdateEmbLoopBody`)
5. `sufBlocksProc` (`selectUpdateSuffixBlocksBody`)
6. `heapPhaseProc` (`selectUpdateHeapPhaseBody`)
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

/-- Post-core select-maintenance body executed immediately after `ordChainUpdateCoreBody`.
Arguments (`reg 0..2`): `[root, selOutBase, scratch]`. Returns the new heap pointer `sc5`. -/
def selectUpdatePostCoreBody
    (tableWriteProc g0Proc fPhiLenLoopProc embLoopProc sufBlocksProc heapPhaseProc : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;; -- handle
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;; -- table
  .assign 5 (.load (.bin .add (.reg 0) (.const 6))) ;; -- slots
  .assign 6 (.load (.bin .add (.reg 0) (.const 10))) ;; -- edgeRecords
  .assign 7 (.load (.reg 3)) ;; -- treeHeap
  .assign 8 (.load (.bin .add (.reg 3) (.const 11))) ;; -- d
  .assign 9 (.bin .add (.reg 3) (.const 18)) ;; -- levelTable
  .assign 10 (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 8))) (.const 2)) ;; -- lvlMeta
  .assign 11 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 8))) (.const 2))) ;; -- sb
  .assign 12 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 8))) (.const 3))) ;; -- blkBase
  .assign 13 (.load (.bin .add (.reg 11) (.const 13))) ;; -- metaBase
  .assign 14 (.load (.bin .add (.reg 11) (.const 3))) ;; -- L
  .assign 15 (.bin .add (.reg 8) (.const 1)) ;; -- d + 1
  .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 2)) (.reg 15))) ;; -- vCap
  .assign 17 (.load (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 2) (.reg 15)))) ;; -- eCap
  .assign 18 (.load (.bin .add (.bin .add (.bin .add (.reg 13) (.const 2))
    (.bin .mul (.const 7) (.reg 15))) (.reg 8))) ;; -- pLast
  .assign 19 (.load (.bin .add (.bin .add (.reg 13) (.const 2)) (.bin .mul (.const 5) (.reg 15)))) ;; -- embPtr 0
  .assign 20 (.load (.bin .add (.bin .add (.bin .add (.reg 13) (.const 2))
    (.bin .mul (.const 6) (.reg 15))) (.const 1))) ;; -- fPtr 1
  .assign 21 (.bin .div (.bin .sub (.bin .sub (.reg 20) (.reg 19)) (.reg 17)) (.reg 17)) ;; -- slot
  .assign 22 (.load (.reg 13)) ;; -- g0Ptr
  .assign 23 (.load (.bin .add (.reg 10) (.reg 8))) ;; -- solverLevelG 0
  .assign 24 (.load (.bin .add (.reg 9) (.reg 8))) ;; -- termHandle
  .assign 25 (.load (.bin .add (.bin .add (.reg 9) (.reg 15)) (.reg 8))) ;; -- termBran
  .assign 26 (.load (.reg 1)) ;; -- firstReb
  .assign 27 (.bin .add (.reg 1) (.const 1)) ;; -- slot0
  .cond (.bin .lt (.reg 26) (.reg 8))
    (.assign 28 (.reg 26))
    (.assign 28 (.reg 8)) ;; -- limit = min firstReb d
  .call 29 tableWriteProc
    [.reg 13, .reg 12, .reg 8, .reg 16, .reg 17, .reg 14, .reg 21, .reg 10, .reg 18] ;;
  .call 30 g0Proc
    [.reg 26, .reg 5, .reg 6, .reg 7, .reg 22, .reg 23, .reg 16, .reg 27, .reg 14, .reg 2] ;;
  .call 31 fPhiLenLoopProc
    [.reg 13, .const 0, .reg 28, .reg 10, .reg 1, .reg 8, .reg 14, .reg 30] ;;
  .call 32 embLoopProc
    [.reg 13, .const 0, .reg 28, .reg 9, .reg 1, .reg 8, .reg 21, .reg 31] ;;
  .call 33 sufBlocksProc
    [.reg 13, .reg 26, .reg 8, .reg 9, .reg 10, .reg 24, .reg 25, .reg 14, .reg 21, .reg 18, .reg 32] ;;
  .call 34 heapPhaseProc
    [.reg 11, .reg 13, .reg 26, .reg 8, .reg 1, .reg 33] ;;
  .ret (.reg 34)

theorem selectUpdatePostCoreBody_noRand (a b c d e f : ℕ) :
    (selectUpdatePostCoreBody a b c d e f).NoRand := by
  simp [selectUpdatePostCoreBody, Stmt.NoRand]

/-- Raw scratch space of `selectUpdatePostCoreBody` (sum of Phases 2, 3a-1, 3a-2, 3b, 4). -/
noncomputable def selectUpdatePostCoreRawSpace {T : SparseCoreRestartTool} {P : ChainParams}
    (mem : ℕ → ℕ) (loc : SelectHeapLoc) (C' : ChainState T P)
    (diffLists : ℕ → LevelDiffLists) (stLw : ℕ → ℕ)
    (firstReb L capExp evalSpace : ℕ) : ℕ :=
  let lim := min firstReb P.d
  selUpdateG0Space firstReb (diffLists 0).uG.length +
  selectUpdateFPhiLenLoopSpace diffLists stLw 0 lim L +
  selectUpdateEmbLoopSpace diffLists 0 lim +
  selectUpdateSuffixBlocksSpace C' firstReb L capExp +
  selectUpdateHeapPhaseSpace mem loc C'.toTreeChain diffLists firstReb evalSpace

/-- Raw step cost of `selectUpdatePostCoreBody` (sum of Phases 1..4 plus glue overhead). -/
noncomputable def selectUpdatePostCoreRawCost {T : SparseCoreRestartTool} {P : ChainParams}
    (mem : ℕ → ℕ) (loc : SelectHeapLoc) (oldCh newCh : ChainState T P)
    (levelU : ℕ → List Update) (diffLists : ℕ → LevelDiffLists) (uWords stLw : ℕ → ℕ)
    (readoutCost firstReb L capExp slot evalCost : ℕ) : ℕ :=
  let lim := min firstReb P.d
  let oldF := fun j => (oldCh.toTreeChain.activeLSF j).F.F
  let oldGd := oldCh.G P.d
  (240 * P.d + 840) +
  selUpdateG0Cost firstReb (newCh.G 0).m (diffLists 0).uG.length L +
  selectUpdateFPhiLenLoopCost levelU uWords diffLists stLw 0 lim L +
  selectUpdateEmbLoopCost readoutCost diffLists 0 lim slot +
  selectUpdateSuffixBlocksCost oldF oldGd newCh readoutCost firstReb L capExp slot +
  selectUpdateHeapPhaseCost mem loc newCh.toTreeChain diffLists firstReb evalCost + 600

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

private lemma runs_seq_cond_min_le {w rA rB rOut k T : ℕ} {p : Program} {ω : ℕ → Bool}
    {rest : Stmt} {st : State} {Q : Outcome → State → Prop}
    {a b : ℕ} (ha : st.regs rA = a) (hb : st.regs rB = b) (hw1 : 1 < 2 ^ w)
    (hrest : ∃ o out c, Runs w p ω rest ⟨st.mem, Function.update st.regs rOut (min a b), st.pos⟩ o out c ∧
      Q o out ∧ (k + 7) + c ≤ T) :
    ∃ o out c, Runs w p ω
      (.cond (.bin .lt (.reg rA) (.reg rB)) (.assign rOut (.reg rA)) (.assign rOut (.reg rB)) ;; rest)
      st o out c ∧ Q o out ∧ k + c ≤ T := by
  obtain ⟨o, out, c, hr, hQ, hc⟩ := hrest
  by_cases hlt : a < b
  · have hmin : min a b = a := Nat.min_eq_left (Nat.le_of_lt hlt)
    have hcond : Runs w p ω
        (.cond (.bin .lt (.reg rA) (.reg rB)) (.assign rOut (.reg rA)) (.assign rOut (.reg rB)))
        st .normal ⟨st.mem, Function.update st.regs rOut (min a b), st.pos⟩ 6 := by
      refine runs_cond_iff.mpr ⟨1, 2, ?_, ?_, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, ha, hb, hlt, hw1]
      · exact runs_assign_iff.mpr ⟨min a b, by simp [Expr.eval, ha, hmin], rfl, rfl,
          by simp [Expr.size]⟩
    exact ⟨o, out, 6 + c + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcond, hr, rfl⟩), hQ, by omega⟩
  · have hmin : min a b = b := Nat.min_eq_right (Nat.le_of_not_lt hlt)
    have hcond : Runs w p ω
        (.cond (.bin .lt (.reg rA) (.reg rB)) (.assign rOut (.reg rA)) (.assign rOut (.reg rB)))
        st .normal ⟨st.mem, Function.update st.regs rOut (min a b), st.pos⟩ 6 := by
      refine runs_cond_iff.mpr ⟨0, 2, ?_, ?_, by simp [Expr.size]⟩
      · simp [Expr.eval, BinOp.eval, ha, hb, hlt]
      · exact runs_assign_iff.mpr ⟨min a b, by simp [Expr.eval, hb, hmin], rfl, rfl,
          by simp [Expr.size]⟩
    exact ⟨o, out, 6 + c + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcond, hr, rfl⟩), hQ, by omega⟩

private lemma runs_seq_call_runs_pc {w dst proc k T c1 : ℕ} {p : Program} {ω : ℕ → Bool}
    {args : List Expr} {body rest : Stmt} {st st1 : State} {o1 : Outcome}
    {Q : Outcome → State → Prop} {vs : List ℕ}
    (hb : p.procs[proc]? = some body)
    (heval : evalArgs w st args = some vs)
    (hr : Runs w p ω body (startState vs st.mem st.pos) o1 st1 c1)
    (hrest : ∃ o out c2, Runs w p ω rest
      ⟨st1.mem, Function.update st.regs dst o1.value, st1.pos⟩ o out c2 ∧
      Q o out ∧ (k + (argsSize args + c1 + 2)) + c2 ≤ T) :
    ∃ o out c, Runs w p ω (.call dst proc args ;; rest) st o out c ∧ Q o out ∧ k + c ≤ T := by
  obtain ⟨o, out, c2, hr2, hQ, hc⟩ := hrest
  have h1 : Runs w p ω (.call dst proc args) st .normal
      ⟨st1.mem, Function.update st.regs dst o1.value, st1.pos⟩ (argsSize args + c1 + 1) :=
    runs_call_iff.mpr ⟨vs, body, o1, st1, c1, heval, hb, hr, rfl, rfl, rfl⟩
  exact ⟨o, out, (argsSize args + c1 + 1) + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1, hr2, rfl⟩), hQ, by omega⟩

set_option maxHeartbeats 1200000 in
/-- Word-RAM execution stitching for `selectUpdatePostCoreBody`: combines the 6 sub-call `Runs`
witnesses into a single `Runs` witness with at most `600` glue steps. -/
theorem selectUpdatePostCoreBody_stitch
    {w root selOutBase scratch pos handle table slots edgeRecords treeHeap d sb blkBase metaBase
      L vCap eCap pLast emb0 f1 slot g0Ptr G0Ptr termHandle termBran firstReb
      sc1 sc2 sc3 sc4 sc5 cTW cG0 cFPL cEmb cSuf cHeap
      tableWriteProc g0Proc fPhiLenLoopProc embLoopProc sufBlocksProc heapPhaseProc : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {bTW bG0 bFPL bEmb bSuf bHeap : Stmt} {oTW : Outcome}
    {stTW st1 st2 st3 st4 st5 : State}
    (hw16 : 16 < 2 ^ w) (hdPos : 0 < d) (heCapPos : 0 < eCap)
    (hrootW : root + 10 < 2 ^ w) (hOutW : selOutBase + 1 < 2 ^ w)
    (hHndW : handle + 18 + 2 * (d + 1) < 2 ^ w) (hTabW : table + 4 * d + 3 < 2 ^ w)
    (hdW : d + 1 < 2 ^ w) (hSbW : sb + 13 < 2 ^ w)
    (hMetaW : metaBase + 2 + 8 * (d + 1) < 2 ^ w)
    (hEmb0LeF1 : emb0 + eCap ≤ f1) (hF1W : f1 < 2 ^ w) (hSlotW : slot < 2 ^ w)
    (hSlotEq : ((f1 - emb0) - eCap) / eCap = slot)
    (hReadHnd : mem root = handle)
    (hReadTab : mem (root + 1) = table)
    (hReadSlots : mem (root + 6) = slots)
    (hReadRecs : mem (root + 10) = edgeRecords)
    (hReadTree : mem handle = treeHeap)
    (hReadD : mem (handle + 11) = d)
    (hReadSb : mem (table + 4 * d + 2) = sb)
    (hReadBlk : mem (table + 4 * d + 3) = blkBase)
    (hReadMeta : mem (sb + 13) = metaBase)
    (hReadL : mem (sb + 3) = L)
    (hReadVCap : mem (metaBase + 2 + (d + 1)) = vCap)
    (hReadECap : mem (metaBase + 2 + 2 * (d + 1)) = eCap)
    (hReadPLast : mem (metaBase + 2 + 7 * (d + 1) + d) = pLast)
    (hReadEmb0 : mem (metaBase + 2 + 5 * (d + 1)) = emb0)
    (hReadF1 : mem (metaBase + 2 + 6 * (d + 1) + 1) = f1)
    (hReadG0 : mem metaBase = g0Ptr)
    (hReadG0Ptr : mem (table + 2 * d + 2 + d) = G0Ptr)
    (hReadTermH : mem (handle + 18 + d) = termHandle)
    (hReadTermB : mem (handle + 18 + (d + 1) + d) = termBran)
    (hReadFR : mem selOutBase = firstReb)
    (hbTW : p.procs[tableWriteProc]? = some bTW)
    (hrTW : Runs w p ω bTW
      (startState [metaBase, blkBase, d, vCap, eCap, L, slot, table + 2 * d + 2, pLast] mem pos)
      oTW stTW cTW)
    (hbG0 : p.procs[g0Proc]? = some bG0)
    (hrG0 : Runs w p ω bG0
      (startState [firstReb, slots, edgeRecords, treeHeap, g0Ptr, G0Ptr, vCap, selOutBase + 1,
        L, scratch] stTW.mem stTW.pos)
      (.returned sc1) st1 cG0)
    (hbFPL : p.procs[fPhiLenLoopProc]? = some bFPL)
    (hrFPL : Runs w p ω bFPL
      (startState [metaBase, 0, min firstReb d, table + 2 * d + 2, selOutBase, d, L, sc1]
        st1.mem st1.pos)
      (.returned sc2) st2 cFPL)
    (hbEmb : p.procs[embLoopProc]? = some bEmb)
    (hrEmb : Runs w p ω bEmb
      (startState [metaBase, 0, min firstReb d, handle + 18, selOutBase, d, slot, sc2]
        st2.mem st2.pos)
      (.returned sc3) st3 cEmb)
    (hbSuf : p.procs[sufBlocksProc]? = some bSuf)
    (hrSuf : Runs w p ω bSuf
      (startState [metaBase, firstReb, d, handle + 18, table + 2 * d + 2, termHandle, termBran,
        L, slot, pLast, sc3] st3.mem st3.pos)
      (.returned sc4) st4 cSuf)
    (hbHeap : p.procs[heapPhaseProc]? = some bHeap)
    (hrHeap : Runs w p ω bHeap
      (startState [sb, metaBase, firstReb, d, selOutBase, sc4] st4.mem st4.pos)
      (.returned sc5) st5 cHeap) :
    ∃ outF cBody,
      Runs w p ω
        (selectUpdatePostCoreBody tableWriteProc g0Proc fPhiLenLoopProc embLoopProc
          sufBlocksProc heapPhaseProc)
        (startState [root, selOutBase, scratch] mem pos) (.returned sc5) outF cBody ∧
      outF.mem = st5.mem ∧
      cBody ≤ cTW + cG0 + cFPL + cEmb + cSuf + cHeap + 600 := by
  let Q_goal (o : Outcome) (out : State) : Prop := o = .returned sc5 ∧ out.mem = st5.mem
  suffices h : ∃ o out c,
      Runs w p ω
        (selectUpdatePostCoreBody tableWriteProc g0Proc fPhiLenLoopProc embLoopProc
          sufBlocksProc heapPhaseProc)
        (startState [root, selOutBase, scratch] mem pos) o out c ∧ Q_goal o out ∧
        c ≤ cTW + cG0 + cFPL + cEmb + cSuf + cHeap + 600 by
    obtain ⟨_, out, c, hr, ⟨rfl, hm⟩, hc⟩ := h; exact ⟨out, c, hr, hm, hc⟩
  refine runs_start_le (T := cTW + cG0 + cFPL + cEmb + cSuf + cHeap + 600) (Q := Q_goal) ?_
  dsimp only [startState]
  unfold selectUpdatePostCoreBody
  refine runs_seq_assign_flat (v := handle) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := table) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := slots) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := edgeRecords) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := treeHeap) (by eval_expr) ?_
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
  refine runs_seq_assign_flat (v := g0Ptr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := G0Ptr) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := termHandle) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := termBran) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := firstReb) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := selOutBase + 1) (by eval_expr) ?_
  refine runs_seq_cond_min_le (a := firstReb) (b := d) (by simp) (by simp) (by omega) ?_
  refine runs_seq_call_runs_pc (hb := hbTW) (hr := hrTW)
    (vs := [metaBase, blkBase, d, vCap, eCap, L, slot, table + 2 * d + 2, pLast]) (by eval_expr) ?_
  refine runs_seq_call_runs_pc (hb := hbG0) (hr := hrG0)
    (vs := [firstReb, slots, edgeRecords, treeHeap, g0Ptr, G0Ptr, vCap, selOutBase + 1, L, scratch])
    (by eval_expr) ?_
  refine runs_seq_call_runs_pc (hb := hbFPL) (hr := hrFPL)
    (vs := [metaBase, 0, min firstReb d, table + 2 * d + 2, selOutBase, d, L, sc1])
    (by eval_expr) ?_
  refine runs_seq_call_runs_pc (hb := hbEmb) (hr := hrEmb)
    (vs := [metaBase, 0, min firstReb d, handle + 18, selOutBase, d, slot, sc2])
    (by eval_expr) ?_
  refine runs_seq_call_runs_pc (hb := hbSuf) (hr := hrSuf)
    (vs := [metaBase, firstReb, d, handle + 18, table + 2 * d + 2, termHandle, termBran,
      L, slot, pLast, sc3])
    (by eval_expr) ?_
  refine runs_seq_call_runs_pc (hb := hbHeap) (hr := hrHeap)
    (vs := [sb, metaBase, firstReb, d, selOutBase, sc4])
    (by eval_expr) ?_
  exact WordRAM.runs_ret_le (v := sc5) (by eval_expr) ⟨rfl, rfl⟩
    (by simp only [argsSize, Expr.size]; omega)

/-- Congruence of `selectUpdateHeapPhaseSpace` and `selectUpdateHeapPhaseCost` when memory agrees
on `[loc.hb, loc.endAddr)`. -/
theorem selectUpdateHeapPhase_congr_mem {T : SparseCoreRestartTool} {P : ChainParams}
    {loc : SelectHeapLoc} {C' : ChainState T P} {diffLists : ℕ → LevelDiffLists}
    {firstReb evalSpace evalCost : ℕ} {m1 m2 : ℕ → ℕ}
    (hag : ∀ a, loc.hb ≤ a → a < loc.endAddr → m1 a = m2 a) :
    selectUpdateHeapPhaseSpace m1 loc C'.toTreeChain diffLists firstReb evalSpace =
      selectUpdateHeapPhaseSpace m2 loc C'.toTreeChain diffLists firstReb evalSpace ∧
    selectUpdateHeapPhaseCost m1 loc C'.toTreeChain diffLists firstReb evalCost =
      selectUpdateHeapPhaseCost m2 loc C'.toTreeChain diffLists firstReb evalCost := by
  have hcc : ∀ j, levelCandCount m1 loc j = levelCandCount m2 loc j := fun j =>
    levelCandCount_congr_eq hag
  constructor
  · unfold selectUpdateHeapPhaseSpace selectRebuildSuffixSpace
    have hEq : (Finset.Icc firstReb C'.toTreeChain.d).sum
        (fun j => selectRebuildLevelSpace (levelCandCount m1 loc j) (C'.toTreeChain.G j).E.card loc.cap loc.Lk evalSpace) =
        (Finset.Icc firstReb C'.toTreeChain.d).sum
        (fun j => selectRebuildLevelSpace (levelCandCount m2 loc j) (C'.toTreeChain.G j).E.card loc.cap loc.Lk evalSpace) :=
      Finset.sum_congr rfl fun j _ => by rw [hcc j]
    rw [hEq]
  · unfold selectUpdateHeapPhaseCost selectRebuildSuffixCost
    have hEq : (Finset.Icc firstReb C'.toTreeChain.d).sum
        (fun j => selectRebuildLevelCost (levelCandCount m1 loc j) (C'.toTreeChain.G j).E.card loc.cap loc.Lk evalCost + 40) =
        (Finset.Icc firstReb C'.toTreeChain.d).sum
        (fun j => selectRebuildLevelCost (levelCandCount m2 loc j) (C'.toTreeChain.G j).E.card loc.cap loc.Lk evalCost + 40) :=
      Finset.sum_congr rfl fun j _ => by rw [hcc j]
    rw [hEq]

/-- Congruence of `selectUpdateSuffixBlocksCost` when `oldF₁` and `oldF₂` agree on
`firstReb .. P.d`. -/
theorem selectUpdateSuffixBlocksCost_congr {T : SparseCoreRestartTool} {P : ChainParams}
    {oldF₁ oldF₂ : ℕ → MGraph} {oldGd : MGraph} {C' : ChainState T P}
    {readoutCost firstReb L capExp slot : ℕ}
    (hF : ∀ j, firstReb ≤ j → j ≤ P.d → oldF₁ j = oldF₂ j) :
    selectUpdateSuffixBlocksCost oldF₁ oldGd C' readoutCost firstReb L capExp slot =
      selectUpdateSuffixBlocksCost oldF₂ oldGd C' readoutCost firstReb L capExp slot := by
  unfold selectUpdateSuffixBlocksCost
  split_ifs with hle
  · have hIntEq : selectRefreshInteriorLoopCost oldF₁ C' readoutCost firstReb L capExp slot =
        selectRefreshInteriorLoopCost oldF₂ C' readoutCost firstReb L capExp slot := by
      unfold selectRefreshInteriorLoopCost
      exact congrArg (· + 10) (Finset.sum_congr rfl fun j hj => by
        rw [hF j (Finset.mem_Ico.mp hj).1 (Nat.le_of_lt (Finset.mem_Ico.mp hj).2)])
    rw [hIntEq, hF P.d hle le_rfl]
  · rfl

end MinCostFlow.MinRatio
