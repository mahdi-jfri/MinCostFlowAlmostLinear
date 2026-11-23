module

public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.WireChainCoreOps
import WordRAM.Tactic

/-!
# Phase 0 register initialization and select-footprint core runners under `KFBL`/`KFRBL` (`WireChainCoreInitKFBL`)

Provides:
1. `stretchValuesAt_of_agree`: memory-agreement lemma for `StretchValuesAt`.
2. `ordCoreReadLSFKFBLStretch_runs`: executes `ordCoreReadLSFStmt (op 2)` under
   `SparseCoreSelectFootAt`, returning both `LSFAt` (forest in core footprint or `[heap, ret)`)
   and core-footprint containment of the stretch descriptor `stDesc .. stDesc + 2` and stretch
   limb tables for every `e ∈ a.G.E`.
3. `ordCoreUpdateKFRBLSelOut_runs`: executes `ordCoreUpdateStmt (op 0)` combining `KFRBL` with
   `SparseCoreSelectFootAt`, returning `BranchOutAt`, `BranchOutFChgAt` with `chgPtr` disjoint
   from `Rcore.foot handle y`, `ReembListAt` with `reembPtr` in `[heap, ret)` and disjoint from
   `Rcore.foot handle y`, and `bPtr`/`ePtr` placement + `edMul` bounds on the same deterministic run.
4. `updateCoreInitRegsKFBL` and `updateCoreInitRegsKFBL_runs`: Phase 0 register initialization
   reserving `selOut = [heap, heap + 1 + 12 * d)` at `reg 72`, `oldPtrs`/`newPtrs`/`emptyPtrs`/
   `emptyGraphPtr` immediately after `selOut` at `arrBase := heap + 1 + 12 * d`, and loading
   `depth = mem[handle + 17]` into `reg 98`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-! ### 1. Memory-agreement helper for `StretchValuesAt` -/

/-- `StretchValuesAt` is preserved when the 2-word descriptor `[a, a + 2)` and the numerator and
denominator limb blocks for all `e ∈ E` are unchanged. -/
theorem stretchValuesAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a h L P : ℕ} {E : Finset ℕ}
    {values : ℕ → ℝ}
    (hv : StretchValuesAt mem₁ a h L P E values)
    (ha0 : mem₂ a = mem₁ a) (ha1 : mem₂ (a + 1) = mem₁ (a + 1))
    (hnum : ∀ e ∈ E, ∀ t < L, mem₂ (mem₁ a + e * L + t) = mem₁ (mem₁ a + e * L + t))
    (hden : ∀ e ∈ E, ∀ t < L, mem₂ (mem₁ (a + 1) + e * L + t) = mem₁ (mem₁ (a + 1) + e * L + t)) :
    StretchValuesAt mem₂ a h L P E values := by
  intro e he
  obtain ⟨hvn, hvd, hpos, hdiv⟩ := hv e he
  rw [ha0, ha1]
  have hNumAgree : ∀ i < L, mem₂ (mem₁ a + e * L + i) = mem₁ (mem₁ a + e * L + i) := hnum e he
  have hDenAgree : ∀ i < L, mem₂ (mem₁ (a + 1) + e * L + i) = mem₁ (mem₁ (a + 1) + e * L + i) :=
    hden e he
  have hvn2 : Num.Valid mem₂ (mem₁ a + e * L) h L := fun i hi => by
    rw [hNumAgree i hi]; exact hvn i hi
  have hvd2 : Num.Valid mem₂ (mem₁ (a + 1) + e * L) h L := fun i hi => by
    rw [hDenAgree i hi]; exact hvd i hi
  have hfn : Num.fixVal mem₂ (mem₁ a + e * L) h L P = Num.fixVal mem₁ (mem₁ a + e * L) h L P := by
    unfold Num.fixVal Num.intVal
    rw [Num.unsignedVal_congr hNumAgree]
  have hfd : Num.fixVal mem₂ (mem₁ (a + 1) + e * L) h L P =
      Num.fixVal mem₁ (mem₁ (a + 1) + e * L) h L P := by
    unfold Num.fixVal Num.intVal
    rw [Num.unsignedVal_congr hDenAgree]
  rw [hfn, hfd]
  exact ⟨hvn2, hvd2, hpos, hdiv⟩

/-! ### 2. Op `2` (`readLSF`) and Op `0` (`update`) runners under `SparseCoreSelectFootAt` -/

/-- Execute `ordCoreReadLSFStmt (op 2)` under `SparseCoreSelectFootAt`, returning `LSFAt`,
forest placement inside `R.foot handle y ∨ [heap, ret)`, and core-footprint containment of the
stretch descriptor `stDesc .. stDesc + 2` and numerator/denominator limb blocks for all `e ∈ a.G.E`. -/
theorem ordCoreReadLSFKFBLStretch_runs
    {w L depth k M N vCap eCap capExp edMul branch handle graph heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hSel : SparseCoreSelectFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ heap)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 5 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      out.mem (heap + 4) ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
      (∃ vc ec,
        LSFAt out.mem heap vc ec fmt.limbBits (out.mem (heap + 4)) fmt.precision a.G.E
          (tool.lsfs a.st branch) ∧
        out.mem (heap + 1) + dynGraphSize vc ec ≤ heap ∧
        (∀ addr, out.mem (heap + 1) ≤ addr → addr < out.mem (heap + 1) + dynGraphSize vc ec →
          R.foot handle y addr ∨ (heap ≤ addr ∧ addr < ret)) ∧
        dynGraphSize vc ec ≤ dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) ∧
      out.mem (heap + 3) + 2 ≤ heap ∧
      (∀ addr, out.mem (heap + 3) ≤ addr → addr < out.mem (heap + 3) + 2 →
        R.foot handle y addr) ∧
      (∀ e ∈ a.G.E,
        out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + out.mem (heap + 4) ≤ heap ∧
        out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + out.mem (heap + 4) ≤ heap ∧
        ∀ t < out.mem (heap + 4),
          R.foot handle y (out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + t) ∧
          R.foot handle y (out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + t)) ∧
      R.Respects (R.foot handle x) heap 5 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, graph, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hrespect, hcost⟩ :=
    hSel.op2_runs handle a x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, graph, heap, rfl, hj, hG, hgEnd⟩ hfoot hz hroom
  obtain ⟨vc, ec, hLw, hlsf, hfEnd, hfIn, hstEnd, hstFoot, hstTbl, hfCap⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hLw hlsf hfEnd hfIn hstEnd hstFoot hstTbl
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 6, .reg 4] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hg, hp]
  have hcall : Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 4 + c + 1, y, hcall, by simp [out], hrep', hLw,
    ⟨vc, ec, hlsf, hfEnd, hfIn, hfCap⟩, hstEnd, hstFoot, hstTbl, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  change c + R.phi handle y out.mem ≤ P.readout + R.phi handle x st.mem at hcost
  omega

/-- Execute `ordCoreUpdateStmt (op 0)` combining `KFRBL` with `SparseCoreSelectFootAt`, returning
`BranchOutAt`, `BranchOutFChgAt` with `chgPtr` disjoint from `R.foot handle y`, `ReembListAt`
with `reembPtr` in `[heap, ret)` and disjoint from `R.foot handle y`, and `bPtr`/`ePtr` placement
and `edMul` bounds on the exact same deterministic run. -/
theorem ordCoreUpdateKFRBLSelOut_runs
    {w L depth k M N vCap eCap capExp edMul handle graph batch words edits editWords lengths
      gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph} {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hImpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N vCap eCap capExp P
        allocation))
    (hSel : SparseCoreSelectFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p op)
    (hh : st.regs 3 = handle) (hg : st.regs 6 = graph)
    (hb : st.regs 10 = batch) (hbw : st.regs 11 = words)
    (he : st.regs 12 = edits) (hew : st.regs 13 = editWords)
    (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient) (hp : st.regs 4 = heap)
    (hwords : ∀ v ∈ [handle, graph, batch, words, edits, editWords, lengths, gradient, heap],
      v < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hpre : SparseCoreOrdUpdateAt fmt L tool k M N vCap eCap a
      [handle, graph, batch, words, edits, editWords, lengths, gradient, heap] st.mem)
    (hvalid : OrdEditsValidFor vCap eCap a.ord (readOrdEdits st.mem edits))
    (hblocks : OrdEditsForBatch a.G
      (ordUpdateBatch a [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
        st.mem) (readOrdEdits st.mem edits))
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0
      [handle, graph, batch, words, edits, editWords, lengths, gradient, heap] < 2 ^ w) :
    let args := [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
    let a' := ordUpdateNext fmt L a args st.mem
    let batches := (ordUpdateModel fmt L a args st.mem).2
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreUpdateStmt (op 0)) st .normal out cost ∧
      out.regs 5 = ret ∧
      R.rep handle a' y out.mem ∧
      SparseCoreOrdInput tool k M N a'.st a'.G a'.ord a'.n ∧
      BranchOutAt out.mem heap k (tool.S a.st) batches (tool.rot a.st) (tool.rot a'.st) ∧
      BranchOutFChgAt w out.mem heap ret k (tool.lsfs a.st) (tool.lsfs a'.st) ∧
      (let fChgPtr := out.mem (heap + 1 + 6 * k)
       ∀ j < k, ∃ chg : Read.LSFChange,
         let chgPtr := out.mem (fChgPtr + j)
         Read.LSFChangeAt out.mem chgPtr chg ∧
         chg.Exact (tool.lsfs a.st j) (tool.lsfs a'.st j) ∧
         heap ≤ chgPtr ∧ chgPtr + chg.words ≤ ret ∧
         (∀ e ∈ chg.fDel, e < 2 ^ w) ∧
         (∀ t < chg.words, ¬ R.foot handle y (chgPtr + t))) ∧
      (∀ j < k, ReembListAt out.mem
        (out.mem (heap + 1 + 4 * k + 2 * j)) (out.mem (heap + 2 + 4 * k + 2 * j))
        (reemb a.st (ordUpdateBatch a args st.mem) (ordUpdateOrder a args st.mem) j)) ∧
      (∀ j < k, OrdEditsForBatch (tool.S a.st j) (batches j)
        (readOrdEdits out.mem (out.mem (heap + 3 + 4 * j)))) ∧
      (∀ j < k, OrdEditsValidFor vCap eCap (tool.rot a.st j)
        (readOrdEdits out.mem (out.mem (heap + 3 + 4 * j)))) ∧
      (∀ j < k,
        let base := heap + 1 + 4 * j
        let bPtr := out.mem base
        let bW := out.mem (base + 1)
        let ePtr := out.mem (base + 2)
        let eW := out.mem (base + 3)
        let rPtr := out.mem (heap + 1 + 4 * k + 2 * j)
        let rLen := out.mem (heap + 2 + 4 * k + 2 * j)
        heap + 1 + 4 * j + 3 < ret ∧
        heap + 2 + 4 * k + 2 * j < ret ∧
        heap ≤ bPtr ∧ bPtr + bW ≤ ret ∧
        heap ≤ ePtr ∧ ePtr + eW ≤ ret ∧
        heap ≤ rPtr ∧ rPtr + rLen ≤ ret ∧
        (∀ t < bW, out.mem (bPtr + t) < 2 ^ w) ∧
        (∀ t < eW, out.mem (ePtr + t) < 2 ^ w) ∧
        (∀ t < bW, ¬ R.foot handle y (bPtr + t)) ∧
        (∀ t < eW, ¬ R.foot handle y (ePtr + t)) ∧
        (∀ t < rLen, ¬ R.foot handle y (rPtr + t)) ∧
        (decodeBatch out.mem bPtr (tool.S a.st j)).1 = batches j ∧
        eW ≤ edMul * (tool.cost a'.st - tool.cost a.st +
          (words + editWords + 1) * SparseCore.bundleLogFactor M N)) ∧
      R.Respects (R.foot handle x) heap (allocation 0 args) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (tool.cost a'.st - tool.cost a.st +
          (k + 1) * (words + editWords + 1) * SparseCore.bundleLogFactor M N) +
        R.phi handle x st.mem + 10 ∧
      ∀ r, r ≠ 5 → out.regs r = st.regs r := by
  intro args a' batches
  have hDpre : (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N
      vCap eCap capExp P allocation).pre 0 a args st.mem :=
    ⟨⟨hpre, hvalid⟩, hblocks⟩
  obtain ⟨body1, hbody1, o1, after1, c1, y, hrun1, hrep', hpost1, hFChg, hChgDisj, hSlots,
      hResp, hCost⟩ :=
    hSel.op0_runs handle a x args st.mem st.pos ω hwords rfl hrep hDpre hfoot hz hroom
  have hDpreR : (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N
      vCap eCap capExp P allocation).pre 0 a args st.mem :=
    ⟨⟨hpre, hvalid⟩, hblocks⟩
  obtain ⟨body2, hbody2, o2, st2, c2, hrun2, a2, y2, _, hpost2, _, _⟩ :=
    hImpl.2.2 0 handle a x args st.mem st.pos ω hwords rfl hrep hDpreR hfoot hz hroom
  have hBodyEq : body2 = body1 := Option.some.inj (hbody2.symm.trans hbody1)
  subst hBodyEq
  obtain ⟨_, hstEq, _⟩ := hrun2.det hrun1
  let out := { after1 with regs := Function.update st.regs 5 o1.value }
  have hargs : evalArgs w st
      [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4] = some args := by
    simp [evalArgs, Expr.eval, args, hh, hg, hb, hbw, he, hew, hl, hc, hp]
  have hcall : Runs w p ω (ordCoreUpdateStmt (op 0)) st .normal out (9 + c1 + 1) :=
    runs_call_iff.mpr ⟨args, body2, o1, after1, c1, hargs, hbody1, hrun1, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
  have hheap : heapArg args = heap := by simp [args, heapArg]
  have hW3 : args.getD 3 0 = words := by simp [args]
  have hW5 : args.getD 5 0 = editWords := by simp [args]
  rw [hheap] at hFChg hChgDisj hSlots hResp
  rw [hW3, hW5] at hSlots
  obtain ⟨⟨hnext, hbout⟩, hFor, hVal⟩ := hpost1
  have hIn' := sparseCoreOrdMachineContract_update_input (fmt := fmt) (L := L)
    (tool := tool) (initialGraph := initialGraph) (k := k) (M := M) (N := N)
    (vCap := vCap) (eCap := eCap) (P := P) (allocation := allocation) hpre ⟨hnext, hbout⟩
  have hBO : BranchOutAt after1.mem heap k (tool.S a.st) batches (tool.rot a.st) (tool.rot a'.st) := by
    simpa [hheap] using hbout
  have hFor' : ∀ j < k, OrdEditsForBatch (tool.S a.st j) (batches j)
      (readOrdEdits after1.mem (after1.mem (heap + 3 + 4 * j))) := by
    simpa [hheap] using hFor
  have hVal' : ∀ j < k, OrdEditsValidFor vCap eCap (tool.rot a.st j)
      (readOrdEdits after1.mem (after1.mem (heap + 3 + 4 * j))) := by
    simpa [hheap] using hVal
  have hMemEq : out.mem = st2.mem := show after1.mem = st2.mem from congrArg State.mem hstEq.symm
  have hReemb : ∀ j < k, ReembListAt out.mem
      (out.mem (heap + 1 + 4 * k + 2 * j)) (out.mem (heap + 2 + 4 * k + 2 * j))
      (reemb a.st (ordUpdateBatch a args st.mem) (ordUpdateOrder a args st.mem) j) := fun j hj => by
    rw [hMemEq]
    exact reembListAt_of_readList (by simpa [heapArg, args] using hpost2.1.2 j hj)
  refine ⟨out, o1.value, 9 + c1 + 1, y, hcall, by simp [out], hrep', hIn', hBO, hFChg,
    hChgDisj, hReemb, hFor', hVal', hSlots, hResp, ?_, fun r hr => Function.update_of_ne hr _ _⟩
  change c1 + R.phi handle y out.mem ≤
      P.mul * (tool.cost a'.st - tool.cost a.st +
        (k + 1) * (words + editWords + 1) * SparseCore.bundleLogFactor M N) +
      R.phi handle x st.mem at hCost
  omega

/-! ### 3. Phase 0 register initialization under `KFBL` (`updateCoreInitRegsKFBL`) -/

/-- Phase 0 under `KFBL`: decode `[root, uIntBuf, editsPtr, editWords, g, l, heap]` (`regs 0..6`)
and solver header addresses into permanent high registers `70..95` and `98`, reserving:
* `selOut` (`1 + 12 * d` words) at `reg 72 = heap`,
* `oldPtrs`, `newPtrs`, `emptyPtrs`, and 4-word `emptyGraphPtr` at
  `arrBase := heap + 1 + 12 * d .. arrBase + 3 * (d + 1) + 4`,
* `reg 4 = arrBase + 3 * (d + 1) + 4`,
* `reg 98 = mem[handle + 17]` (`depth = Expander.chosenL (cfg.P.M₀ ^ 2)`). -/
@[expose] def updateCoreInitRegsKFBL : Stmt :=
  .assign 70 (.reg 0) ;;
  .assign 71 (.const 0) ;;
  .assign 72 (.reg 6) ;;
  .assign 87 (.reg 1) ;;
  .assign 88 (.reg 2) ;;
  .assign 89 (.reg 3) ;;
  .assign 90 (.reg 4) ;;
  .assign 91 (.reg 5) ;;
  .assign 73 (.load (.reg 70)) ;;
  .assign 74 (.load (.bin .add (.reg 70) (.const 1))) ;;
  .assign 84 (.load (.bin .add (.reg 70) (.const 2))) ;;
  .assign 75 (.load (.bin .add (.reg 73) (.const 11))) ;;
  .assign 76 (.load (.bin .add (.reg 73) (.const 12))) ;;
  .assign 94 (.load (.bin .add (.reg 73) (.const 5))) ;;
  .assign 95 (.load (.bin .add (.reg 73) (.const 8))) ;;
  .assign 98 (.load (.bin .add (.reg 73) (.const 17))) ;;
  .assign 77 (.bin .add (.reg 73) (.const 18)) ;;
  .assign 78 (.bin .add (.reg 77) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 79 (.bin .add (.reg 75) (.const 1)) ;;
  .assign 80 (.bin .add (.bin .add (.reg 72) (.const 1)) (.bin .mul (.const 12) (.reg 75))) ;;
  .assign 81 (.bin .add (.reg 80) (.reg 79)) ;;
  .assign 92 (.bin .add (.reg 81) (.reg 79)) ;;
  .assign 93 (.bin .add (.reg 92) (.reg 79)) ;;
  .assign 4 (.bin .add (.reg 93) (.const 4)) ;;
  .assign 82 (.bin .add (.bin .add (.reg 74) (.reg 79)) (.const 1)) ;;
  .assign 83 (.bin .add (.reg 82) (.reg 75)) ;;
  .assign 86 (.bin .add (.reg 84) (.bin .mul (.const 2) (.reg 79))) ;;
  .assign 85 (.bin .add (.reg 86) (.reg 79))

theorem updateCoreInitRegsKFBL_noRand : updateCoreInitRegsKFBL.NoRand := by
  simp [updateCoreInitRegsKFBL, Stmt.NoRand]

/-- Execute `updateCoreInitRegsKFBL`, populating `regs 70..95`, `reg 98 = depth`, and
`reg 4 = heap + (1 + 12 * d) + 3 * (d + 1) + 4` without modifying memory. -/
theorem updateCoreInitRegsKFBL_runs
    {w root uIntBuf editsPtr editWords g l heap handle table levelsEnd d k L P depth pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hRoot0 : mem root = handle) (hRoot1 : mem (root + 1) = table)
    (hRoot2 : mem (root + 2) = levelsEnd)
    (hH5 : mem (handle + 5) = L) (hH8 : mem (handle + 8) = P)
    (hH11 : mem (handle + 11) = d) (hH12 : mem (handle + 12) = k)
    (hH17 : mem (handle + 17) = depth)
    (hRootW : root + 2 < 2 ^ w) (hHandleW : handle + 18 + (d + 1) < 2 ^ w)
    (hTableW : solverLevelMetaAddr table d < 2 ^ w) (hSchedW : levelsEnd + 3 * (d + 1) < 2 ^ w)
    (hHeapW : heap + (1 + 12 * d) + 3 * (d + 1) + 4 < 2 ^ w) (hw18 : 18 < 2 ^ w) :
    let cnt := d + 1
    let handleBase := handle + 18
    let branchBase := handleBase + cnt
    let lvlMTable := solverLvlMAddr table d
    let levelMeta := solverLevelMetaAddr table d
    let rebuildCountBase := levelsEnd + 2 * cnt
    let updCountBase := levelsEnd + 3 * cnt
    let arrBase := heap + 1 + 12 * d
    let heapStart := arrBase + 3 * cnt + 4
    ∃ out c,
      Runs w p ω updateCoreInitRegsKFBL
        (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) .normal out c ∧
      c ≤ 190 ∧ out.mem = mem ∧
      out.regs 70 = root ∧ out.regs 71 = 0 ∧ out.regs 72 = heap ∧
      out.regs 73 = handle ∧ out.regs 74 = table ∧ out.regs 75 = d ∧ out.regs 76 = k ∧
      out.regs 77 = handleBase ∧ out.regs 78 = branchBase ∧ out.regs 79 = cnt ∧
      out.regs 80 = arrBase ∧ out.regs 81 = arrBase + cnt ∧
      out.regs 82 = lvlMTable ∧ out.regs 83 = levelMeta ∧
      out.regs 84 = levelsEnd ∧ out.regs 85 = updCountBase ∧ out.regs 86 = rebuildCountBase ∧
      out.regs 87 = uIntBuf ∧ out.regs 88 = editsPtr ∧ out.regs 89 = editWords ∧
      out.regs 90 = g ∧ out.regs 91 = l ∧
      out.regs 92 = arrBase + 2 * cnt ∧ out.regs 93 = arrBase + 3 * cnt ∧
      out.regs 94 = L ∧ out.regs 95 = P ∧ out.regs 98 = depth ∧ out.regs 4 = heapStart := by
  dsimp only
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw8 : 8 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw12 : 12 < 2 ^ w := by omega
  have hw17 : 17 < 2 ^ w := by omega
  have goA {s : State} {r : ℕ} {e : Expr} {v : ℕ} {rest : Stmt} {sOut : State} {cRest : ℕ}
      (he : e.eval w s = some v)
      (hr : Runs w p ω rest { s with regs := Function.update s.regs r v } .normal sOut cRest) :
      Runs w p ω (.assign r e ;; rest) s .normal sOut (e.size + 1 + cRest + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, cRest,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩)
  set s0 := startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos
  have hEvalLast :
      ∃ out c, Runs w p ω updateCoreInitRegsKFBL s0 .normal out c ∧ c ≤ 190 ∧
        out.mem = mem ∧
        out.regs 70 = root ∧ out.regs 71 = 0 ∧ out.regs 72 = heap ∧
        out.regs 73 = handle ∧ out.regs 74 = table ∧ out.regs 75 = d ∧ out.regs 76 = k ∧
        out.regs 77 = handle + 18 ∧ out.regs 78 = handle + 18 + (d + 1) ∧ out.regs 79 = d + 1 ∧
        out.regs 80 = heap + 1 + 12 * d ∧ out.regs 81 = heap + 1 + 12 * d + (d + 1) ∧
        out.regs 82 = solverLvlMAddr table d ∧ out.regs 83 = solverLevelMetaAddr table d ∧
        out.regs 84 = levelsEnd ∧ out.regs 85 = levelsEnd + 3 * (d + 1) ∧
        out.regs 86 = levelsEnd + 2 * (d + 1) ∧
        out.regs 87 = uIntBuf ∧ out.regs 88 = editsPtr ∧ out.regs 89 = editWords ∧
        out.regs 90 = g ∧ out.regs 91 = l ∧
        out.regs 92 = heap + 1 + 12 * d + 2 * (d + 1) ∧
        out.regs 93 = heap + 1 + 12 * d + 3 * (d + 1) ∧
        out.regs 94 = L ∧ out.regs 95 = P ∧ out.regs 98 = depth ∧
        out.regs 4 = heap + 1 + 12 * d + 3 * (d + 1) + 4 := by
    have hrun : Runs w p ω updateCoreInitRegsKFBL s0 .normal _ _ :=
      goA (v := root) (by simp [s0, startState, Expr.eval])
      (goA (v := 0) (by simp [Expr.eval, hw0])
      (goA (v := heap) (by simp [s0, startState, Expr.eval])
      (goA (v := uIntBuf) (by simp [s0, startState, Expr.eval])
      (goA (v := editsPtr) (by simp [s0, startState, Expr.eval])
      (goA (v := editWords) (by simp [s0, startState, Expr.eval])
      (goA (v := g) (by simp [s0, startState, Expr.eval])
      (goA (v := l) (by simp [s0, startState, Expr.eval])
      (goA (v := handle) (by simp [s0, startState, Expr.eval, hRoot0])
      (goA (v := table) (by simp [s0, startState, Expr.eval, BinOp.eval, hw1, show root + 1 < 2 ^ w by omega, hRoot1])
      (goA (v := levelsEnd) (by simp [s0, startState, Expr.eval, BinOp.eval, hw2, hRootW, hRoot2])
      (goA (v := d) (by simp [s0, startState, Expr.eval, BinOp.eval, hw11, show handle + 11 < 2 ^ w by omega, hH11])
      (goA (v := k) (by simp [s0, startState, Expr.eval, BinOp.eval, hw12, show handle + 12 < 2 ^ w by omega, hH12])
      (goA (v := L) (by simp [s0, startState, Expr.eval, BinOp.eval, hw5, show handle + 5 < 2 ^ w by omega, hH5])
      (goA (v := P) (by simp [s0, startState, Expr.eval, BinOp.eval, hw8, show handle + 8 < 2 ^ w by omega, hH8])
      (goA (v := depth) (by simp [s0, startState, Expr.eval, BinOp.eval, hw17, show handle + 17 < 2 ^ w by omega, hH17])
      (goA (v := handle + 18) (by simp [Expr.eval, BinOp.eval, hw18, show handle + 18 < 2 ^ w by omega])
      (goA (v := handle + 18 + (d + 1)) (by simp [Expr.eval, BinOp.eval, hw1, show d + 1 < 2 ^ w by omega, hHandleW])
      (goA (v := d + 1) (by simp [Expr.eval, BinOp.eval, hw1, show d + 1 < 2 ^ w by omega])
      (goA (v := heap + 1 + 12 * d) (by simp [Expr.eval, BinOp.eval, hw1, hw12, show heap + 1 < 2 ^ w by omega, show 12 * d < 2 ^ w by omega, show heap + 1 + 12 * d < 2 ^ w by omega])
      (goA (v := heap + 1 + 12 * d + (d + 1)) (by simp [Expr.eval, BinOp.eval, show heap + 1 + 12 * d + (d + 1) < 2 ^ w by omega])
      (goA (v := heap + 1 + 12 * d + 2 * (d + 1)) (by simp [Expr.eval, BinOp.eval, show heap + 1 + 12 * d + (d + 1) + (d + 1) = heap + 1 + 12 * d + 2 * (d + 1) by omega, show heap + 1 + 12 * d + 2 * (d + 1) < 2 ^ w by omega])
      (goA (v := heap + 1 + 12 * d + 3 * (d + 1)) (by simp [Expr.eval, BinOp.eval, show heap + 1 + 12 * d + 2 * (d + 1) + (d + 1) = heap + 1 + 12 * d + 3 * (d + 1) by omega, show heap + 1 + 12 * d + 3 * (d + 1) < 2 ^ w by omega])
      (goA (v := heap + 1 + 12 * d + 3 * (d + 1) + 4) (by simp [Expr.eval, BinOp.eval, hw4, show heap + 1 + 12 * d + 3 * (d + 1) + 4 < 2 ^ w by omega])
      (goA (v := solverLvlMAddr table d) (by
        simp [Expr.eval, BinOp.eval, hw1, solverLvlMAddr, solverN0Addr,
          show table + (d + 1) < 2 ^ w by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hTableW; omega,
          show table + (d + 1) + 1 < 2 ^ w by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hTableW; omega])
      (goA (v := solverLevelMetaAddr table d) (by
        simp [Expr.eval, BinOp.eval, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr,
          show table + (d + 1) + 1 + d < 2 ^ w by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr at hTableW; omega])
      (goA (v := levelsEnd + 2 * (d + 1)) (by simp [Expr.eval, BinOp.eval, hw2, show 2 * (d + 1) < 2 ^ w by omega, show levelsEnd + 2 * (d + 1) < 2 ^ w by omega])
      (runs_assign_iff.mpr ⟨levelsEnd + 3 * (d + 1), by
        simp [Expr.eval, BinOp.eval, show levelsEnd + 2 * (d + 1) + (d + 1) = levelsEnd + 3 * (d + 1) by omega,
          hSchedW], rfl, rfl, rfl⟩)))))))))))))))))))))))))))
    refine ⟨_, _, hrun, by simp [Expr.size], rfl, ?_⟩
    simp
  exact hEvalLast

end MinCostFlow.MinRatio
