module

public import MinCostFlow.MinRatio.WireCoreOpsKFBL
public import MinCostFlow.MinRatio.WireChainCoreFilter
public import MinCostFlow.SparseCore.Program.ReadSpec
import WordRAM.Tactic

/-!
# Op `0` output footprint, LSF-change tree-edit emitter, and batch-insert collector (`WireChainCoreOp0KFBL`)

Provides the `KFBL` op-`0` companion specification and two linear-time `O(|changes|)` helpers used
by Branch B of the chain update core (`WireChainCoreSpecKFBL.lean`, `WireChainCoreCostKFBL.lean`)
and by the select-block update:

1. `BranchOutFChgAt` and `SparseCoreUpdateOutFootAt`: companion to `SparseCoreReadoutFootAt` and
   `SparseCoreForestCapAt` (`WireCoreForestCapKFBL.lean`) for `op 0` (`update`). Adds:
   * output buffer placement inside `[heap, o.value)` disjoint from `R.foot`, with in-range words
     and `(decodeBatch ...).1 = batches j`;
   * the pointer `fChgPtr := mem (heap + 1 + 6 * k)` to `k` `Read.LSFChangeAt` records where branch
     `j`'s record `c` satisfies `c.Exact (tool.lsfs a.st j) (tool.lsfs a'.st j)` (giving `fDel`,
     the exact nodup list of forest edges leaving `F_j`);
   * the output order-edit word bound `eW_j ≤ edMul * (Δ tool.cost + (words + editWords + 1) * B)`
     (matching `AsmBrCoreStepAt`'s `ysMul` bound and `OutStepSpec`'s `ordEditsEnc` bound).
2. `ordCoreUpdateKFBLOut_runs`: executes `ordCoreUpdateStmt (op 0)` under
   `SparseCoreUpdateOutFootAt`.
3. `wireEmitLSFChangeEditsBody` and `wireEmitLSFChangeEditsBody_runs`: appends `(.delete e)` pairs
   for every `e ∈ c.fDel` of a `Read.LSFChangeAt` record into a `TreeEditsAt` buffer in
   `O(|c.fDel| + 1)` steps (no graph copy or forest scan).
4. `batchInsertedEdges`, `wireCollectInsertedEdgesBody`, and `wireCollectInsertedEdgesBody_runs`:
   extracts all edges inserted by a `SmallBatchAt` batch `U` (re-insertions included) into a flat
   `ListAt` array in `O(|U| + 1)` steps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-! ### 1. Companion op-`0` output layout, `fChgPtr`, and `eW` bound -/

/-- The per-branch `Read.LSFChangeAt` array published by `op 0` at `mem (heap + 1 + 6 * k)`:
for each branch `j < k`, `mem (fChgPtr + j)` points to an exact change record `c` between
`oldLsf j` and `newLsf j`, lying inside `[heap, ret)` with all `fDel` entries in word range. -/
@[expose] def BranchOutFChgAt (w : ℕ) (mem : ℕ → ℕ) (heap ret k : ℕ)
    (oldLsf newLsf : ℕ → LSF) : Prop :=
  let fChgPtr := mem (heap + 1 + 6 * k)
  heap + 2 + 6 * k ≤ ret ∧
  heap ≤ fChgPtr ∧ fChgPtr + k ≤ ret ∧
  ∀ j < k, ∃ c : Read.LSFChange,
    let chgPtr := mem (fChgPtr + j)
    Read.LSFChangeAt mem chgPtr c ∧
    c.Exact (oldLsf j) (newLsf j) ∧
    heap ≤ chgPtr ∧ chgPtr + c.words ≤ ret ∧
    ∀ e ∈ c.fDel, e < 2 ^ w

/-- Companion per-run output guarantees for `op 0` (`update`) under
`sparseCoreOrdMachineContractKFBL`: placement of each branch's batch and order edits inside
`[heap, o.value)` disjoint from `R.foot`, `BranchOutFChgAt` at `heap + 1 + 6 * k`, and the
`edMul`-bounded output order-edit word length `eW_j`. -/
structure SparseCoreUpdateOutFootAt {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (edMul : ℕ)
    (R : DSRep (SparseCoreOrdAbs tool)) (p : Program) (op : ℕ → ℕ) : Prop where
  op0_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 0 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 0 a args mem < 2 ^ w →
      ∃ body, p.procs[op 0]? = some body ∧ ∃ o st' c x',
        let h := heapArg args
        let words := args.getD 3 0
        let editWords := args.getD 5 0
        let a' := ordUpdateNext fmt L a args mem
        let batches := (ordUpdateModel fmt L a args mem).2
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a' x' st'.mem ∧
        D.post 0 a args mem a' st'.mem ∧
        BranchOutFChgAt w st'.mem h o.value k (tool.lsfs a.st) (tool.lsfs a'.st) ∧
        (∀ j < k,
          let base := h + 1 + 4 * j
          let bPtr := st'.mem base
          let bW := st'.mem (base + 1)
          let ePtr := st'.mem (base + 2)
          let eW := st'.mem (base + 3)
          h + 1 + 4 * j + 3 < o.value ∧
          h ≤ bPtr ∧ bPtr + bW ≤ o.value ∧
          h ≤ ePtr ∧ ePtr + eW ≤ o.value ∧
          (∀ t < bW, st'.mem (bPtr + t) < 2 ^ w) ∧
          (∀ t < eW, st'.mem (ePtr + t) < 2 ^ w) ∧
          (∀ t < bW, ¬ R.foot b x' (bPtr + t)) ∧
          (∀ t < eW, ¬ R.foot b x' (ePtr + t)) ∧
          (decodeBatch st'.mem bPtr (tool.S a.st j)).1 = batches j ∧
          eW ≤ edMul * (tool.cost a'.st - tool.cost a.st +
            (words + editWords + 1) * SparseCore.bundleLogFactor M N)) ∧
        R.Respects (R.foot b x) h (D.space 0 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 0 a args mem + R.phi b x mem

/-- Execute `ordCoreUpdateStmt (op 0)` under `SparseCoreUpdateOutFootAt`, returning all postconditions
of `ordCoreUpdateKFBL_runs` together with `BranchOutFChgAt`, output buffer placement, and the `edMul`
bound on each branch's output `editWords`. -/
theorem ordCoreUpdateKFBLOut_runs
    {w L depth k M N vCap eCap capExp edMul handle graph batch words edits editWords lengths
      gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hOut : SparseCoreUpdateOutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
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
        heap + 1 + 4 * j + 3 < ret ∧
        heap ≤ bPtr ∧ bPtr + bW ≤ ret ∧
        heap ≤ ePtr ∧ ePtr + eW ≤ ret ∧
        (∀ t < bW, out.mem (bPtr + t) < 2 ^ w) ∧
        (∀ t < eW, out.mem (ePtr + t) < 2 ^ w) ∧
        (∀ t < bW, ¬ R.foot handle y (bPtr + t)) ∧
        (∀ t < eW, ¬ R.foot handle y (ePtr + t)) ∧
        (decodeBatch out.mem bPtr (tool.S a.st j)).1 = batches j ∧
        eW ≤ edMul * (tool.cost a'.st - tool.cost a.st +
          (words + editWords + 1) * SparseCore.bundleLogFactor M N)) ∧
      R.Respects (R.foot handle x) heap (allocation 0 args) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (tool.cost a'.st - tool.cost a.st +
          (k + 1) * (words + editWords + 1) * SparseCore.bundleLogFactor M N) +
          R.phi handle x st.mem + 10 ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  dsimp only
  let args := [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hfchg, hplace, hrespect, hcost⟩ :=
    hOut.op0_runs handle a x args st.mem st.pos ω hwords rfl hrep
      ⟨⟨hpre, by simpa [args] using hvalid⟩, hblocks⟩ hfoot hz hroom
  obtain ⟨⟨hnext, hbout⟩, hblk', hval'⟩ := hpost
  have hIn' := sparseCoreOrdMachineContract_update_input (fmt := fmt) (L := L)
    (tool := tool) (initialGraph := initialGraph) (k := k) (M := M) (N := N)
    (vCap := vCap) (eCap := eCap) (P := P) (allocation := allocation) hpre ⟨hnext, hbout⟩
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st
      [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4] =
        some args := by
    simp [evalArgs, Expr.eval, args, hh, hg, hb, hbw, he, hew, hl, hc, hp]
  have hcall : Runs w p ω (ordCoreUpdateStmt (op 0)) st .normal out (9 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 9 + c + 1, y, hcall, by simp [out], hrep', hIn',
    by simpa [out, heapArg, args] using hbout,
    by simpa [out, heapArg, args] using hfchg,
    fun j hj => by simpa [out, heapArg, args] using hblk' j hj,
    fun j hj => by simpa [out, heapArg, args] using hval' j hj,
    fun j hj => by
      simpa [out, heapArg, args, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] using hplace j hj,
    hrespect, ?_, fun r hr => Function.update_of_ne hr _ _⟩
  simp only [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
    sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK, args,
    List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

/-! ### 2. `wireEmitLSFChangeEditsBody`: emit `TreeChange.delete` edits from `LSFChangeAt` -/

/-- Procedure `[chgPtr, outBuf, curCnt]` (`regs 0..2`): reads `c.fDel` from `Read.LSFChangeAt` at
`chgPtr`, appends `(0, e)` (`.delete e`) pairs to `outBuf` starting at index `curCnt`, and returns
`curCnt + c.fDel.length`. -/
@[expose] def wireEmitLSFChangeEditsBody : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 3))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 3)) ;;
  forRange 6 (.const 0) (.reg 4)
    (.assign 7 (.load (.bin .add (.reg 5) (.reg 6))) ;;
     .assign 8 (.bin .add (.reg 1) (.bin .mul (.const 2) (.bin .add (.reg 2) (.reg 6)))) ;;
     .store (.reg 8) (.const 0) ;;
     .store (.bin .add (.reg 8) (.const 1)) (.reg 7)) ;;
  .ret (.bin .add (.reg 2) (.reg 4))

theorem wireEmitLSFChangeEditsBody_noRand : wireEmitLSFChangeEditsBody.NoRand := by
  simp [wireEmitLSFChangeEditsBody, forRange, forUp, Stmt.NoRand]

/-- Execute `wireEmitLSFChangeEditsBody`: appends `c.fDel.map TreeChange.delete` onto existing
`TreeEditsAt mem outBuf pref` in `O(|c.fDel| + 1)` steps. -/
theorem wireEmitLSFChangeEditsBody_runs
    {w chgPtr outBuf pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {c : Read.LSFChange} {pref : List TreeChange}
    (hChg : Read.LSFChangeAt mem chgPtr c)
    (hPref : TreeEditsAt mem outBuf pref)
    (hChgLe : chgPtr + c.words ≤ outBuf + 2 * pref.length)
    (hDelW : ∀ e ∈ c.fDel, e < 2 ^ w)
    (hz : ZeroFrom mem (outBuf + 2 * pref.length))
    (hRoom : outBuf + 2 * (pref.length + c.fDel.length) < 2 ^ w)
    (hw2 : 2 < 2 ^ w) :
    let newEdits := pref ++ c.fDel.map TreeChange.delete
    ∃ out cost,
      Runs w p ω wireEmitLSFChangeEditsBody
        (startState [chgPtr, outBuf, pref.length] mem pos)
        (.returned newEdits.length) out cost ∧
      cost ≤ 45 * c.fDel.length + 40 ∧
      TreeEditsAt out.mem outBuf newEdits ∧
      ZeroFrom out.mem (outBuf + 2 * newEdits.length) ∧
      ∀ a < outBuf + 2 * pref.length, out.mem a = mem a := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hcw : c.words = 2 + c.roots.length + c.fDel.length := by
    simp [Read.LSFChange.words, Read.LSFChange.size]; omega
  let rLen := c.roots.length
  let dLen := c.fDel.length
  let dPtr := chgPtr + 2 + rLen
  let s0 := startState [chgPtr, outBuf, pref.length] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 3 rLen }
  let s2 := { s1 with regs := Function.update s1.regs 4 dLen }
  let s3 := { s2 with regs := Function.update s2.regs 5 dPtr }
  have r1 : Runs w p ω (.assign 3 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨rLen, by simp [Expr.eval, s0, startState, hChg.1, rLen], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 4 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 3))))
      s1 .normal s2 7 :=
    runs_assign_iff.mpr ⟨dLen, by
      have hm := hChg.2.2.1
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show chgPtr + 1 < 2 ^ w by omega,
        show chgPtr + 1 + rLen < 2 ^ w by omega, rLen, dLen, hm], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 5 (.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 3)))
      s2 .normal s3 6 :=
    runs_assign_iff.mpr ⟨dPtr, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, hw2, show chgPtr + 2 < 2 ^ w by omega,
        show chgPtr + 2 + rLen < 2 ^ w by omega, dPtr], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    let cur := pref ++ (c.fDel.take i).map TreeChange.delete
    s.regs 0 = chgPtr ∧ s.regs 1 = outBuf ∧ s.regs 2 = pref.length ∧
    s.regs 3 = rLen ∧ s.regs 4 = dLen ∧ s.regs 5 = dPtr ∧ s.regs 6 = i ∧
    TreeEditsAt s.mem outBuf cur ∧
    ZeroFrom s.mem (outBuf + 2 * (pref.length + i)) ∧
    ∀ a < outBuf + 2 * pref.length, s.mem a = mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 4)
    (P := fun s => s = s3) (Inv := Inv) (fun _ => 30) 0 dLen (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w],
        by simp [s3, s2, s1, s0, startState], by simp [s3, s2, s1, s0, startState],
        by simp [s3, s2, s1, s0, startState], by simp [s3, s2, s1], by simp [s3, s2],
        by simp [s3], by simp, by simpa [s3, s2, s1, s0, startState] using hPref,
        by simpa [s3, s2, s1, s0, startState] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
    (fun _ s _ _ h => by simp [Expr.eval, h.2.2.2.2.1])
    (fun i _ hi s ω' hInv => by
      rcases hInv with ⟨h0, h1, h2, h3, h4, h5, h6, hEd, hZ, hFr⟩
      have hiLen : i < c.fDel.length := hi
      let e := c.fDel[i]'hiLen
      have heW : e < 2 ^ w := hDelW e (List.getElem_mem hiLen)
      have hmE : s.mem (dPtr + i) = e := by
        rw [hFr (dPtr + i) (by dsimp [dPtr]; omega)]
        exact hChg.2.2.2 i hiLen
      let dst := outBuf + 2 * (pref.length + i)
      let t1 := { s with regs := Function.update s.regs 7 e }
      let t2 := { t1 with regs := Function.update t1.regs 8 dst }
      let t3 := { t2 with mem := Function.update t2.mem dst 0 }
      let t4 := { t3 with mem := Function.update t3.mem (dst + 1) e }
      have rt1 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 5) (.reg 6)))) s .normal t1 5 :=
        runs_assign_iff.mpr ⟨e, by
          simp [Expr.eval, BinOp.eval, h5, h6, show dPtr + i < 2 ^ w by dsimp [dPtr]; omega, hmE],
          rfl, rfl, rfl⟩
      have rt2 : Runs w p ω' (.assign 8 (.bin .add (.reg 1) (.bin .mul (.const 2) (.bin .add (.reg 2) (.reg 6)))))
          t1 .normal t2 8 :=
        runs_assign_iff.mpr ⟨dst, by
          simp [Expr.eval, BinOp.eval, t1, h1, h2, h6, hw2,
            show pref.length + i < 2 ^ w by omega,
            show 2 * (pref.length + i) < 2 ^ w by omega,
            show dst < 2 ^ w by dsimp [dst]; omega, dst], rfl, rfl, rfl⟩
      have rt3 : Runs w p ω' (.store (.reg 8) (.const 0)) t2 .normal t3 3 :=
        runs_store_iff.mpr ⟨dst, 0, by simp [Expr.eval, t2], by simp [Expr.eval, Nat.two_pow_pos w],
          rfl, rfl, rfl⟩
      have rt4 : Runs w p ω' (.store (.bin .add (.reg 8) (.const 1)) (.reg 7)) t3 .normal t4 5 :=
        runs_store_iff.mpr ⟨dst + 1, e, by
          simp [Expr.eval, BinOp.eval, t3, t2, hw1, show dst + 1 < 2 ^ w by dsimp [dst]; omega],
          by simp [Expr.eval, t3, t2, t1], rfl, rfl, rfl⟩
      have rstep : Runs w p ω' _ s .normal t4 (5 + (8 + (3 + 5 + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨t1, 5, _, rt1,
          runs_seq_iff.mpr (Or.inr ⟨t2, 8, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 3, 5, rt3, rt4, rfl⟩), rfl⟩), rfl⟩)
      refine ⟨.normal, t4, _, rstep, ⟨⟨by simp [t4, t3, t2, t1, h0], by simp [t4, t3, t2, t1, h1],
        by simp [t4, t3, t2, t1, h2], by simp [t4, t3, t2, t1, h3], by simp [t4, t3, t2, t1, h4],
        by simp [t4, t3, t2, t1, h5], by simp, ?_, ?_, ?_⟩, by simp [t4, t3, t2, t1, h6]⟩, by dsimp; omega⟩
      · have hCurLen : (pref ++ (c.fDel.take i).map TreeChange.delete).length = pref.length + i := by
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hiLen)]
        have hEqTake : pref ++ (c.fDel.take (i + 1)).map TreeChange.delete =
            (pref ++ (c.fDel.take i).map TreeChange.delete) ++ [.delete e] := by
          rw [List.take_succ_eq_append_getElem hiLen, List.map_append, List.map_singleton,
            List.append_assoc]
        rw [hEqTake]
        refine treeEditsAt_append_singleton
          (treeEditsAt_of_agree hEd fun j hj => by
            rw [hCurLen] at hj
            simp [t4, t3, t2, t1, Function.update_of_ne (by dsimp [dst]; omega : outBuf + j ≠ dst + 1),
              Function.update_of_ne (by dsimp [dst]; omega : outBuf + j ≠ dst)])
          (by rw [hCurLen]; simp [t4, t3, dst, treeChangeTag])
          (by rw [hCurLen]; simp [t4, dst, treeChangeEdge])
      · intro a ha
        simp only [t4, t3, t2, t1, Function.update_of_ne (by dsimp [dst]; omega : a ≠ dst + 1),
          Function.update_of_ne (by dsimp [dst]; omega : a ≠ dst)]
        exact hZ a (by omega)
      · intro a ha
        simp only [t4, t3, t2, t1, Function.update_of_ne (by dsimp [dst]; omega : a ≠ dst + 1),
          Function.update_of_ne (by dsimp [dst]; omega : a ≠ dst)]
        exact hFr a ha)
  obtain ⟨o, s4, cLoop, rLoop, hInv4, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv4
  | normal =>
    rcases hInv4 with ⟨_, _, h2, _, h4, _, _, hEd4, hZ4, hFr4⟩
    have hTakeAll : c.fDel.take dLen = c.fDel := List.take_of_length_le le_rfl
    rw [hTakeAll] at hEd4
    have hRetLen : (pref ++ c.fDel.map TreeChange.delete).length = pref.length + dLen := by
      simp [dLen]
    have rRet : Runs w p ω (.ret (.bin .add (.reg 2) (.reg 4))) s4
        (.returned (pref.length + dLen)) s4 4 :=
      runs_ret_iff.mpr ⟨pref.length + dLen, by
        simp [Expr.eval, BinOp.eval, h2, h4, show pref.length + dLen < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rAll : Runs w p ω wireEmitLSFChangeEditsBody s0 (.returned (pref.length + dLen)) s4
        (3 + (7 + (6 + (cLoop + 4 + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 7, _, r2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 6, _, r3,
            runs_seq_iff.mpr (Or.inr ⟨s4, cLoop, 4, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 30) 0 dLen = dLen * 30 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    rw [hRetLen]
    exact ⟨s4, _, rAll, by dsimp [dLen] at hcLoop ⊢; omega, hEd4, hZ4, hFr4⟩

/-! ### 3. `wireCollectInsertedEdgesBody`: collect all inserted edges of `U` (re-insertions included) -/

/-- Exact list of edge IDs inserted by a batch `U` in batch order (re-insertions included). -/
@[expose] def batchInsertedEdges : List Update → List ℕ
  | [] => []
  | .insert e _ _ :: rest => e :: batchInsertedEdges rest
  | .delete _ :: rest => batchInsertedEdges rest
  | .split _ _ _ _ :: rest => batchInsertedEdges rest

theorem batchInsertedEdges_length_le (U : List Update) :
    (batchInsertedEdges U).length ≤ U.length := by
  induction U with
  | nil => simp [batchInsertedEdges]
  | cons u rest ih =>
    cases u <;> simp [batchInsertedEdges] <;> omega

theorem batchInsertedEdges_append (U₁ U₂ : List Update) :
    batchInsertedEdges (U₁ ++ U₂) = batchInsertedEdges U₁ ++ batchInsertedEdges U₂ := by
  induction U₁ with
  | nil => simp [batchInsertedEdges]
  | cons u rest ih =>
    cases u <;> simp [batchInsertedEdges, ih]

theorem mem_batchInsertedEdges_iff (U : List Update) (e : ℕ) :
    e ∈ batchInsertedEdges U ↔ ∃ u ∈ U, u.Inserts e := by
  induction U with
  | nil => simp [batchInsertedEdges]
  | cons u rest ih =>
    cases u with
    | insert e₀ _ _ =>
      simp only [batchInsertedEdges, List.mem_cons, ih, Update.Inserts, exists_eq_or_imp]
      exact ⟨fun h => h.elim (fun he => Or.inl he.symm) Or.inr,
        fun h => h.elim (fun he => Or.inl he.symm) Or.inr⟩
    | delete _ => simp [batchInsertedEdges, ih, Update.Inserts]
    | split _ _ _ _ => simp [batchInsertedEdges, ih, Update.Inserts]

/-- Procedure `[batchPtr, outBuf]` (`regs 0..1`): scans a `SmallBatchAt` batch at `batchPtr`,
writes every edge `e` inserted by an `.insert e u v` update into `outBuf` as a flat `ListAt`
(re-insertions included), and returns the count. -/
@[expose] def wireCollectInsertedEdgesBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.bin .add (.reg 0) (.const 1)) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 2)
    (.assign 6 (.load (.reg 3)) ;;
     .cond (.bin .eq (.reg 6) (.const 0))
       (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
        .assign 3 (.bin .add (.reg 3) (.const 4)))
       (.cond (.bin .eq (.reg 6) (.const 1))
         (.assign 3 (.bin .add (.reg 3) (.const 2)))
         (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
          .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
          .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8))))) ;;
  .ret (.reg 4)

theorem wireCollectInsertedEdgesBody_noRand : wireCollectInsertedEdgesBody.NoRand := by
  simp [wireCollectInsertedEdgesBody, forRange, forUp, Stmt.NoRand]

/-- Execute `wireCollectInsertedEdgesBody`: writes `batchInsertedEdges U` to `outBuf` in
`O(|U| + 1)` steps. -/
theorem wireCollectInsertedEdgesBody_runs
    {w batchPtr outBuf totalWords pos : ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {G : MGraph} {U : List Update}
    (hSmall : SmallBatchAt mem batchPtr G U totalWords)
    (hBatchW : ∀ j < totalWords, mem (batchPtr + j) < 2 ^ w)
    (hBatchLe : batchPtr + totalWords ≤ outBuf)
    (hz : ZeroFrom mem outBuf)
    (hRoom : outBuf + U.length < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    let ins := batchInsertedEdges U
    ∃ out cost,
      Runs w p ω wireCollectInsertedEdgesBody
        (startState [batchPtr, outBuf] mem pos)
        (.returned ins.length) out cost ∧
      cost ≤ 55 * U.length + 35 ∧
      ListAt out.mem outBuf ins ∧
      ZeroFrom out.mem (outBuf + ins.length) ∧
      ∀ a < outBuf, out.mem a = mem a := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  obtain ⟨⟨hTotPos, hLen0, hBody0⟩, _⟩ := hSmall
  have hULenW : U.length < 2 ^ w := by simpa [hLen0] using hBatchW 0 (by omega)
  let s0 := startState [batchPtr, outBuf] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 2 U.length }
  let s2 := { s1 with regs := Function.update s1.regs 3 (batchPtr + 1) }
  let s3 := { s2 with regs := Function.update s2.regs 4 0 }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨U.length, by simp [Expr.eval, s0, startState, hLen0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.bin .add (.reg 0) (.const 1))) s1 .normal s2 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show batchPtr + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.const 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  let Inv (i : ℕ) (s : State) : Prop :=
    ∃ ptr remW,
      let pref := batchInsertedEdges (U.take i)
      s.regs 0 = batchPtr ∧ s.regs 1 = outBuf ∧ s.regs 2 = U.length ∧
      s.regs 3 = ptr ∧ s.regs 4 = pref.length ∧ s.regs 5 = i ∧
      batchPtr + 1 ≤ ptr ∧ ptr + remW = batchPtr + totalWords ∧
      BatchBodyAt mem ptr (G.applyBatch (U.take i)) (U.drop i) remW ∧
      ListAt s.mem outBuf pref ∧
      ZeroFrom s.mem (outBuf + pref.length) ∧
      ∀ a < outBuf, s.mem a = mem a
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (P := fun s => s = s3) (Inv := Inv) (fun _ => 43) 0 U.length (Nat.zero_le _) hw1
    (fun _ => hULenW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, Nat.two_pow_pos w],
        batchPtr + 1, totalWords - 1,
        by simp [s3, s2, s1, s0, startState], by simp [s3, s2, s1, s0, startState],
        by simp [s3, s2, s1], by simp [s3, s2], by simp [s3, batchInsertedEdges], by simp,
        le_rfl, by omega, by simpa [MGraph.applyBatch] using hBody0,
        fun _ h => by simp [batchInsertedEdges] at h,
        by simpa [s3, s2, s1, s0, startState, batchInsertedEdges] using hz, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => by rcases h with ⟨_, _, _, _, _, _, _, h5, _⟩; exact h5)
    (fun _ s _ _ h => by rcases h with ⟨_, _, _, _, h2, _⟩; simp [Expr.eval, h2])
    (fun i _ hi s ω' ⟨ptr, remW, h0, h1, h2, h3, h4, h5, hPtrLo, hPtrEnd, hBody, hList, hZ, hFr⟩ => by
      have hDrop : U.drop i = U[i] :: U.drop (i + 1) := List.drop_eq_getElem_cons hi
      rw [hDrop] at hBody
      obtain ⟨uLen, hULenLe, hUAt, hRest⟩ := hBody
      have hTakeSucc : U.take (i + 1) = U.take i ++ [U[i]] := List.take_succ_eq_append_getElem hi
      have hPrefLe : (batchInsertedEdges (U.take i)).length ≤ i :=
        (batchInsertedEdges_length_le _).trans (by simp [List.length_take, Nat.le_of_lt hi])
      have hGStep : G.applyBatch (U.take (i + 1)) = (G.applyBatch (U.take i)).applyUpdate U[i] := by
        unfold MGraph.applyBatch
        rw [hTakeSucc, List.foldl_append]
        rfl
      cases hu : U[i] with
      | insert e u v =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 0 := by simpa using hLA 0 (by simp)
        have hE : mem (ptr + 1) = e := by simpa using hLA 1 (by simp)
        have hm0 : s.mem ptr = 0 := (hFr ptr (by omega)).trans hTag
        have hm1 : s.mem (ptr + 1) = e := (hFr (ptr + 1) (by omega)).trans hE
        have heW : e < 2 ^ w := by
          have := hBatchW (ptr + 1 - batchPtr) (by omega)
          rwa [show batchPtr + (ptr + 1 - batchPtr) = ptr + 1 by omega, hE] at this
        let pref := batchInsertedEdges (U.take i)
        let t1 := { s with regs := Function.update s.regs 6 0 }
        let t2 := { t1 with regs := Function.update t1.regs 7 e }
        let t3 := { t2 with mem := Function.update t2.mem (outBuf + pref.length) e }
        let t4 := { t3 with regs := Function.update t3.regs 4 (pref.length + 1) }
        let t5 := { t4 with regs := Function.update t4.regs 3 (ptr + 4) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 1)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨e, by
            simp [Expr.eval, BinOp.eval, t1, h3, hw1, show ptr + 1 < 2 ^ w by omega, hm1],
            rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.store (.bin .add (.reg 1) (.reg 4)) (.reg 7)) t2 .normal t3 5 :=
          runs_store_iff.mpr ⟨outBuf + pref.length, e, by
            have hOutPl : outBuf + (batchInsertedEdges (U.take i)).length < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t2, t1, h1, h4, pref, hOutPl],
            by simp [Expr.eval, t2], rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 4 (.bin .add (.reg 4) (.const 1))) t3 .normal t4 4 :=
          runs_assign_iff.mpr ⟨pref.length + 1, by
            have hplW : (batchInsertedEdges (U.take i)).length + 1 < 2 ^ w := by omega
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h4, hw1, pref, hplW], rfl, rfl, rfl⟩
        have rt5 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 4))) t4 .normal t5 4 :=
          runs_assign_iff.mpr ⟨ptr + 4, by
            simp [Expr.eval, BinOp.eval, t4, t3, t2, t1, h3, hw4, show ptr + 4 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rCond : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.cond (.bin .eq (.reg 6) (.const 1)) (.assign 3 (.bin .add (.reg 3) (.const 2)))
                (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                 .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                 .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))))
            t1 .normal t5 (3 + (5 + (5 + (4 + 4 + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1, Nat.two_pow_pos w],
            by simpa only [one_ne_zero, ↓reduceIte] using
              runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
                runs_seq_iff.mpr (Or.inr ⟨t3, 5, _, rt3,
                  runs_seq_iff.mpr (Or.inr ⟨t4, 4, 4, rt4, rt5, rfl⟩), rfl⟩), rfl⟩), rfl⟩
        have rstep : Runs w p ω' _ s .normal t5 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rCond, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) = pref ++ [e] := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; rfl
        refine ⟨.normal, t5, _, rstep, ⟨⟨ptr + 4, remW - 4,
          by simp [t5, t4, t3, t2, t1, h0], by simp [t5, t4, t3, t2, t1, h1],
          by simp [t5, t4, t3, t2, t1, h2], by simp [t5],
          by rw [hNewPref]; simp [t5, t4, pref], by simp,
          by omega, by omega, by rw [hGStep]; exact hRest, ?_, ?_, ?_⟩,
          by simp [t5, t4, t3, t2, t1, h5]⟩, by dsimp only; omega⟩
        · rw [hNewPref]
          intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hlt : j < pref.length
          · rw [List.getElem_append_left hlt]
            change Function.update s.mem (outBuf + pref.length) e (outBuf + j) = pref[j]
            rw [Function.update_of_ne (by omega)]
            exact hList j hlt
          · have hjeq : j = pref.length := by omega
            subst hjeq
            simp [t5, t4, t3]
        · rw [hNewPref]; intro a ha
          simp only [List.length_append, List.length_singleton] at ha
          change Function.update s.mem (outBuf + pref.length) e a = 0
          rw [Function.update_of_ne (by omega)]
          exact hZ a (by dsimp only [pref] at ha; omega)
        · intro a ha
          change Function.update s.mem (outBuf + pref.length) e a = mem a
          rw [Function.update_of_ne (by omega)]
          exact hFr a ha
      | delete e =>
        rw [hu] at hUAt
        obtain ⟨rfl, hLA⟩ := hUAt
        have hTag : mem ptr = 1 := by simpa using hLA 0 (by simp)
        have hm0 : s.mem ptr = 1 := (hFr ptr (by omega)).trans hTag
        let t1 := { s with regs := Function.update s.regs 6 1 }
        let t2 := { t1 with regs := Function.update t1.regs 3 (ptr + 2) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 3 (.bin .add (.reg 3) (.const 2))) t1 .normal t2 4 :=
          runs_assign_iff.mpr ⟨ptr + 2, by
            simp [Expr.eval, BinOp.eval, t1, h3, show 2 < 2 ^ w by omega, show ptr + 2 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have rIn : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 1)) (.assign 3 (.bin .add (.reg 3) (.const 2)))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
               .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
               .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8))))
            t1 .normal t2 (3 + 4 + 1) :=
          runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, BinOp.eval, t1, hw1], by simpa using rt2, rfl⟩
        have rOut : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.cond (.bin .eq (.reg 6) (.const 1)) (.assign 3 (.bin .add (.reg 3) (.const 2)))
                (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                 .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                 .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))))
            t1 .normal t2 (3 + (3 + 4 + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, Nat.two_pow_pos w],
            by simpa using rIn, rfl⟩
        have rstep : Runs w p ω' _ s .normal t2 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rOut, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) = batchInsertedEdges (U.take i) := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; simp [batchInsertedEdges]
        refine ⟨.normal, t2, _, rstep, ⟨⟨ptr + 2, remW - 2,
          by simp [t2, t1, h0], by simp [t2, t1, h1], by simp [t2, t1, h2], by simp [t2],
          by rw [hNewPref]; simp [t2, t1, h4], by simp, by omega, by omega,
          by rw [hGStep]; exact hRest, by rw [hNewPref]; exact hList,
          by rw [hNewPref]; exact hZ, hFr⟩, by simp [t2, t1, h5]⟩, by dsimp only; omega⟩
      | split v v' St Sh =>
        rw [hu] at hUAt
        have hSp : ∃ tag, (tag = 2 ∨ tag = 3) ∧ ∃ lT lH : List ℕ,
            uLen = 5 + lT.length + lH.length ∧
            ListAt mem ptr ([tag, v, v', lT.length, lH.length] ++ lT ++ lH) := by
          rcases hUAt with ⟨lT, lH, _, _, _, _, hEq, hLA⟩ | ⟨lT, lH, _, _, _, _, hEq, hLA⟩
          · exact ⟨2, Or.inl rfl, lT, lH, hEq, hLA⟩
          · exact ⟨3, Or.inr rfl, lT, lH, hEq, hLA⟩
        obtain ⟨tag, hTag23, lT, lH, hULenEq, hLA⟩ := hSp
        have hm0 : s.mem ptr = tag := by
          have h0' := hLA 0 (by simp)
          simpa using (hFr ptr (by omega)).trans h0'
        have hm3 : s.mem (ptr + 3) = lT.length := by
          have h3' := hLA 3 (by simp)
          simpa using (hFr (ptr + 3) (by omega)).trans h3'
        have hm4 : s.mem (ptr + 4) = lH.length := by
          have h4' := hLA 4 (by simp)
          simpa using (hFr (ptr + 4) (by omega)).trans h4'
        let t1 := { s with regs := Function.update s.regs 6 tag }
        let t2 := { t1 with regs := Function.update t1.regs 7 lT.length }
        let t3 := { t2 with regs := Function.update t2.regs 8 lH.length }
        let t4 := { t3 with regs := Function.update t3.regs 3 (ptr + uLen) }
        have rt1 : Runs w p ω' (.assign 6 (.load (.reg 3))) s .normal t1 3 :=
          runs_assign_iff.mpr ⟨tag, by simp [Expr.eval, h3, hm0], rfl, rfl, rfl⟩
        have rt2 : Runs w p ω' (.assign 7 (.load (.bin .add (.reg 3) (.const 3)))) t1 .normal t2 5 :=
          runs_assign_iff.mpr ⟨lT.length, by
            simp [Expr.eval, BinOp.eval, t1, h3, show 3 < 2 ^ w by omega, show ptr + 3 < 2 ^ w by omega, hm3],
            rfl, rfl, rfl⟩
        have rt3 : Runs w p ω' (.assign 8 (.load (.bin .add (.reg 3) (.const 4)))) t2 .normal t3 5 :=
          runs_assign_iff.mpr ⟨lH.length, by
            simp [Expr.eval, BinOp.eval, t2, t1, h3, hw4, show ptr + 4 < 2 ^ w by omega, hm4],
            rfl, rfl, rfl⟩
        have rt4 : Runs w p ω' (.assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))
            t3 .normal t4 8 :=
          runs_assign_iff.mpr ⟨ptr + uLen, by
            simp [Expr.eval, BinOp.eval, t3, t2, t1, h3, hw5, show ptr + 5 < 2 ^ w by omega,
              show ptr + 5 + lT.length < 2 ^ w by omega,
              show ptr + 5 + lT.length + lH.length = ptr + uLen by omega,
              show ptr + uLen < 2 ^ w by omega], rfl, rfl, rfl⟩
        have rBr : Runs w p ω' _ t1 .normal t4 (5 + (5 + 8 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨t2, 5, _, rt2,
            runs_seq_iff.mpr (Or.inr ⟨t3, 5, 8, rt3, rt4, rfl⟩), rfl⟩)
        have hTagNe0 : tag ≠ 0 := by omega
        have hTagNe1 : tag ≠ 1 := by omega
        have rIn : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 1)) (.assign 3 (.bin .add (.reg 3) (.const 2)))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
               .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
               .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8))))
            t1 .normal t4 (3 + (5 + (5 + 8 + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, hw1, hTagNe1], by simpa using rBr, rfl⟩
        have rOut : Runs w p ω'
            (.cond (.bin .eq (.reg 6) (.const 0))
              (.assign 7 (.load (.bin .add (.reg 3) (.const 1))) ;;
               .store (.bin .add (.reg 1) (.reg 4)) (.reg 7) ;;
               .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
               .assign 3 (.bin .add (.reg 3) (.const 4)))
              (.cond (.bin .eq (.reg 6) (.const 1)) (.assign 3 (.bin .add (.reg 3) (.const 2)))
                (.assign 7 (.load (.bin .add (.reg 3) (.const 3))) ;;
                 .assign 8 (.load (.bin .add (.reg 3) (.const 4))) ;;
                 .assign 3 (.bin .add (.bin .add (.bin .add (.reg 3) (.const 5)) (.reg 7)) (.reg 8)))))
            t1 .normal t4 (3 + (3 + (5 + (5 + 8 + 1) + 1) + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, _, by simp [Expr.eval, BinOp.eval, t1, Nat.two_pow_pos w, hTagNe0],
            by simpa using rIn, rfl⟩
        have rstep : Runs w p ω' _ s .normal t4 _ :=
          runs_seq_iff.mpr (Or.inr ⟨t1, 3, _, rt1, rOut, rfl⟩)
        have hNewPref : batchInsertedEdges (U.take (i + 1)) = batchInsertedEdges (U.take i) := by
          rw [hTakeSucc, batchInsertedEdges_append, hu]; simp [batchInsertedEdges]
        refine ⟨.normal, t4, _, rstep, ⟨⟨ptr + uLen, remW - uLen,
          by simp [t4, t3, t2, t1, h0], by simp [t4, t3, t2, t1, h1],
          by simp [t4, t3, t2, t1, h2], by simp [t4],
          by rw [hNewPref]; simp [t4, t3, t2, t1, h4], by simp,
          by omega, by omega, by rw [hGStep]; exact hRest, by rw [hNewPref]; exact hList,
          by rw [hNewPref]; exact hZ, hFr⟩, by simp [t4, t3, t2, t1, h5]⟩, by dsimp only; omega⟩)
  obtain ⟨o, s4, cLoop, rLoop, hInv4, hcLoop⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv4
  | normal =>
    rcases hInv4 with ⟨_, _, _, _, _, _, h4, _, _, _, _, hList4, hZ4, hFr4⟩
    have hTakeAll : U.take U.length = U := List.take_of_length_le le_rfl
    rw [hTakeAll] at h4 hList4 hZ4
    have rRet : Runs w p ω (.ret (.reg 4)) s4 (.returned (batchInsertedEdges U).length) s4 2 :=
      runs_ret_iff.mpr ⟨(batchInsertedEdges U).length, by simp [Expr.eval, h4], rfl, rfl, rfl⟩
    have rAll : Runs w p ω wireCollectInsertedEdgesBody s0
        (.returned (batchInsertedEdges U).length) s4 (3 + (4 + (2 + (cLoop + 2 + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
        runs_seq_iff.mpr (Or.inr ⟨s2, 4, _, r2,
          runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
            runs_seq_iff.mpr (Or.inr ⟨s4, cLoop, 2, rLoop, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hrc : rangeCost (fun _ => 43) 0 U.length = U.length * 43 := by simp [rangeCost]
    simp only [Expr.size, hrc] at hcLoop
    exact ⟨s4, _, rAll, by omega, hList4, hZ4, hFr4⟩

end MinCostFlow.MinRatio
