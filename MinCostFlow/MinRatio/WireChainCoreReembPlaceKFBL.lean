module

public import MinCostFlow.MinRatio.WireChainCoreSelectOutKFBL

/-!
# Where op `0` leaves the re-embedding lists (`WireChainCoreReembPlaceKFBL`)

At a non-rebuilt level the select part of `Update` reads the re-embedding list of the active
branch from the select-output slot of the level (`UpdateCoreSelectOutAt`). The contract of op `0`
under `sparseCoreOrdMachineContractKFRBL` says only that the list is at the pointer that op `0`
writes, and nothing on where that pointer points. A list of unknown place cannot be copied: the
addresses of its words need not be machine words, and its length bounds no space. The companion
`SparseCoreReembPlaceAt` says that the list of each branch lies in the output region of the call,
as the change records of `BranchOutFChgAt` do. `ordCoreUpdateKFRBLPlace_runs` adds this fact to
`ordCoreUpdateKFRBLOut_runs`, on the same run, since op `0` is deterministic (`Runs.det`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Companion of op `0` (`update`) under `sparseCoreOrdMachineContractKFBL`: in every run of op `0`
with heap pointer `h`, the re-embedding list of each branch `j < k`, whose pointer and length op `0`
writes at `h + 1 + 4 k + 2 j` and `h + 2 + 4 k + 2 j`, lies in the output region `[h, o.value)` of
the call. -/
structure SparseCoreReembPlaceAt {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep (SparseCoreOrdAbs tool)) (p : Program) (op : ℕ → ℕ) : Prop where
  op0_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 0 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 0 a args mem < 2 ^ w →
      ∃ body, p.procs[op 0]? = some body ∧ ∃ o st' c,
        Runs w p ω body (startState args mem pos) o st' c ∧
        ∀ j < k, heapArg args ≤ st'.mem (heapArg args + 1 + 4 * k + 2 * j) ∧
          st'.mem (heapArg args + 1 + 4 * k + 2 * j) +
            st'.mem (heapArg args + 2 + 4 * k + 2 * j) ≤ o.value

/-- `SparseCoreReembPlaceAt` at every level `j < d` of the chain, with the caps and sizes of
`UpdateCoreOp0FootKFBL`. -/
@[expose] def UpdateCoreReembPlaceKFBL {w : ℕ} (fmt : Num.Format w) (L vCap eCap capExp : ℕ)
    (cfg : Alg2Config) (Psc : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program) (op : ℕ → ℕ) : Prop :=
  ∀ j < cfg.P.d, ∀ G : MGraph, G.n ≤ G.m + 1 →
    SparseCoreReembPlaceAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T G cfg.P.k
      (levelM cfg.TP cfg.P j) cfg.N₀ vCap eCap capExp Psc allocation Rcore p op

/-- `ordCoreUpdateKFRBLOut_runs` with the place of the re-embedding lists: each list lies in the
output region `[heap, ret)` of the call. -/
theorem ordCoreUpdateKFRBLPlace_runs
    {w L depth k M N vCap eCap capExp edMul handle graph batch words edits editWords lengths
      gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph} {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {init : ℕ} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hImpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N vCap eCap capExp P
        allocation))
    (hOut : SparseCoreUpdateOutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation edMul R p op)
    (hPlace : SparseCoreReembPlaceAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
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
      (∀ j < k, ReembListAt out.mem
        (out.mem (heap + 1 + 4 * k + 2 * j)) (out.mem (heap + 2 + 4 * k + 2 * j))
        (reemb a.st (ordUpdateBatch a args st.mem) (ordUpdateOrder a args st.mem) j)) ∧
      (∀ j < k, heap ≤ out.mem (heap + 1 + 4 * k + 2 * j) ∧
        out.mem (heap + 1 + 4 * k + 2 * j) + out.mem (heap + 2 + 4 * k + 2 * j) ≤ ret) ∧
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
      ∀ r, r ≠ 5 → out.regs r = st.regs r := by
  intro args a' batches
  obtain ⟨out, ret, cost, y, hcall, hreg5, hrep', hIn', hBr, hFChg, hReemb, hFor, hVal, hSlots,
    hResp, hCost, hRegs⟩ :=
    ordCoreUpdateKFRBLOut_runs hImpl hOut hh hg hb hbw he hew hl hc hp hwords hrep hpre hvalid
      hblocks hfoot hz hroom
  obtain ⟨vargs, body1, o1, after1, c1, hargs1, hbody1, hrun1, _, hOutEq, _⟩ :=
    runs_call_iff.mp hcall
  have hArgsEq : vargs = args := by
    have hEval : evalArgs w st
        [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4] =
          some args := by
      simp [evalArgs, Expr.eval, args, hh, hg, hb, hbw, he, hew, hl, hc, hp]
    exact Option.some.inj (hargs1.symm.trans hEval)
  subst hArgsEq
  obtain ⟨body2, hbody2, o2, st2, c2, hrun2, hplace2⟩ :=
    hPlace.op0_runs handle a x args st.mem st.pos ω hwords rfl hrep
      ⟨⟨hpre, by simpa [args] using hvalid⟩, hblocks⟩ hfoot hz hroom
  have hBodyEq : body2 = body1 := Option.some.inj (hbody2.symm.trans hbody1)
  subst hBodyEq
  obtain ⟨hoEq, hstEq, _⟩ := hrun2.det hrun1
  subst hoEq hstEq
  have hMemEq : out.mem = st2.mem := by rw [hOutEq]
  have hRetEq : ret = o2.value := by
    rw [← hreg5, hOutEq]
    simp
  refine ⟨out, ret, cost, y, hcall, hreg5, hrep', hIn', hBr, hFChg, hReemb, fun j hj => ?_, hFor,
    hVal, hSlots, hResp, hCost, hRegs⟩
  rw [hMemEq, hRetEq]
  simpa [heapArg, args] using hplace2 j hj

end MinCostFlow.MinRatio
