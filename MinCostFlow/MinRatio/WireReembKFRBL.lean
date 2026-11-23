module

public import MinCostFlow.MinRatio.WireCoreOpsKFBL
public import MinCostFlow.MinRatio.WireSelectUpdate
import WordRAM.Tactic

/-!
# Op `0` under the contract with re-embedded lists (`WireReembKFRBL`)

The contract `sparseCoreOrdMachineContractKFRBL` (`SparseCore/Program/AssemblyContractLayout.lean`)
is `KFBL` with one more fact in the post of op `0`: for every branch `j < k`, the two words at
`heap + 1 + 4 k + 2 j` and `heap + 2 + 4 k + 2 j` give a list that `readList` reads as
`reemb a.st U ord' j`, for the batch `U` and the new order `ord'` of the call. The select heap
needs this list as a `ReembListAt` (`WireSelectUpdate.lean`).

* `reembListAt_of_readList`: a list read by `readList` is a `ReembListAt`.
* `ordCoreUpdateKFRBL_runs`: the run of op `0` under `KFRBL`. It has the conclusions of
  `ordCoreUpdateKFBL_runs` (`WireCoreOpsKFBL.lean`), and for every branch `j < k` the list of
  re-embedded edges as a `ReembListAt`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- The words that `readList` reads from `ptr` form a `ReembListAt` of length `len`. -/
theorem reembListAt_of_readList {mem : ℕ → ℕ} {ptr len : ℕ} {l : List ℕ}
    (h : readList mem ptr len = l) : ReembListAt mem ptr len l := by
  subst h
  refine ⟨by simp [readList], fun i hi => ?_⟩
  simp [readList]

section Execution

/-- Execute `ordCoreUpdateStmt` (op `0`) against `sparseCoreOrdMachineContractKFRBL`. The result
is the one of `ordCoreUpdateKFBL_runs`, and for every branch `j < k` the list at the two words
`heap + 1 + 4 k + 2 j`, `heap + 2 + 4 k + 2 j` is the re-embedded list `reemb a.st U ord' j` of
the step, for the batch `U` and the order `ord'` that op `0` reads. -/
theorem ordCoreUpdateKFRBL_runs
    {w L depth k M N vCap eCap capExp init handle graph batch words edits editWords lengths
      gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {reemb : ToolReembFn tool}
    {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFRBL fmt L depth tool reemb initialGraph k M N vCap eCap
        capExp P allocation))
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
      (∀ j < k, ReembListAt out.mem (out.mem (heap + 1 + 4 * k + 2 * j))
        (out.mem (heap + 2 + 4 * k + 2 * j))
        (reemb a.st (ordUpdateBatch a args st.mem) (ordUpdateOrder a args st.mem) j)) ∧
      (∀ j < k, OrdEditsForBatch (tool.S a.st j) (batches j)
        (readOrdEdits out.mem (out.mem (heap + 3 + 4 * j)))) ∧
      (∀ j < k, OrdEditsValidFor vCap eCap (tool.rot a.st j)
        (readOrdEdits out.mem (out.mem (heap + 3 + 4 * j)))) ∧
      R.Respects (R.foot handle x) heap (allocation 0 args) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (tool.cost a'.st - tool.cost a.st +
          (k + 1) * (words + editWords + 1) * SparseCore.bundleLogFactor M N) +
          R.phi handle x st.mem + 10 ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  dsimp only
  let args := [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 0 handle a x args st.mem st.pos ω hwords rfl hrep
      ⟨⟨hpre, by simpa [args] using hvalid⟩, hblocks⟩ hfoot hz hroom
  obtain ⟨⟨⟨hnext, hbout⟩, hreemb⟩, hblk', hval'⟩ := hpost
  have hIn' := sparseCoreOrdMachineContract_update_input (fmt := fmt) (L := L)
    (tool := tool) (initialGraph := initialGraph) (k := k) (M := M) (N := N)
    (vCap := vCap) (eCap := eCap) (P := P) (allocation := allocation) hpre ⟨hnext, hbout⟩
  subst hnext
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st
      [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4] =
        some args := by
    simp [evalArgs, Expr.eval, args, hh, hg, hb, hbw, he, hew, hl, hc, hp]
  have hcall : Runs w p ω (ordCoreUpdateStmt (op 0)) st .normal out (9 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 9 + c + 1, y, hcall, by simp [out], hrep', hIn',
    by simpa [out, heapArg, args] using hbout,
    fun j hj => reembListAt_of_readList (by simpa [out, heapArg, args] using hreemb j hj),
    fun j hj => by simpa [out, heapArg, args] using hblk' j hj,
    fun j hj => by simpa [out, heapArg, args] using hval' j hj, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  simp only [sparseCoreOrdMachineContractKFRBL, sparseCoreOrdMachineContractKFRB,
    sparseCoreOrdMachineContractKFR, sparseCoreOrdMachineContractKF,
    sparseCoreOrdMachineContractK, args, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

end Execution

end MinCostFlow.MinRatio
