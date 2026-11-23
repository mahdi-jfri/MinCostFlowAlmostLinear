module

public import MinCostFlow.MinRatio.WireCoreReadKFBL
import WordRAM.Tactic

/-!
# A bound on the caps of the forest that op `2` returns

Phase 1 of the deep shift copies the active forest of level `i` to fresh memory before it
restarts level `i` in place (`shiftDeepCollectOld`). The copy costs and uses
`dynGraphSize vc ec` words, where `(vc, ec)` are the caps of the forest that op `2` returns.
The layout contract `sparseCoreOrdMachineContractKFBL` with `SparseCoreReadoutFootAt` says where
this forest lies, but not how large its caps are. Op `3` returns the graph at the caps of the
level, but op `2` returns the forest at caps of its own.

So the deep shift needs one more fact of the module: the forest of op `2` has caps of size at
most `fcap`. In the sparse-core program the forest of a branch has the caps `(vCap, tCap)` with
`tCap ≤ 2 * (vCap + eCap + 2) ^ 2`, so the fact
holds there with `fcap = dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)`.
* `SparseCoreForestCapAt`: op `2` runs as in `SparseCoreReadoutFootAt.op2_runs`, and the caps of
  the forest have size at most `fcap`.
* `ordCoreReadLSFKFBLCap_runs`: `ordCoreReadLSFKFBL_runs` with this bound.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Op `2` under the layout contract, with a bound `fcap` on the size of the caps of the forest it
returns. It is the field `op2_runs` of `SparseCoreReadoutFootAt` with the extra conjunct
`dynGraphSize forestVCap forestECap ≤ fcap`. -/
structure SparseCoreForestCapAt {w : ℕ} (fmt : Num.Format w) (L depth : ℕ)
    (tool : SparseCoreRestartTool) (initialGraph : MGraph) (k M N vCap eCap capExp : ℕ)
    (P : SparseCoreOrdParams) (allocation : ℕ → List ℕ → ℕ) (fcap : ℕ)
    (R : DSRep (SparseCoreOrdAbs tool)) (p : Program) (op : ℕ → ℕ) : Prop where
  op2_runs :
    let D := sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation
    ∀ (b : ℕ) (a : SparseCoreOrdAbs tool) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some b →
      R.rep b a x mem → D.pre 2 a args mem → (∀ addr, R.foot b x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 2 a args mem < 2 ^ w →
      ∃ body, p.procs[op 2]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep b a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         let fBase := st'.mem (cur + 1)
         let stDesc := st'.mem (cur + 3)
         let Lw := st'.mem (cur + 4)
         ∃ forestVCap forestECap,
           Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
           LSFAt st'.mem cur forestVCap forestECap fmt.limbBits Lw fmt.precision a.G.E
             (tool.lsfs a.st br) ∧
           fBase + dynGraphSize forestVCap forestECap ≤ cur ∧
           (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize forestVCap forestECap →
             R.foot b x' addr ∨ (cur ≤ addr ∧ addr < o.value)) ∧
           stDesc + 2 ≤ cur ∧
           (∀ e ∈ a.G.E, st'.mem stDesc + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw, R.foot b x' (st'.mem stDesc + e * Lw + t) ∨
               (cur ≤ st'.mem stDesc + e * Lw + t ∧ st'.mem stDesc + e * Lw + t < o.value)) ∧
           (∀ e ∈ a.G.E, st'.mem (stDesc + 1) + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw, R.foot b x' (st'.mem (stDesc + 1) + e * Lw + t) ∨
               (cur ≤ st'.mem (stDesc + 1) + e * Lw + t ∧ st'.mem (stDesc + 1) + e * Lw + t < o.value)) ∧
           dynGraphSize forestVCap forestECap ≤ fcap) ∧
        R.Respects (R.foot b x) (heapArg args) (D.space 2 a args mem) mem o.value b x' st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost 2 a args mem + R.phi b x mem

variable {w L depth k M N vCap eCap capExp fcap : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {P : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

/-- Execute `ordCoreReadLSFStmt` (op `2`) under `SparseCoreForestCapAt`: the results of
`ordCoreReadLSFKFBL_runs`, and the caps of the forest have size at most `fcap`. -/
theorem ordCoreReadLSFKFBLCap_runs {branch handle graph heap : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hCap : SparseCoreForestCapAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation fcap R p op)
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
      (∃ vc ec, LSFAt out.mem heap vc ec fmt.limbBits (out.mem (heap + 4)) fmt.precision a.G.E
          (tool.lsfs a.st branch) ∧
        out.mem (heap + 1) + dynGraphSize vc ec ≤ heap ∧
        (∀ addr, out.mem (heap + 1) ≤ addr → addr < out.mem (heap + 1) + dynGraphSize vc ec →
          R.foot handle y addr ∨ (heap ≤ addr ∧ addr < ret)) ∧
        dynGraphSize vc ec ≤ fcap) ∧
      R.Respects (R.foot handle x) heap 5 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, graph, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hrespect, hcost⟩ :=
    hCap.op2_runs handle a x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, graph, heap, rfl, hj, hG, hgEnd⟩ hfoot hz hroom
  obtain ⟨vc, ec, hLw, hlsf, hfEnd, hfIn, -, -, -, hfcap⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hLw hlsf hfEnd hfIn
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 6, .reg 4] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hg, hp]
  have hcall : Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 4 + c + 1, y, hcall, by simp [out], hrep', hLw,
    ⟨vc, ec, hlsf, hfEnd, hfIn, hfcap⟩, hrespect, ?_, fun r hr => Function.update_of_ne hr _ _⟩
  change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

end MinCostFlow.MinRatio
