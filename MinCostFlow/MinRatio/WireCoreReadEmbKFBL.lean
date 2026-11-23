module

public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
public import MinCostFlow.MinRatio.OrdCoreOps
public import MinCostFlow.MinRatio.SelectEmbCopy
import WordRAM.Tactic

/-!
# Embedding readout under the layout contract and bridge to `SelEmbSrcOk` (`WireCoreReadEmbKFBL`)

Op `4` of the sparse-core contract reads the core-to-sparsifier embedding of the active branch.
Under `sparseCoreOrdMachineContractKFBL` and `SparseCoreReadoutFootAt`
(`SparseCore/Program/AssemblyContractLayout.lean`), op `4` guarantees:
* `MEmbBounded` below `cur` (the pointer table and every walk lie in `[0, cur)`),
* `embCap ≤ eCap`,
* every word of every walk fits below `2 ^ w`, and
* every cell of the pointer table and of every walk lies in `R.foot handle y ∨ [cur, ret)`.

This file provides:
* `selEmbSrcOk_of_op4_layout`: turns those op `4` layout, word-bound, and footprint facts into
  `SelEmbSrcOk` (`MinRatio/SelectEmbCopy.lean`) for any edge `e ∈ coreE` whose walk fits in `slot`,
  given any nonempty select region `[lo, hi)` disjoint from `foot` and `[cur, ret)`.
* `selEmbSrcOk_of_op4_selectRegion`: specialization to the select embedding region
  `[entryBase, entryBase + eCapSel + eCapSel * slot)` where `e < eCapSel` discharges `lo < hi`.
* `ordCoreReadEmbKFBL_runs`: runs `ordCoreReadEmbStmt (op 4)` under `SparseCoreReadoutFootAt`,
  returning the embedding readout, layout, word bounds, and footprint guarantees.
* `ordCoreReadEmbKFBL_selEmbSrcOk`: combines `ordCoreReadEmbKFBL_runs` with `selEmbSrcOk_of_op4_layout`
  using `R.Respects` so a caller with a pre-call disjoint select region `[lo, hi)` (`hi ≤ heap`)
  directly receives `SelEmbSrcOk` for every core edge whose walk fits in `slot`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Bridge

/-- Turn the op `4` layout (`MEmbBounded` below `cur`), word bounds, and footprint facts into
`SelEmbSrcOk` for any edge `e ∈ coreE` whose encoded walk fits in `slot`, given a nonempty select
region `[lo, hi)` disjoint from `foot` and from `[cur, ret)`. -/
theorem selEmbSrcOk_of_op4_layout {mem : ℕ → ℕ} {w embTable embCap cur ret slot lo hi e : ℕ}
    {coreE : Finset ℕ} {emb : MinCostFlow.Embedding} {foot : ℕ → Prop}
    (hB : MEmbBounded mem embTable coreE embCap emb 0 cur)
    (hWords : ∀ e' ∈ coreE, ∀ t < (mWalkEncode (emb e')).length,
      mem (mem (embTable + e') + t) < 2 ^ w)
    (hTableFoot : ∀ addr, embTable ≤ addr → addr < embTable + embCap →
      foot addr ∨ (cur ≤ addr ∧ addr < ret))
    (hWalkFoot : ∀ e' ∈ coreE, ∀ addr,
      mem (embTable + e') ≤ addr →
      addr < mem (embTable + e') + (mWalkEncode (emb e')).length →
      foot addr ∨ (cur ≤ addr ∧ addr < ret))
    (hcurW : cur < 2 ^ w)
    (hlohi : lo < hi)
    (hDisjFoot : ∀ addr, lo ≤ addr → addr < hi → ¬ foot addr)
    (hDisjNew : ∀ addr, lo ≤ addr → addr < hi → ¬ (cur ≤ addr ∧ addr < ret))
    (he : e ∈ coreE)
    (hslot : (mWalkEncode (emb e)).length ≤ slot) :
    SelEmbSrcOk mem w embTable slot lo hi emb e := by
  obtain ⟨_, hTblEnd, hWalks⟩ := hB
  obtain ⟨heCap, _, hWalkEnd, hWalkAt⟩ := hWalks e he
  refine ⟨hslot, hWalkAt, by omega, ?_, by omega, hWords e he, ?_⟩
  · by_contra h
    have hlo : lo ≤ embTable + e := by omega
    have hhi : embTable + e < hi := by omega
    rcases hTableFoot (embTable + e) (by omega) (by omega) with hf | hn
    · exact hDisjFoot (embTable + e) hlo hhi hf
    · exact hDisjNew (embTable + e) hlo hhi hn
  · by_contra h
    have hlenPos : 0 < (mWalkEncode (emb e)).length := by
      simp [mWalkEncode]
    let addr := max lo (mem (embTable + e))
    have hlo : lo ≤ addr := le_max_left _ _
    have hhi : addr < hi := max_lt hlohi (by omega)
    have hwp : mem (embTable + e) ≤ addr := le_max_right _ _
    have hwend : addr < mem (embTable + e) + (mWalkEncode (emb e)).length :=
      max_lt (by omega) (by omega)
    rcases hWalkFoot e he addr hwp hwend with hf | hn
    · exact hDisjFoot addr hlo hhi hf
    · exact hDisjNew addr hlo hhi hn

/-- Specialization of `selEmbSrcOk_of_op4_layout` to the select embedding region
`[entryBase, entryBase + eCapSel + eCapSel * slot)` used by `selEmbCopyContract`, where
`e < eCapSel` automatically implies the region is nonempty. -/
theorem selEmbSrcOk_of_op4_selectRegion
    {mem : ℕ → ℕ} {w embTable embCap cur ret entryBase eCapSel slot e : ℕ}
    {coreE : Finset ℕ} {emb : MinCostFlow.Embedding} {foot : ℕ → Prop}
    (hB : MEmbBounded mem embTable coreE embCap emb 0 cur)
    (hWords : ∀ e' ∈ coreE, ∀ t < (mWalkEncode (emb e')).length,
      mem (mem (embTable + e') + t) < 2 ^ w)
    (hTableFoot : ∀ addr, embTable ≤ addr → addr < embTable + embCap →
      foot addr ∨ (cur ≤ addr ∧ addr < ret))
    (hWalkFoot : ∀ e' ∈ coreE, ∀ addr,
      mem (embTable + e') ≤ addr →
      addr < mem (embTable + e') + (mWalkEncode (emb e')).length →
      foot addr ∨ (cur ≤ addr ∧ addr < ret))
    (hcurW : cur < 2 ^ w)
    (heSel : e < eCapSel)
    (hDisjFoot : ∀ addr, entryBase ≤ addr → addr < entryBase + eCapSel + eCapSel * slot →
      ¬ foot addr)
    (hDisjNew : ∀ addr, entryBase ≤ addr → addr < entryBase + eCapSel + eCapSel * slot →
      ¬ (cur ≤ addr ∧ addr < ret))
    (he : e ∈ coreE)
    (hslot : (mWalkEncode (emb e)).length ≤ slot) :
    SelEmbSrcOk mem w embTable slot entryBase (entryBase + eCapSel + eCapSel * slot) emb e :=
  selEmbSrcOk_of_op4_layout hB hWords hTableFoot hWalkFoot hcurW (by omega)
    hDisjFoot hDisjNew he hslot

end Bridge

section Execution

variable {w L depth k M N vCap eCap capExp : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {P : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

/-- Execute `ordCoreReadEmbStmt` (op `4`) under `SparseCoreReadoutFootAt`: returns the embedding
readout, `MEmbBounded` below `heap`, `embCap ≤ eCap`, word bounds on every walk word, and footprint
containment for the pointer table and every walk. -/
theorem ordCoreReadEmbKFBL_runs {branch handle graph heap : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ heap)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 2 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadEmbStmt (op 4)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      EmbeddingReadoutAt out.mem heap (out.mem (heap + 1)) a.G (tool.lsfs a.st branch)
        (tool.emb a.st branch) ∧
      MEmbBounded out.mem (out.mem heap) (coreGraph a.G (tool.lsfs a.st branch)).E
        (out.mem (heap + 1)) (tool.emb a.st branch) 0 heap ∧
      out.mem (heap + 1) ≤ eCap ∧
      (∀ e ∈ (coreGraph a.G (tool.lsfs a.st branch)).E,
        ∀ t < (mWalkEncode (tool.emb a.st branch e)).length,
          out.mem (out.mem (out.mem heap + e) + t) < 2 ^ w) ∧
      (∀ addr, out.mem heap ≤ addr → addr < out.mem heap + out.mem (heap + 1) →
        R.foot handle y addr ∨ (heap ≤ addr ∧ addr < ret)) ∧
      (∀ e ∈ (coreGraph a.G (tool.lsfs a.st branch)).E, ∀ addr,
        out.mem (out.mem heap + e) ≤ addr →
        addr < out.mem (out.mem heap + e) + (mWalkEncode (tool.emb a.st branch e)).length →
        R.foot handle y addr ∨ (heap ≤ addr ∧ addr < ret)) ∧
      R.Respects (R.foot handle x) heap 2 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, graph, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hrespect, hcost⟩ :=
    hFootAt.op4_runs handle a x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, graph, heap, rfl, hj, hG, hgEnd⟩ hfoot hz hroom
  obtain ⟨hEmbRd, hBounded, hCapLe, hWalkWords, hTableFoot, hWalkFoot⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hEmbRd hBounded hCapLe hWalkWords hTableFoot hWalkFoot
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 6, .reg 4] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hg, hp]
  have hcall : Runs w p ω (ordCoreReadEmbStmt (op 4)) st .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 4 + c + 1, y, hcall, by simp [out], hrep', hEmbRd, hBounded, hCapLe,
    hWalkWords, hTableFoot, hWalkFoot, hrespect, ?_, fun r hr => Function.update_of_ne hr _ _⟩
  change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

/-- Execute `ordCoreReadEmbStmt` (op `4`) under `SparseCoreReadoutFootAt` and immediately derive
`e < eCap ∧ SelEmbSrcOk` for every core edge whose walk fits in `slot`, given a nonempty select
region `[lo, hi)` below `heap` and disjoint from the pre-call footprint `R.foot handle x`. -/
theorem ordCoreReadEmbKFBL_selEmbSrcOk {branch handle graph heap slot lo hi : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ heap)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 2 < 2 ^ w)
    (hlohi : lo < hi)
    (hhi : hi ≤ heap)
    (hDisjFoot : ∀ addr, lo ≤ addr → addr < hi → ¬ R.foot handle x addr) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadEmbStmt (op 4)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      EmbeddingReadoutAt out.mem heap (out.mem (heap + 1)) a.G (tool.lsfs a.st branch)
        (tool.emb a.st branch) ∧
      out.mem (heap + 1) ≤ eCap ∧
      (∀ e ∈ (coreGraph a.G (tool.lsfs a.st branch)).E,
        (mWalkEncode (tool.emb a.st branch e)).length ≤ slot →
        e < eCap ∧ SelEmbSrcOk out.mem w (out.mem heap) slot lo hi (tool.emb a.st branch) e) ∧
      R.Respects (R.foot handle x) heap 2 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  obtain ⟨out, ret, cost, y, hrun, hret, hrep', hEmbRd, hBounded, hCapLe, hWalkWords,
    hTableFoot, hWalkFoot, hrespect, hcost, hregs⟩ :=
    ordCoreReadEmbKFBL_runs hFootAt hb hh hg hp hj hw hhw hG hgEnd hrep hIn hfoot hz hroom
  have hDisjFoot' : ∀ addr, lo ≤ addr → addr < hi → ¬ R.foot handle y addr := by
    intro addr hlo hlt hfy
    rcases hrespect.2.2.2.2 addr hfy with hfx | hnew
    · exact hDisjFoot addr hlo hlt hfx
    · omega
  have hDisjNew : ∀ addr, lo ≤ addr → addr < hi → ¬ (heap ≤ addr ∧ addr < ret) := by
    intro addr _ hlt hnew
    omega
  refine ⟨out, ret, cost, y, hrun, hret, hrep', hEmbRd, hCapLe, ?_, hrespect, hcost, hregs⟩
  intro e he hslot
  have heCap : e < eCap := lt_of_lt_of_le (hBounded.2.2 e he).1 hCapLe
  exact ⟨heCap, selEmbSrcOk_of_op4_layout hBounded hWalkWords hTableFoot hWalkFoot
    (by omega) hlohi hDisjFoot' hDisjNew he hslot⟩

end Execution

end MinCostFlow.MinRatio
