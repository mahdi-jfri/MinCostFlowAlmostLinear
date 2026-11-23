module

public import MinCostFlow.MinRatio.OrdSparseCoreHelpers
public import MinCostFlow.MinRatio.ShiftBranch
import WordRAM.Tactic

/-!
# Deterministic Word-RAM primitives for `sparseCoreOrdMachineContract`

Provides the direct machine-level wrappers and execution specifications for every operation
of the ordered sparse-core machine contract (`SparseCore.Program.sparseCoreOrdMachineContract`,
Lemma 5.17, page 23, with the bundle repair described in the README,
'Where the proof departs from the paper'):
1. `ordCoreInitStmt` (`init [graph, lengths, gradient, ord, heap]`): initializes `tool.initOrd`
   and selects branch `0`, charging `P.mul * (tool.cost a'.st + G.n + G.m + ordListWords + 1) + 12`.
2. `ordCoreUpdateStmt` (op `0`, `[handle, graph, batch, words, edits, editWords, lengths, grad, heap]`):
   applies an ordered batch update, writes `BranchOutAt` at `heap`, and charges
   `P.mul * (tool.cost a'.st - tool.cost a.st + words + editWords + 1) + 10`.
3. `ordLoadBranchOutStmt`: reads the 4-word `(batchPtr, batchWords, editsPtr, editsWords)` record
   for branch `j` from `BranchOutAt`.
4. `ordCoreRestartStmt` (`shiftBranch` + op `1`, `[handle, newBranch, heap]`): advances the active
   branch `(branch + 1) % k` and restarts its spanner, charging
   `P.mul * (tool.cost (restart a.st newBranch) - tool.cost a.st + 1) + 19`.
5. `ordCoreReadLSFStmt` (op `2`), `ordCoreReadGraphStmt` (op `3`), `ordCoreReadEmbStmt` (op `4`),
   and `ordCoreReadOrdStmt` (op `5`, output order `OrdListAt` for `tool.rot a.st branch`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Statements

/-- Initialize an ordered sparse-core level from `(graph, lengths, gradient, ord, heap)` in
registers `6, 7, 8, 9, 4`. Saves the handle in register `3`, stores the returned heap in
register `4`, and selects branch `0` in register `2`. -/
@[expose] def ordCoreInitStmt (init : ℕ) : Stmt :=
  .assign 3 (.reg 4) ;;
  .call 4 init [.reg 6, .reg 7, .reg 8, .reg 9, .reg 4] ;;
  .assign 2 (.const 0)

theorem ordCoreInitStmt_noRand (init : ℕ) : (ordCoreInitStmt init).NoRand := by
  simp [ordCoreInitStmt, Stmt.NoRand]

theorem ordCoreInitStmt_preserves_regs {w init cost r : ℕ} {p : Program}
    {st out : State} {ω : ℕ → Bool}
    (hrun : Runs w p ω (ordCoreInitStmt init) st .normal out cost)
    (h₂ : r ≠ 2) (h₃ : r ≠ 3) (h₄ : r ≠ 4) :
    out.regs r = st.regs r := by
  rcases runs_seq_iff.mp hrun with ⟨_, _, _, h, _⟩ | ⟨s1, _, _, h1, hrest, _⟩
  · cases h
  rcases runs_seq_iff.mp hrest with ⟨_, _, _, h, _⟩ | ⟨s2, _, _, h2, h3, _⟩
  · cases h
  obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp h1
  obtain ⟨_, _, _, _, _, _, _, _, _, rfl, _⟩ := runs_call_iff.mp h2
  obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp h3
  simp [Function.update_of_ne, h₂, h₃, h₄]

/-- Update an ordered sparse-core level (op `0`) with arguments
`[handle, graph, batch, words, edits, editWords, lengths, gradient, heap]` in registers
`3, 6, 10, 11, 12, 13, 7, 8, 4`. Stores the returned heap in register `5` while keeping
the `BranchOutAt` address in register `4`. -/
@[expose] def ordCoreUpdateStmt (upd : ℕ) : Stmt :=
  .call 5 upd [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4]

theorem ordCoreUpdateStmt_noRand (upd : ℕ) : (ordCoreUpdateStmt upd).NoRand := by
  simp [ordCoreUpdateStmt, Stmt.NoRand]

/-- Load the 4-word branch-output record `(batchPtr, batchWords, editsPtr, editsWords)` for
branch `j` (`reg 2`) from `BranchOutAt` at `branchOutAddr` (`reg 4`) into registers
`10, 11, 12, 13`, using register `14` as scratch. -/
@[expose] def ordLoadBranchOutStmt : Stmt :=
  .assign 14 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 10 (.load (.reg 14)) ;;
  .assign 11 (.load (.bin .add (.reg 14) (.const 1))) ;;
  .assign 12 (.load (.bin .add (.reg 14) (.const 2))) ;;
  .assign 13 (.load (.bin .add (.reg 14) (.const 3)))

theorem ordLoadBranchOutStmt_noRand : ordLoadBranchOutStmt.NoRand := by
  simp [ordLoadBranchOutStmt, Stmt.NoRand]

/-- Advance the active branch `(branch + 1) % k` in memory (`reg 0` = branch cell, `reg 1` = `k`)
and restart that branch (op `1`) using handle `reg 3` and heap `reg 4`. -/
@[expose] def ordCoreRestartStmt (restart : ℕ) : Stmt :=
  shiftBranch ;; .call 4 restart [.reg 3, .reg 2, .reg 4]

theorem ordCoreRestartStmt_noRand (restart : ℕ) : (ordCoreRestartStmt restart).NoRand := by
  simp [ordCoreRestartStmt, shiftBranch, Stmt.NoRand]

/-- LSF readout (op `2`): `[handle, branch, graph, heap]` in registers `3, 2, 6, 4`, returning
the new heap in register `5`. -/
@[expose] def ordCoreReadLSFStmt (readLSF : ℕ) : Stmt :=
  .call 5 readLSF [.reg 3, .reg 2, .reg 6, .reg 4]

theorem ordCoreReadLSFStmt_noRand (readLSF : ℕ) : (ordCoreReadLSFStmt readLSF).NoRand := by
  simp [ordCoreReadLSFStmt, Stmt.NoRand]

/-- Sparsifier graph readout (op `3`): `[handle, branch, heap]` in registers `3, 2, 4`, returning
the new heap in register `5`. The graph pointer is stored at `mem[reg 4]`. -/
@[expose] def ordCoreReadGraphStmt (readGraph : ℕ) : Stmt :=
  .call 5 readGraph [.reg 3, .reg 2, .reg 4]

theorem ordCoreReadGraphStmt_noRand (readGraph : ℕ) : (ordCoreReadGraphStmt readGraph).NoRand := by
  simp [ordCoreReadGraphStmt, Stmt.NoRand]

/-- Embedding readout (op `4`): `[handle, branch, graph, heap]` in registers `3, 2, 6, 4`, returning
the new heap in register `5`. -/
@[expose] def ordCoreReadEmbStmt (readEmb : ℕ) : Stmt :=
  .call 5 readEmb [.reg 3, .reg 2, .reg 6, .reg 4]

theorem ordCoreReadEmbStmt_noRand (readEmb : ℕ) : (ordCoreReadEmbStmt readEmb).NoRand := by
  simp [ordCoreReadEmbStmt, Stmt.NoRand]

/-- Output-order readout (op `5`): calls `[handle, branch, heap]` in registers `3, 2, 4` to write
the pointer to `OrdListAt` of `tool.rot a.st branch` at `mem[heap]`, stores the new heap in
register `5`, and loads the `OrdListAt` pointer into register `9`. -/
@[expose] def ordCoreReadOrdStmt (readOrd : ℕ) : Stmt :=
  .call 5 readOrd [.reg 3, .reg 2, .reg 4] ;;
  .assign 9 (.load (.reg 4))

theorem ordCoreReadOrdStmt_noRand (readOrd : ℕ) : (ordCoreReadOrdStmt readOrd).NoRand := by
  simp [ordCoreReadOrdStmt, Stmt.NoRand]

end Statements

section Execution

/-- Execute `ordCoreInitStmt` against `sparseCoreOrdMachineContract`. -/
theorem ordCoreInit_runs {w L k M N vCap eCap init graph lengths gradient ord heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool G k M N vCap eCap P allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (ho : st.regs 9 = ord) (hh : st.regs 4 = heap)
    (hwords : ∀ a ∈ [graph, lengths, gradient, ord, heap], a < 2 ^ w)
    (hpre : (sparseCoreOrdMachineContract fmt L tool G k M N vCap eCap P allocation).initPre
      [graph, lengths, gradient, ord, heap] st.mem)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 6 [graph, lengths, gradient, ord, heap] < 2 ^ w) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G
        (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
        (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E)
        (readOrd st.mem ord), G, readOrd st.mem ord, 0⟩
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreInitStmt init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap a0 y out.mem ∧
      SparseCoreOrdInput tool k M N a0.st a0.G a0.ord a0.n ∧
      R.Respects (fun _ => False) heap (allocation 6 [graph, lengths, gradient, ord, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤
        P.mul * (tool.cost a0.st + G.n + G.m + ordListWords st.mem ord + 1) + 12 := by
  dsimp only
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep, hpost, hframe, hcost⟩ :=
    himpl.2.1 [graph, lengths, gradient, ord, heap] st.mem st.pos ω hwords hpre hz hroom
  have hinput := sparseCoreOrdMachineContract_init_input hpre hpost
  have hnext : next =
      ⟨tool.initOrd k M N G
        (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
        (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E)
        (readOrd st.mem ord), G, readOrd st.mem ord, 0⟩ := by
    simpa [sparseCoreOrdMachineContract] using hpost
  subst hnext
  let s1 := { st with regs := Function.update st.regs 3 heap }
  let s2 := { after with regs := Function.update s1.regs 4 o.value }
  let out := { s2 with regs := Function.update s2.regs 2 0 }
  have h1 : Runs w p ω (.assign 3 (.reg 4)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hargs : evalArgs w s1 [.reg 6, .reg 7, .reg 8, .reg 9, .reg 4] =
      some [graph, lengths, gradient, ord, heap] := by
    simp [evalArgs, Expr.eval, s1, Function.update_of_ne, hg, hl, hc, ho, hh]
  have h2 : Runs w p ω (.call 4 init [.reg 6, .reg 7, .reg 8, .reg 9, .reg 4])
      s1 .normal s2 (5 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 2 (.const 0)) s2 .normal out 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  refine ⟨out, o.value, 2 + ((5 + c + 1) + 2 + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, 2, h2, h3, rfl⟩), rfl⟩),
    by simp [out], by simp [out, s2, s1, Function.update_of_ne],
    by simp [out, s2, Function.update_of_ne], hrep, hinput, hframe, ?_⟩
  simp only [sparseCoreOrdMachineContract, heapArg, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.getLastD_cons, List.getLastD_nil] at hcost
  change (2 + ((5 + c + 1) + 2 + 1) + 1) + R.phi heap y after.mem ≤ _
  omega

/-- Execute `ordCoreInitStmt` directly from prepared graph, edge-value tables, and `OrdListAt`. -/
theorem ordCoreInit_tables_runs
    {w L k M N vCap eCap init graph lengths gradient ord ordWords heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool G k M N vCap eCap P allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (ho : st.regs 9 = ord) (hh : st.regs 4 = heap)
    (hk : 0 < k) (hword : (M + N + 2) ^ P.wordExp < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgb : graph + dynGraphSize vCap eCap ≤ heap)
    (hlb : lengths + eCap * L ≤ heap) (hgrb : gradient + eCap * L ≤ heap)
    (hord : OrdListAt st.mem ord ordFn ordWords)
    (hordb : ord + ordWords ≤ heap) (hordW : ∀ j < ordWords, st.mem (ord + j) < 2 ^ w)
    (hrot : IsRotationOrder G ordFn)
    (hℓ : EdgeValuesAt st.mem lengths fmt.limbBits L fmt.precision G.E ℓ)
    (hgv : EdgeValuesAt st.mem gradient fmt.limbBits L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 6 [graph, lengths, gradient, ord, heap] < 2 ^ w) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G
        (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreInitStmt init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap a0 y out.mem ∧
      SparseCoreOrdInput tool k M N a0.st a0.G a0.ord a0.n ∧
      R.Respects (fun _ => False) heap (allocation 6 [graph, lengths, gradient, ord, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤
        P.mul * (tool.cost a0.st + G.n + G.m + ordWords + 1) + 12 := by
  dsimp only
  have hwords : ∀ a ∈ [graph, lengths, gradient, ord, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  have hpre := sparseCoreOrdMachineContract_initPre_of_tables (tool := tool) (P := P)
    (allocation := allocation) hk hword hG hm hn hgb hlb hgrb hord hordb hordW hrot hℓ hgv hpos
  have h1 : readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E =
      fun e => if e ∈ G.E then ℓ e else 0 := by
    funext e
    by_cases he : e ∈ G.E
    · simp only [readEdgeValues, he, ↓reduceIte, (hℓ e he).2]
    · simp [readEdgeValues, he]
  have h2 : readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E =
      fun e => if e ∈ G.E then g e else 0 := by
    funext e
    by_cases he : e ∈ G.E
    · simp only [readEdgeValues, he, ↓reduceIte, (hgv e he).2]
    · simp [readEdgeValues, he]
  have hordW' : ordListWords st.mem ord = ordWords := hord.2.2.symm
  have hr := ordCoreInit_runs (ω := ω) himpl hg hl hc ho hh hwords hpre hz hroom
  dsimp only at hr
  rw [h1, h2, hord.2.1, hordW'] at hr
  exact hr

/-- Execute `ordCoreReadGraphStmt` (op `3`): reads the sparsifier `DynGraphAt` for `branch`
at `mem[heap]`, charging `P.readout + 4`. -/
theorem ordCoreReadGraph_runs {w L k M N vCap eCap init branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 1 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadGraphStmt (op 3)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.mem heap) vc ec (tool.S a.st branch)) ∧
      R.Respects (R.foot handle x) heap 1 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 4 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 3 handle a x [handle, branch, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, heap, rfl, hj⟩ hfoot hz hroom
  obtain ⟨rfl, hgraph⟩ := hpost
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 4] = some [handle, branch, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hp]
  have hcall : Runs w p ω (ordCoreReadGraphStmt (op 3)) st .normal out (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 3 + c + 1, y, hcall, by simp [out], hrep', ?_, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  · simpa [heapArg, List.getD_eq_getElem?_getD] using hgraph
  · change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
    change _ + R.phi handle y after.mem ≤ _
    omega

/-- Execute `ordCoreReadLSFStmt` (op `2`): writes `LSFAt` for `branch` at `heap`,
charging `P.readout + 5`. -/
theorem ordCoreReadLSF_runs {w L k M N vCap eCap init branch handle graph heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ heap)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 4 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      (∃ vc ec, LSFAt out.mem heap vc ec fmt.limbBits L fmt.precision a.G.E
        (tool.lsfs a.st branch)) ∧
      R.Respects (R.foot handle x) heap 4 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, graph, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 2 handle a x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, graph, heap, rfl, hj, hG, hgEnd⟩ hfoot hz hroom
  obtain ⟨rfl, hlsf⟩ := hpost
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 6, .reg 4] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hg, hp]
  have hcall : Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 4 + c + 1, y, hcall, by simp [out], hrep', ?_, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  · simpa [heapArg, List.getD_eq_getElem?_getD] using hlsf
  · change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
    change _ + R.phi handle y after.mem ≤ _
    omega

/-- Execute `ordCoreReadOrdStmt` (op `5`): writes pointer to `OrdListAt` of `tool.rot a.st branch`
at `mem[heap]` and loads it into `reg 9`, charging `P.mul * (ordRotWords a branch + 1) + 8`. -/
theorem ordCoreReadOrd_runs {w L k M N vCap eCap init branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + (1 + ordRotWords a branch) < 2 ^ w) :
    ∃ (out : State) (ret words cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadOrdStmt (op 5)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.regs 9 = out.mem heap ∧
      R.rep handle a y out.mem ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) words ∧
      words ≤ ordRotWords a branch ∧
      R.Respects (R.foot handle x) heap (1 + ordRotWords a branch) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.mul * (ordRotWords a branch + 1) + 8 + R.phi handle x st.mem ∧
      (∀ r, r ≠ 5 → r ≠ 9 → out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 5 handle a x [handle, branch, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, heap, rfl, hj⟩ hfoot hz hroom
  obtain ⟨rfl, words, hordAt, hwordsLe⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil] at hordAt hwordsLe hcost
  let mid := { after with regs := Function.update st.regs 5 o.value }
  let out := { mid with regs := Function.update mid.regs 9 (after.mem heap) }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 4] = some [handle, branch, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hp]
  have hcall : Runs w p ω (.call 5 (op 5) [.reg 3, .reg 2, .reg 4]) st .normal mid (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  have hload : Runs w p ω (.assign 9 (.load (.reg 4))) mid .normal out 3 :=
    runs_assign_iff.mpr ⟨after.mem heap, by simp [Expr.eval, mid, Function.update_of_ne, hp], rfl, rfl, rfl⟩
  refine ⟨out, o.value, words, (3 + c + 1) + 3 + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 3 + c + 1, 3, hcall, hload, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out, mid], hrep',
    by simpa [out, mid] using hordAt, hwordsLe, hrespect, ?_, ?_⟩
  · simp only [sparseCoreOrdMachineContract, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hcost
    change ((3 + c + 1) + 3 + 1) + R.phi handle y after.mem ≤ _
    omega
  · intro r hr5 hr9
    simp [out, mid, Function.update_of_ne hr5, Function.update_of_ne hr9]

/-- Execute `ordCoreRestartStmt` (`shiftBranch` + op `1`): advances the branch cell at `addr`
to `(branch + 1) % k` and restarts that branch, charging the telescoping `tool.cost` difference. -/
theorem ordCoreRestart_runs {w L k M N vCap eCap init addr branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = branch) (hj : branch < k) (hw : k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr', R.foot handle x addr' → addr' < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (branch + 1) % k, heap] < 2 ^ w) :
    let selected := (branch + 1) % k
    let a' := ordRestartNext a selected
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreRestartStmt (op 1)) st .normal out cost ∧
      out.regs 2 = selected ∧ out.regs 3 = handle ∧ out.regs 4 = ret ∧ out.mem addr = selected ∧
      SparseCoreOrdInput tool k M N a'.st a'.G a'.ord a'.n ∧ R.rep handle a' y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 1 [handle, selected, heap])
        (Function.update st.mem addr selected) ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (tool.cost a'.st - tool.cost a.st + 1) + R.phi handle x st.mem + 19 ∧
      (∀ r, r ≠ 2 → r ≠ 4 → out.regs r = st.regs r) := by
  dsimp only
  let j := (branch + 1) % k
  obtain ⟨mid, hbranch, hmem, hreg, hsaved, _⟩ :=
    shiftBranch_runs (p := p) (ω := ω) ha hk hb hj hw
  have hlocal := himpl.1 handle a x st.mem mid.mem (fun addr' hf => by
    have hne : addr' ≠ addr := fun h => hsep (h ▸ hf)
    rw [hmem, Function.update_of_ne hne])
  have hz' : ZeroFrom mid.mem heap := by
    intro addr' h
    rw [hmem, Function.update_of_ne (by omega)]
    exact hz addr' h
  have hj' : j < k := Nat.mod_lt _ (by omega)
  have hword : ∀ v ∈ [handle, j, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, state, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 1 handle a x [handle, j, heap] mid.mem mid.pos ω hword rfl
      (hlocal.1 hrep) ⟨hIn, handle, j, heap, rfl, hj'⟩ hfoot hz' hroom
  have hstate : state = ordRestartNext a j := by simpa [sparseCoreOrdMachineContract] using hpost
  subst hstate
  let out := { after with regs := Function.update mid.regs 4 o.value }
  have hargs : evalArgs w mid [.reg 3, .reg 2, .reg 4] = some [handle, j, heap] := by
    simp [evalArgs, Expr.eval, hreg, (hsaved 3 (by decide)).trans hh,
      (hsaved 4 (by decide)).trans hheap, j]
  have hcall : Runs w p ω (.call 4 (op 1) [.reg 3, .reg 2, .reg 4]) mid .normal out (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 14 + (3 + c + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 14, _, hbranch, hcall, rfl⟩),
    by simpa [out, Function.update_of_ne] using hreg,
    by simpa only [out, Function.update_of_ne (by decide : 3 ≠ 4)] using (hsaved 3 (by decide)).trans hh,
    by simp [out], ?_, .restart hIn j hj', hrep', by rwa [hmem] at hrespect, ?_,
    fun r hr2 hr4 => by simpa only [out, Function.update_of_ne hr4] using hsaved r hr2⟩
  · change after.mem addr = j
    rw [hrespect.2.2.2.1 addr haheap hsep, hmem, Function.update_self]
  · simp only [sparseCoreOrdMachineContract, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hcost
    dsimp only [ordRestartNext, j] at hcost ⊢
    change _ + R.phi handle y after.mem ≤ _
    rw [← hlocal.2] at hcost
    omega

/-- Execute `ordCoreUpdateStmt` (op `0`): runs ordered batch update, writes `BranchOutAt` at `heap`,
and charges the telescoping `tool.cost` difference plus input batch/edit word counts. -/
theorem ordCoreUpdate_runs
    {w L k M N vCap eCap init handle graph batch words edits editWords lengths gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation))
    (hh : st.regs 3 = handle) (hg : st.regs 6 = graph)
    (hb : st.regs 10 = batch) (hbw : st.regs 11 = words)
    (he : st.regs 12 = edits) (hew : st.regs 13 = editWords)
    (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient) (hp : st.regs 4 = heap)
    (hwords : ∀ v ∈ [handle, graph, batch, words, edits, editWords, lengths, gradient, heap],
      v < 2 ^ w)
    (hrep : R.rep handle a x st.mem)
    (hpre : SparseCoreOrdUpdateAt fmt L tool k M N vCap eCap a
      [handle, graph, batch, words, edits, editWords, lengths, gradient, heap] st.mem)
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
      R.Respects (R.foot handle x) heap (allocation 0 args) st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤
        P.mul * (tool.cost a'.st - tool.cost a.st + words + editWords + 1) +
          R.phi handle x st.mem + 10 ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  dsimp only
  let args := [handle, graph, batch, words, edits, editWords, lengths, gradient, heap]
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 0 handle a x args st.mem st.pos ω hwords rfl hrep hpre hfoot hz hroom
  have hIn' := sparseCoreOrdMachineContract_update_input (fmt := fmt) (L := L)
    (tool := tool) (initialGraph := initialGraph) (k := k) (M := M) (N := N)
    (vCap := vCap) (eCap := eCap) (P := P) (allocation := allocation) hpre hpost
  obtain ⟨hnext, hbout⟩ := hpost
  subst hnext
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st
      [.reg 3, .reg 6, .reg 10, .reg 11, .reg 12, .reg 13, .reg 7, .reg 8, .reg 4] = some args := by
    simp [evalArgs, Expr.eval, args, hh, hg, hb, hbw, he, hew, hl, hc, hp]
  have hcall : Runs w p ω (ordCoreUpdateStmt (op 0)) st .normal out (9 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 9 + c + 1, y, hcall, by simp [out], hrep', hIn',
    by simpa [out, heapArg, args] using hbout, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  simp only [sparseCoreOrdMachineContract, args, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

/-- Execute `ordLoadBranchOutStmt`: extracts `(batchPtr, batchWords, editsPtr, editsWords)`
for active branch `j < k` from `BranchOutAt` into registers `10, 11, 12, 13` in 30 steps. -/
theorem ordLoadBranchOut_runs {w branchOutAddr k j : ℕ}
    {oldGraphs : ℕ → MGraph} {batches : ℕ → List Update} {oldRot newRot : ℕ → ℕ → List End}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 2 = j) (hp : st.regs 4 = branchOutAddr)
    (hj : j < k) (hBO : BranchOutAt st.mem branchOutAddr k oldGraphs batches oldRot newRot)
    (hroom : branchOutAddr + 1 + 4 * j + 3 < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    ∃ out, Runs w p ω ordLoadBranchOutStmt st .normal out 30 ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧
      SmallBatchAt out.mem (out.regs 10) (oldGraphs j) (batches j) (out.regs 11) ∧
      (∃ edits, OrdEditsAt out.mem (out.regs 12) edits (out.regs 13) ∧
        applyOrdEdits (oldRot j) edits = newRot j) ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → out.regs r = st.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  let base := branchOutAddr + 1 + 4 * j
  have h1 : Runs w p ω
      (.assign 14 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 4) (.reg 2))))
      st .normal { st with regs := Function.update st.regs 14 base } 8 :=
    runs_assign_iff.mpr ⟨base, by
      simp [Expr.eval, BinOp.eval, hp, hb, hw1, hw4, base,
        show branchOutAddr + 1 < 2 ^ w by omega, show 4 * j < 2 ^ w by omega,
        show branchOutAddr + 1 + 4 * j < 2 ^ w by omega], rfl, rfl, rfl⟩
  let s1 := { st with regs := Function.update st.regs 14 base }
  let s2 := { s1 with regs := Function.update s1.regs 10 (st.mem base) }
  let s3 := { s2 with regs := Function.update s2.regs 11 (st.mem (base + 1)) }
  let s4 := { s3 with regs := Function.update s3.regs 12 (st.mem (base + 2)) }
  let s5 := { s4 with regs := Function.update s4.regs 13 (st.mem (base + 3)) }
  have h2 : Runs w p ω (.assign 10 (.load (.reg 14))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨st.mem base, by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 14) (.const 1)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨st.mem (base + 1), by
      simp [Expr.eval, BinOp.eval, s2, s1, Function.update_of_ne, hw1, show base + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have h4 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 14) (.const 2)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨st.mem (base + 2), by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, Function.update_of_ne, hw2, show base + 2 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have h5 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 14) (.const 3)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨st.mem (base + 3), by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, Function.update_of_ne, hw3, show base + 3 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hrun : Runs w p ω ordLoadBranchOutStmt st .normal s5 30 :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 8, 21, h1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 3, 17, h2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, 11, h3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, 5, h4, h5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- The steps cost 8 + 3 + 5 + 5 + 5 + 4 = 30, the cost in the statement below.
  obtain ⟨hSB, hEO⟩ := hBO.2 j hj
  have hs5_10 : s5.regs 10 = st.mem base := by simp [s5, s4, s3, s2, Function.update_of_ne]
  have hs5_11 : s5.regs 11 = st.mem (base + 1) := by simp [s5, s4, s3, Function.update_of_ne]
  have hs5_12 : s5.regs 12 = st.mem (base + 2) := by simp [s5, s4, Function.update_of_ne]
  have hs5_13 : s5.regs 13 = st.mem (base + 3) := by simp [s5]
  refine ⟨s5, hrun, rfl, rfl, ?_, ?_, fun r h10 h11 h12 h13 h14 => by
    simp [s5, s4, s3, s2, s1, Function.update_of_ne h10, Function.update_of_ne h11,
      Function.update_of_ne h12, Function.update_of_ne h13, Function.update_of_ne h14]⟩
  · rw [hs5_10, hs5_11]
    simpa [s5, s4, s3, s2, s1, base, Nat.add_assoc, show 1 + 4 * j + 1 = 2 + 4 * j by omega] using hSB
  · rw [hs5_12, hs5_13]
    simpa [s5, s4, s3, s2, s1, base, Nat.add_assoc,
      show 1 + 4 * j + 2 = 3 + 4 * j by omega, show 1 + 4 * j + 3 = 4 + 4 * j by omega] using hEO

end Execution

end MinCostFlow.MinRatio
