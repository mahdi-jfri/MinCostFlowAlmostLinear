module

public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
public import MinCostFlow.MinRatio.WireCoreOpsK
import WordRAM.Tactic

/-!
# The sparse-core operations under the layout contract (`WireCoreOpsKFBL`)

The solver moves from the sparse-core contract `sparseCoreOrdMachineContractK` to
`sparseCoreOrdMachineContractKFBL` (`SparseCore/Program/AssemblyContractLayout.lean`). The new
contract changes three things that the operation wrappers see.
* Init takes 11 arguments `[graph, lengths, gradient, ord, k, M, N, L, P, depth, heap]`. The new
  words are the limb count `L`, the precision `P` and the depth of the sparse core. The wrapper
  `ordCoreInitStmtKFBL` reads them from registers `67`, `68` and `98`.
* The pre of op `0` also asks for `OrdEditsValidFor` and `OrdEditsForBatch`, and its post also
  gives these facts for the edits of every branch.
* The posts of ops `2`, `3` and `5` give layout facts. Their wrappers are in `WireCoreReadKFBL.lean`.

This file has the wrappers for init (`ordCoreInitKFBL_runs`, `ordCoreInitKFBL_tables_runs`),
restart (`ordCoreRestartKFBL_runs`) and update (`ordCoreUpdateKFBL_runs`). They have the
conclusions of the `K` wrappers of `WireCoreOpsK.lean`, which stay until the chain core moves to
the new contract.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Statements

/-- Initialize an ordered sparse-core level under `sparseCoreOrdMachineContractKFBL` from
`(graph, lengths, gradient, ord, k, M, N, L, P, depth, heap)` in registers
`6, 7, 8, 9, 1, 55, 56, 67, 68, 98, 4`. Saves the handle in register `3`, stores the returned heap
in register `4`, and selects branch `0` in register `2`. -/
@[expose] def ordCoreInitStmtKFBL (init : ℕ) : Stmt :=
  .assign 3 (.reg 4) ;;
  .call 4 init [.reg 6, .reg 7, .reg 8, .reg 9, .reg 1, .reg 55, .reg 56, .reg 67, .reg 68,
    .reg 98, .reg 4] ;;
  .assign 2 (.const 0)

theorem ordCoreInitStmtKFBL_noRand (init : ℕ) : (ordCoreInitStmtKFBL init).NoRand := by
  simp [ordCoreInitStmtKFBL, Stmt.NoRand]

theorem ordCoreInitStmtKFBL_preserves_regs {w init cost r : ℕ} {p : Program}
    {st out : State} {ω : ℕ → Bool}
    (hrun : Runs w p ω (ordCoreInitStmtKFBL init) st .normal out cost)
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

end Statements

section Execution

/-- Execute `ordCoreInitStmtKFBL` against `sparseCoreOrdMachineContractKFBL`. The result is the
one of `ordCoreInitK_runs`; the space is the allocation at the 11 init arguments. -/
theorem ordCoreInitKFBL_runs
    {w L depth k M N vCap eCap capExp init graph lengths gradient ord heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool G k M N vCap eCap capExp P allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (ho : st.regs 9 = ord) (hkR : st.regs 1 = k) (hMR : st.regs 55 = M) (hNR : st.regs 56 = N)
    (hLR : st.regs 67 = L) (hPR : st.regs 68 = fmt.precision) (hDR : st.regs 98 = depth)
    (hh : st.regs 4 = heap)
    (hwords : ∀ a ∈ [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap],
      a < 2 ^ w)
    (hwordL : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
    (hpre : (sparseCoreOrdMachineContract fmt L tool G k M N vCap eCap P allocation).initPre
      [graph, lengths, gradient, ord, heap] st.mem)
    (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 6
      [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] < 2 ^ w) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G
        (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
        (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E)
        (readOrd st.mem ord), G, readOrd st.mem ord, 0⟩
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreInitStmtKFBL init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap a0 y out.mem ∧
      SparseCoreOrdInput tool k M N a0.st a0.G a0.ord a0.n ∧
      R.Respects (fun _ => False) heap
        (allocation 6 [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤
        P.mul * (tool.cost a0.st + G.n + G.m + ordListWords st.mem ord + 1) + 18 := by
  dsimp only
  let args := [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap]
  have hpreK : (sparseCoreOrdMachineContractKFBL fmt L depth tool G k M N vCap eCap capExp P
      allocation).initPre args st.mem :=
    ⟨graph, lengths, gradient, ord, heap, rfl, graph, lengths, gradient, ord, heap, rfl,
      graph, lengths, gradient, ord, heap, rfl, hwordL, hpre⟩
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep, hpost, hframe, hcost⟩ :=
    himpl.2.1 args st.mem st.pos ω hwords hpreK hz hroom
  have hnext : next =
      ⟨tool.initOrd k M N G
        (readEdgeValues st.mem lengths fmt.limbBits L fmt.precision G.E)
        (readEdgeValues st.mem gradient fmt.limbBits L fmt.precision G.E)
        (readOrd st.mem ord), G, readOrd st.mem ord, 0⟩ := by
    simpa [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
      sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK,
      sparseCoreOrdMachineContract, args] using hpost
  have hinput : SparseCoreOrdInput tool k M N next.st next.G next.ord next.n :=
    sparseCoreOrdMachineContract_init_input (mem' := after.mem) hpre
      (by simpa [sparseCoreOrdMachineContract] using hnext)
  subst hnext
  let s1 := { st with regs := Function.update st.regs 3 heap }
  let s2 := { after with regs := Function.update s1.regs 4 o.value }
  let out := { s2 with regs := Function.update s2.regs 2 0 }
  have h1 : Runs w p ω (.assign 3 (.reg 4)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hargs : evalArgs w s1 [.reg 6, .reg 7, .reg 8, .reg 9, .reg 1, .reg 55, .reg 56, .reg 67,
      .reg 68, .reg 98, .reg 4] = some args := by
    simp [evalArgs, Expr.eval, s1, Function.update_of_ne, hg, hl, hc, ho, hkR, hMR, hNR, hLR, hPR,
      hDR, hh, args]
  have h2 : Runs w p ω
      (.call 4 init [.reg 6, .reg 7, .reg 8, .reg 9, .reg 1, .reg 55, .reg 56, .reg 67, .reg 68,
        .reg 98, .reg 4])
      s1 .normal s2 (11 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 2 (.const 0)) s2 .normal out 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  refine ⟨out, o.value, 2 + ((11 + c + 1) + 2 + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, 2, h2, h3, rfl⟩), rfl⟩),
    by simp [out], by simp [out, s2, s1, Function.update_of_ne],
    by simp [out, s2, Function.update_of_ne], hrep, hinput, hframe, ?_⟩
  simp only [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
    sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK,
    sparseCoreOrdMachineContract, args, heapArg,
    List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.getLastD_cons, List.getLastD_nil] at hcost
  change (2 + ((11 + c + 1) + 2 + 1) + 1) + R.phi heap y after.mem ≤ _
  omega

/-- Execute `ordCoreInitStmtKFBL` directly from prepared graph, edge-value tables, and
`OrdListAt`. -/
theorem ordCoreInitKFBL_tables_runs
    {w L depth k M N vCap eCap capExp init graph lengths gradient ord ordWords heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool G k M N vCap eCap capExp P allocation))
    (hg : st.regs 6 = graph) (hl : st.regs 7 = lengths) (hc : st.regs 8 = gradient)
    (ho : st.regs 9 = ord) (hkR : st.regs 1 = k) (hMR : st.regs 55 = M) (hNR : st.regs 56 = N)
    (hLR : st.regs 67 = L) (hPR : st.regs 68 = fmt.precision) (hDR : st.regs 98 = depth)
    (hh : st.regs 4 = heap)
    (hk : 0 < k) (hwk : k < 2 ^ w) (hMw : M < 2 ^ w) (hNw : N < 2 ^ w)
    (hLw : L < 2 ^ w) (hPw : fmt.precision < 2 ^ w) (hDw : depth < 2 ^ w)
    (hword : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
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
    (hroom : heap + allocation 6
      [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] < 2 ^ w) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G
        (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreInitStmtKFBL init) st .normal out cost ∧
      out.regs 2 = 0 ∧ out.regs 3 = heap ∧ out.regs 4 = ret ∧
      R.rep heap a0 y out.mem ∧
      SparseCoreOrdInput tool k M N a0.st a0.G a0.ord a0.n ∧
      R.Respects (fun _ => False) heap
        (allocation 6 [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap])
        st.mem ret heap y out.mem ∧
      cost + R.phi heap y out.mem ≤
        P.mul * (tool.cost a0.st + G.n + G.m + ordWords + 1) + 18 := by
  dsimp only
  have hwords : ∀ a ∈ [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap],
      a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hword0 : (M + N + 2) ^ P.wordExp < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)) hword
  have hpre := sparseCoreOrdMachineContract_initPre_of_tables (tool := tool) (P := P)
    (allocation := allocation) hk hword0 hG hm hn hgb hlb hgrb hord hordb hordW hrot hℓ hgv hpos
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
  have hr := ordCoreInitKFBL_runs (ω := ω) himpl hg hl hc ho hkR hMR hNR hLR hPR hDR hh hwords
    hword hpre hz hroom
  dsimp only at hr
  rw [h1, h2, hord.2.1, hordW'] at hr
  exact hr

/-- Execute `ordCoreRestartStmt` (`shiftBranch` + op `1`) against
`sparseCoreOrdMachineContractKFBL`. Op `1` is the same as in the `K` contract, so the result is
the one of `ordCoreRestartK_runs`. -/
theorem ordCoreRestartKFBL_runs
    {w L depth k M N vCap eCap capExp init addr branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
        allocation))
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
  have hstate : state = ordRestartNext a j := by
    simpa [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
      sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK,
      sparseCoreOrdMachineContract] using hpost
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
    by simpa only [out, Function.update_of_ne (by decide : 3 ≠ 4)] using
      (hsaved 3 (by decide)).trans hh,
    by simp [out], ?_, .restart hIn j hj', hrep', by rwa [hmem] at hrespect, ?_,
    fun r hr2 hr4 => by simpa only [out, Function.update_of_ne hr4] using hsaved r hr2⟩
  · change after.mem addr = j
    rw [hrespect.2.2.2.1 addr haheap hsep, hmem, Function.update_self]
  · simp only [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
      sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK,
      sparseCoreOrdMachineContract,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at hcost
    dsimp only [ordRestartNext, j] at hcost ⊢
    change _ + R.phi handle y after.mem ≤ _
    rw [← hlocal.2] at hcost
    omega

/-- Execute `ordCoreUpdateStmt` (op `0`) against `sparseCoreOrdMachineContractKFBL`. The pre of
op `0` asks also that the edits can be sent to the order store and come in blocks along the
batch. The result is the one of `ordCoreUpdateK_runs`, and for every branch `j < k` the written
edits come in blocks along the batch of that branch and can be sent to its order store. -/
theorem ordCoreUpdateKFBL_runs
    {w L depth k M N vCap eCap capExp init handle graph batch words edits editWords lengths
      gradient heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp P
        allocation))
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
  obtain ⟨⟨hnext, hbout⟩, hblk', hval'⟩ := hpost
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
    fun j hj => by simpa [out, heapArg, args] using hblk' j hj,
    fun j hj => by simpa [out, heapArg, args] using hval' j hj, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  simp only [sparseCoreOrdMachineContractKFBL, sparseCoreOrdMachineContractKFB,
    sparseCoreOrdMachineContractKF, sparseCoreOrdMachineContractK, args,
    List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

end Execution

end MinCostFlow.MinRatio
