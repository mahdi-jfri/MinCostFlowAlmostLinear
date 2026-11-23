module

public import MinCostFlow.MinRatio.ShiftRestart

/-!
# Reading the new next-level graph

In Algorithm 1 (page 20), Shift sets the next graph to the sparsifier
of the selected branch. The readout runs on the state after restart.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Obtain the selected branch's sparsifier from the restarted tool.
Register 5 receives the new heap. The graph pointer is in the
readout cell at the heap passed in register 4. -/
@[expose] def shiftGraphRead (entry : ℕ) : Stmt :=
  .call 5 entry [.reg 3, .reg 2, .reg 4]

/-- The sparsifier returned after a restart represents exactly the
graph used by `algorithm1_shift` to begin the suffix rebuild. -/
theorem shiftGraphRead_runs {w L k M N vCap eCap init branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart k s G)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 1 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (shiftGraphRead (op 3)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle s y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.mem heap) vc ec (tool.S s branch)) ∧
      R.Respects (R.foot handle x) heap 1 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ 68 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ a ∈ [handle, branch, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 3 handle s x [handle, branch, heap] st.mem st.pos ω hwords rfl hrep
      ⟨handle, branch, heap, G, rfl, hj, hG⟩ hfoot hz hroom
  obtain ⟨rfl, hgraph⟩ := hpost
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 4] = some [handle, branch, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hp]
  have hcall : Runs w p ω (shiftGraphRead (op 3)) st .normal out (3 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 3 + c + 1, y, hcall, by simp [out], hrep', hgraph, hrespect, ?_, ?_⟩
  · change c + R.phi handle y after.mem ≤ 64 + R.phi handle x st.mem at hcost
    change _ + R.phi handle y after.mem ≤ _
    omega
  · intro r hr
    exact Function.update_of_ne hr _ _

/-- Chain the restart and graph readout. Only the two calls and
their sequence instruction contribute additional cost. -/
theorem shiftRestartGraph_runs {w restart read c d : ℕ} {p : Program} {ω : ℕ → Bool}
    {st mid out : State}
    (hr : Runs w p ω (shiftRestart restart) st .normal mid c)
    (hg : Runs w p ω (shiftGraphRead read) mid .normal out d) :
    Runs w p ω (shiftRestart restart ;; shiftGraphRead read) st .normal out (c + d + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hg, rfl⟩)

/-- The nonterminal prefix of Algorithm 1 Shift restarts the new
branch and reads the next level's graph from the restarted state. -/
theorem shiftRestartGraph_model_runs {w L k M N vCap eCap init addr branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = branch) (hj : branch < k) (hw : k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart k s G)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (branch + 1) % k, heap] + 1 < 2 ^ w) :
    let selected := (branch + 1) % k
    let next := tool.restart s selected
    ∃ (out : State) (ret ptr cost : ℕ) (y : R.τ),
      Runs w p ω (shiftRestart (op 1) ;; shiftGraphRead (op 3)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.mem addr = selected ∧
      R.rep handle next y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.mem ptr) vc ec (tool.S next selected)) ∧
      cost + R.phi handle y out.mem ≤ costs.restartCost M N + R.phi handle x st.mem + 88 ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k next G ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ addr → out.mem a = st.mem a) ∧
      heap ≤ ret ∧ ret ≤ heap + allocation 1 [handle, selected, heap] + 1 ∧
      ZeroFrom out.mem ret ∧ (∀ a, R.foot handle y a → a < ret) ∧
      out.regs 2 = selected ∧ out.regs 3 = handle ∧ out.regs 4 = ptr ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → out.regs r = st.regs r) ∧
      (∀ a < heap, R.foot handle y a → R.foot handle x a) := by
  dsimp only
  obtain ⟨mid, ptr, c, y, hr, hbranch, hhandle', hptr, hcell, hinput, hrep', hrespect, hc, hrestartRegs⟩ :=
    shiftRestart_runs (ω := ω) himpl ha hk hh hheap hb hj hw hhandle haheap hsep hrep hG
      hfoot hz (by omega)
  have hptrRoom := hrespect.2.1
  have hfoot' : ∀ a, R.foot handle y a → a < ptr := by
    intro a h
    rcases hrespect.2.2.2.2 a h with ho | ⟨_, hn⟩
    · exact (hfoot a ho).trans_le hrespect.1
    · exact hn
  obtain ⟨out, ret, d, z, hg, hret, hrep'', hgraph, hframe, hd, hsaved⟩ :=
    shiftGraphRead_runs (ω := ω) himpl hbranch hhandle' hptr (Nat.mod_lt _ (by omega)) hw
      hhandle hrep' hinput hfoot' hrespect.2.2.1 (by omega)
  have hsep' : ¬ R.foot handle y addr := by
    intro h
    rcases hrespect.2.2.2.2 addr h with ho | ⟨hn, _⟩
    · exact hsep ho
    · exact (Nat.not_le_of_lt haheap) hn
  refine ⟨out, ret, ptr, c + d + 1, z, shiftRestartGraph_runs hr hg, hret, ?_,
    hrep'', hgraph, by omega, hinput, ?_, hrespect.1.trans hframe.1, (Nat.le_trans hframe.2.1 (Nat.add_le_add_right hrespect.2.1 1)),
    hframe.2.2.1, ?_,
    (hsaved 2 (by decide)).trans hbranch, (hsaved 3 (by decide)).trans hhandle',
    (hsaved 4 (by decide)).trans hptr, ?_, ?_⟩
  · exact (hframe.2.2.2.1 addr (haheap.trans_le hrespect.1) hsep').trans hcell
  · intro a ha hf hne
    have hf' : ¬ R.foot handle y a := by
      intro h
      rcases hrespect.2.2.2.2 a h with ho | ⟨hn, _⟩
      · exact hf ho
      · exact (Nat.not_le_of_lt ha) hn
    rw [hframe.2.2.2.1 a (ha.trans_le hrespect.1) hf',
      hrespect.2.2.2.1 a ha hf, Function.update_of_ne hne]

  · intro a ha
    rcases hframe.2.2.2.2 a ha with ho | ⟨_, hn⟩
    · exact (hfoot' a ho).trans_le hframe.1
    · exact hn
  · intro r hr₂ hr₄ hr₅
    exact (hsaved r hr₅).trans (hrestartRegs r hr₂ hr₄)

  · intro a ha hf
    rcases hframe.2.2.2.2 a hf with hy | ⟨hnew, _⟩
    · rcases hrespect.2.2.2.2 a hy with hx | ⟨hnew, _⟩
      · exact hx
      · omega
    · have := hrespect.1
      omega

/-- Load the restarted sparsifier for the next level of Algorithm 1
(page 20). Register 4 is the readout slot and register 6 is the graph input. -/
@[expose] def loadShiftGraph : Stmt :=
  .assign 6 (.load (.reg 4))

/-- Loading the graph input preserves its layout and the returned heap. -/
theorem loadShiftGraph_runs {w slot vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hslot : st.regs 4 = slot) (hgraph : DynGraphAt st.mem (st.mem slot) vc ec G) :
    ∃ out, Runs w p ω loadShiftGraph st .normal out 3 ∧
      out.regs 6 = st.mem slot ∧ DynGraphAt out.mem (out.regs 6) vc ec G ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧ (∀ r ≠ 6, out.regs r = st.regs r) := by
  let out := { st with regs := Function.update st.regs 6 (st.mem slot) }
  have hr : Runs w p ω loadShiftGraph st .normal out 3 :=
    runs_assign_iff.mpr ⟨st.mem slot, by simp [Expr.eval, hslot], rfl, rfl, rfl⟩
  refine ⟨out, hr, by simp [out], ?_, rfl, rfl, ?_⟩
  · simpa [out] using hgraph
  · intro r hr
    exact Function.update_of_ne hr _ _

/-- Restart the selected spanner and load its graph for the deeper
rebuild in Algorithm 1 Shift (page 20). -/
@[expose] def shiftRestartLoadGraph (restart read : ℕ) : Stmt :=
  (shiftRestart restart ;; shiftGraphRead read) ;; loadShiftGraph

/-- The loaded graph, heap, and selected branch are ready for the next level. -/
theorem shiftRestartLoadGraph_runs {w L k M N vCap eCap init addr branch handle heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = branch) (hj : branch < k) (hw : k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart k s G)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (branch + 1) % k, heap] + 1 < 2 ^ w) :
    let selected := (branch + 1) % k
    let next := tool.restart s selected
    ∃ (out : State) (ret ptr cost : ℕ) (y : R.τ),
      Runs w p ω (shiftRestartLoadGraph (op 1) (op 3)) st .normal out cost ∧
      out.regs 5 = ret ∧ out.regs 6 = out.mem ptr ∧ out.mem addr = selected ∧
      R.rep handle next y out.mem ∧
      (∃ vc ec, DynGraphAt out.mem (out.regs 6) vc ec (tool.S next selected)) ∧
      cost + R.phi handle y out.mem ≤ costs.restartCost M N + R.phi handle x st.mem + 92 ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k next G ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ addr → out.mem a = st.mem a) ∧
      heap ≤ ret ∧ ret ≤ heap + allocation 1 [handle, selected, heap] + 1 ∧
      ZeroFrom out.mem ret ∧ (∀ a, R.foot handle y a → a < ret) ∧
      out.regs 2 = selected ∧ out.regs 3 = handle ∧ out.regs 4 = ptr ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 6 → out.regs r = st.regs r) ∧
      (∀ a < heap, R.foot handle y a → R.foot handle x a) := by
  dsimp only
  obtain ⟨mid, ret, ptr, c, y, hr, hret, hcell, hs, ⟨vc, ec, hg⟩, hc,
      hinput, hframe, hheap', hretBound, hz', hf', hbranch, hh', hptr, hrestartRegs, hfootBelow⟩ :=
    shiftRestartGraph_model_runs (ω := ω) himpl ha hk hh hheap hb hj hw hhandle haheap
      hsep hrep hG hfoot hz hroom
  obtain ⟨out, hload, hvalue, hgraph, hm, _, hregs⟩ :=
    loadShiftGraph_runs (ω := ω) hptr hg
  refine ⟨out, ret, ptr, c + 4, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, 3, hr, hload, by omega⟩),
    (hregs 5 (by decide)).trans hret, by simpa only [hm] using hvalue,
    by simpa only [hm] using hcell, hm.symm ▸ hs, ⟨vc, ec, hgraph⟩,
    ?_, hinput, ?_, hheap', hretBound, hm.symm ▸ hz', hf',
    (hregs 2 (by decide)).trans hbranch, (hregs 3 (by decide)).trans hh',
    (hregs 4 (by decide)).trans hptr, ?_, hfootBelow⟩
  · rw [hm]
    omega
  · simpa only [hm] using hframe

  · intro r hr₂ hr₄ hr₅ hr₆
    exact (hregs r hr₆).trans (hrestartRegs r hr₂ hr₄ hr₅)

/-- Read the forest of the restarted branch (Algorithm 1, page 20).
Register 7 holds the shifted level's input graph. Register 9 keeps
the address where the tool writes its four-word forest descriptor. -/
@[expose] def shiftForestRead (entry : ℕ) : Stmt :=
  .assign 9 (.reg 5) ;; .call 5 entry [.reg 3, .reg 2, .reg 7, .reg 5]

/-- The forest readout preserves the restarted abstract state and exposes
the fixed-point forest layout in at most 72 steps plus potential change. -/
theorem shiftForestRead_runs {w L k M N vCap eCap init branch handle graph heap : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hg : st.regs 7 = graph)
    (hp : st.regs 5 = heap) (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreGraphAt tool.toSparseCoreTool tool.restart k s st.mem graph vCap eCap G)
    (hgraphRoom : graph + dynGraphSize vCap eCap ≤ heap)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 4 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (shiftForestRead (op 2)) st .normal out cost ∧ out.regs 5 = ret ∧
      out.regs 9 = heap ∧ R.rep handle s y out.mem ∧
      (∃ fv fe, LSFAt out.mem heap fv fe fmt.limbBits L fmt.precision G.E (tool.lsfs s branch)) ∧
      R.Respects (R.foot handle x) heap 4 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ 72 + R.phi handle x st.mem ∧
      (∀ r, r ≠ 5 → r ≠ 9 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 9 heap }
  have hsave : Runs w p ω (.assign 9 (.reg 5)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hp], rfl, rfl, rfl⟩
  have hwords : ∀ a ∈ [handle, branch, graph, heap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, hrun, next, y, hrep', hpost, hrespect, hcost⟩ :=
    himpl.2.2 2 handle s x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨handle, branch, graph, heap, G, rfl, hj, hG, hgraphRoom⟩ hfoot hz hroom
  obtain ⟨rfl, hforest⟩ := hpost
  let out := { after with regs := Function.update mid.regs 5 o.value }
  have hargs : evalArgs w mid [.reg 3, .reg 2, .reg 7, .reg 5] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, mid, Function.update_of_ne, hh, hb, hg, hp]
  have hcall : Runs w p ω (.call 5 (op 2) [.reg 3, .reg 2, .reg 7, .reg 5])
      mid .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 2 + (4 + c + 1) + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 2, _, hsave, hcall, rfl⟩),
    by simp [out], by simp [out, mid, Function.update_of_ne], hrep', ?_, hrespect, ?_, ?_⟩
  · change (∃ fv fe, LSFAt after.mem heap fv fe fmt.limbBits L fmt.precision
      (readNamedGraph st.mem graph vCap eCap).E (tool.lsfs next branch)) at hforest
    simpa only [readNamedGraph_edges hG.2] using hforest
  · change c + R.phi handle y after.mem ≤ 64 + R.phi handle x st.mem at hcost
    change _ + R.phi handle y after.mem ≤ _
    omega

  · intro r hr₅ hr₉
    simp [out, mid, Function.update_of_ne hr₅, Function.update_of_ne hr₉]

/-- The caller-owned copy leaves the restarted tool and its potential
unchanged. Its block is disjoint from the tool for the forest call. -/
theorem copyShiftGraph_preserves_tool_runs {w src heap vc ec handle : ℕ} {G : MGraph}
    {σ : Type} {R : DSRep σ} {s : σ} {x : R.τ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hLocal : R.Local) (hrep : R.rep handle s x st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hsrc : st.regs 6 = src) (hheap : st.regs 5 = heap)
    (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out cost, Runs w p ω copyGraphFromHeader st .normal out cost ∧
      DynGraphAt out.mem (out.regs 6) vc ec G ∧ out.regs 6 = heap ∧
      out.regs 5 = heap + dynGraphSize vc ec ∧ ZeroFrom out.mem (out.regs 5) ∧
      R.rep handle s x out.mem ∧ R.phi handle x out.mem = R.phi handle x st.mem ∧
      (∀ a, heap ≤ a → ¬ R.foot handle x a) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      out.pos = st.pos ∧ cost ≤ 17 * dynGraphSize vc ec + 43 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 10 → r ≠ 11 → r ≠ 12 → out.regs r = st.regs r) := by
  obtain ⟨out, c, hr, hg, hgraph, hnew, hz', hmem, hp, hc, hregs⟩ :=
    copyGraphFromHeader_runs (ω := ω) hsrc hheap hG hdisj hword hw hz
  have hstate := hLocal handle s x st.mem out.mem (fun a ha => (hmem a (hfoot a ha)).symm)
  exact ⟨out, c, hr, hgraph.symm ▸ hg, hgraph, hnew, hnew.symm ▸ hz', hstate.1 hrep,
    hstate.2.symm, fun a ha hf => Nat.not_lt_of_ge ha (hfoot a hf), hmem, hp, hc, hregs⟩

/-- Restart, read, and copy the sparsifier into caller memory. -/
@[expose] def shiftRestartCopyGraph (restart read : ℕ) : Stmt :=
  shiftRestartLoadGraph restart read ;; copyGraphFromHeader

/-- The shift prefix returns a graph block outside the restarted tool's
footprint, given room to copy the readout's layout. -/
theorem shiftRestartCopyGraph_runs {w L k M N vCap eCap init addr branch handle heap reserve : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep tool.State} {s : tool.State} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (himpl : R.Implements w p init op
      (sparseCoreMachineContract fmt L tool initialGraph k M N vCap eCap costs allocation))
    (ha : st.regs 0 = addr) (hk : st.regs 1 = k)
    (hh : st.regs 3 = handle) (hheap : st.regs 4 = heap)
    (hb : st.mem addr = branch) (hj : branch < k) (hw : k < 2 ^ w)
    (hhandle : handle < 2 ^ w) (haheap : addr < heap) (hsep : ¬ R.foot handle x addr)
    (hrep : R.rep handle s x st.mem)
    (hG : SparseCoreInput tool.toSparseCoreTool tool.restart k s G)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 [handle, (branch + 1) % k, heap] + 1 < 2 ^ w)
    (hword : 9 < 2 ^ w)
    (hcopyRoom : ∀ (mid : State) ret vc ec prefixCost,
      let selected := (branch + 1) % k
      let next := tool.restart s selected
      Runs w p ω (shiftRestartLoadGraph (op 1) (op 3)) st .normal mid prefixCost →
      mid.regs 5 = ret →
      DynGraphAt mid.mem (mid.regs 6) vc ec (tool.S next selected) →
      ret ≤ heap + allocation 1 [handle, selected, heap] + 1 →
      mid.regs 6 + dynGraphSize vc ec ≤ ret ∧ ret + dynGraphSize vc ec + reserve < 2 ^ w) :
    let selected := (branch + 1) % k
    let next := tool.restart s selected
    ∃ (out : State) (ret vc ec cost : ℕ) (y : R.τ),
      Runs w p ω (shiftRestartCopyGraph (op 1) (op 3)) st .normal out cost ∧
      out.regs 6 = ret ∧ out.regs 5 = ret + dynGraphSize vc ec ∧ heap ≤ ret ∧ out.regs 5 + reserve < 2 ^ w ∧
      out.regs 2 = selected ∧ out.regs 3 = handle ∧
      out.mem addr = selected ∧ R.rep handle next y out.mem ∧
      DynGraphAt out.mem ret vc ec (tool.S next selected) ∧
      SparseCoreInput tool.toSparseCoreTool tool.restart k next G ∧
      ZeroFrom out.mem (out.regs 5) ∧ (∀ a, R.foot handle y a → a < ret) ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ addr → out.mem a = st.mem a) ∧
      cost + R.phi handle y out.mem ≤ costs.restartCost M N + R.phi handle x st.mem +
        17 * dynGraphSize vc ec + 136 ∧
      (∀ r, r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
        out.regs r = st.regs r) ∧
      (∀ a < heap, R.foot handle y a → R.foot handle x a) := by
  dsimp only
  obtain ⟨mid, ret, _, c, y, hr, hheap', _, hcell, hrep', ⟨vc, ec, hg⟩, hc, hinput,
    hframe, hret, hretHi, hz', hf', hbranch, hhandle', _, hprefixRegs, hfootBelow⟩ :=
    shiftRestartLoadGraph_runs (ω := ω) himpl ha hk hh hheap hb hj hw hhandle haheap
      hsep hrep hG hfoot hz hroom
  obtain ⟨hsrc, hdst⟩ := hcopyRoom mid ret vc ec c hr hheap' hg hretHi
  obtain ⟨out, d, hcopy, hgraph, hptr, hnew, hzero, hstate, hphi, _, hmem, _, hd, hregs⟩ :=
    copyShiftGraph_preserves_tool_runs (ω := ω) himpl.1 hrep' hf' rfl hheap' hg hsrc (by omega) hword hz'
  refine ⟨out, ret, vc, ec, c + d + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, d, hr, hcopy, rfl⟩), hptr, hnew, hret, by omega,
    (hregs 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbranch,
    (hregs 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hhandle',
    (hmem addr (haheap.trans_le hret)).trans hcell, hstate, hptr ▸ hgraph,
    hinput, hzero, hf', ?_, ?_, ?_, hfootBelow⟩
  · intro a ha hfa hne
    exact (hmem a (ha.trans_le hret)).trans (hframe a ha hfa hne)
  · rw [hphi]
    omega

  · intro r hr₂ hr₄ hr₅ hr₆ hr₁₀ hr₁₁ hr₁₂
    exact (hregs r hr₅ hr₆ hr₁₀ hr₁₁ hr₁₂).trans (hprefixRegs r hr₂ hr₄ hr₅ hr₆)

end MinCostFlow.MinRatio
