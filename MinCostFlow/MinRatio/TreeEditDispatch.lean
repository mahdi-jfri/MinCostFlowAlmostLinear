module

public import MinCostFlow.MinRatio.TreeEdit

/-!
# Dispatching a tree change

The tree changes of Lemma 5.11 (page 20) are applied in list order.
A deletion resolves its edge in the old graph and cuts it. An
insertion resolves it in the new graph and links its supplied record.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut DynSpanner.Program

/-- Copy the three table bases for one graph into the lookup registers. -/
@[expose] def treeEditGraphArgs (r : ℕ) : Stmt :=
  .assign 9 (.reg r) ;;
  .assign 10 (.reg (r + 1)) ;;
  .assign 11 (.reg (r + 2))

/-- Look up the inserted edge's payload address by its decoded name.
Register 22 holds the base of the payload address table. -/
@[expose] def treeEditLoadPayload : Stmt :=
  .assign 4 (.load (.bin .add (.reg 22) (.reg 8)))

/-- The lookup changes only the argument register and costs five steps. -/
theorem treeEditLoadPayload_runs {w edge record : ℕ} {p : Program}
    {ω : ℕ → Bool} {st : State}
    (he : st.regs 8 = edge) (haddr : st.regs 22 + edge < 2 ^ w)
    (hrecord : st.mem (st.regs 22 + edge) = record) :
    let out := { st with regs := Function.update st.regs 4 record }
    Runs w p ω treeEditLoadPayload st .normal out 5 :=
  runs_assign_iff.mpr ⟨record, by simp [Expr.eval, BinOp.eval, he, haddr, hrecord],
    rfl, rfl, rfl⟩

/-- Link takes the parent endpoint first. The stored direction identifies
which endpoint is the parent for the account read from off-tree storage. -/
@[expose] def treeEditOrientLink : Stmt :=
  .cond (.load (.bin .add (.reg 4) (.const 1))) .nop
    (.assign 5 (.reg 1) ;; .assign 1 (.reg 2) ;; .assign 2 (.reg 5))

/-- Orient the endpoints without changing the saved account or the heap. -/
theorem treeEditOrientLink_runs {w h L : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {value : PathEdgeValue}
    (hw : st.regs 4 + 1 < 2 ^ w)
    (hv : PathEdgeAt st.mem (st.regs 4) h L (some value)) :
    ∃ out cost, Runs w p ω treeEditOrientLink st .normal out cost ∧
      out.regs 1 = (if value.forward then st.regs 1 else st.regs 2) ∧
      out.regs 2 = (if value.forward then st.regs 2 else st.regs 1) ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 5 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ cost ≤ 13 := by
  have hbit := hv.2.1
  have hne : w ≠ 0 := by intro hz; simp [hz] at hw
  cases hd : value.forward with
  | true =>
    refine ⟨st, 6, ?_, rfl, rfl, fun _ _ _ _ => rfl, rfl, by decide⟩
    exact runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, BinOp.eval, hne, hw, hbit, hd],
      runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
  | false =>
    let first := { st with regs := Function.update st.regs 5 (st.regs 1) }
    let second := { first with regs := Function.update first.regs 1 (st.regs 2) }
    let out := { second with regs := Function.update second.regs 2 (st.regs 1) }
    have h₁ : Runs w p ω (.assign 5 (.reg 1)) st .normal first 2 :=
      runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
    have h₂ : Runs w p ω (.assign 1 (.reg 2)) first .normal second 2 :=
      runs_assign_iff.mpr ⟨_, by simp [Expr.eval, first], rfl, rfl, rfl⟩
    have h₃ : Runs w p ω (.assign 2 (.reg 5)) second .normal out 2 :=
      runs_assign_iff.mpr ⟨_, by simp [Expr.eval, second, first], rfl, rfl, rfl⟩
    have hrun : Runs w p ω
        (.assign 5 (.reg 1) ;; .assign 1 (.reg 2) ;; .assign 2 (.reg 5)) st .normal out 8 :=
      runs_seq_iff.mpr (Or.inr ⟨first, 2, 5, h₁,
        runs_seq_iff.mpr (Or.inr ⟨second, 2, 2, h₂, h₃, rfl⟩), rfl⟩)
    refine ⟨out, 13, ?_, by simp [out, second], by simp [out], ?_, rfl, le_rfl⟩
    · exact runs_cond_iff.mpr ⟨0, 8, by simp [Expr.eval, BinOp.eval, hne, hw, hbit, hd], hrun, rfl⟩
    · intro r h1 h2 h5
      simp [out, second, first, Function.update_of_ne, h1, h2, h5]

/-- Link a stored account with the endpoint order picked by its direction bit. -/
theorem treeEditOrientedLink_runs {w L constant init handle tail head record heap : ℕ}
    {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hregs : st.regs 0 = handle ∧ st.regs 1 = tail ∧ st.regs 2 = head ∧
      st.regs 3 = heap ∧ st.regs 4 = record)
    (haddr : record + 1 < 2 ^ w)
    (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hrep : R.rep handle s x st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap) :
    let u := if value.forward then tail else head
    let v := if value.forward then head else tail
    (∀ a ∈ [handle, u, v, record, heap], a < 2 ^ w) →
    (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, u, v, record, heap] st.mem →
    heap + allocation 0 s.n [handle, u, v, record, heap] < 2 ^ w →
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditOrientLink ;; treeEditLink (op 0)) st .normal out cost ∧
      out.regs 3 = ret ∧ out.mem heap = s.freeHead ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 5 → out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 20 := by
  dsimp only
  intro hwords hpre hroom
  obtain ⟨h0, h1, h2, h3, h4⟩ := hregs
  obtain ⟨mid, c, horient, hu, hv, hkeep, hm, hc⟩ :=
    treeEditOrientLink_runs (p := p) (ω := ω) (value := value) (by rwa [h4]) (by rwa [h4])
  have hu' : mid.regs 1 = (if value.forward then tail else head) := by
    simpa only [h1, h2] using hu
  have hv' : mid.regs 2 = (if value.forward then head else tail) := by
    simpa only [h1, h2] using hv
  obtain ⟨out, ret, d, y, hr, hret, hregs, hrep', hfree, hf, hd⟩ :=
    treeEditLink_runs (ω := ω) himpl
      ⟨(hkeep 0 (by decide) (by decide) (by decide)).trans h0, hu', hv',
        (hkeep 3 (by decide) (by decide) (by decide)).trans h3,
        (hkeep 4 (by decide) (by decide) (by decide)).trans h4⟩
      hwords (by rwa [hm]) (by rwa [hm]) (by rwa [hm]) hfoot (by rwa [hm]) hroom
  refine ⟨out, ret, c + d + 1, y, runs_seq_iff.mpr (Or.inr ⟨mid, c, d, horient, hr, rfl⟩),
    hret, hfree, fun r h1 h2 h3 h5 => (hregs r h3).trans (hkeep r h1 h2 h5), hrep', ?_, ?_⟩
  · simpa only [hm] using hf
  · rw [hm] at hd
    omega

/-- Disconnection of the graph endpoints supplies the oriented Link precondition. -/
theorem treeEditOrientedLink_named_pre {w L constant handle heap record base vc ec e : ℕ}
    {G : MGraph} {fmt : Num.Format w} {mem : ℕ → ℕ} {s : PathTreeState}
    {value : PathEdgeValue} {allocation : ℕ → ℕ → List ℕ → ℕ}
    (he : TreeEditEndpointAt mem base vc ec G e) (hvc : vc ≤ s.n)
    (hi : LctInv pathPayload s) (hf : pathTreeFits fmt.limbBits L s)
    (hw : 2 * s.n + 1 < 2 ^ w) (hwidth : Nat.log 2 (2 * s.n + 1) ≤ fmt.limbBits * L)
    (hc : ¬ pathTreeConnected s (vid (G.tail e)) (vid (G.head e)))
    (hb : record + (2 + 4 * L) ≤ heap)
    (hr : PathEdgeAt mem record fmt.limbBits L (some value)) :
    let u := vid (if value.forward then G.tail e else G.head e)
    let v := vid (if value.forward then G.head e else G.tail e)
    pathTreeFits fmt.limbBits L (lctLink pathPayload s u v (some value)) →
    (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, u, v, record, heap] mem := by
  dsimp only
  intro hnext
  have ht := he.tailNameBound.trans_le hvc
  have hh := he.headNameBound.trans_le hvc
  have hfree := treeEdit_freeHead_of_disconnected hi ht hh hc
  have hswap : ¬ pathTreeConnected s (vid (G.head e)) (vid (G.tail e)) := by
    obtain ⟨trees, free, depth, hinv⟩ := hi
    intro hconn
    exact hc ((pathTreeConnected_iff_induced_roots hinv ht hh).mpr
      ((pathTreeConnected_iff_induced_roots hinv hh ht).mp hconn).symm)
  have hpre u v (hu : u < s.n) (hv : v < s.n)
      (hconn : ¬ pathTreeConnected s (vid u) (vid v))
      (hn : pathTreeFits fmt.limbBits L (lctLink pathPayload s (vid u) (vid v) (some value))) :
      (pathTreeMachineContract fmt L constant allocation).pre 0 s
        [handle, vid u, vid v, record, heap] mem := by
    have hread := readPathEdge_eq hr
    refine ⟨hi, hf, hw, hwidth, handle, vid u, vid v, record, heap, rfl,
      ⟨by simp [vid], by simp [vid]; omega⟩, ⟨by simp [vid], by simp [vid]; omega⟩,
      hconn, hfree, hb, ?_, ?_, ?_⟩
    · rwa [hread]
    · rw [hread]
      rfl
    · rwa [hread]
  cases hd : value.forward
  · simpa only [hd, Bool.false_eq_true, ite_false] using
      hpre _ _ hh ht hswap (by simpa [hd] using hnext)
  · simpa only [hd, ite_true] using hpre _ _ ht hh hc (by simpa [hd] using hnext)

/-- Resolve the graph endpoints and link in the stored account direction. -/
theorem treeEditOrientedLink_named_runs {w L constant init handle heap base vc ec e record : ℕ}
    {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h8 : st.regs 8 = e) (h9 : st.regs 9 = dgETailSlotBase base vc ec)
    (h10 : st.regs 10 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 11 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (h4 : st.regs 4 = record) (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hrecordAddr : record + 1 < 2 ^ w)
    (hwords : ∀ a ∈ [handle, (if value.forward then G.tail e else G.head e) + 1,
        (if value.forward then G.head e else G.tail e) + 1, record, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, (if value.forward then G.tail e else G.head e) + 1,
        (if value.forward then G.head e else G.tail e) + 1, record, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0 s.n [handle, (if value.forward then G.tail e else G.head e) + 1,
        (if value.forward then G.head e else G.tail e) + 1, record, heap] < 2 ^ w) :
    let u := if value.forward then G.tail e + 1 else G.head e + 1
    let v := if value.forward then G.head e + 1 else G.tail e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω ((treeEditEndpoints ;; treeEditVertexIndices) ;; (treeEditOrientLink ;; treeEditLink (op 0)))
        st .normal out cost ∧ out.regs 3 = ret ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 5 → out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧
      out.mem heap = s.freeHead ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 48 := by
  dsimp only
  obtain ⟨mid, hresolve, hu, hv, _, _, hmem, hreg⟩ :=
    treeEditResolve_runs (p := p) (ω := ω) he hgraphRoom hvc hn h8 h9 h10 h11
  obtain ⟨out, ret, c, y, hr, hret, hslot, hsave, hrep', hframe, hc⟩ :=
    treeEditOrientedLink_runs (ω := ω) himpl
      ⟨(hreg 0 (by decide) (by decide)).trans h0, hu, hv,
        (hreg 3 (by decide) (by decide)).trans h3, (hreg 4 (by decide) (by decide)).trans h4⟩
      hrecordAddr (by rwa [hmem]) (by rwa [hmem]) hfoot (by rwa [hmem])
      (by cases hd : value.forward <;> simpa [hd] using hwords)
      (by rw [hmem]; cases hd : value.forward <;> simpa [hd] using hpre)
      (by cases hd : value.forward <;> simpa [hd] using hroom)
  rw [hmem] at hframe hc
  exact ⟨out, ret, 27 + c + 1, y,
    runs_seq_iff.mpr (Or.inr ⟨mid, 27, c, hresolve, hr, rfl⟩),
    hret, (fun r h1 h2 h3 h5 => (hsave r h1 h2 h3 h5).trans (hreg r h1 h2)),
    hrep', hslot, hframe, by omega⟩

/-- Registers 12 through 14 describe the old graph and registers
15 through 17 describe the new graph. The record tag selects the
graph and operation together. -/
@[expose] def treeEditDispatchWithBodies (linkBody deleteBody : Stmt) : Stmt :=
  treeEditRead ;;
  .cond (.reg 7)
    (treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; linkBody)
    (treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; deleteBody)

/-- Use the given deletion body with the ordinary Link call. -/
@[expose] def treeEditDispatchWithCut (link : ℕ) (deleteBody : Stmt) : Stmt :=
  treeEditDispatchWithBodies (treeEditLink link) deleteBody

/-- Dispatch the tree-only edits. -/
@[expose] def treeEditDispatch (link cut : ℕ) : Stmt :=
  treeEditDispatchWithCut link (treeEditCut cut)

/-- The three table bases are copied in eight steps. -/
theorem treeEditGraphArgs_runs {w r tail head inverse : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hr : 11 < r)
    (ht : st.regs r = tail) (hh : st.regs (r + 1) = head) (hi : st.regs (r + 2) = inverse) :
    ∃ out, Runs w p ω (treeEditGraphArgs r) st .normal out 8 ∧
      out.regs 9 = tail ∧ out.regs 10 = head ∧ out.regs 11 = inverse ∧
      out.mem = st.mem ∧
      (∀ j, j ≠ 9 → j ≠ 10 → j ≠ 11 → out.regs j = st.regs j) := by
  let first := { st with regs := Function.update st.regs 9 tail }
  let second := { first with regs := Function.update first.regs 10 head }
  let out := { second with regs := Function.update second.regs 11 inverse }
  have h1 : Runs w p ω (.assign 9 (.reg r)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, ht], rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 10 (.reg (r + 1))) first .normal second 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, first, Function.update_of_ne (show r + 1 ≠ 9 by omega), hh],
      rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 11 (.reg (r + 2))) second .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, second, first,
      Function.update_of_ne (show r + 2 ≠ 10 by omega),
      Function.update_of_ne (show r + 2 ≠ 9 by omega), hi], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨first, 2, 5, h1,
    runs_seq_iff.mpr (Or.inr ⟨second, 2, 2, h2, h3, rfl⟩), rfl⟩),
    by simp [out, second, first, Function.update_of_ne],
    by simp [out, second, Function.update_of_ne], by simp [out], rfl, ?_⟩
  intro j h9 h10 h11
  simp [out, second, first, Function.update_of_ne, h9, h10, h11]

/-- Reading a record and dispatching the selected branch adds twelve
steps to the graph setup and edit execution. -/
theorem treeEditDispatchWithBodies_runs_of_branch {w tag c : ℕ} {linkBody deleteBody : Stmt} {p : Program}
    {ω : ℕ → Bool} {st mid out : State}
    (hread : Runs w p ω treeEditRead st .normal mid 9)
    (htag : mid.regs 7 = tag)
    (hbranch : Runs w p ω
      (if tag = 0 then
        treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; deleteBody
      else
        treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; linkBody)
      mid .normal out c) :
    Runs w p ω (treeEditDispatchWithBodies linkBody deleteBody) st .normal out (c + 12) := by
  have hcond : Runs w p ω (.cond (.reg 7)
      (treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; linkBody)
      (treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; deleteBody))
      mid .normal out (c + 2) :=
    runs_cond_iff.mpr ⟨tag, c, by simp [Expr.eval, htag], hbranch, by simp only [Expr.size]; omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨mid, 9, c + 2, hread, hcond, by omega⟩)

theorem treeEditDispatchWithCut_runs_of_branch {w link tag c : ℕ} {deleteBody : Stmt} {p : Program}
    {ω : ℕ → Bool} {st mid out : State}
    (hread : Runs w p ω treeEditRead st .normal mid 9)
    (htag : mid.regs 7 = tag)
    (hbranch : Runs w p ω
      (if tag = 0 then
        treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; deleteBody
      else
        treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditLink link)
      mid .normal out c) :
    Runs w p ω (treeEditDispatchWithCut link deleteBody) st .normal out (c + 12) :=
  treeEditDispatchWithBodies_runs_of_branch hread htag hbranch

/-- Specialize the dispatch proof to a tree-only Cut. -/
theorem treeEditDispatch_runs_of_branch {w link cut tag c : ℕ} {p : Program}
    {ω : ℕ → Bool} {st mid out : State}
    (hread : Runs w p ω treeEditRead st .normal mid 9)
    (htag : mid.regs 7 = tag)
    (hbranch : Runs w p ω
      (if tag = 0 then
        treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditCut cut
      else
        treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditLink link)
      mid .normal out c) :
    Runs w p ω (treeEditDispatch link cut) st .normal out (c + 12) :=
  treeEditDispatchWithCut_runs_of_branch hread htag hbranch

/-- Decode and apply the named cut from the old graph. -/
theorem treeEditDispatch_cut_runs {w L constant init addr link cut handle heap base vc ec e : ℕ}
    {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ}
    (hentry : cut = op 1)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h6 : st.regs 6 = addr) (hrecordWords : ListAt st.mem addr [0, e])
    (haddr : addr + 1 < 2 ^ w) (h9 : st.regs 12 = dgETailSlotBase base vc ec)
    (h10 : st.regs 13 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 14 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 1 s
      [handle, G.tail e + 1, G.head e + 1, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 1 s.n [handle, G.tail e + 1, G.head e + 1, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditDispatch link cut)
        st .normal out cost ∧ out.regs 3 = ret ∧ out.regs 7 = 0 ∧ out.regs 8 = e ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        out.regs r = st.regs r) ∧
      R.rep handle (lctCut pathPayload s u v) y out.mem ∧
      R.Respects (R.foot handle x) heap (allocation 1 s.n [handle, u, v, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 54 := by
  dsimp only
  obtain ⟨decoded, hread, htag, hedge, hmem, hs⟩ :=
    treeEditRead_runs (p := p) (ω := ω) h6 hrecordWords haddr
  obtain ⟨ready, hargs, ht, hh, hi, hm, hsave⟩ :=
    treeEditGraphArgs_runs (p := p) (ω := ω) (by decide)
      ((hs 12 (by decide) (by decide)).trans h9)
      ((hs 13 (by decide) (by decide)).trans h10)
      ((hs 14 (by decide) (by decide)).trans h11)
  have hmem' := hm.trans hmem
  have hkeep (r : ℕ) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
      (h11 : r ≠ 11) := (hsave r h9 h10 h11).trans (hs r h7 h8)
  obtain ⟨out, ret, c, y, hrun, hret, hregs, hrep', hframe, hcost⟩ :=
    treeEditCut_named_runs (ω := ω) himpl (by rwa [hmem']) hgraphRoom hvc hn
      ((hsave 8 (by decide) (by decide) (by decide)).trans hedge) ht hh hi
      ((hkeep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0)
      ((hkeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3)
       hwords (by rwa [hmem']) (by rwa [hmem']) hfoot (by rwa [hmem']) hroom
  have hseq := runs_seq_iff.mpr (Or.inr ⟨ready, 8, c, hargs, hrun, rfl⟩)
  have hbranch : Runs w p ω
      (if 0 = 0 then
        treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditCut cut
      else
        treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditLink link)
      decoded .normal out (8 + c + 1) := by
    simpa [hentry] using hseq
  rw [hmem'] at hframe hcost
  refine ⟨out, ret, (8 + c + 1) + 12, y, treeEditDispatch_runs_of_branch hread htag hbranch,
    hret, ?_, ?_, ?_, hrep', hframe, by omega⟩
  · exact (hregs 7 (by decide) (by decide) (by decide)).trans
      ((hsave 7 (by decide) (by decide) (by decide)).trans htag)
  · exact (hregs 8 (by decide) (by decide) (by decide)).trans
      ((hsave 8 (by decide) (by decide) (by decide)).trans hedge)
  · intro r h1 h2 h3 h7 h8 h9 h10 h11
    exact (hregs r h1 h2 h3).trans (hkeep r h7 h8 h9 h10 h11)

/-- Decode and apply the named link from the new graph. -/
theorem treeEditDispatchWithCut_link_runs {w L constant init addr link handle heap base vc ec e record : ℕ}
    {deleteBody : Stmt} {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (hentry : link = op 0)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h6 : st.regs 6 = addr) (hrecordWords : ListAt st.mem addr [1, e])
    (haddr : addr + 1 < 2 ^ w) (h9 : st.regs 15 = dgETailSlotBase base vc ec)
    (h10 : st.regs 16 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 17 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (hpayloadRoom : st.regs 22 + e < 2 ^ w)
    (hpayload : st.mem (st.regs 22 + e) = record)
    (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, record, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, G.tail e + 1, G.head e + 1, record, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0 s.n [handle, G.tail e + 1, G.head e + 1, record, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditDispatchWithCut link deleteBody)
        st .normal out cost ∧ out.regs 3 = ret ∧ out.regs 7 = 1 ∧ out.regs 8 = e ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧
      out.mem heap = s.freeHead ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 61 := by
  dsimp only
  obtain ⟨decoded, hread, htag, hedge, hmem, hs⟩ :=
    treeEditRead_runs (p := p) (ω := ω) h6 hrecordWords haddr
  obtain ⟨ready, hargs, ht, hh, hi, hm, hsave⟩ :=
    treeEditGraphArgs_runs (p := p) (ω := ω) (by decide)
      ((hs 15 (by decide) (by decide)).trans h9)
      ((hs 16 (by decide) (by decide)).trans h10)
      ((hs 17 (by decide) (by decide)).trans h11)
  have hmem' := hm.trans hmem
  have hkeep (r : ℕ) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
      (h11 : r ≠ 11) := (hsave r h9 h10 h11).trans (hs r h7 h8)
  have hreadyEdge := (hsave 8 (by decide) (by decide) (by decide)).trans hedge
  have hbase := hkeep 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  let loaded := { ready with regs := Function.update ready.regs 4 record }
  have hload : Runs w p ω treeEditLoadPayload ready .normal loaded 5 :=
    treeEditLoadPayload_runs hreadyEdge (by rwa [hbase]) (by rwa [hbase, hmem'])
  have hloaded (r : ℕ) (h : r ≠ 4) : loaded.regs r = ready.regs r :=
    Function.update_of_ne h _ _
  have hloadedMem : loaded.mem = st.mem := hmem'
  obtain ⟨out, ret, c, y, hrun, hret, hregs, hrep', hslot, hframe, hcost⟩ :=
    treeEditLink_named_runs (st := loaded) (ω := ω) himpl (by rwa [hloadedMem]) hgraphRoom hvc hn
      ((hloaded 8 (by decide)).trans hreadyEdge)
      ((hloaded 9 (by decide)).trans ht) ((hloaded 10 (by decide)).trans hh)
      ((hloaded 11 (by decide)).trans hi)
      ((hloaded 0 (by decide)).trans ((hkeep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0))
      ((hloaded 3 (by decide)).trans ((hkeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3))
      (by simp [loaded]) (by rwa [hloadedMem]) hwords (by rwa [hloadedMem]) (by rwa [hloadedMem])
      hfoot (by rwa [hloadedMem]) hroom
  have hseq := runs_seq_iff.mpr (Or.inr ⟨ready, 8, 5 + c + 1, hargs,
    runs_seq_iff.mpr (Or.inr ⟨loaded, 5, c, hload, hrun, rfl⟩), rfl⟩)
  have hbranch : Runs w p ω
      (if 1 = 0 then
        treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; deleteBody
      else
        treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; treeEditLink link)
      decoded .normal out (8 + (5 + c + 1) + 1) := by
    simpa [hentry] using hseq
  rw [hloadedMem] at hframe hcost
  refine ⟨out, ret, (8 + (5 + c + 1) + 1) + 12, y, treeEditDispatchWithCut_runs_of_branch hread htag hbranch,
    hret, ?_, ?_, ?_, hrep', hslot, hframe, by omega⟩
  · exact (hregs 7 (by decide) (by decide) (by decide)).trans
      ((hloaded 7 (by decide)).trans ((hsave 7 (by decide) (by decide) (by decide)).trans htag))
  · exact (hregs 8 (by decide) (by decide) (by decide)).trans
      ((hloaded 8 (by decide)).trans hreadyEdge)
  · intro r h1 h2 h3 h4 h7 h8 h9 h10 h11
    exact (hregs r h1 h2 h3).trans ((hloaded r h4).trans (hkeep r h7 h8 h9 h10 h11))

/-- Dispatch a packed insertion with the endpoint order of its off-tree account. -/
theorem treeEditDispatch_oriented_link_runs {w L constant init addr link handle heap base vc ec e record : ℕ}
    {deleteBody : Stmt} {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (hentry : link = op 0)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h6 : st.regs 6 = addr) (hrecordWords : ListAt st.mem addr [1, e])
    (haddr : addr + 1 < 2 ^ w) (h9 : st.regs 15 = dgETailSlotBase base vc ec)
    (h10 : st.regs 16 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 17 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (hpayloadRoom : st.regs 22 + e < 2 ^ w)
    (hpayload : st.mem (st.regs 22 + e) = record)
    (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hrecordAddr : record + 1 < 2 ^ w)
    (hwords : ∀ a ∈ [handle, (if value.forward then G.tail e else G.head e) + 1,
        (if value.forward then G.head e else G.tail e) + 1, record, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, (if value.forward then G.tail e else G.head e) + 1,
        (if value.forward then G.head e else G.tail e) + 1, record, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0 s.n [handle, (if value.forward then G.tail e else G.head e) + 1,
        (if value.forward then G.head e else G.tail e) + 1, record, heap] < 2 ^ w) :
    let u := if value.forward then G.tail e + 1 else G.head e + 1
    let v := if value.forward then G.head e + 1 else G.tail e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditDispatchWithBodies (treeEditOrientLink ;; treeEditLink link) deleteBody)
        st .normal out cost ∧ out.regs 3 = ret ∧ out.regs 7 = 1 ∧ out.regs 8 = e ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧
      out.mem heap = s.freeHead ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 75 := by
  dsimp only
  obtain ⟨decoded, hread, htag, hedge, hmem, hs⟩ :=
    treeEditRead_runs (p := p) (ω := ω) h6 hrecordWords haddr
  obtain ⟨ready, hargs, ht, hh, hi, hm, hsave⟩ :=
    treeEditGraphArgs_runs (p := p) (ω := ω) (by decide)
      ((hs 15 (by decide) (by decide)).trans h9)
      ((hs 16 (by decide) (by decide)).trans h10)
      ((hs 17 (by decide) (by decide)).trans h11)
  have hmem' := hm.trans hmem
  have hkeep (r : ℕ) (h7 : r ≠ 7) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10)
      (h11 : r ≠ 11) := (hsave r h9 h10 h11).trans (hs r h7 h8)
  have hreadyEdge := (hsave 8 (by decide) (by decide) (by decide)).trans hedge
  have hbase := hkeep 22 (by decide) (by decide) (by decide) (by decide) (by decide)
  let loaded := { ready with regs := Function.update ready.regs 4 record }
  have hload : Runs w p ω treeEditLoadPayload ready .normal loaded 5 :=
    treeEditLoadPayload_runs hreadyEdge (by rwa [hbase]) (by rwa [hbase, hmem'])
  have hloaded (r : ℕ) (h : r ≠ 4) : loaded.regs r = ready.regs r :=
    Function.update_of_ne h _ _
  have hloadedMem : loaded.mem = st.mem := hmem'
  obtain ⟨out, ret, c, y, hrun, hret, hregs, hrep', hslot, hframe, hcost⟩ :=
    treeEditOrientedLink_named_runs (st := loaded) (ω := ω) himpl (by rwa [hloadedMem]) hgraphRoom hvc hn
      ((hloaded 8 (by decide)).trans hreadyEdge)
      ((hloaded 9 (by decide)).trans ht) ((hloaded 10 (by decide)).trans hh)
      ((hloaded 11 (by decide)).trans hi)
      ((hloaded 0 (by decide)).trans ((hkeep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0))
      ((hloaded 3 (by decide)).trans ((hkeep 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3))
      (by simp [loaded]) (by rwa [hloadedMem]) hrecordAddr hwords (by rwa [hloadedMem]) (by rwa [hloadedMem])
      hfoot (by rwa [hloadedMem]) hroom
  have hseq := runs_seq_iff.mpr (Or.inr ⟨ready, 8, 5 + c + 1, hargs,
    runs_seq_iff.mpr (Or.inr ⟨loaded, 5, c, hload, hrun, rfl⟩), rfl⟩)
  have hbranch : Runs w p ω
      (if 1 = 0 then
        treeEditGraphArgs 12 ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; deleteBody
      else
        treeEditGraphArgs 15 ;; treeEditLoadPayload ;; (treeEditEndpoints ;; treeEditVertexIndices) ;; (treeEditOrientLink ;; treeEditLink link))
      decoded .normal out (8 + (5 + c + 1) + 1) := by
    simpa [hentry] using hseq
  rw [hloadedMem] at hframe hcost
  refine ⟨out, ret, (8 + (5 + c + 1) + 1) + 12, y, treeEditDispatchWithBodies_runs_of_branch hread htag hbranch,
    hret, ?_, ?_, ?_, hrep', hslot, hframe, by omega⟩
  · exact (hregs 7 (by decide) (by decide) (by decide) (by decide)).trans
      ((hloaded 7 (by decide)).trans ((hsave 7 (by decide) (by decide) (by decide)).trans htag))
  · exact (hregs 8 (by decide) (by decide) (by decide) (by decide)).trans
      ((hloaded 8 (by decide)).trans hreadyEdge)
  · intro r h1 h2 h3 h4 h5 h7 h8 h9 h10 h11
    exact (hregs r h1 h2 h3 h5).trans ((hloaded r h4).trans (hkeep r h7 h8 h9 h10 h11))

/-- Specialize the insertion branch to tree-only deletion dispatch. -/
theorem treeEditDispatch_link_runs {w L constant init addr link cut handle heap base vc ec e record : ℕ}
    {G : MGraph} {fmt : Num.Format w} {p : Program} {ω : ℕ → Bool} {st : State}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {value : PathEdgeValue}
    (hentry : link = op 0)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hgraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w) (hvc : vc ≤ s.n) (hn : s.n < 2 ^ w)
    (h6 : st.regs 6 = addr) (hrecordWords : ListAt st.mem addr [1, e])
    (haddr : addr + 1 < 2 ^ w) (h9 : st.regs 15 = dgETailSlotBase base vc ec)
    (h10 : st.regs 16 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 17 = dgIntToExtBase base vc) (h0 : st.regs 0 = handle)
    (h3 : st.regs 3 = heap)
    (hpayloadRoom : st.regs 22 + e < 2 ^ w)
    (hpayload : st.mem (st.regs 22 + e) = record)
    (hrecord : PathEdgeAt st.mem record fmt.limbBits L (some value))
    (hwords : ∀ a ∈ [handle, G.tail e + 1, G.head e + 1, record, heap], a < 2 ^ w)
    (hrep : R.rep handle s x st.mem)
    (hpre : (pathTreeMachineContract fmt L constant allocation).pre 0 s
      [handle, G.tail e + 1, G.head e + 1, record, heap] st.mem)
    (hfoot : ∀ a, R.foot handle x a → a < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + allocation 0 s.n [handle, G.tail e + 1, G.head e + 1, record, heap] < 2 ^ w) :
    let u := G.tail e + 1
    let v := G.head e + 1
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (treeEditDispatch link cut)
        st .normal out cost ∧ out.regs 3 = ret ∧ out.regs 7 = 1 ∧ out.regs 8 = e ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        out.regs r = st.regs r) ∧
      R.rep handle (lctLink pathPayload s u v (some value)) y out.mem ∧
      out.mem heap = s.freeHead ∧
      R.Respects (R.foot handle x) heap (allocation 0 s.n [handle, u, v, record, heap])
        st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ pathTreeBudget constant L s.n + R.phi handle x st.mem + 61 :=
  treeEditDispatchWithCut_link_runs (deleteBody := treeEditCut cut) hentry himpl he hgraphRoom hvc hn
    h6 hrecordWords haddr h9 h10 h11 h0 h3 hpayloadRoom hpayload hrecord hwords hrep hpre hfoot hz hroom

/-- Save the Link output address before dispatch. The decoded tag
then controls whether to record the returned slot. -/
@[expose] def treeEditBindDispatch (bind : ℕ) (dispatch : Stmt) : Stmt :=
  .assign 21 (.reg 3) ;; dispatch ;;
    .cond (.reg 7) (treeEditBindSlot bind) .nop

/-- Retain the ordinary Link dispatch and select the deletion body. -/
@[expose] def treeEditDispatchBoundWithCut (link bind : ℕ) (deleteBody : Stmt) : Stmt :=
  treeEditBindDispatch bind (treeEditDispatchWithCut link deleteBody)

/-- Dispatch and bind using a tree-only deletion. -/
@[expose] def treeEditDispatchBound (link cut bind : ℕ) : Stmt :=
  treeEditDispatchBoundWithCut link bind (treeEditCut cut)

/-- Save the heap address that Link uses to return its edge slot. -/
theorem treeEditSaveSlotAddress_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} (st : State) :
    let out := { st with regs := Function.update st.regs 21 (st.regs 3) }
    Runs w p ω (.assign 21 (.reg 3)) st .normal out 2 :=
  runs_assign_iff.mpr ⟨st.regs 3, rfl, rfl, rfl, rfl⟩

/-- Compose dispatch and the conditional binding. On a cut the
conditional executes only a no-op. -/
theorem treeEditBindDispatch_runs {w bind tag dispatchCost bindCost : ℕ}
    {dispatch : Stmt} {p : Program} {ω : ℕ → Bool} {st mid out : State}
    (hdispatch : Runs w p ω dispatch
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal mid dispatchCost)
    (htag : mid.regs 7 = tag)
    (hbind : Runs w p ω (if tag = 0 then .nop else treeEditBindSlot bind)
      mid .normal out bindCost) :
    Runs w p ω (treeEditBindDispatch bind dispatch) st .normal out
      (dispatchCost + bindCost + 6) := by
  have hc : Runs w p ω (.cond (.reg 7) (treeEditBindSlot bind) .nop)
      mid .normal out (bindCost + 2) :=
    runs_cond_iff.mpr ⟨tag, bindCost, by simp [Expr.eval, htag], hbind,
      by simp only [Expr.size]; omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, 2, _, treeEditSaveSlotAddress_runs st,
    runs_seq_iff.mpr (Or.inr ⟨mid, dispatchCost, bindCost + 2, hdispatch, hc, rfl⟩), by omega⟩)

theorem treeEditDispatchBoundWithCut_runs {w link bind tag dispatchCost bindCost : ℕ}
    {deleteBody : Stmt} {p : Program} {ω : ℕ → Bool} {st mid out : State}
    (hdispatch : Runs w p ω (treeEditDispatchWithCut link deleteBody)
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal mid dispatchCost)
    (htag : mid.regs 7 = tag)
    (hbind : Runs w p ω (if tag = 0 then .nop else treeEditBindSlot bind)
      mid .normal out bindCost) :
    Runs w p ω (treeEditDispatchBoundWithCut link bind deleteBody) st .normal out
      (dispatchCost + bindCost + 6) :=
  treeEditBindDispatch_runs hdispatch htag hbind

/-- Specialize binding to a tree-only deletion. -/
theorem treeEditDispatchBound_runs {w link cut bind tag dispatchCost bindCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st mid out : State}
    (hdispatch : Runs w p ω (treeEditDispatch link cut)
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal mid dispatchCost)
    (htag : mid.regs 7 = tag)
    (hbind : Runs w p ω (if tag = 0 then .nop else treeEditBindSlot bind)
      mid .normal out bindCost) :
    Runs w p ω (treeEditDispatchBound link cut bind) st .normal out
      (dispatchCost + bindCost + 6) :=
  treeEditDispatchBoundWithCut_runs hdispatch htag hbind

/-- Deletions skip slot binding. Saving the response address and
testing the decoded tag add seven steps to a Cut. -/
theorem treeEditDispatchBound_cut {w link cut bind cost : ℕ} {p : Program}
    {ω : ℕ → Bool} {st out : State}
    (hdispatch : Runs w p ω (treeEditDispatch link cut)
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal out cost)
    (htag : out.regs 7 = 0) :
    Runs w p ω (treeEditDispatchBound link cut bind) st .normal out (cost + 7) := by
  have hnop : Runs w p ω .nop out .normal out 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
  exact treeEditDispatchBound_runs hdispatch htag (by simpa using hnop)

/-- Finish a dispatched insertion by binding the slot that Link
wrote at the saved address, while retaining its tree potential. -/
theorem treeEditBindDispatch_link {w bind dispatchCost slots names edge slot heap handle : ℕ}
    {dispatch : Stmt} {p : Program} {ω : ℕ → Bool} {st mid : State} {R : DSRep PathTreeState}
    {x : R.τ} {tree : PathTreeState}
    (hdispatch : Runs w p ω dispatch
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal mid dispatchCost)
    (htag : mid.regs 7 = 1)
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hlocal : R.Local) (hrep : R.rep handle tree x mid.mem)
    (hregs : mid.regs 19 = slots ∧ mid.regs 20 = names ∧ mid.regs 8 = edge ∧
      mid.regs 21 = st.regs 3 ∧ mid.regs 3 = heap)
    (hslot : mid.mem (st.regs 3) = slot)
    (hs : slots + edge < heap) (hn : names + slot < heap) (hsep : slots + edge ≠ names + slot)
    (hsf : ¬ R.foot handle x (slots + edge)) (hnf : ¬ R.foot handle x (names + slot))
    (hh : heap < 2 ^ w) (hz : ZeroFrom mid.mem heap) :
    ∃ out cost, Runs w p ω (treeEditBindDispatch bind dispatch) st .normal out cost ∧
      out.regs 3 = heap ∧ (∀ r, r ≠ 3 → out.regs r = mid.regs r) ∧
      (pathSlotBindContract w).post [slots, names, edge, slot, heap] mid.mem heap out.mem ∧
      R.rep handle tree x out.mem ∧ R.phi handle x out.mem = R.phi handle x mid.mem ∧
      cost ≤ dispatchCost + 29 := by
  obtain ⟨out, c, hr, hheap, hsave, hp, htree, hphi, hc⟩ :=
    treeEditBindSlot_runs (ω := ω) hbind hlocal hrep hregs hslot hs hn hsep hsf hnf hh hz
  exact ⟨out, dispatchCost + c + 6, treeEditBindDispatch_runs hdispatch htag (by simpa using hr),
    hheap, hsave, hp, htree, hphi, by omega⟩
theorem treeEditDispatchBound_link {w link bind dispatchCost slots names edge slot heap handle : ℕ}
    {deleteBody : Stmt} {p : Program} {ω : ℕ → Bool} {st mid : State} {R : DSRep PathTreeState}
    {x : R.τ} {tree : PathTreeState}
    (hdispatch : Runs w p ω (treeEditDispatchWithCut link deleteBody)
      { st with regs := Function.update st.regs 21 (st.regs 3) } .normal mid dispatchCost)
    (htag : mid.regs 7 = 1)
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hlocal : R.Local) (hrep : R.rep handle tree x mid.mem)
    (hregs : mid.regs 19 = slots ∧ mid.regs 20 = names ∧ mid.regs 8 = edge ∧
      mid.regs 21 = st.regs 3 ∧ mid.regs 3 = heap)
    (hslot : mid.mem (st.regs 3) = slot)
    (hs : slots + edge < heap) (hn : names + slot < heap) (hsep : slots + edge ≠ names + slot)
    (hsf : ¬ R.foot handle x (slots + edge)) (hnf : ¬ R.foot handle x (names + slot))
    (hh : heap < 2 ^ w) (hz : ZeroFrom mid.mem heap) :
    ∃ out cost, Runs w p ω (treeEditDispatchBoundWithCut link bind deleteBody) st .normal out cost ∧
      out.regs 3 = heap ∧ (∀ r, r ≠ 3 → out.regs r = mid.regs r) ∧
      (pathSlotBindContract w).post [slots, names, edge, slot, heap] mid.mem heap out.mem ∧
      R.rep handle tree x out.mem ∧ R.phi handle x out.mem = R.phi handle x mid.mem ∧
      cost ≤ dispatchCost + 29 :=
  treeEditBindDispatch_link hdispatch htag hbind hlocal hrep hregs hslot hs hn hsep hsf hnf hh hz

end MinCostFlow.MinRatio
