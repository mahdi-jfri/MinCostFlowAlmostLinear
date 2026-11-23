module

public import MinCostFlow.MinRatio.ShiftGradientStep
import MinCostFlow.Chain.WalkFlow

/-!
# Reading a child vertex during Shift

The incidence direction selects the opposite endpoint of the scanned half-edge.
The dynamic graph's slot map converts that endpoint to the name used by the
potential table for Definition 5.6 (page 18).
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program

/-- Read the opposite endpoint into register 26. Registers 33, 34 and 35
hold the tail array base, edge capacity and slot-to-name array base. -/
@[expose] def loadForestChild : Stmt :=
  .assign 26 (.load (.bin .add (.reg 35) (.load
    (.bin .add (.bin .add (.reg 33)
      (.bin .mul (.bin .sub (.const 1) (.reg 23)) (.reg 34))) (.reg 32)))))

/-- The endpoint lookup follows the child-to-parent orientation and leaves
the adjacency cursor and memory intact. -/
theorem loadForestChild_runs {w a vc ec e : ℕ} {direction : Bool} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hgraph : DynGraphAt st.mem a vc ec F) (he : e ∈ F.E)
    (heReg : st.regs 32 = e) (hd : st.regs 23 = if direction then 1 else 0)
    (ht : st.regs 33 = dgETailSlotBase a vc ec) (hc : st.regs 34 = ec)
    (hn : st.regs 35 = dgIntToExtBase a vc)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w) :
    ∃ out, Runs w p ω loadForestChild st .normal out 14 ∧
      out.regs 26 = F.src (e, direction) ∧
      (∀ r, r ≠ 26 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  rcases hgraph with ⟨hvalid, hvCap, heCap, _, _, _, _, _, _, hind, _, _, _, hends, _⟩
  let child := F.src (e, direction)
  let offset := if direction then 0 else ec
  let addr := dgETailSlotBase a vc ec + offset + e
  have hchild : child ∈ F.V := by
    cases direction
    · exact (hvalid e he).2
    · exact (hvalid e he).1
  have hslot : st.mem addr = st.mem (dgExtToIntBase a vc + child) := by
    cases direction
    · have eq : addr = dgEHeadSlotBase a vc ec + e := by
        simp only [addr, offset, Bool.false_eq_true, ↓reduceIte, dgETailSlotBase, dgEHeadSlotBase]
        omega
      rw [eq]
      exact (hends e he).2
    · simpa [addr, offset, child, MGraph.src] using (hends e he).1
  have hslotCap := hvCap _ (hind child hchild).1
  have heLt := heCap e he
  have hoff : offset ≤ ec := by cases direction <;> simp [offset]
  have ha : addr < 2 ^ w := by
    simp only [addr, dgETailSlotBase, dynGraphSize] at *
    omega
  have hb : dgIntToExtBase a vc + st.mem addr < 2 ^ w := by
    rw [hslot]
    simp only [dgIntToExtBase, dynGraphSize] at *
    omega
  have hbase : dgETailSlotBase a vc ec + offset < 2 ^ w := by
    change dgETailSlotBase a vc ec + offset + e < 2 ^ w at ha
    omega
  have hmul : offset < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by simp only [dynGraphSize] at hroom; omega
  let out := { st with regs := Function.update st.regs 26 child }
  refine ⟨out, runs_assign_iff.mpr ⟨child, ?_, rfl, rfl, rfl⟩,
    by simp [out, child], fun r hr => Function.update_of_ne hr _ _, rfl, rfl⟩
  have hdecoded := (hind child hchild).2
  cases direction <;>
    simp_all [Expr.eval, BinOp.eval, addr, offset]

/-- Decode a live incidence and recover the child vertex's external name. -/
@[expose] def readForestChild : Stmt :=
  decodeForestIncidence ;; loadForestChild

/-- A live incidence supplies the child name and oriented edge for the
potential recurrence in twenty-nine steps. -/
theorem readForestChild_runs {w a vc ec j parent : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (he : j / 2 ∈ F.E)
    (hparent : (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hcursor : st.regs 29 = j + 1) (hj : j < 2 ^ w) (hw : 2 < 2 ^ w)
    (ht : st.regs 33 = dgETailSlotBase a vc ec) (hc : st.regs 34 = ec)
    (hn : st.regs 35 = dgIntToExtBase a vc)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w) :
    let edge := (j / 2, decide (j % 2 ≠ 0))
    ∃ out, Runs w p ω readForestChild st .normal out 29 ∧
      out.regs 26 = F.src edge ∧ out.regs 28 = j ∧
      out.regs 23 = (if edge.2 then 1 else 0) ∧ out.regs 32 = edge.1 ∧
      F.src edge ∈ F.V ∧ F.IsPath (F.src edge) parent [edge] ∧
      (∀ r, r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hrun, hhalf, hdir, hedge, hregs, hmem, hpos⟩ :=
    decodeForestIncidence_runs (ω := ω) hcursor hj hw
  let direction := decide (j % 2 ≠ 0)
  have hdir' : mid.regs 23 = if direction then 1 else 0 := by
    simpa [direction] using hdir
  obtain ⟨out, hload, hchild, hkeep, houtMem, houtPos⟩ :=
    loadForestChild_runs (ω := ω) (hmem.symm ▸ hgraph) he hedge hdir'
      ((hregs 33 (by decide) (by decide) (by decide)).trans ht)
      ((hregs 34 (by decide) (by decide) (by decide)).trans hc)
      ((hregs 35 (by decide) (by decide) (by decide)).trans hn) hroom
  obtain ⟨hvertex, hpath⟩ := forestHalfEdge_childPath hforest he hparent
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 14, 14, hrun, hload, rfl⟩),
    hchild, (hkeep 28 (by decide)).trans hhalf, (hkeep 23 (by decide)).trans hdir',
    (hkeep 32 (by decide)).trans hedge, hvertex, hpath,
    fun r h26 h28 h23 h32 => (hkeep r h26).trans (hregs r h28 h23 h32),
    houtMem.trans hmem, houtPos.trans hpos⟩

/-- A cursor at an entry of the parent's adjacency list supplies the
signed path without requiring a separate endpoint test. -/
theorem readForestChild_at_runs {w a vc ec parent i : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool} {L : List ℕ}
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hi : i < L.length) (hcursor : st.regs 29 = L[i] + 1)
    (ht : st.regs 33 = dgETailSlotBase a vc ec) (hc : st.regs 34 = ec)
    (hn : st.regs 35 = dgIntToExtBase a vc)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w) :
    let j := L[i]
    let edge := (j / 2, decide (j % 2 ≠ 0))
    ∃ out, Runs w p ω readForestChild st .normal out 29 ∧
      out.regs 26 = F.src edge ∧ out.regs 28 = j ∧
      out.regs 23 = (if edge.2 then 1 else 0) ∧ out.regs 32 = edge.1 ∧
      F.src edge ∈ F.V ∧ F.IsPath (F.src edge) parent [edge] ∧
      (∀ r, r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨hj, he, hp⟩ := (hmembers L[i]).mp (List.getElem_mem hi)
  have hcapacity : 2 * ec ≤ 2 ^ w ∧ 2 < 2 ^ w := by
    simp only [dynGraphSize] at hroom
    omega
  exact readForestChild_runs hgraph hforest he hp hcursor
    (lt_of_lt_of_le hj hcapacity.1) hcapacity.2 ht hc hn hroom

/-- Read a live incidence and move to its successor. -/
@[expose] def readForestChildAndAdvance : Stmt :=
  readForestChild ;; loadForestIncidenceNext

/-- A scan step returns the oriented child path and the next cursor in thirty-five steps. -/
theorem readForestChildAndAdvance_runs {w a vc ec parent i prev next head : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool} {L : List ℕ}
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hlist : IsDoublyLinkedList st.mem prev next head (2 * ec) L)
    (hnext : st.regs 27 = next)
    (hi : i < L.length) (hcursor : st.regs 29 = L[i] + 1)
    (ht : st.regs 33 = dgETailSlotBase a vc ec) (hc : st.regs 34 = ec)
    (hn : st.regs 35 = dgIntToExtBase a vc)
    (hnextRoom : next + L[i] < 2 ^ w)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w) :
    let j := L[i]
    let edge := (j / 2, decide (j % 2 ≠ 0))
    ∃ out, Runs w p ω readForestChildAndAdvance st .normal out 35 ∧
      out.regs 26 = F.src edge ∧ out.regs 28 = j ∧
      out.regs 23 = (if edge.2 then 1 else 0) ∧ out.regs 32 = edge.1 ∧
      F.src edge ∈ F.V ∧ F.IsPath (F.src edge) parent [edge] ∧
      out.regs 29 = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) ∧
      (∀ r, r ≠ 29 → r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hread, hchild, hhalf, hdir, hedge, hv, hpath, hkeep, hmem, hpos⟩ :=
    readForestChild_at_runs (ω := ω) hgraph hforest hmembers hi hcursor ht hc hn hroom
  have hnext' := (hkeep 27 (by decide) (by decide) (by decide) (by decide)).trans hnext
  obtain ⟨out, hadvance, hcursor', hkeep', hmem', hpos'⟩ :=
    loadForestIncidenceNext_runs (ω := ω) (hmem.symm ▸ hlist) hi hnext' hhalf hnextRoom
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 29, 5, hread, hadvance, rfl⟩),
    (hkeep' 26 (by decide)).trans hchild, (hkeep' 28 (by decide)).trans hhalf,
    (hkeep' 23 (by decide)).trans hdir, (hkeep' 32 (by decide)).trans hedge, hv, hpath,
    hcursor', fun r h29 h26 h28 h23 h32 => (hkeep' r h29).trans (hkeep r h26 h28 h23 h32),
    hmem'.trans hmem, hpos'.trans hpos⟩

/-- One word per vertex name records whether the traversal has visited it. -/
@[expose] def ForestVisitedAt (mem : ℕ → ℕ) (base capacity : ℕ) (visited : Finset ℕ) : Prop :=
  ∀ v < capacity, mem (base + v) = if v ∈ visited then 1 else 0

/-- Read the visited word for the child in register 26. -/
@[expose] def loadForestChildVisited : Stmt :=
  .assign 37 (.load (.bin .add (.reg 36) (.reg 26)))

/-- The visited test uses the child's external name and preserves the traversal cursor. -/
theorem loadForestChildVisited_runs {w base capacity child : ℕ} {visited : Finset ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hvisited : ForestVisitedAt st.mem base capacity visited)
    (hb : st.regs 36 = base) (hc : st.regs 26 = child)
    (hchild : child < capacity) (hroom : base + capacity ≤ 2 ^ w) :
    ∃ out, Runs w p ω loadForestChildVisited st .normal out 5 ∧
      out.regs 37 = (if child ∈ visited then 1 else 0) ∧
      (∀ r, r ≠ 37 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let value := st.mem (base + child)
  let out := { st with regs := Function.update st.regs 37 value }
  have ha : base + child < 2 ^ w := by omega
  have hrun : Runs w p ω loadForestChildVisited st .normal out 5 :=
    runs_assign_iff.mpr ⟨value, by simp [Expr.eval, BinOp.eval, hb, hc, ha, value],
      rfl, rfl, rfl⟩
  exact ⟨out, hrun, by change value = _; exact hvisited child hchild,
    fun r hr => Function.update_of_ne hr _ _, rfl, rfl⟩

/-- Mark the vertex in register 26 visited after its potential is ready. -/
@[expose] def markForestChildVisited : Stmt :=
  .store (.bin .add (.reg 36) (.reg 26)) (.const 1)

/-- Marking one vertex adds it to the visited set and changes only its flag. -/
theorem markForestChildVisited_runs {w base capacity child : ℕ} {visited : Finset ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hvisited : ForestVisitedAt st.mem base capacity visited)
    (hb : st.regs 36 = base) (hc : st.regs 26 = child)
    (hchild : child < capacity) (hroom : base + capacity ≤ 2 ^ w)
    (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω markForestChildVisited st .normal out 5 ∧
      ForestVisitedAt out.mem base capacity (insert child visited) ∧
      (∀ a, a ≠ base + child → out.mem a = st.mem a) ∧
      out.regs = st.regs ∧ out.pos = st.pos := by
  let out := { st with mem := Function.update st.mem (base + child) 1 }
  have ha : base + child < 2 ^ w := by omega
  have hrun : Runs w p ω markForestChildVisited st .normal out 5 :=
    runs_store_iff.mpr ⟨base + child, 1, by simp [Expr.eval, BinOp.eval, hb, hc, ha],
      by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  have hframe (a : ℕ) (hne : a ≠ base + child) : out.mem a = st.mem a :=
    Function.update_of_ne hne _ _
  refine ⟨out, hrun, ?_, hframe, rfl, rfl⟩
  intro v hv
  by_cases heq : v = child
  · subst v
    simp [out]
  · rw [hframe _ (by omega), hvisited v hv]
    simp [Finset.mem_insert, heq]

/-- Reserve one zeroed marker for each vertex name. Register 21 holds the
vertex capacity and register 36 receives the marker array base. -/
@[expose] def reserveForestVisited : Stmt :=
  .assign 36 (.reg 4) ;; .assign 4 (.bin .add (.reg 4) (.reg 21))

/-- Reserving the marker array represents the empty visited set in seven
steps and leaves a zeroed tail for further allocations. -/
theorem reserveForestVisited_runs {w heap capacity : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 4 = heap) (hc : st.regs 21 = capacity)
    (hz : ZeroFrom st.mem heap) (hroom : heap + capacity < 2 ^ w) :
    ∃ out, Runs w p ω reserveForestVisited st .normal out 7 ∧
      out.regs 36 = heap ∧ out.regs 4 = heap + capacity ∧
      ForestVisitedAt out.mem heap capacity ∅ ∧ ZeroFrom out.mem (heap + capacity) ∧
      (∀ r, r ≠ 36 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 36 heap }
  let out := { mid with regs := Function.update mid.regs 4 (heap + capacity) }
  have hfirst : Runs w p ω (.assign 36 (.reg 4)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.reg 21))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hh, hc, hroom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 4, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, ?_, ?_, rfl, rfl⟩
  · intro v _
    simpa only [Finset.notMem_empty, ite_false] using hz (heap + v) (Nat.le_add_right _ _)
  · exact fun a ha => hz a (by omega)
  · intro r h36 h4
    simp [out, mid, Function.update_of_ne, h36, h4]

/-- Compute a fresh child's potential before marking it visited. -/
@[expose] def writeAndMarkForestChild (entry : ℕ) : Stmt :=
  writeNamedForestPotential entry ;; markForestChildVisited

/-- Disjoint potential and flag arrays let the child step advance both
representations of the visited set. -/
theorem writeAndMarkForestChild_runs
    {w h limbs precision base edgePtr zeroPtr heap entry flags capacity : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 20 = base) (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    {visited : Finset ℕ} (hvisited : ForestPotentialsAt st.mem base h limbs precision F g visited)
    (hpVisited : parent ∈ visited) (hcFresh : child ∉ visited)
    (hflags : ForestVisitedAt st.mem flags capacity visited)
    (hflagsReg : st.regs 36 = flags) (hchildCap : child < capacity)
    (hflagsRoom : flags + capacity ≤ heap)
    (hdisjoint : ∀ v ∈ insert child visited,
      base + v * limbs + limbs ≤ flags ∨ flags + capacity ≤ base + v * limbs)
    (hslots : ∀ v ∈ visited, base + v * limbs + limbs ≤ heap)
    (edgeValue : ℤ)
    (hedge : g edge.1 = (edgeValue : ℝ) / (2 : ℝ) ^ precision)
    (himpl : let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      MeetsContract w p entry (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)))
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hr₂₂ : st.regs 22 = zeroPtr)
    (hr₂₃ : st.regs 23 = if edge.2 then 1 else 0) (hr₂₄ : st.regs 24 = edgePtr)
    (he : PathIntAt st.mem edgePtr h limbs edgeValue)
    (hz : PathIntAt st.mem zeroPtr h limbs 0)
    (heRoom : edgePtr + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap) (hdRoom : (base + child * limbs) + limbs ≤ heap)
    (hzero : ZeroFrom st.mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hfit : let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      Num.Fits h limbs (parentValue +
      ((if edge.2 then edgeValue else 0) - (if edge.2 then 0 else edgeValue)))) :
    ∃ out ret cost, Runs w p ω (writeAndMarkForestChild entry) st .normal out cost ∧
      out.regs 4 = ret ∧ ret = heap + 3 * limbs ∧ ZeroFrom out.mem ret ∧
      ForestPotentialsAt out.mem base h limbs precision F g (insert child visited) ∧
      ForestVisitedAt out.mem flags capacity (insert child visited) ∧
      (∀ a < heap, a ≠ flags + child →
        a < base + child * limbs ∨ base + child * limbs + limbs ≤ a →
        out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → out.regs r = st.regs r) ∧ cost ≤ 129 * limbs + 145 := by
  obtain ⟨mid, ret, cost, hwrite, hret, hnext, hzero, hpots, hmem, hregs, hcost⟩ :=
    writeNamedForestPotential_insert_runs (ω := ω) hb hp hc hforest hpath g
      hvisited hpVisited hcFresh hslots edgeValue hedge himpl hr₃ hr₄ hr₂₂ hr₂₃ hr₂₄
      he hz heRoom hzRoom hdRoom hzero hroom hw hfit
  have hmidFlags : ForestVisitedAt mid.mem flags capacity visited := by
    intro v hv
    rw [hmem _ (by omega) (by rcases hdisjoint child (Finset.mem_insert_self ..) with h | h <;> omega)]
    exact hflags v hv
  obtain ⟨out, hmark, hflags', hmarkMem, hmarkRegs, _⟩ :=
    markForestChildVisited_runs (w := w) (p := p) (ω := ω) hmidFlags
      ((hregs 36 (by decide)).trans hflagsReg) ((hregs 26 (by decide)).trans hc)
      hchildCap (by omega) (by omega)
  refine ⟨out, ret, cost + 5 + 1, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 5, hwrite, hmark, rfl⟩),
    by rw [hmarkRegs, hret], hnext, ?_, ?_, hflags', ?_, ?_, by omega⟩
  · intro a ha
    rw [hmarkMem _ (by omega)]
    exact hzero a ha
  · unfold ForestPotentialsAt; intro v hv
    obtain ⟨hvalid, hvalue⟩ := hpots v hv
    have hagree (j : ℕ) (hj : j < limbs) :=
      hmarkMem (base + v * limbs + j) (by rcases hdisjoint v hv with h | h <;> omega)
    exact ⟨fun j hj => (hagree j hj) ▸ hvalid j hj,
      by rw [Num.fixVal, Num.intVal_congr hagree]; exact hvalue⟩
  · intro a ha hflag hslot
    exact (hmarkMem a hflag).trans (hmem a ha hslot)
  · intro r hr
    rw [hmarkRegs, hregs r hr]

/-- Read the visited flag and perform the child action only on a fresh vertex. -/
@[expose] def visitFreshForestChild (action : Stmt) : Stmt :=
  loadForestChildVisited ;; .cond (.reg 37) .nop action

/-- A visited child skips the action. A fresh child runs it with register 37
set to zero, with eight extra steps charged for testing and dispatch. -/
theorem visitFreshForestChild_runs {w base capacity child : ℕ} {visited : Finset ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {action : Stmt}
    (hvisited : ForestVisitedAt st.mem base capacity visited)
    (hb : st.regs 36 = base) (hc : st.regs 26 = child)
    (hchild : child < capacity) (hroom : base + capacity ≤ 2 ^ w) :
    ∃ input, input.mem = st.mem ∧ input.pos = st.pos ∧
      (∀ r, r ≠ 37 → input.regs r = st.regs r) ∧
      input.regs 37 = (if child ∈ visited then 1 else 0) ∧
      (child ∈ visited → Runs w p ω (visitFreshForestChild action) st .normal input 9) ∧
      (child ∉ visited → ∀ {out cost}, Runs w p ω action input .normal out cost →
        Runs w p ω (visitFreshForestChild action) st .normal out (cost + 8)) := by
  obtain ⟨mid, hload, hflag, hkeep, hmem, hpos⟩ :=
    loadForestChildVisited_runs (p := p) (ω := ω) hvisited hb hc hchild hroom
  refine ⟨mid, hmem, hpos, hkeep, hflag, ?_, ?_⟩
  · intro hv
    have hnop : Runs w p ω .nop mid .normal mid 1 :=
      runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have hskip : Runs w p ω (.cond (.reg 37) .nop action) mid .normal mid 3 :=
      runs_cond_iff.mpr ⟨1, 1, by simp [Expr.eval, hflag, hv],
        by simpa only [Nat.one_ne_zero, ite_false] using hnop, rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨mid, 5, 3, hload, hskip, rfl⟩)
  · intro hv out cost hact
    have hdo : Runs w p ω (.cond (.reg 37) .nop action) mid .normal out (cost + 2) :=
      runs_cond_iff.mpr ⟨0, cost, by simp [Expr.eval, hflag, hv],
        by simpa only [ite_true] using hact, by simp [Expr.size]; omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨mid, 5, cost + 2, hload, hdo, by omega⟩)

/-- Scan one incidence and dispatch the action only if its child is fresh. -/
@[expose] def scanForestIncidence (action : Stmt) : Stmt :=
  readForestChildAndAdvance ;; visitFreshForestChild action

/-- The scan advances the cursor before dispatch, preserving the inputs
needed by the action and charging a fixed overhead in either branch. -/
theorem scanForestIncidence_runs {w a vc ec parent i prev next head flags : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool} {L : List ℕ}
    {visited : Finset ℕ} {action : Stmt}
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hlist : IsDoublyLinkedList st.mem prev next head (2 * ec) L)
    (hnext : st.regs 27 = next)
    (hi : i < L.length) (hcursor : st.regs 29 = L[i] + 1)
    (ht : st.regs 33 = dgETailSlotBase a vc ec) (hc : st.regs 34 = ec)
    (hn : st.regs 35 = dgIntToExtBase a vc)
    (hnextRoom : next + L[i] < 2 ^ w)
    (hflags : ForestVisitedAt st.mem flags vc visited) (hf : st.regs 36 = flags)
    (hflagRoom : flags + vc ≤ 2 ^ w)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w) :
    let edge := (L[i] / 2, decide (L[i] % 2 ≠ 0))
    let child := F.src edge
    ∃ input, input.mem = st.mem ∧ input.pos = st.pos ∧
      input.regs 26 = child ∧ input.regs 32 = edge.1 ∧
      input.regs 23 = (if edge.2 then 1 else 0) ∧
      input.regs 29 = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) ∧
      (∀ r, r ≠ 37 → r ≠ 29 → r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 →
        input.regs r = st.regs r) ∧
      F.IsPath child parent [edge] ∧
      (child ∈ visited → Runs w p ω (scanForestIncidence action) st .normal input 45) ∧
      (child ∉ visited → ∀ {out cost}, Runs w p ω action input .normal out cost →
        Runs w p ω (scanForestIncidence action) st .normal out (cost + 44)) := by
  obtain ⟨mid, hscan, hchild, _, hdir, hedge, hv, hpath, hcur, hregs, hmem, hpos⟩ :=
    readForestChildAndAdvance_runs (ω := ω) hgraph hforest hmembers hlist hnext hi
      hcursor ht hc hn hnextRoom hroom
  have hflagsReg := (hregs 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hf
  obtain ⟨input, hm, hp, hkeep, _, hskip, hvisit⟩ :=
    visitFreshForestChild_runs (p := p) (ω := ω) (hmem.symm ▸ hflags) hflagsReg hchild
      (hgraph.2.1 _ hv) hflagRoom
  refine ⟨input, hm.trans hmem, hp.trans hpos, (hkeep 26 (by decide)).trans hchild,
    (hkeep 32 (by decide)).trans hedge, (hkeep 23 (by decide)).trans hdir,
    (hkeep 29 (by decide)).trans hcur, ?_, hpath, ?_, ?_⟩
  · intro r h37 h29 h26 h28 h23 h32
    exact (hkeep r h37).trans (hregs r h29 h26 h28 h23 h32)
  · intro hv
    exact runs_seq_iff.mpr (Or.inr ⟨mid, 35, 9, hscan, hskip hv, rfl⟩)
  · intro hv out cost hact
    exact runs_seq_iff.mpr (Or.inr ⟨mid, 35, cost + 8, hscan, hvisit hv hact, by omega⟩)

/-- Address the input gradient of the incidence's edge. Register 38 holds
the input gradient table base and register 32 holds the edge name. -/
@[expose] def addressForestGradient : Stmt :=
  .assign 24 (.bin .add (.reg 38) (.bin .mul (.reg 32) (.reg 3)))

/-- The computed pointer supplies the fixed-point numerator of the scanned edge. -/
theorem addressForestGradient_runs {w base edge h limbs precision : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {edges : Finset ℕ} {g : ℕ → ℝ}
    (hvalues : EdgeValuesAt st.mem base h limbs precision edges g) (he : edge ∈ edges)
    (hb : st.regs 38 = base) (hr : st.regs 32 = edge) (hl : st.regs 3 = limbs)
    (hroom : base + edge * limbs < 2 ^ w) :
    ∃ out value, Runs w p ω addressForestGradient st .normal out 6 ∧
      out.regs 24 = base + edge * limbs ∧
      PathIntAt out.mem (out.regs 24) h limbs value ∧
      g edge = (value : ℝ) / (2 : ℝ) ^ precision ∧
      (∀ r, r ≠ 24 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let ptr := base + edge * limbs
  let out := { st with regs := Function.update st.regs 24 ptr }
  have hmul : edge * limbs < 2 ^ w := by omega
  have hrun : Runs w p ω addressForestGradient st .normal out 6 :=
    runs_assign_iff.mpr ⟨ptr, by simp [Expr.eval, BinOp.eval, hb, hr, hl, hmul, hroom, ptr],
      rfl, rfl, rfl⟩
  obtain ⟨hvalid, hvalue⟩ := hvalues edge he
  exact ⟨out, Num.intVal st.mem ptr h limbs, hrun, by simp [out, ptr],
    by simpa [out] using (show PathIntAt st.mem ptr h limbs (Num.intVal st.mem ptr h limbs) from
      ⟨hvalid, rfl⟩),
    hvalue.symm, fun r hne => Function.update_of_ne hne _ _, rfl, rfl⟩

/-- Look up an edge gradient, write its child's potential, and mark the child. -/
@[expose] def propagateForestChild (entry : ℕ) : Stmt :=
  addressForestGradient ;; writeAndMarkForestChild entry

/-- A fresh child step takes its gradient directly from the input table. -/
theorem propagateForestChild_runs
    {w h limbs precision base gradients zeroPtr heap entry flags capacity : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 20 = base) (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    {visited : Finset ℕ} (hvisited : ForestPotentialsAt st.mem base h limbs precision F g visited)
    (hpVisited : parent ∈ visited) (hcFresh : child ∉ visited)
    (hflags : ForestVisitedAt st.mem flags capacity visited)
    (hflagsReg : st.regs 36 = flags) (hchildCap : child < capacity)
    (hflagsRoom : flags + capacity ≤ heap)
    (hdisjoint : ∀ v ∈ insert child visited,
      base + v * limbs + limbs ≤ flags ∨ flags + capacity ≤ base + v * limbs)
    (hslots : ∀ v ∈ visited, base + v * limbs + limbs ≤ heap)
    {edges : Finset ℕ} (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g)
    (he : edge.1 ∈ edges) (hgradientReg : st.regs 38 = gradients) (heReg : st.regs 32 = edge.1)
    (himpl : let edgeValue := Num.intVal st.mem (gradients + edge.1 * limbs) h limbs
      let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      MeetsContract w p entry (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)))
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hr₂₂ : st.regs 22 = zeroPtr)
    (hr₂₃ : st.regs 23 = if edge.2 then 1 else 0)
    (hz : PathIntAt st.mem zeroPtr h limbs 0)
    (heRoom : gradients + edge.1 * limbs + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap) (hdRoom : (base + child * limbs) + limbs ≤ heap)
    (hzero : ZeroFrom st.mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hfit : let edgeValue := Num.intVal st.mem (gradients + edge.1 * limbs) h limbs
      let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      Num.Fits h limbs (parentValue +
      ((if edge.2 then edgeValue else 0) - (if edge.2 then 0 else edgeValue)))) :
    ∃ out ret cost, Runs w p ω (propagateForestChild entry) st .normal out cost ∧
      out.regs 4 = ret ∧ ret = heap + 3 * limbs ∧ ZeroFrom out.mem ret ∧
      ForestPotentialsAt out.mem base h limbs precision F g (insert child visited) ∧
      ForestVisitedAt out.mem flags capacity (insert child visited) ∧
      (∀ a < heap, a ≠ flags + child →
        a < base + child * limbs ∨ base + child * limbs + limbs ≤ a →
        out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 24 → out.regs r = st.regs r) ∧ cost ≤ 129 * limbs + 152 := by
  have haddrRoom : gradients + edge.1 * limbs < 2 ^ w := by omega
  obtain ⟨mid, value, ha, hptr, hvalue, hg, hregs, hmem, _⟩ :=
    addressForestGradient_runs (p := p) (ω := ω) hvalues he hgradientReg heReg hr₃ haddrRoom
  have hvalueEq : value = Num.intVal st.mem (gradients + edge.1 * limbs) h limbs := by
    have heq := hvalue.2
    rw [hptr, hmem] at heq
    exact heq.symm
  subst value
  obtain ⟨out, ret, cost, hwrt, hret, hnext, htail, hpots, hmarks, hframe, hkeep, hcost⟩ :=
    writeAndMarkForestChild_runs (ω := ω)
      ((hregs 20 (by decide)).trans hb) ((hregs 25 (by decide)).trans hp)
      ((hregs 26 (by decide)).trans hc) hforest hpath g (hmem.symm ▸ hvisited)
      hpVisited hcFresh (hmem.symm ▸ hflags) ((hregs 36 (by decide)).trans hflagsReg)
      hchildCap hflagsRoom hdisjoint hslots (Num.intVal st.mem (gradients + edge.1 * limbs) h limbs) hg
      (by simpa only [hmem] using himpl)
      ((hregs 3 (by decide)).trans hr₃) ((hregs 4 (by decide)).trans hr₄)
      ((hregs 22 (by decide)).trans hr₂₂) ((hregs 23 (by decide)).trans hr₂₃) hptr
      (hptr ▸ hvalue) (hmem.symm ▸ hz) heRoom hzRoom hdRoom (hmem.symm ▸ hzero)
      hroom hw (by simpa only [hmem] using hfit)
  exact ⟨out, ret, 6 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 6, cost, ha, hwrt, rfl⟩),
    hret, hnext, htail, hpots, hmarks, fun a ha hf hs => (hframe a ha hf hs).trans (congrFun hmem a),
    fun r hr hne => (hkeep r hr).trans (hregs r hne), by omega⟩

/-- Reserve a queue of vertex names, with base in register 39 and read and
write indices in registers 40 and 41. -/
@[expose] def reserveForestQueue : Stmt :=
  .assign 39 (.reg 4) ;;
  .assign 40 (.const 0) ;;
  .assign 41 (.const 0) ;;
  .assign 4 (.bin .add (.reg 4) (.reg 21))

/-- Queue initialization sets both indices to zero and reserves one word
per possible vertex name in thirteen steps. -/
theorem reserveForestQueue_runs {w heap capacity : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 4 = heap) (hc : st.regs 21 = capacity)
    (hz : ZeroFrom st.mem heap) (hroom : heap + capacity < 2 ^ w) :
    ∃ out, Runs w p ω reserveForestQueue st .normal out 13 ∧
      out.regs 39 = heap ∧ out.regs 40 = 0 ∧ out.regs 41 = 0 ∧
      out.regs 4 = heap + capacity ∧ ZeroFrom out.mem (heap + capacity) ∧
      (∀ r, r ≠ 39 → r ≠ 40 → r ≠ 41 → r ≠ 4 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let s1 := { st with regs := Function.update st.regs 39 heap }
  let s2 := { s1 with regs := Function.update s1.regs 40 0 }
  let s3 := { s2 with regs := Function.update s2.regs 41 0 }
  let out := { s3 with regs := Function.update s3.regs 4 (heap + capacity) }
  have h1 : Runs w p ω (.assign 39 (.reg 4)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have h2 : Runs w p ω (.assign 40 (.const 0)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  have h3 : Runs w p ω (.assign 41 (.const 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, rfl⟩
  have h4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.reg 21))) s3 .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, Function.update_of_ne, hh, hc, hroom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 10, h1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 7, h2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, 4, h3, h4, rfl⟩), rfl⟩), rfl⟩),
    by simp [out, s3, s2, s1, Function.update_of_ne],
    by simp [out, s3, s2, Function.update_of_ne], by simp [out, s3, Function.update_of_ne],
    by simp [out], fun a ha => hz a (by omega), ?_, rfl, rfl⟩
  intro r h39 h40 h41 h4
  simp [out, s3, s2, s1, Function.update_of_ne, h39, h40, h41, h4]

/-- Append the child name in register 26 and advance the queue's write index. -/
@[expose] def enqueueForestChild : Stmt :=
  .store (.bin .add (.reg 39) (.reg 41)) (.reg 26) ;;
  .assign 41 (.bin .add (.reg 41) (.const 1))

/-- Enqueueing appends one name in ten steps and writes only the next queue cell. -/
theorem enqueueForestChild_runs {w base capacity child : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hlist : ListAt st.mem base names)
    (hb : st.regs 39 = base) (hi : st.regs 41 = names.length) (hc : st.regs 26 = child)
    (hspace : names.length < capacity) (hroom : base + capacity < 2 ^ w) :
    ∃ out, Runs w p ω enqueueForestChild st .normal out 10 ∧
      out.regs 41 = (names ++ [child]).length ∧ ListAt out.mem base (names ++ [child]) ∧
      (∀ a, a ≠ base + names.length → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 41 → out.regs r = st.regs r) ∧ out.pos = st.pos := by
  let mid := { st with mem := Function.update st.mem (base + names.length) child }
  let out := { mid with regs := Function.update mid.regs 41 (names.length + 1) }
  have ha : base + names.length < 2 ^ w := by omega
  have hn : names.length + 1 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hs : Runs w p ω (.store (.bin .add (.reg 39) (.reg 41)) (.reg 26)) st .normal mid 5 :=
    runs_store_iff.mpr ⟨_, child, by simp [Expr.eval, BinOp.eval, hb, hi, ha],
      by simp [Expr.eval, hc], rfl, rfl, rfl⟩
  have hr : Runs w p ω (.assign 41 (.bin .add (.reg 41) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, hi, hw, hn],
      rfl, rfl, rfl⟩
  have hframe (a : ℕ) (hne : a ≠ base + names.length) : out.mem a = st.mem a :=
    Function.update_of_ne hne _ _
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 4, hs, hr, rfl⟩),
    by simp [out], ?_, hframe, fun r hne => Function.update_of_ne hne _ _, rfl⟩
  intro i hidx
  by_cases hlt : i < names.length
  · rw [hframe _ (by omega), hlist i hlt, List.getElem_append_left hlt]
  · have heq : i = names.length := by simp only [List.length_append, List.length_singleton] at hidx; omega
    subst i
    simp [out, mid, List.getElem_append_right]

/-- Read the next queued parent into register 25 and advance the read index. -/
@[expose] def dequeueForestParent : Stmt :=
  .assign 25 (.load (.bin .add (.reg 39) (.reg 40))) ;;
  .assign 40 (.bin .add (.reg 40) (.const 1))

/-- A dequeue reads the next name in ten steps and preserves the queue contents. -/
theorem dequeueForestParent_runs {w base i : ℕ} {names : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hlist : ListAt st.mem base names) (hi : i < names.length)
    (hb : st.regs 39 = base) (hr : st.regs 40 = i)
    (hroom : base + names.length < 2 ^ w) :
    ∃ out, Runs w p ω dequeueForestParent st .normal out 10 ∧
      out.regs 25 = names[i] ∧ out.regs 40 = i + 1 ∧
      (∀ r, r ≠ 25 → r ≠ 40 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 25 names[i] }
  let out := { mid with regs := Function.update mid.regs 40 (i + 1) }
  have ha : base + i < 2 ^ w := by omega
  have hn : i + 1 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hload : Runs w p ω (.assign 25 (.load (.bin .add (.reg 39) (.reg 40)))) st .normal mid 5 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hb, hr, ha, hlist i hi], rfl, rfl, rfl⟩
  have hstep : Runs w p ω (.assign 40 (.bin .add (.reg 40) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hr, hw, hn],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 5, 4, hload, hstep, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r h25 h40
  simp [out, mid, Function.update_of_ne, h25, h40]

/-- After computing the potential and marking the child, enqueue it for scanning. -/
@[expose] def propagateAndEnqueueForestChild (entry : ℕ) : Stmt :=
  propagateForestChild entry ;; enqueueForestChild

/-- A disjoint queue retains its contents through propagation and receives
one additional vertex after the potential and marker are ready. -/
theorem propagateAndEnqueueForestChild_runs
    {w entry limbs base capacity child heap flags potentials h precision vc : ℕ} {names : List ℕ}
    {F : MGraph} {g : ℕ → ℝ}
    {p : Program} {st mid : State} {ω : ℕ → Bool} {cost : ℕ}
    (hrun : Runs w p ω (propagateForestChild entry) st .normal mid cost)
    (hcost : cost ≤ 129 * limbs + 152)
    (hframe : ∀ a < heap, a ≠ flags + child →
      a < potentials + child * limbs ∨ potentials + child * limbs + limbs ≤ a →
      mid.mem a = st.mem a)
    (hregs : ∀ r, r = 3 ∨ 6 ≤ r → r ≠ 24 → mid.regs r = st.regs r)
    (hpots : ForestPotentialsAt mid.mem potentials h limbs precision F g (insert child names.toFinset))
    (hflags : ForestVisitedAt mid.mem flags vc (insert child names.toFinset))
    (hflagsDisjoint : flags + vc ≤ base ∨ base + capacity ≤ flags)
    (hpotsDisjoint : ∀ v ∈ insert child names.toFinset,
      potentials + v * limbs + limbs ≤ base ∨ base + capacity ≤ potentials + v * limbs)
    (hmidHeap : heap ≤ mid.regs 4) (hzero : ZeroFrom mid.mem (mid.regs 4))
    (hlist : ListAt st.mem base names) (hb : st.regs 39 = base)
    (hi : st.regs 41 = names.length) (hc : st.regs 26 = child)
    (hspace : names.length < capacity) (hheap : base + capacity ≤ heap)
    (hroom : base + capacity < 2 ^ w)
    (hflag : flags + child < base ∨ base + capacity ≤ flags + child)
    (hpot : base + capacity ≤ potentials + child * limbs ∨
      potentials + child * limbs + limbs ≤ base) :
    ∃ out, Runs w p ω (propagateAndEnqueueForestChild entry) st .normal out (cost + 11) ∧
      out.regs 41 = (names ++ [child]).length ∧ ListAt out.mem base (names ++ [child]) ∧
      ForestPotentialsAt out.mem potentials h limbs precision F g (names ++ [child]).toFinset ∧
      ForestVisitedAt out.mem flags vc (names ++ [child]).toFinset ∧
      (∀ a, a ≠ base + names.length → out.mem a = mid.mem a) ∧
      (∀ r, r ≠ 41 → out.regs r = mid.regs r) ∧
      out.regs 4 = mid.regs 4 ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ a < heap, a ≠ base + names.length → a ≠ flags + child →
        a < potentials + child * limbs ∨ potentials + child * limbs + limbs ≤ a →
        out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 24 → r ≠ 41 → out.regs r = st.regs r) ∧ cost + 11 ≤ 129 * limbs + 163 := by
  have hmidList : ListAt mid.mem base names := by
    intro i hidx
    rw [hframe _ (by omega) (by rcases hflag with h | h <;> omega)
      (by rcases hpot with h | h <;> omega)]
    exact hlist i hidx
  obtain ⟨out, hqueue, hlen, houtList, hmem, houtRegs, _⟩ :=
    enqueueForestChild_runs (p := p) (ω := ω) hmidList
      ((hregs 39 (by decide) (by decide)).trans hb)
      ((hregs 41 (by decide) (by decide)).trans hi)
      ((hregs 26 (by decide) (by decide)).trans hc) hspace hroom
  have hset : (names ++ [child]).toFinset = insert child names.toFinset := by
    ext v
    simp [List.toFinset_append, Finset.mem_insert]
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 10, hrun, hqueue, by omega⟩),
    hlen, houtList, ?_, ?_, hmem, houtRegs, houtRegs 4 (by decide), ?_,
    fun a ha hq hf hp => (hmem a hq).trans (hframe a ha hf hp),
    fun r hr h24 h41 => (houtRegs r h41).trans (hregs r hr h24), by omega⟩
  · rw [hset]
    intro v hv
    obtain ⟨hvalid, hvalue⟩ := hpots v hv
    have hagree (j : ℕ) (hj : j < limbs) :
        out.mem (potentials + v * limbs + j) = mid.mem (potentials + v * limbs + j) :=
      hmem _ (by rcases hpotsDisjoint v hv with h | h <;> omega)
    exact ⟨fun j hj => (hagree j hj) ▸ hvalid j hj,
      by rw [Num.fixVal, Num.intVal_congr hagree]; exact hvalue⟩
  · rw [hset]
    intro v hv
    rw [hmem _ (by rcases hflagsDisjoint with h | h <;> omega)]
    exact hflags v hv
  · rw [houtRegs 4 (by decide)]
    intro a ha
    rw [hmem a (by omega)]
    exact hzero a ha

/-- Propagate and schedule a fresh child from the input gradient and queue tables. -/
theorem propagateAndEnqueueForestChild_of_tables_runs
    {w h limbs precision base gradients zeroPtr heap entry flags capacity queue : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 20 = base) (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    {names : List ℕ} (hvisited : ForestPotentialsAt st.mem base h limbs precision F g names.toFinset)
    (hpVisited : parent ∈ names.toFinset) (hcFresh : child ∉ names.toFinset)
    (hflags : ForestVisitedAt st.mem flags capacity names.toFinset)
    (hflagsReg : st.regs 36 = flags) (hchildCap : child < capacity)
    (hflagsRoom : flags + capacity ≤ heap)
    (hdisjoint : ∀ v ∈ insert child names.toFinset,
      base + v * limbs + limbs ≤ flags ∨ flags + capacity ≤ base + v * limbs)
    (hslots : ∀ v ∈ names.toFinset, base + v * limbs + limbs ≤ heap)
    {edges : Finset ℕ} (hvalues : EdgeValuesAt st.mem gradients h limbs precision edges g)
    (he : edge.1 ∈ edges) (hgradientReg : st.regs 38 = gradients) (heReg : st.regs 32 = edge.1)
    (himpl : let edgeValue := Num.intVal st.mem (gradients + edge.1 * limbs) h limbs
      let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      MeetsContract w p entry (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)))
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hr₂₂ : st.regs 22 = zeroPtr)
    (hr₂₃ : st.regs 23 = if edge.2 then 1 else 0)
    (hz : PathIntAt st.mem zeroPtr h limbs 0)
    (heRoom : gradients + edge.1 * limbs + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap) (hdRoom : (base + child * limbs) + limbs ≤ heap)
    (hzero : ZeroFrom st.mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hfit : let edgeValue := Num.intVal st.mem (gradients + edge.1 * limbs) h limbs
      let parentValue := Num.intVal st.mem (base + parent * limbs) h limbs
      Num.Fits h limbs (parentValue +
      ((if edge.2 then edgeValue else 0) - (if edge.2 then 0 else edgeValue))))
    (hlist : ListAt st.mem queue names) (hq : st.regs 39 = queue) (hi : st.regs 41 = names.length)
    (hspace : names.length < capacity) (hqEnd : queue + capacity ≤ heap)
    (hqRoom : queue + capacity < 2 ^ w) (hflagsEnd : flags + capacity ≤ queue)
    (hslotsEnd : ∀ v ∈ insert child names.toFinset, base + v * limbs + limbs ≤ queue) :
    ∃ out cost, Runs w p ω (propagateAndEnqueueForestChild entry) st .normal out cost ∧
      out.regs 4 = heap + 3 * limbs ∧ ZeroFrom out.mem (out.regs 4) ∧
      out.regs 41 = (names ++ [child]).length ∧ ListAt out.mem queue (names ++ [child]) ∧
      ForestPotentialsAt out.mem base h limbs precision F g (names ++ [child]).toFinset ∧
      ForestVisitedAt out.mem flags capacity (names ++ [child]).toFinset ∧
      (∀ a < heap, a ≠ queue + names.length → a ≠ flags + child →
        a < base + child * limbs ∨ base + child * limbs + limbs ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → r ≠ 24 → r ≠ 41 → out.regs r = st.regs r) ∧ cost ≤ 129 * limbs + 163 := by
  obtain ⟨mid, ret, cost, hrun, hret, hnext, htail, hpots, hmarks, hmem, hregs, hcost⟩ :=
    propagateForestChild_runs (ω := ω) hb hp hc hforest hpath g hvisited hpVisited hcFresh
      hflags hflagsReg hchildCap hflagsRoom hdisjoint hslots hvalues he hgradientReg heReg himpl
      hr₃ hr₄ hr₂₂ hr₂₃ hz heRoom hzRoom hdRoom hzero hroom hw hfit
  obtain ⟨out, hout, hlen, hqueue, hopots, homarks, _, _, hheap, hzero, hframe, hkeep, hbound⟩ :=
    propagateAndEnqueueForestChild_runs hrun hcost hmem hregs hpots hmarks
      (Or.inl hflagsEnd) (fun v hv => Or.inl (hslotsEnd v hv))
      (by omega) (hret.symm ▸ htail) hlist hq hi hc hspace hqEnd hqRoom (Or.inl (by omega))
      (Or.inr (hslotsEnd child (Finset.mem_insert_self ..)))
  exact ⟨out, cost + 11, hout, hheap.trans (hret.trans hnext), hzero, hlen, hqueue,
    hopots, homarks, hframe, hkeep, hbound⟩

/-- Process a single incidence during the Shift potential traversal. -/
@[expose] def propagateForestIncidence (entry : ℕ) : Stmt :=
  scanForestIncidence (propagateAndEnqueueForestChild entry)

/-- Every live incidence is processed at the fresh-child cost or less.
The action premise supplies the arithmetic and storage invariants for fresh children. -/
theorem propagateForestIncidence_runs {w a vc ec parent i prev next head flags entry limbs : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool} {L : List ℕ}
    {visited : Finset ℕ}
    (hgraph : DynGraphAt st.mem a vc ec F) (hforest : F.IsForest)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent)
    (hlist : IsDoublyLinkedList st.mem prev next head (2 * ec) L)
    (hnext : st.regs 27 = next)
    (hi : i < L.length) (hcursor : st.regs 29 = L[i] + 1)
    (ht : st.regs 33 = dgETailSlotBase a vc ec) (hc : st.regs 34 = ec)
    (hn : st.regs 35 = dgIntToExtBase a vc)
    (hnextRoom : next + L[i] < 2 ^ w)
    (hflags : ForestVisitedAt st.mem flags vc visited) (hf : st.regs 36 = flags)
    (hflagRoom : flags + vc ≤ 2 ^ w)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w)
    (Inv : Finset ℕ → State → Prop)
    (hskipInv : ∀ input, input.mem = st.mem →
      (∀ r, r ≠ 37 → r ≠ 29 → r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 →
        input.regs r = st.regs r) → Inv visited input)
    (haction : ∀ input, input.mem = st.mem →
      input.regs 26 = F.src (L[i] / 2, decide (L[i] % 2 ≠ 0)) →
      input.regs 32 = L[i] / 2 →
      input.regs 23 = (if L[i] % 2 ≠ 0 then 1 else 0) →
      (∀ r, r ≠ 37 → r ≠ 29 → r ≠ 26 → r ≠ 28 → r ≠ 23 → r ≠ 32 →
        input.regs r = st.regs r) →
      F.IsPath (input.regs 26) parent [(L[i] / 2, decide (L[i] % 2 ≠ 0))] →
      input.regs 26 ∉ visited →
      ∃ out cost, Runs w p ω (propagateAndEnqueueForestChild entry) input .normal out cost ∧
        out.regs 29 = input.regs 29 ∧ Inv (insert (input.regs 26) visited) out ∧ cost ≤ 129 * limbs + 163) :
    ∃ out cost, Runs w p ω (propagateForestIncidence entry) st .normal out cost ∧
      out.regs 29 = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) ∧
      Inv (insert (F.src (L[i] / 2, decide (L[i] % 2 ≠ 0))) visited) out ∧
      cost ≤ 129 * limbs + 207 := by
  obtain ⟨input, hm, _, hchild, he, hd, hcur, hkeep, hpath, hskip, hvisit⟩ :=
    scanForestIncidence_runs (p := p) (ω := ω) (action := propagateAndEnqueueForestChild entry)
      hgraph hforest hmembers hlist hnext hi hcursor ht hc hn hnextRoom hflags hf hflagRoom hroom
  by_cases hv : F.src (L[i] / 2, decide (L[i] % 2 ≠ 0)) ∈ visited
  · exact ⟨input, 45, hskip hv, hcur,
      by simpa only [Finset.insert_eq_of_mem hv] using hskipInv input hm hkeep, by omega⟩
  · have hd' : input.regs 23 = (if L[i] % 2 ≠ 0 then 1 else 0) := by simpa using hd
    obtain ⟨out, cost, hr, hnext', hInv, hcost⟩ :=
      haction input hm hchild he hd' hkeep (hchild.symm ▸ hpath) (hchild.symm ▸ hv)
    exact ⟨out, cost + 44, hvisit hv hr, hnext'.trans hcur,
      by simpa only [hchild] using hInv, by omega⟩

/-- Scan the parent's adjacency list through its zero end marker. -/
@[expose] def propagateForestAdjacency (entry : ℕ) : Stmt :=
  .loop (.reg 29) (propagateForestIncidence entry)

/-- The adjacency loop charges for exactly the remaining entries and the
final end-marker test. The invariant tracks the cursor and traversal memory. -/
theorem propagateForestAdjacency_runs {w entry limbs : ℕ} {L : List ℕ}
    {p : Program} {ω : ℕ → Bool} (Inv : ℕ → State → Prop)
    (hcursor : ∀ i st, Inv i st →
      st.regs 29 = if i < L.length then L.getD i 0 + 1 else 0)
    (hstep : ∀ i st, i < L.length → Inv i st →
      ∃ out cost, Runs w p ω (propagateForestIncidence entry) st .normal out cost ∧
        Inv (i + 1) out ∧ cost ≤ 129 * limbs + 207)
    {i : ℕ} {st : State} (hi : i ≤ L.length) (hin : Inv i st) :
    ∃ out cost, Runs w p ω (propagateForestAdjacency entry) st .normal out cost ∧
      Inv L.length out ∧ cost ≤ (L.length - i) * (129 * limbs + 209) + 2 := by
  suffices h : ∀ n i st, i + n = L.length → Inv i st →
      ∃ out cost, Runs w p ω (propagateForestAdjacency entry) st .normal out cost ∧
        Inv L.length out ∧ cost ≤ n * (129 * limbs + 209) + 2 by
    exact h (L.length - i) i st (by omega) hin
  intro n
  induction n with
  | zero =>
    intro i st heq hin
    have he : i = L.length := by omega
    subst i
    have htest : Expr.eval w st (.reg 29) = some 0 := by
      simp [Expr.eval, hcursor _ _ hin]
    exact ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨htest, rfl, rfl, rfl⟩), hin, by simp⟩
  | succ n ih =>
    intro i st heq hin
    have hi : i < L.length := by omega
    have htest : Expr.eval w st (.reg 29) = some (L.getD i 0 + 1) := by
      simp [Expr.eval, hcursor _ _ hin, hi]
    obtain ⟨mid, c, hr, hmid, hc⟩ := hstep i st hi hin
    obtain ⟨out, d, hrest, hout, hd⟩ := ih (i + 1) mid (by omega) hmid
    refine ⟨out, c + 2 + d, runs_loop_iff.mpr (Or.inr (Or.inr
      ⟨L.getD i 0 + 1, mid, c, d, htest, by omega, hr, hrest, by simp [Expr.size]; omega⟩)),
      hout, ?_⟩
    rw [Nat.succ_mul]
    omega

/-- Open and scan the adjacency list of the named parent. -/
@[expose] def propagateForestParent (entry : ℕ) : Stmt :=
  loadForestIncidenceHead ;; propagateForestAdjacency entry

/-- Opening the list establishes the initial cursor, including for an
isolated parent. The remaining invariant is supplied by the traversal. -/
theorem propagateForestParent_runs {w a vc ec parent entry limbs : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hgraph : DynGraphAt st.mem a vc ec F) (hv : parent ∈ F.V)
    (hp : st.regs 25 = parent) (hm : st.regs 30 = dgExtToIntBase a vc)
    (hh : st.regs 31 = dgIncHeadBase a vc)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w)
    (Inv : List ℕ → ℕ → State → Prop)
    (hinit : ∀ mid L, mid.mem = st.mem → mid.pos = st.pos →
      (∀ r, r ≠ 29 → mid.regs r = st.regs r) →
      IsDoublyLinkedList st.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
        (dgIncHeadBase a vc + st.mem (dgExtToIntBase a vc + parent)) (2 * ec) L →
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) →
      mid.regs 29 = (if 0 < L.length then L.getD 0 0 + 1 else 0) → Inv L 0 mid)
    (hcursor : ∀ L i st, Inv L i st →
      st.regs 29 = if i < L.length then L.getD i 0 + 1 else 0)
    (hstep : ∀ L i st, i < L.length → Inv L i st →
      ∃ out cost, Runs w p ω (propagateForestIncidence entry) st .normal out cost ∧
        Inv L (i + 1) out ∧ cost ≤ 129 * limbs + 207) :
    ∃ out cost L, Runs w p ω (propagateForestParent entry) st .normal out cost ∧
      Inv L L.length out ∧ cost ≤ L.length * (129 * limbs + 209) + 11 := by
  obtain ⟨mid, L, hhead, hlist, hmembers, hc, hregs, hmem, hpos⟩ :=
    loadForestIncidenceHead_runs (p := p) (ω := ω) hgraph hv hp hm hh hroom
  have hc' : mid.regs 29 = (if 0 < L.length then L.getD 0 0 + 1 else 0) := by
    cases L <;> simpa using hc
  obtain ⟨out, cost, hr, hout, hcost⟩ :=
    propagateForestAdjacency_runs (Inv L) (hcursor L) (hstep L)
      (Nat.zero_le _) (hinit mid L hmem hpos hregs hlist hmembers hc')
  refine ⟨out, 8 + cost + 1, L, runs_seq_iff.mpr (Or.inr ⟨mid, 8, cost, hhead, hr, rfl⟩),
    hout, ?_⟩
  simp only [Nat.sub_zero] at hcost
  omega

/-- The vertex reached by following a half-edge out of its incident vertex. -/
@[expose] def forestIncidenceChild (F : MGraph) (j : ℕ) : ℕ :=
  F.src (j / 2, decide (j % 2 ≠ 0))

/-- The scan visits precisely the starting set together with the children
in the scanned prefix, regardless of whether some were already visited. -/
theorem propagateForestAdjacency_visited_runs {w entry limbs : ℕ} {L : List ℕ}
    {F : MGraph} {start : Finset ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (Inv : Finset ℕ → ℕ → State → Prop)
    (hcursor : ∀ visited i s, Inv visited i s →
      s.regs 29 = if i < L.length then L.getD i 0 + 1 else 0)
    (hstep : ∀ visited i s (hi : i < L.length), Inv visited i s →
      ∃ out cost, Runs w p ω (propagateForestIncidence entry) s .normal out cost ∧
        Inv (insert (forestIncidenceChild F L[i]) visited) (i + 1) out ∧
        cost ≤ 129 * limbs + 207)
    (hin : Inv start 0 st) :
    ∃ out cost, Runs w p ω (propagateForestAdjacency entry) st .normal out cost ∧
      Inv (start ∪ (L.map (forestIncidenceChild F)).toFinset) L.length out ∧
      cost ≤ L.length * (129 * limbs + 209) + 2 := by
  let visited (i : ℕ) := start ∪ ((L.take i).map (forestIncidenceChild F)).toFinset
  have hnext (i : ℕ) (hi : i < L.length) :
      visited (i + 1) = insert (forestIncidenceChild F L[i]) (visited i) := by
    simp only [visited, List.take_succ_eq_append_getElem hi, List.map_append,
      List.map_cons, List.map_nil, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    ext v
    simp [or_comm]
  obtain ⟨out, cost, hr, hout, hc⟩ :=
    propagateForestAdjacency_runs (fun i s => Inv (visited i) i s)
      (fun i s hs => hcursor (visited i) i s hs)
      (fun i s hi hs => by simpa only [hnext i hi] using hstep (visited i) i s hi hs)
      (Nat.zero_le _) (show Inv (visited 0) 0 st by simpa [visited] using hin)
  exact ⟨out, cost, hr, by simpa only [visited, List.take_length] using hout, by simpa using hc⟩

/-- The image of the incidence list consists of all neighbors of its parent.
The tail and head incidences use names `2 * e` and `2 * e + 1`, respectively. -/
theorem mem_forestIncidenceChildren_iff {F : MGraph} {ec parent child : ℕ} {L : List ℕ}
    (hcap : ∀ e ∈ F.E, e < ec)
    (hmembers : ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
      (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) :
    child ∈ (L.map (forestIncidenceChild F)).toFinset ↔
      ∃ e ∈ F.E, (F.tail e = parent ∧ F.head e = child) ∨
        (F.head e = parent ∧ F.tail e = child) := by
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨j, hj, hchild⟩
    obtain ⟨_, he, hp⟩ := (hmembers j).mp hj
    refine ⟨j / 2, he, ?_⟩
    by_cases h : j % 2 = 0
    · exact Or.inl ⟨by simpa [h] using hp, by simpa [forestIncidenceChild, MGraph.src, h] using hchild⟩
    · exact Or.inr ⟨by simpa [h] using hp, by simpa [forestIncidenceChild, MGraph.src, h] using hchild⟩
  · rintro ⟨e, he, hends | hends⟩
    · have hdiv : 2 * e / 2 = e := by omega
      have hmod : 2 * e % 2 = 0 := by omega
      have hlt := hcap e he
      exact ⟨2 * e, (hmembers _).mpr ⟨by omega, by simpa [hdiv] using he,
        by simpa [hdiv, hmod] using hends.1⟩,
        by simpa [forestIncidenceChild, MGraph.src, hdiv, hmod] using hends.2⟩
    · have hdiv : (2 * e + 1) / 2 = e := by omega
      have hmod : (2 * e + 1) % 2 = 1 := by omega
      have hlt := hcap e he
      exact ⟨2 * e + 1, (hmembers _).mpr ⟨by omega, by simpa [hdiv] using he,
        by simpa [hdiv, hmod] using hends.1⟩,
        by simpa [forestIncidenceChild, MGraph.src, hdiv, hmod] using hends.2⟩

/-- If every visited parent has had its incidence list scanned, visitation
is closed along any walk starting at a visited vertex. -/
theorem forestVisited_of_walk {F : MGraph} {visited : Finset ℕ}
    (hclosed : ∀ u ∈ visited, ∀ v, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) → v ∈ visited)
    {u v : ℕ} {P : List (ℕ × Bool)} (hwalk : F.IsWalk u v P)
    (hu : u ∈ visited) : v ∈ visited := by
  induction hwalk with
  | nil => exact hu
  | @cons u v edge P he hsrc _ ih =>
    apply ih
    apply hclosed u hu (F.dst edge)
    refine ⟨edge.1, he, ?_⟩
    cases edge with
    | mk e direction =>
      cases direction
      · exact Or.inr ⟨hsrc, rfl⟩
      · exact Or.inl ⟨hsrc, rfl⟩

/-- After the worklist has scanned all visited parents, visiting each
canonical root suffices to cover the forest's active vertices. -/
theorem forestVisited_covers_vertices {F : MGraph} {visited : Finset ℕ}
    (hroots : ∀ v ∈ F.V, Chain.compRoot F v ∈ visited)
    (hclosed : ∀ u ∈ visited, ∀ v, (∃ e ∈ F.E,
      (F.tail e = u ∧ F.head e = v) ∨ (F.head e = u ∧ F.tail e = v)) → v ∈ visited) :
    F.V ⊆ visited := by
  intro v hv
  obtain ⟨P, hwalk⟩ := MGraph.connected_symm (Chain.connected_compRoot F v)
  exact forestVisited_of_walk hclosed hwalk (hroots v hv)

end MinCostFlow.MinRatio
