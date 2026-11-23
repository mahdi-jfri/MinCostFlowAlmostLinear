module

public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Link
import WordRAM.Logic

/-!
# Reading named graphs at a tool boundary

Section 2 (page 5) names vertices and edges by natural numbers. A tool
reads the active names and endpoints from the shared dynamic-graph layout.
Inactive edge endpoints are zero. This fixes the otherwise unused values
of the total endpoint functions when a model tool receives a graph.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open DynSpanner.Program

/-- Decode a dynamic named graph. Inactive edge endpoints are zero. -/
noncomputable def readNamedGraph (mem : ℕ → ℕ) (a vCap eCap : ℕ) : MGraph where
  V := (Finset.range vCap).filter fun v => mem (dgVPresBase a + v) = 1
  E := (Finset.range eCap).filter fun e => mem (dgEPresBase a vCap + e) = 1
  tail := fun e => if mem (dgEPresBase a vCap + e) = 1 ∧ e < eCap then
    mem (dgIntToExtBase a vCap + mem (dgETailSlotBase a vCap eCap + e)) else 0
  head := fun e => if mem (dgEPresBase a vCap + e) = 1 ∧ e < eCap then
    mem (dgIntToExtBase a vCap + mem (dgEHeadSlotBase a vCap eCap + e)) else 0

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open DynSpanner.Program

/-- Reading a represented graph recovers its active vertex names. -/
theorem readNamedGraph_vertices {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) : (readNamedGraph mem a vCap eCap).V = G.V := by
  classical
  ext v
  simp only [readNamedGraph, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hbit⟩
    have hv' := Finset.mem_range.mp hv
    have hcell := hG.2.2.2.2.2.2.2.1 v hv'
    by_contra hn
    simp only [hn, ↓reduceIte] at hcell
    omega
  · intro hv
    refine ⟨Finset.mem_range.mpr (hG.2.1 v hv), ?_⟩
    rw [hG.2.2.2.2.2.2.2.1 v (hG.2.1 v hv)]
    simp only [hv, ↓reduceIte]

/-- Reading a represented graph recovers its active edge names. -/
theorem readNamedGraph_edges {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) : (readNamedGraph mem a vCap eCap).E = G.E := by
  classical
  rcases hG with ⟨_, _, heCap, _, _, _, _, _, _, _, _, hpres, _⟩
  ext e
  simp only [readNamedGraph, Finset.mem_filter]
  constructor
  · rintro ⟨he, hbit⟩
    have hcell := hpres e (Finset.mem_range.mp he)
    by_contra hn
    simp only [hn, ↓reduceIte] at hcell
    omega
  · intro he
    refine ⟨Finset.mem_range.mpr (heCap e he), ?_⟩
    rw [hpres e (heCap e he)]
    simp only [he, ↓reduceIte]

/-- Slot indirection recovers both endpoints of every active edge. -/
theorem readNamedGraph_endpoints {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) {e : ℕ} (he : e ∈ G.E) :
    (readNamedGraph mem a vCap eCap).tail e = G.tail e ∧
    (readNamedGraph mem a vCap eCap).head e = G.head e := by
  classical
  rcases hG with ⟨hvalid, _, heCap, _, _, _, _, _, _, hind, _, hpres, _, hends, _⟩
  have hbit : mem (dgEPresBase a vCap + e) = 1 := by
    rw [hpres e (heCap e he)]
    simp only [he, ↓reduceIte]
  simp only [readNamedGraph, hbit, heCap e he, and_self, ↓reduceIte]
  rw [(hends e he).1, (hends e he).2]
  exact ⟨(hind _ (hvalid e he).1).2, (hind _ (hvalid e he).2).2⟩

/-- The adjacency list at a vertex's internal slot enumerates exactly its
incident half-edges. Even half-edges are tails and odd half-edges are heads. -/
theorem dynGraphAt_incident {mem : ℕ → ℕ} {a vc ec : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vc ec G) {v : ℕ} (hv : v ∈ G.V) :
    let slot := mem (dgExtToIntBase a vc + v)
    ∃ L, IsDoublyLinkedList mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
        (dgIncHeadBase a vc + slot) (2 * ec) L ∧
      ∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ G.E ∧
        (if j % 2 = 0 then G.tail (j / 2) else G.head (j / 2)) = v := by
  rcases hG with ⟨hvalid, hvCap, _, _, _, _, _, _, _, hind, _, _, _, hends, inc, hinc⟩
  let slot := mem (dgExtToIntBase a vc + v)
  obtain ⟨hlist, _, hmem⟩ := hinc slot (hvCap _ (hind v hv).1)
  refine ⟨inc slot, hlist, fun j => (hmem j).trans ?_⟩
  refine and_congr_right fun _ => and_congr_right fun he => ?_
  have hslot {u : ℕ} (hu : u ∈ G.V) : mem (dgExtToIntBase a vc + u) = slot ↔ u = v := by
    constructor
    · intro eq
      rw [← (hind u hu).2, eq]
      exact (hind v hv).2
    · rintro rfl
      rfl
  by_cases hj : j % 2 = 0
  · simpa only [hj, ↓reduceIte, (hends _ he).1] using hslot (hvalid _ he).1
  · simpa only [hj, ↓reduceIte, (hends _ he).2] using hslot (hvalid _ he).2

/-- A valid graph layout decodes to a valid model graph. -/
theorem readNamedGraph_valid {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) : (readNamedGraph mem a vCap eCap).IsValid := by
  intro e he
  rw [readNamedGraph_edges hG] at he
  rw [(readNamedGraph_endpoints hG he).1, (readNamedGraph_endpoints hG he).2,
    readNamedGraph_vertices hG]
  exact hG.1 e he

/-- The named graph block uses offsets and names, so reading it through
a memory function based at its start gives the same layout at zero. -/
theorem dynGraphAt_rebase_zero {mem : ℕ → ℕ} {base vc ec : ℕ} {G : MGraph} :
    DynGraphAt (fun offset => mem (base + offset)) 0 vc ec G ↔
      DynGraphAt mem base vc ec G := by
  simp only [DynGraphAt, IsDoublyLinkedList, WordRAM.ListAt, dgVCapOff, dgECapOff, dgNOff, dgMOff,
    dgVPresBase, dgVListBase, dgVPosBase, dgExtToIntBase, dgIntToExtBase,
    dgEPresBase, dgEListBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase,
    dgHePrevBase, dgHeNextBase, dgIncHeadBase, dgSlotDegBase, Nat.zero_add, Nat.add_zero, Nat.add_assoc]

/-- Copying every word at the same offset preserves the named graph
layout, including the adjacency lists and name maps. -/
theorem dynGraphAt_of_copy {mem mem' : ℕ → ℕ} {src dst vc ec : ℕ} {G : MGraph}
    (hG : DynGraphAt mem src vc ec G)
    (hcopy : ∀ offset < dynGraphSize vc ec, mem' (dst + offset) = mem (src + offset)) :
    DynGraphAt mem' dst vc ec G := by
  apply dynGraphAt_rebase_zero.mp
  exact (dynGraphAt_rebase_zero.mpr hG).of_agree (fun offset _ hlt => hcopy offset (by simpa using hlt))

/-- Copy a readout graph into caller memory before another linked call.
Registers 6, 10, and 11 hold the source, destination, and block size. -/
@[expose] def copyReadoutGraph : WordRAM.Stmt :=
  WordRAM.copyWordsStmt 6 10 11 12

/-- The caller-owned copy costs at most seventeen steps per layout word
plus seventeen. The cost depends on the layout capacities. -/
theorem copyReadoutGraph_runs {w src dst vc ec : ℕ} {G : MGraph}
    {p : WordRAM.Program} {st : WordRAM.State} {ω : ℕ → Bool}
    (hsrc : st.regs 6 = src) (hdst : st.regs 10 = dst)
    (hlen : st.regs 11 = dynGraphSize vc ec) (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ dst) (hword : dst + dynGraphSize vc ec < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) :
    ∃ out cost, WordRAM.Runs w p ω copyReadoutGraph st .normal out cost ∧
      DynGraphAt out.mem dst vc ec G ∧
      (∀ a, a < dst ∨ dst + dynGraphSize vc ec ≤ a → out.mem a = st.mem a) ∧
      out.pos = st.pos ∧ (∀ r ≠ 12, out.regs r = st.regs r) ∧
      cost ≤ 17 * (dynGraphSize vc ec + 1) := by
  let words := List.ofFn fun i : Fin (dynGraphSize vc ec) => st.mem (src + i.val)
  have hwlen : words.length = dynGraphSize vc ec := List.length_ofFn
  have hlist : WordRAM.ListAt st.mem src words := by
    intro i hi
    simp [words]
  obtain ⟨out, t, hr, hout, hmem, hp, hregs, hc⟩ :=
    WordRAM.Link.copyWords_runs (p := p) (ω := ω)
      (srcReg := 6) (dstReg := 10) (lenReg := 11) (idxReg := 12)
      (by decide) hsrc hdst (hlen.trans hwlen.symm) hlist
      (by rwa [hwlen]) (by rwa [hwlen]) hw
  refine ⟨out, t, hr, dynGraphAt_of_copy hG ?_, ?_, hp, hregs, by simpa only [hwlen] using hc⟩
  · intro offset hoff
    rw [hout offset (by rwa [hwlen])]
    simp only [words, List.getElem_ofFn]
  · simpa only [hwlen] using hmem

open WordRAM in
/-- Allocate a caller-owned graph copy at the current heap in register 5,
then return the advanced heap and the new graph pointer in registers 5 and 6. -/
@[expose] def copyReadoutGraphAtHeap : WordRAM.Stmt :=
  .assign 10 (.reg 5) ;; copyReadoutGraph ;;
  .assign 5 (.bin .add (.reg 10) (.reg 11)) ;; .assign 6 (.reg 10)

open WordRAM in
/-- The fresh copy preserves the old heap prefix and leaves all memory
beyond the new heap zero for the next linked call. -/
theorem copyReadoutGraphAtHeap_runs {w src heap vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hsrc : st.regs 6 = src) (hheap : st.regs 5 = heap)
    (hlen : st.regs 11 = dynGraphSize vc ec) (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out cost, Runs w p ω copyReadoutGraphAtHeap st .normal out cost ∧
      DynGraphAt out.mem heap vc ec G ∧
      out.regs 6 = heap ∧ out.regs 5 = heap + dynGraphSize vc ec ∧
      ZeroFrom out.mem (heap + dynGraphSize vc ec) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ out.pos = st.pos ∧
      cost ≤ 17 * (dynGraphSize vc ec + 1) + 11 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 10 → r ≠ 12 → out.regs r = st.regs r) := by
  let first := { st with regs := Function.update st.regs 10 heap }
  have hs : Runs w p ω (.assign 10 (.reg 5)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hheap], rfl, rfl, rfl⟩
  obtain ⟨mid, c, hr, hgraph, hmem, hp, hregs, hc⟩ :=
    copyReadoutGraph_runs (ω := ω) (st := first)
      (by simp [first, Function.update_of_ne, hsrc]) (by simp [first])
      (by simp [first, Function.update_of_ne, hlen]) hG hdisj hword hw
  let advanced := { mid with regs := Function.update mid.regs 5 (heap + dynGraphSize vc ec) }
  let out := { advanced with regs := Function.update advanced.regs 6 heap }
  have hb : mid.regs 10 = heap := by rw [hregs 10 (by decide)]; simp [first]
  have hn : mid.regs 11 = dynGraphSize vc ec := by
    rw [hregs 11 (by decide)]
    simp [first, Function.update_of_ne, hlen]
  have ha : Runs w p ω (.assign 5 (.bin .add (.reg 10) (.reg 11))) mid .normal advanced 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hb, hn, hword], rfl, rfl, rfl⟩
  have ho : Runs w p ω (.assign 6 (.reg 10)) advanced .normal out 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, advanced, Function.update_of_ne, hb], rfl, rfl, rfl⟩
  refine ⟨out, 2 + (c + (4 + 2 + 1) + 1) + 1, ?_, hgraph,
    by simp [out], by simp [out, advanced, Function.update_of_ne],
    fun a h => (hmem a (Or.inr h)).trans (hz a (by omega)),
    fun a h => hmem a (Or.inl h), hp, by omega, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨first, 2, _, hs,
      runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hr,
        runs_seq_iff.mpr (Or.inr ⟨advanced, 4, 2, ha, ho, rfl⟩), rfl⟩), rfl⟩)
  · intro r h5 h6 h10 h12
    simp only [out, advanced, Function.update_of_ne h6, Function.update_of_ne h5]
    rw [hregs r h12]
    exact Function.update_of_ne h10 _ _

open WordRAM in
/-- Read the capacity words and compute the dynamic graph block size
for the shift copy. Register 6 holds the graph and register 11 receives its size. -/
@[expose] def readGraphCopySize : Stmt :=
  .assign 11 (.bin .add
    (.bin .add (.const 4) (.bin .mul (.const 7) (.load (.reg 6))))
    (.bin .mul (.const 9) (.load (.bin .add (.reg 6) (.const 1)))))

open WordRAM in
/-- The graph header supplies the exact copy length in fourteen steps. -/
theorem readGraphCopySize_runs {w src vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hsrc : st.regs 6 = src) (hG : DynGraphAt st.mem src vc ec G)
    (haddr : src + 1 < 2 ^ w) (hword : dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w) :
    ∃ out, Runs w p ω readGraphCopySize st .normal out 14 ∧
      out.regs 11 = dynGraphSize vc ec ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r ≠ 11, out.regs r = st.regs r) := by
  have hv : st.mem src = vc := by simpa [dgVCapOff] using hG.2.2.2.1
  have he : st.mem (src + 1) = ec := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hsize : 4 + 7 * vc + 9 * ec < 2 ^ w := hword
  let out := { st with regs := Function.update st.regs 11 (dynGraphSize vc ec) }
  refine ⟨out, runs_assign_iff.mpr ⟨dynGraphSize vc ec, ?_, rfl, rfl, rfl⟩,
    by simp [out], rfl, rfl, fun _ hr => Function.update_of_ne hr _ _⟩
  simp [Expr.eval, BinOp.eval, hsrc, hv, he, haddr, dynGraphSize, hsize,
    show 1 < 2 ^ w by omega, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
    hw, show 7 * vc < 2 ^ w by omega, show 4 + 7 * vc < 2 ^ w by omega,
    show 9 * ec < 2 ^ w by omega]

open WordRAM in
/-- Copy the readout at the current heap using the size in its own header. -/
@[expose] def copyGraphFromHeader : Stmt :=
  readGraphCopySize ;; copyReadoutGraphAtHeap

open WordRAM in
/-- The complete copy and pointer handoff charge seventeen steps per
layout word plus forty-three steps, and preserve the previous heap prefix. -/
theorem copyGraphFromHeader_runs {w src heap vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hsrc : st.regs 6 = src) (hheap : st.regs 5 = heap)
    (hG : DynGraphAt st.mem src vc ec G)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w) (hz : ZeroFrom st.mem heap) :
    ∃ out cost, Runs w p ω copyGraphFromHeader st .normal out cost ∧
      DynGraphAt out.mem heap vc ec G ∧
      out.regs 6 = heap ∧ out.regs 5 = heap + dynGraphSize vc ec ∧
      ZeroFrom out.mem (heap + dynGraphSize vc ec) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ out.pos = st.pos ∧
      cost ≤ 17 * dynGraphSize vc ec + 43 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 10 → r ≠ 11 → r ≠ 12 → out.regs r = st.regs r) := by
  have hsize : 4 ≤ dynGraphSize vc ec := by unfold dynGraphSize; omega
  obtain ⟨mid, hr, hlen, hm, hp, hregs⟩ :=
    readGraphCopySize_runs (w := w) (ω := ω) hsrc hG (by omega) (by omega) hw
  obtain ⟨out, c, hc, hgraph, hptr, hnew, hz', hframe, hp', hcost, hregs'⟩ :=
    copyReadoutGraphAtHeap_runs (ω := ω) ((hregs 6 (by decide)).trans hsrc)
      ((hregs 5 (by decide)).trans hheap) hlen (hm.symm ▸ hG)
      hdisj hword (by omega) (hm.symm ▸ hz)
  refine ⟨out, 14 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 14, c, hr, hc, rfl⟩),
    hgraph, hptr, hnew, hz', fun a ha => (hframe a ha).trans (congrFun hm a),
    hp'.trans hp, by omega, ?_⟩
  intro r hr₅ hr₆ hr₁₀ hr₁₁ hr₁₂
  exact (hregs' r hr₅ hr₆ hr₁₀ hr₁₂).trans (hregs r hr₁₁)

end MinCostFlow.MinRatio
