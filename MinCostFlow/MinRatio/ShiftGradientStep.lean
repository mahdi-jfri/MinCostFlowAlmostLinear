module

public import MinCostFlow.MinRatio.ShiftGradientProgram
import MinCostFlow.MinRatio.PathSummaryWalk

/-!
# Writing a deeper gradient from a scanned edge

Definition 5.6 (page 18) gives the core gradient as the input gradient plus
the head potential minus the tail potential. The machine step computes
the named slots, calls the fixed-point routine, and keeps the scan cursor.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program Chain

/-- Prepare the six call arguments and write the gradient for register 18. -/
@[expose] def shiftGradientStep (entry : ℕ) : Stmt :=
  shiftGradientArgs ;; callShiftGradientCell entry

/-- The cell step preserves the edge-list registers and returns the
arithmetic postcondition for the selected edge slot. -/
theorem shiftGradientStep_runs {w h base vc ec e potential limbs src dst heap entry : ℕ}
    {G : MGraph} {p : Program} {st : State} {ω : ℕ → Bool} (gradient headPot tailPot : ℤ)
    (himpl : MeetsContract w p entry (writeCoreGradientCellContract w h gradient headPot tailPot))
    (hG : DynGraphAt st.mem base vc ec G) (he : e ∈ G.E)
    (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hr₁₃ : st.regs 13 = src) (hr₁₄ : st.regs 14 = dst)
    (hr₁₅ : st.regs 15 = dgETailSlotBase base vc ec)
    (hr₁₆ : st.regs 16 = dgEHeadSlotBase base vc ec)
    (hr₁₇ : st.regs 17 = dgIntToExtBase base vc)
    (hr₁₈ : st.regs 18 = e) (hr₂₀ : st.regs 20 = potential)
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hwords : ∀ a ∈ [src + e * limbs, potential + G.head e * limbs,
        potential + G.tail e * limbs, limbs, heap, dst + e * limbs], a < 2 ^ w)
    (hpre : (writeCoreGradientCellContract w h gradient headPot tailPot).pre
      [src + e * limbs, potential + G.head e * limbs, potential + G.tail e * limbs,
        limbs, heap, dst + e * limbs] st.mem) :
    ∃ out ret cost, Runs w p ω (shiftGradientStep entry) st .normal out cost ∧
      out.regs 4 = ret ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 4 → r ≠ 5 → out.regs r = st.regs r) ∧
      (writeCoreGradientCellContract w h gradient headPot tailPot).post
        [src + e * limbs, potential + G.head e * limbs, potential + G.tail e * limbs,
          limbs, heap, dst + e * limbs] st.mem ret out.mem ∧
      cost ≤ 129 * limbs + 157 := by
  obtain ⟨mid, hr, hs, hd, hh, ht, hregs, hm, _⟩ :=
    shiftGradientArgs_runs (ω := ω) hG he hroom hr₁₃ hr₁₄ hr₁₅ hr₁₆ hr₁₇ hr₁₈ hr₂₀ hr₃
      (hwords _ (by simp)) (hwords _ (by simp)) (hwords _ (by simp)) (hwords _ (by simp))
  obtain ⟨out, ret, c, hr', hret, hregs', hpost, hc⟩ :=
    callShiftGradientCell_runs (ω := ω) gradient headPot tailPot himpl hs hh ht
      ((hregs 3 (by decide) (by decide) (by decide) (by decide)).trans hr₃)
      ((hregs 4 (by decide) (by decide) (by decide) (by decide)).trans hr₄)
      hd hwords (hm.symm ▸ hpre)
  exact ⟨out, ret, 39 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 39, c, hr, hr', rfl⟩), hret,
    fun r h₀ h₁ h₂ h₄ h₅ => (hregs' r h₄).trans (hregs r h₀ h₁ h₂ h₅), hm ▸ hpost, by omega⟩

/-- The linked gradient step extends the set of prepared edge slots.
All previous slots survive provided they lie below the arithmetic heap. -/
theorem shiftGradientStep_extend_runs {w h base vc ec e potential limbs src dst heap entry : ℕ}
    {G : MGraph} {forest : LSF} {g : ℕ → ℝ} {done : Finset ℕ} {precision : ℕ} {p : Program} {st : State} {ω : ℕ → Bool} (ng potentialValue : ℕ → ℤ)
    (himpl : MeetsContract w p entry (writeCoreGradientCellContract w h (ng e)
      (potentialValue (G.head e)) (potentialValue (G.tail e))))
    (hG : DynGraphAt st.mem base vc ec G) (he : e ∈ G.E)
    (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hr₁₃ : st.regs 13 = src) (hr₁₄ : st.regs 14 = dst)
    (hr₁₅ : st.regs 15 = dgETailSlotBase base vc ec)
    (hr₁₆ : st.regs 16 = dgEHeadSlotBase base vc ec)
    (hr₁₇ : st.regs 17 = dgIntToExtBase base vc)
    (hr₁₈ : st.regs 18 = e) (hr₂₀ : st.regs 20 = potential)
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hwords : ∀ a ∈ [src + e * limbs, potential + G.head e * limbs,
        potential + G.tail e * limbs, limbs, heap, dst + e * limbs], a < 2 ^ w)
    (hpre : (writeCoreGradientCellContract w h (ng e) (potentialValue (G.head e))
      (potentialValue (G.tail e))).pre
      [src + e * limbs, potential + G.head e * limbs, potential + G.tail e * limbs,
        limbs, heap, dst + e * limbs] st.mem)
    (hg : g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (potentialValue v : ℝ) / (2 : ℝ) ^ precision)
    (hready : EdgeValuesAt st.mem dst h limbs precision done (coreGrad G forest g))
    (hslots : ∀ j ∈ done, dst + j * limbs + limbs ≤ heap)
    (hgHeap : base + dynGraphSize vc ec ≤ heap)
    (hgSep : base + dynGraphSize vc ec ≤ dst + e * limbs ∨ dst + e * limbs + limbs ≤ base) :
    ∃ out ret cost, Runs w p ω (shiftGradientStep entry) st .normal out cost ∧
      out.regs 4 = ret ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 4 → r ≠ 5 → out.regs r = st.regs r) ∧
      EdgeValuesAt out.mem dst h limbs precision (insert e done) (coreGrad G forest g) ∧
      DynGraphAt out.mem base vc ec G ∧
      cost ≤ 129 * limbs + 157 ∧ ret = heap + 3 * limbs ∧ ZeroFrom out.mem ret ∧
      (∀ a < heap, a < dst + e * limbs ∨ dst + e * limbs + limbs ≤ a →
        out.mem a = st.mem a) ∧
      (∀ (edges : List ℕ) listBase, ListAt st.mem listBase edges →
        listBase + edges.length ≤ heap →
        (listBase + edges.length ≤ dst + e * limbs ∨ dst + e * limbs + limbs ≤ listBase) →
        ListAt out.mem listBase edges) := by
  obtain ⟨out, ret, cost, hr, hret, hregs, hpost, hc⟩ :=
    shiftGradientStep_runs (ω := ω) (ng e) (potentialValue (G.head e))
      (potentialValue (G.tail e)) himpl hG he hroom hr₁₃ hr₁₄ hr₁₅ hr₁₆ hr₁₇
      hr₁₈ hr₂₀ hr₃ hr₄ hwords hpre
  have htable := writeCoreGradientCell_extend G forest g ng potentialValue hg hpot hready hslots hpost
  obtain ⟨a, b, c, L, scratch, target, hargs, hnext, _, hzero, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hgraph : DynGraphAt out.mem base vc ec G := hG.of_agree fun a hlo hhi =>
    hframe a (hhi.trans_le hgHeap) (by omega)
  refine ⟨out, ret, cost, hr, hret, hregs, htable, hgraph, hc, hnext, hzero, hframe, ?_⟩
  intro edges listBase hlist hbelow hdisjoint j hj
  rw [hframe _ (by omega) (by omega), hlist j hj]

/-- The arithmetic call can read its three inputs from the named gradient
and potential tables. Only the final result needs to fit its signed block. -/
theorem writeCoreGradientCell_pre_of_tables {w h limbs src potential dst heap e : ℕ}
    {G : MGraph} {mem : ℕ → ℕ} (ng pot : ℕ → ℤ)
    (hg : PathIntAt mem (src + e * limbs) h limbs (ng e))
    (hp : ∀ v ∈ G.V, PathIntAt mem (potential + v * limbs) h limbs (pot v))
    (hG : G.IsValid) (he : e ∈ G.E)
    (hsrc : src + e * limbs + limbs ≤ heap)
    (hpot : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ heap)
    (hdst : dst + e * limbs + limbs ≤ heap)
    (hfit : Num.Fits h limbs (ng e + (pot (G.head e) - pot (G.tail e))))
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w) :
    (writeCoreGradientCellContract w h (ng e) (pot (G.head e)) (pot (G.tail e))).pre
      [src + e * limbs, potential + G.head e * limbs, potential + G.tail e * limbs,
        limbs, heap, dst + e * limbs] mem := by
  have hend := hG e he
  exact ⟨_, _, _, _, _, _, rfl, hdst, hw, _, _, _, _, _, rfl, hsrc,
    hpot _ hend.2, hpot _ hend.1, hg, hp _ hend.2, hp _ hend.1, hfit, hzero, hroom⟩

/-- One scanned gradient write establishes the loop's cell triple.
The caller supplies reusable input tables and an invariant that tolerates
the destination write and the advance of the scratch heap. -/
theorem shiftGradientStep_scan_triple {w h base vc ec potential limbs src dst entry listBase precision : ℕ}
    {G : MGraph} {forest : LSF} {g : ℕ → ℝ} {p : Program}
    (edges : List ℕ) (i : ℕ) (hi : i < edges.length) (ng pot : ℕ → ℤ)
    (Ready : ℕ → State → Prop)
    (he : edges[i] ∈ G.E) (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hgradient : g edges[i] = (ng edges[i] : ℝ) / (2 : ℝ) ^ precision)
    (hpotential : ∀ v, treeRootPot forest.T g v = (pot v : ℝ) / (2 : ℝ) ^ precision)
    (himpl : MeetsContract w p entry (writeCoreGradientCellContract w h (ng edges[i])
      (pot (G.head edges[i])) (pot (G.tail edges[i]))))
    (hinputs : ∀ st, Ready i st →
      let e := edges[i]
      let heap := st.regs 4
      DynGraphAt st.mem base vc ec G ∧
      st.regs 13 = src ∧ st.regs 14 = dst ∧ st.regs 15 = dgETailSlotBase base vc ec ∧
      st.regs 16 = dgEHeadSlotBase base vc ec ∧ st.regs 17 = dgIntToExtBase base vc ∧
      st.regs 20 = potential ∧ st.regs 3 = limbs ∧
      (∀ a ∈ [src + e * limbs, potential + G.head e * limbs,
        potential + G.tail e * limbs, limbs, heap, dst + e * limbs], a < 2 ^ w) ∧
      (writeCoreGradientCellContract w h (ng e) (pot (G.head e)) (pot (G.tail e))).pre
        [src + e * limbs, potential + G.head e * limbs, potential + G.tail e * limbs,
          limbs, heap, dst + e * limbs] st.mem ∧
      (∀ j ∈ (edges.take i).toFinset, dst + j * limbs + limbs ≤ heap) ∧
      base + dynGraphSize vc ec ≤ heap ∧
      (base + dynGraphSize vc ec ≤ dst + e * limbs ∨ dst + e * limbs + limbs ≤ base) ∧
      listBase + edges.length ≤ heap ∧
      (listBase + edges.length ≤ dst + e * limbs ∨ dst + e * limbs + limbs ≤ listBase))
    (hadvance : ∀ (before out : State),
      Ready i before → out.regs 4 = before.regs 4 + 3 * limbs →
      ZeroFrom out.mem (out.regs 4) →
      (∀ a < before.regs 4, a < dst + edges[i] * limbs ∨ dst + edges[i] * limbs + limbs ≤ a →
        out.mem a = before.mem a) →
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 18 →
        out.regs r = before.regs r) →
      Ready (i + 1) { out with regs := Function.update out.regs 19 (i + 1) }) :
    Triple w p (fun st => ∃ before,
        shiftGradientTablePrefix edges listBase dst h limbs precision (coreGrad G forest g) i before ∧
        Ready i before ∧ st = { before with regs := Function.update before.regs 18 edges[i] })
      (shiftGradientStep entry)
      (normalPost fun out =>
        out.regs 19 = i ∧ out.regs 10 = listBase ∧ out.regs 11 = edges.length ∧
        ListAt out.mem listBase edges ∧
        EdgeValuesAt out.mem dst h limbs precision (insert edges[i] (edges.take i).toFinset)
          (coreGrad G forest g) ∧
        Ready (i + 1) { out with regs := Function.update out.regs 19 (i + 1) })
      (fun _ => 129 * limbs + 157) := by
  intro st bits hpre
  obtain ⟨before, ⟨hidx, hbase, hlen, hlist, htable⟩, hready, rfl⟩ := hpre
  let loaded := { before with regs := Function.update before.regs 18 edges[i] }
  have hreg (r : ℕ) (hne : r ≠ 18) : loaded.regs r = before.regs r :=
    Function.update_of_ne hne _ _
  obtain ⟨hG, h13, h14, h15, h16, h17, h20, h3, hwords, hcall, hslots,
    hgHeap, hgSep, hlistHeap, hlistSep⟩ := hinputs before hready
  obtain ⟨out, ret, c, hr, hret, hsaved, hout, _, hc, hnext, hzero, hframe, hscan⟩ :=
    shiftGradientStep_extend_runs (ω := bits) (st := loaded) ng pot himpl hG he hroom
      ((hreg 13 (by decide)).trans h13) ((hreg 14 (by decide)).trans h14)
      ((hreg 15 (by decide)).trans h15) ((hreg 16 (by decide)).trans h16)
      ((hreg 17 (by decide)).trans h17) (by simp [loaded])
      ((hreg 20 (by decide)).trans h20) ((hreg 3 (by decide)).trans h3)
      (hreg 4 (by decide)) hwords hcall hgradient hpotential htable hslots hgHeap hgSep
  have hframeReg r h₀ h₁ h₂ h₄ h₅ h₁₈ := (hsaved r h₀ h₁ h₂ h₄ h₅).trans (hreg r h₁₈)
  refine ⟨.normal, out, c, hr, ⟨?_, ?_, ?_, hscan edges listBase hlist hlistHeap hlistSep,
    hout, hadvance before out hready (hret.trans hnext) (hret.symm ▸ hzero) hframe hframeReg⟩, hc⟩
  · exact (hframeReg 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hidx
  · exact (hframeReg 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbase
  · exact (hframeReg 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlen

/-- Read-only data for the core-gradient scan (Definition 5.6, page 18).
The input gradient table and root potential table occupy named slots. -/
@[expose] def gradientScanInputsAt (mem : ℕ → ℕ) (G : MGraph)
    (graph vc ec src potential h limbs : ℕ) (ng pot : ℕ → ℤ) : Prop :=
  DynGraphAt mem graph vc ec G ∧
  (∀ e ∈ G.E, PathIntAt mem (src + e * limbs) h limbs (ng e)) ∧
  (∀ v ∈ G.V, PathIntAt mem (potential + v * limbs) h limbs (pot v))

/-- A destination write above the read-only prefix keeps all gradient
input words available for the next scanned edge. -/
theorem gradientScanInputsAt_of_prefix_frame {mem mem' : ℕ → ℕ} {G : MGraph}
    {graph vc ec src potential h limbs inputEnd : ℕ} {ng pot : ℕ → ℤ}
    (hinput : gradientScanInputsAt mem G graph vc ec src potential h limbs ng pot)
    (hg : graph + dynGraphSize vc ec ≤ inputEnd)
    (hs : ∀ e ∈ G.E, src + e * limbs + limbs ≤ inputEnd)
    (hp : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ inputEnd)
    (hframe : ∀ a < inputEnd, mem' a = mem a) :
    gradientScanInputsAt mem' G graph vc ec src potential h limbs ng pot := by
  refine ⟨hinput.1.of_agree (fun a _ ha => hframe a (ha.trans_le hg)), ?_, ?_⟩
  · intro e he
    exact (hinput.2.1 e he).congr fun j hj => hframe _ (by have := hs e he; omega)
  · intro v hv
    exact (hinput.2.2 v hv).congr fun j hj => hframe _ (by have := hp v hv; omega)

/-- The cell-writing contract preserves the read-only data when its
destination table starts beyond that data and the scratch heap follows it. -/
theorem writeCoreGradientCell_preserves_inputs {w h limbs src potential dst heap e ret : ℕ}
    {G : MGraph} {mem mem' : ℕ → ℕ} {graph vc ec : ℕ} (ng pot : ℕ → ℤ)
    (hinput : gradientScanInputsAt mem G graph vc ec src potential h limbs ng pot)
    (hg : graph + dynGraphSize vc ec ≤ dst)
    (hs : ∀ j ∈ G.E, src + j * limbs + limbs ≤ dst)
    (hp : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hheap : dst ≤ heap)
    (hpost : (writeCoreGradientCellContract w h (ng e) (pot (G.head e)) (pot (G.tail e))).post
      [src + e * limbs, potential + G.head e * limbs, potential + G.tail e * limbs,
        limbs, heap, dst + e * limbs] mem ret mem') :
    gradientScanInputsAt mem' G graph vc ec src potential h limbs ng pot := by
  obtain ⟨a, b, c, L, scratch, target, hargs, _, _, _, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  exact gradientScanInputsAt_of_prefix_frame hinput hg hs hp fun x hx =>
    hframe x (hx.trans_le hheap) (Or.inl (hx.trans_le (Nat.le_add_right _ _)))

/-- The scan retains the input tables and their pointers. The scratch
heap advances by three fixed-point blocks per processed edge. -/
@[expose] def gradientScanReady (G : MGraph)
    (graph vc ec src potential dst h limbs scratch : ℕ)
    (ng pot : ℕ → ℤ) (reference : ℕ → ℕ) (nextBase lengths i : ℕ) (st : State) : Prop :=
  gradientScanInputsAt st.mem G graph vc ec src potential h limbs ng pot ∧
  st.regs 13 = src ∧ st.regs 14 = dst ∧
  st.regs 15 = dgETailSlotBase graph vc ec ∧
  st.regs 16 = dgEHeadSlotBase graph vc ec ∧
  st.regs 17 = dgIntToExtBase graph vc ∧ st.regs 20 = potential ∧ st.regs 3 = limbs ∧
  st.regs 4 = scratch + 3 * limbs * i ∧ ZeroFrom st.mem (st.regs 4) ∧
  st.regs 6 = nextBase ∧ st.regs 7 = lengths ∧ (∀ a < dst, st.mem a = reference a)

/-- The loop's cell write preserves the input tables and advances the
heap invariant by one iteration. -/
theorem gradientScanReady_advance {G : MGraph}
    {graph vc ec src potential dst h limbs scratch i e : ℕ}
    {ng pot : ℕ → ℤ} {reference : ℕ → ℕ} {nextBase lengths : ℕ} {before out : State}
    (hready : gradientScanReady G graph vc ec src potential dst h limbs scratch ng pot reference nextBase lengths i before)
    (hg : graph + dynGraphSize vc ec ≤ dst)
    (hs : ∀ j ∈ G.E, src + j * limbs + limbs ≤ dst)
    (hp : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hdst : dst ≤ scratch)
    (hnext : out.regs 4 = before.regs 4 + 3 * limbs)
    (hzero : ZeroFrom out.mem (out.regs 4))
    (hframe : ∀ a < before.regs 4, a < dst + e * limbs ∨ dst + e * limbs + limbs ≤ a →
      out.mem a = before.mem a)
    (hregs : ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 4 → r ≠ 5 → r ≠ 18 →
      out.regs r = before.regs r) :
    gradientScanReady G graph vc ec src potential dst h limbs scratch ng pot reference nextBase lengths (i + 1)
      { out with regs := Function.update out.regs 19 (i + 1) } := by
  obtain ⟨hin, h13, h14, h15, h16, h17, h20, h3, h4, _, h6, h7, hmem⟩ := hready
  have hprefix : ∀ a < dst, out.mem a = before.mem a := by
    intro a ha
    apply hframe a (by omega)
    exact Or.inl (ha.trans_le (Nat.le_add_right _ _))
  have hreg (r : ℕ) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2)
      (h4 : r ≠ 4) (h5 : r ≠ 5) (h18 : r ≠ 18) (h19 : r ≠ 19) :
      (Function.update out.regs 19 (i + 1)) r = before.regs r :=
    (Function.update_of_ne h19 _ _).trans (hregs r h0 h1 h2 h4 h5 h18)
  have hheap : (Function.update out.regs 19 (i + 1)) 4 = scratch + 3 * limbs * (i + 1) := by
    rw [Function.update_of_ne (by decide : 4 ≠ 19), hnext, h4, Nat.mul_succ]
    omega
  refine ⟨gradientScanInputsAt_of_prefix_frame hin hg hs hp hprefix,
    (hreg 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13,
    (hreg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14,
    (hreg 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15,
    (hreg 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16,
    (hreg 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17,
    (hreg 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20,
    (hreg 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h3,
    hheap, ?_,
    (hreg 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h6,
    (hreg 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7,
    fun a ha => (hprefix a ha).trans (hmem a ha)⟩
  simpa [Function.update_of_ne] using hzero

/-- Instantiate the scan's cell triple with the named input tables and
the linear scratch allocation for the live edges. -/
theorem shiftGradientStep_ready_triple
    {w h base vc ec potential limbs src dst entry listBase precision scratch : ℕ}
    {G : MGraph} {forest : LSF} {g : ℕ → ℝ} {p : Program}
    {reference : ℕ → ℕ} {nextBase lengths : ℕ}
    (edges : List ℕ) (i : ℕ) (hi : i < edges.length) (ng pot : ℕ → ℤ)
    (hedges : ∀ e ∈ edges, e ∈ G.E)
    (hg : ∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (pot v : ℝ) / (2 : ℝ) ^ precision)
    (himpl : ∀ e ∈ G.E, MeetsContract w p entry
      (writeCoreGradientCellContract w h (ng e) (pot (G.head e)) (pot (G.tail e))))
    (hgEnd : base + dynGraphSize vc ec ≤ dst)
    (hsEnd : ∀ e ∈ G.E, src + e * limbs + limbs ≤ dst)
    (hpEnd : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hlEnd : listBase + edges.length ≤ dst)
    (hdEnd : ∀ e ∈ G.E, dst + e * limbs + limbs ≤ scratch)
    (hdScratch : dst ≤ scratch)
    (hfit : ∀ e ∈ G.E, Num.Fits h limbs (ng e + (pot (G.head e) - pot (G.tail e))))
    (hspace : scratch + 3 * limbs * edges.length < 2 ^ w) (hw : 2 < 2 ^ w) :
    let Ready := gradientScanReady G base vc ec src potential dst h limbs scratch ng pot reference nextBase lengths
    Triple w p (fun st => ∃ before,
        shiftGradientTablePrefix edges listBase dst h limbs precision (coreGrad G forest g) i before ∧
        Ready i before ∧ st = { before with regs := Function.update before.regs 18 edges[i] })
      (shiftGradientStep entry)
      (normalPost fun out =>
        out.regs 19 = i ∧ out.regs 10 = listBase ∧ out.regs 11 = edges.length ∧
        ListAt out.mem listBase edges ∧
        EdgeValuesAt out.mem dst h limbs precision (insert edges[i] (edges.take i).toFinset)
          (coreGrad G forest g) ∧
        Ready (i + 1) { out with regs := Function.update out.regs 19 (i + 1) })
      (fun _ => 129 * limbs + 157) := by
  let e := edges[i]
  have he : e ∈ G.E := hedges e (List.getElem_mem hi)
  have hbudget := Nat.mul_le_mul_left (3 * limbs) (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at hbudget
  have hGraphRoom : base + dynGraphSize vc ec ≤ 2 ^ w := by omega
  refine shiftGradientStep_scan_triple (src := src) (potential := potential) edges i hi ng pot _ he hGraphRoom
    (hg e he) hpot (himpl e he) ?_ ?_
  · intro st hready
    obtain ⟨hin, h13, h14, h15, h16, h17, h20, h3, h4, hz, _, _, _⟩ := hready
    have hheap : scratch ≤ st.regs 4 := by omega
    have hroom : st.regs 4 + 3 * limbs < 2 ^ w := by omega
    have hend := hin.1.1 e he
    have hs := (hsEnd e he).trans (hdScratch.trans hheap)
    have hd := (hdEnd e he).trans hheap
    have hp := fun v hv => (hpEnd v hv).trans (hdScratch.trans hheap)
    have hh := hp (G.head e) hend.2
    have ht := hp (G.tail e) hend.1
    have hwords : ∀ a ∈ [src + e * limbs, potential + G.head e * limbs,
        potential + G.tail e * limbs, limbs, st.regs 4, dst + e * limbs], a < 2 ^ w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hcall := writeCoreGradientCell_pre_of_tables ng pot (hin.2.1 e he) hin.2.2
      hin.1.1 he hs hp hd (hfit e he) hz hroom hw
    refine ⟨hin.1, h13, h14, h15, h16, h17, h20, h3, hwords, hcall, ?_,
      by omega, Or.inl (by omega), by omega, Or.inl (by omega)⟩
    intro j hj
    exact (hdEnd j (hedges j (List.mem_of_mem_take (List.mem_toFinset.mp hj)))).trans hheap
  · intro before out hready hout hz hm hr
    exact gradientScanReady_advance hready hgEnd hsEnd hpEnd hdScratch hout hz hm hr

/-- Prepare the complete core-gradient table on the next graph's live
edge names, given the represented root potentials of the current forest. -/
theorem prepareShiftGradientCells_runs
    {w h base vc ec nextBase nextVC nextEC src dst potential limbs scratch precision entry : ℕ}
    {G H : MGraph} {forest : LSF} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (ng pot : ℕ → ℤ) (nextLengths : ℕ → ℝ) (hsub : H.E ⊆ G.E)
    (hn : st.regs 6 = nextBase) (hnGraph : DynGraphAt st.mem nextBase nextVC nextEC H)
    (hready : gradientScanReady G base vc ec src potential dst h limbs scratch ng pot st.mem nextBase (st.regs 7) 0 st)
    (hg : ∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (pot v : ℝ) / (2 : ℝ) ^ precision)
    (himpl : ∀ e ∈ G.E, MeetsContract w p entry
      (writeCoreGradientCellContract w h (ng e) (pot (G.head e)) (pot (G.tail e))))
    (hgEnd : base + dynGraphSize vc ec ≤ dst)
    (hsEnd : ∀ e ∈ G.E, src + e * limbs + limbs ≤ dst)
    (hpEnd : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hnEnd : nextBase + dynGraphSize nextVC nextEC ≤ dst)
    (hlenTable : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ dst)
    (hdEnd : ∀ e ∈ G.E, dst + e * limbs + limbs ≤ scratch)
    (hdScratch : dst ≤ scratch)
    (hfit : ∀ e ∈ G.E, Num.Fits h limbs (ng e + (pot (G.head e) - pot (G.tail e))))
    (hspace : scratch + 3 * limbs * H.m < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareShiftGradients (shiftGradientStep entry)) st .normal out cost ∧
      EdgeValuesAt out.mem dst h limbs precision H.E (coreGrad G forest g) ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      gradientScanReady G base vc ec src potential dst h limbs scratch ng pot st.mem nextBase (st.regs 7) H.m out ∧
      cost ≤ (129 * limbs + 172) * H.m + 28 := by
  have hnRoom : nextBase + dynGraphSize nextVC nextEC < 2 ^ w := by omega
  obtain ⟨mid, edges, hread, hbase, hlen, hlist, hnames, hnd, hbound, hm, _, hregs⟩ :=
    readShiftGradientEdges_runs (ω := ω) hn hnGraph hnRoom hw
  have hcount : edges.length = H.m := by
    rw [← List.toFinset_card_of_nodup hnd, hnames]
    rfl
  have hlistEnd : dgEListBase nextBase nextVC nextEC + edges.length ≤ dst := by
    have hecap := hnGraph.2.2.1
    have hsub' : H.E ⊆ Finset.range nextEC := fun e he => Finset.mem_range.mpr (hecap e he)
    have hcard := Finset.card_le_card hsub'
    rw [Finset.card_range] at hcard
    change H.m ≤ nextEC at hcard
    unfold dgEListBase dynGraphSize at *
    omega
  let Ready := gradientScanReady G base vc ec src potential dst h limbs scratch ng pot st.mem nextBase (st.regs 7)
  have hinit : Ready 0 { mid with regs := Function.update mid.regs 19 0 } := by
    change gradientScanReady G base vc ec src potential dst h limbs scratch ng pot st.mem nextBase (st.regs 7) 0 _
    simpa (disch := decide) only [gradientScanReady, hm, Function.update_of_ne, hregs] using hready
  have hnames' : ∀ e ∈ edges, e ∈ H.E := fun e he =>
    hnames ▸ List.mem_toFinset.mpr he
  obtain ⟨out, c, hrun, htable, hfinal, hc⟩ :=
    prepareShiftGradientTable_edges_runs (ω := ω) edges (coreGrad G forest g) Ready (129 * limbs + 157)
      hnames hcount hbase hlen (hbase ▸ hlist) hinit (by omega) hbound
      (fun i hi => shiftGradientStep_ready_triple edges i hi ng pot
        (fun e he => hsub (hnames' e he)) hg hpot
        himpl hgEnd hsEnd hpEnd
        hlistEnd hdEnd hdScratch hfit
        (by rw [hcount]; exact hspace) (by omega))
  have hfinalFrame := hfinal
  obtain ⟨_, _, _, _, _, _, _, _, _, _, houtBase, houtLengths, houtMem⟩ := hfinalFrame
  have hgraph : DynGraphAt out.mem (out.regs 6) nextVC nextEC H := by
    rw [houtBase]
    exact hnGraph.of_agree fun a _ ha => houtMem a (ha.trans_le hnEnd)
  have hlengths : EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths := by
    rw [houtLengths]
    exact hlenTable.congr fun e he j hj => houtMem _ (by have := hlenEnd e he; omega)
  refine ⟨out, 20 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 20, c, hread, hrun, rfl⟩),
    htable, hgraph, hlengths, hcount ▸ hfinal, ?_⟩
  change c ≤ (129 * limbs + 172) * H.m + 7 at hc
  omega

/-- Finish preparing the deeper level's initializer arguments after the
gradient scan. Register 8 receives the destination gradient table. -/
@[expose] def prepareShiftGradientInputs (entry : ℕ) : Stmt :=
  prepareShiftGradients (shiftGradientStep entry) ;; .assign 8 (.reg 14)

/-- The completed scan supplies graph, lengths, gradients, and a fresh heap
in the argument registers used by the deeper rebuild. -/
theorem prepareShiftGradientInputs_runs
    {w h base vc ec nextBase nextVC nextEC src dst potential limbs scratch precision entry : ℕ}
    {G H : MGraph} {forest : LSF} {g : ℕ → ℝ} {p : Program} {st : State} {ω : ℕ → Bool}
    (ng pot : ℕ → ℤ) (nextLengths : ℕ → ℝ) (hsub : H.E ⊆ G.E)
    (hn : st.regs 6 = nextBase) (hnGraph : DynGraphAt st.mem nextBase nextVC nextEC H)
    (hready : gradientScanReady G base vc ec src potential dst h limbs scratch ng pot st.mem nextBase (st.regs 7) 0 st)
    (hg : ∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (pot v : ℝ) / (2 : ℝ) ^ precision)
    (himpl : ∀ e ∈ G.E, MeetsContract w p entry
      (writeCoreGradientCellContract w h (ng e) (pot (G.head e)) (pot (G.tail e))))
    (hgEnd : base + dynGraphSize vc ec ≤ dst)
    (hsEnd : ∀ e ∈ G.E, src + e * limbs + limbs ≤ dst)
    (hpEnd : ∀ v ∈ G.V, potential + v * limbs + limbs ≤ dst)
    (hnEnd : nextBase + dynGraphSize nextVC nextEC ≤ dst)
    (hlenTable : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ dst)
    (hdEnd : ∀ e ∈ G.E, dst + e * limbs + limbs ≤ scratch)
    (hdScratch : dst ≤ scratch)
    (hfit : ∀ e ∈ G.E, Num.Fits h limbs (ng e + (pot (G.head e) - pot (G.tail e))))
    (hspace : scratch + 3 * limbs * H.m < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareShiftGradientInputs entry) st .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧ out.regs 8 = dst ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (coreGrad G forest g) ∧
      out.regs 4 = scratch + 3 * limbs * H.m ∧ ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < dst, out.mem addr = st.mem addr) ∧
      cost ≤ (129 * limbs + 172) * H.m + 31 := by
  obtain ⟨mid, c, hr, hgTable, hgraph, hlengths, hready', hc⟩ :=
    prepareShiftGradientCells_runs (ω := ω) ng pot nextLengths hsub hn hnGraph hready
      hg hpot himpl hgEnd hsEnd hpEnd hnEnd hlenTable hlenEnd hdEnd hdScratch hfit hspace hw
  obtain ⟨_, _, hdst, _, _, _, _, _, hheap, hz, hnext, hlen, hframe⟩ := hready'
  let out := { mid with regs := Function.update mid.regs 8 dst }
  have hload : Runs w p ω (.assign 8 (.reg 14)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨dst, by simp [Expr.eval, hdst], rfl, rfl, rfl⟩
  refine ⟨out, c + 3, runs_seq_iff.mpr (Or.inr ⟨mid, c, 2, hr, hload, by omega⟩),
    ?_, ?_, by simp [out], ?_, ?_, ?_, ?_, ?_, hframe, by omega⟩
  · simpa [out, Function.update_of_ne] using hnext
  · simpa [out, Function.update_of_ne] using hlen
  · simpa [out, Function.update_of_ne] using hgraph
  · simpa [out, Function.update_of_ne] using hlengths
  · simpa [out] using hgTable
  · simpa [out, Function.update_of_ne] using hheap
  · simpa [out, Function.update_of_ne] using hz

/-- A signed parent edge uses the same fixed-point writer as a core
gradient. One of the two adjustment blocks is zero. The destination
slot then contains the child's potential at the original precision. -/
theorem writeForestPotentialCell_readout {w h limbs precision src addPtr subPtr heap dst ret : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool} {mem mem' : ℕ → ℕ}
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    (parentValue edgeValue : ℤ)
    (hparent : treeRootPot F g parent = (parentValue : ℝ) / (2 : ℝ) ^ precision)
    (hedge : g edge.1 = (edgeValue : ℝ) / (2 : ℝ) ^ precision)
    (hpost : (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)).post
      [src, addPtr, subPtr, limbs, heap, dst] mem ret mem') :
    Num.Valid mem' dst h limbs ∧ Num.fixVal mem' dst h limbs precision = treeRootPot F g child := by
  obtain ⟨a, b, c, L, scratch, target, hargs, _, hvalue, _, _⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  refine ⟨hvalue.1, ?_⟩
  rw [Num.fixVal, hvalue.2, treeRootPot_of_parent_edge hforest g hpath, hparent, hedge]
  cases hd : edge.2
  · simp [Int.cast_add, Int.cast_neg, add_div, neg_div]
  · simp [Int.cast_add, add_div]

/-- Reserve the zeroed potential table and one shared zero operand.
Register 21 holds the vertex name capacity and register 3 the limb count.
The potential table starts in register 20 and the zero operand in register 22. -/
@[expose] def reserveForestPotentials : Stmt :=
  .assign 20 (.reg 4) ;;
  .assign 22 (.bin .add (.reg 4) (.bin .mul (.reg 21) (.reg 3))) ;;
  .assign 4 (.bin .add (.reg 22) (.reg 3))

/-- Reserving zeroed storage gives each canonical root the correct
initial potential and leaves a zero operand for either orientation. -/
theorem reserveForestPotentials_runs {w heap vc limbs : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 4 = heap) (hv : st.regs 21 = vc) (hl : st.regs 3 = limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + vc * limbs + limbs < 2 ^ w)
    (hforest : F.IsForest) (g : ℕ → ℝ) (h precision : ℕ) :
    ∃ out, Runs w p ω reserveForestPotentials st .normal out 14 ∧
      out.regs 20 = heap ∧ out.regs 22 = heap + vc * limbs ∧
      out.regs 4 = heap + vc * limbs + limbs ∧
      PathIntAt out.mem (out.regs 22) h limbs 0 ∧
      (∀ v, compRoot F v < vc → Num.Valid out.mem (heap + compRoot F v * limbs) h limbs ∧
        Num.fixVal out.mem (heap + compRoot F v * limbs) h limbs precision =
          treeRootPot F g (compRoot F v)) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, r ≠ 20 → r ≠ 22 → r ≠ 4 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let first := { st with regs := Function.update st.regs 20 heap }
  let second := { first with regs := Function.update first.regs 22 (heap + vc * limbs) }
  let out := { second with regs := Function.update second.regs 4 (heap + vc * limbs + limbs) }
  have hmul : vc * limbs < 2 ^ w := by omega
  have hzeroAddr : heap + vc * limbs < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 20 (.reg 4)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, hh], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 22 (.bin .add (.reg 4) (.bin .mul (.reg 21) (.reg 3))))
      first .normal second 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, first, Function.update_of_ne, hh, hv, hl, hmul, hzeroAddr],
      rfl, rfl, rfl⟩
  have hlast : Runs w p ω (.assign 4 (.bin .add (.reg 22) (.reg 3))) second .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, second, first, Function.update_of_ne, hl, hroom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨first, 2, 11, hfirst,
      runs_seq_iff.mpr (Or.inr ⟨second, 6, 4, hsecond, hlast, rfl⟩), rfl⟩),
    by simp [out, second, first, Function.update_of_ne], by simp [out, second, Function.update_of_ne],
    by simp [out], ?_, ?_, ?_, ?_, rfl, rfl⟩
  · change PathIntAt st.mem (out.regs 22) h limbs 0
    have ha : heap ≤ out.regs 22 := by simp [out, second, Function.update_of_ne]
    exact ⟨Num.zeroFrom_valid hz ha, Num.intVal_zeroFrom hz ha⟩
  · intro v _
    rw [treeRootPot_componentRoot F hforest g v]
    exact ⟨Num.zeroFrom_valid hz (Nat.le_add_right _ _), Num.fixVal_zeroFrom hz (Nat.le_add_right _ _)⟩
  · intro a ha
    exact hz a (by change heap + vc * limbs + limbs ≤ a at ha; omega)
  · intro r h20 h22 h4
    simp [out, second, first, Function.update_of_ne, h20, h22, h4]

@[expose] def forestPotentialOperandPair (plus minus : ℕ) : Stmt :=
  .assign 1 (.reg plus) ;; .assign 2 (.reg minus)

/-- Use the edge gradient as an addition or subtraction according to
the child-to-parent direction in register 23. Register 24 contains
the edge gradient pointer and register 22 the shared zero pointer. -/
@[expose] def selectForestPotentialOperands : Stmt :=
  .cond (.reg 23) (forestPotentialOperandPair 24 22) (forestPotentialOperandPair 22 24)

private theorem forestPotentialOperandPair_runs {w plus minus a b : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (hp : st.regs plus = a) (hm : st.regs minus = b) (hne : minus ≠ 1) :
    ∃ out, Runs w p ω (forestPotentialOperandPair plus minus) st .normal out 5 ∧
      out.regs 1 = a ∧ out.regs 2 = b ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r, r ≠ 1 → r ≠ 2 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 1 a }
  let out := { mid with regs := Function.update mid.regs 2 b }
  have hr : Runs w p ω (.assign 1 (.reg plus)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨a, by simp [Expr.eval, hp], rfl, rfl, rfl⟩
  have hr' : Runs w p ω (.assign 2 (.reg minus)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨b, by simp [Expr.eval, mid, Function.update_of_ne hne, hm], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr, hr', rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], rfl, rfl, ?_⟩
  intro r h1 h2
  simp [out, mid, Function.update_of_ne h1, Function.update_of_ne h2]

/-- Operand selection takes seven steps and preserves all memory. -/
theorem selectForestPotentialOperands_runs {w edgePtr zeroPtr : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool} (forward : Bool)
    (hd : st.regs 23 = if forward then 1 else 0)
    (he : st.regs 24 = edgePtr) (hz : st.regs 22 = zeroPtr) :
    ∃ out, Runs w p ω selectForestPotentialOperands st .normal out 7 ∧
      out.regs 1 = (if forward then edgePtr else zeroPtr) ∧
      out.regs 2 = (if forward then zeroPtr else edgePtr) ∧
      out.mem = st.mem ∧ out.pos = st.pos ∧ (∀ r, r ≠ 1 → r ≠ 2 → out.regs r = st.regs r) := by
  cases forward
  · obtain ⟨out, hr, ha, hb, hm, hp, hframe⟩ :=
      forestPotentialOperandPair_runs (ω := ω) hz he (by decide)
    exact ⟨out, runs_cond_iff.mpr ⟨0, 5, by simp [Expr.eval, hd],
      by simpa using hr, rfl⟩, ha, hb, hm, hp, hframe⟩
  · obtain ⟨out, hr, ha, hb, hm, hp, hframe⟩ :=
      forestPotentialOperandPair_runs (ω := ω) he hz (by decide)
    exact ⟨out, runs_cond_iff.mpr ⟨1, 5, by simp [Expr.eval, hd],
      by simpa using hr, rfl⟩, ha, hb, hm, hp, hframe⟩

/-- Propagate one potential from parent to child using the fixed-point
writer. The traversal supplies the two vertex slots and the edge slot. -/
@[expose] def writeForestPotential (entry : ℕ) : Stmt :=
  selectForestPotentialOperands ;; callShiftGradientCell entry

/-- A parent-to-child step computes the child's exact potential in the
fixed-point table and leaves other caller cells intact. -/
theorem writeForestPotential_runs
    {w h limbs precision src edgePtr zeroPtr heap dst entry : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    (parentValue edgeValue : ℤ)
    (hparent : treeRootPot F g parent = (parentValue : ℝ) / (2 : ℝ) ^ precision)
    (hedge : g edge.1 = (edgeValue : ℝ) / (2 : ℝ) ^ precision)
    (himpl : MeetsContract w p entry (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)))
    (hr₀ : st.regs 0 = src) (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hr₅ : st.regs 5 = dst) (hr₂₂ : st.regs 22 = zeroPtr)
    (hr₂₃ : st.regs 23 = if edge.2 then 1 else 0) (hr₂₄ : st.regs 24 = edgePtr)
    (hsrc : PathIntAt st.mem src h limbs parentValue)
    (he : PathIntAt st.mem edgePtr h limbs edgeValue)
    (hz : PathIntAt st.mem zeroPtr h limbs 0)
    (hsRoom : src + limbs ≤ heap) (heRoom : edgePtr + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap) (hdRoom : dst + limbs ≤ heap)
    (hzero : ZeroFrom st.mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hfit : Num.Fits h limbs (parentValue +
      ((if edge.2 then edgeValue else 0) - (if edge.2 then 0 else edgeValue)))) :
    ∃ out ret cost, Runs w p ω (writeForestPotential entry) st .normal out cost ∧
      out.regs 4 = ret ∧ ret = heap + 3 * limbs ∧ ZeroFrom out.mem ret ∧
      Num.Valid out.mem dst h limbs ∧ Num.fixVal out.mem dst h limbs precision = treeRootPot F g child ∧
      (∀ a < heap, a < dst ∨ dst + limbs ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → out.regs r = st.regs r) ∧
      cost ≤ 129 * limbs + 125 := by
  let plus := if edge.2 then edgePtr else zeroPtr
  let minus := if edge.2 then zeroPtr else edgePtr
  have hplus : PathIntAt st.mem plus h limbs (if edge.2 then edgeValue else 0) := by
    cases hd : edge.2
    · simpa [plus, hd] using hz
    · simpa [plus, hd] using he
  have hminus : PathIntAt st.mem minus h limbs (if edge.2 then 0 else edgeValue) := by
    cases hd : edge.2
    · simpa [minus, hd] using he
    · simpa [minus, hd] using hz
  have hplusRoom : plus + limbs ≤ heap := by
    cases hd : edge.2
    · simpa [plus, hd] using hzRoom
    · simpa [plus, hd] using heRoom
  have hminusRoom : minus + limbs ≤ heap := by
    cases hd : edge.2
    · simpa [minus, hd] using heRoom
    · simpa [minus, hd] using hzRoom
  have hpre : (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)).pre
        [src, plus, minus, limbs, heap, dst] st.mem :=
    ⟨src, plus, minus, limbs, heap, dst, rfl, hdRoom, hw,
      src, plus, minus, limbs, heap, rfl, hsRoom, hplusRoom, hminusRoom,
      hsrc, hplus, hminus, hfit, hzero, hroom⟩
  have hwords : ∀ a ∈ [src, plus, minus, limbs, heap, dst], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨mid, hr, hp, hn, hm, _, hframe⟩ :=
    selectForestPotentialOperands_runs (ω := ω) edge.2 hr₂₃ hr₂₄ hr₂₂
  obtain ⟨out, ret, c, hc, hret, hcallRegs, hpost, hcost⟩ :=
    callShiftGradientCell_runs (ω := ω) parentValue _ _ himpl
      ((hframe 0 (by decide) (by decide)).trans hr₀) hp hn
      ((hframe 3 (by decide) (by decide)).trans hr₃)
      ((hframe 4 (by decide) (by decide)).trans hr₄)
      ((hframe 5 (by decide) (by decide)).trans hr₅) hwords (hm.symm ▸ hpre)
  have hpost' := hm ▸ hpost
  obtain ⟨hv, hvalue⟩ :=
    writeForestPotentialCell_readout hforest hpath g parentValue edgeValue hparent hedge hpost'
  obtain ⟨a, b, c', L, scratch, target, hargs, hnext, _, hzero', hmem⟩ := hpost'
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  exact ⟨out, ret, 7 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 7, c, hr, hc, rfl⟩),
    hret, hnext, hzero', hv, hvalue, hmem,
    fun r hr => (hcallRegs r (by omega)).trans (hframe r (by omega) (by omega)), by omega⟩

/-- Address the parent and child potential slots for a forest traversal step.
Registers 25 and 26 hold their vertex names, respectively. -/
@[expose] def forestPotentialAddresses : Stmt :=
  .assign 0 (.bin .add (.reg 20) (.bin .mul (.reg 25) (.reg 3))) ;;
  .assign 5 (.bin .add (.reg 20) (.bin .mul (.reg 26) (.reg 3)))

/-- Preparing both addresses takes thirteen steps and preserves the edge operands. -/
theorem forestPotentialAddresses_runs {w base limbs parent child : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 20 = base) (hl : st.regs 3 = limbs)
    (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hsrc : base + parent * limbs < 2 ^ w)
    (hdst : base + child * limbs < 2 ^ w) :
    ∃ out, Runs w p ω forestPotentialAddresses st .normal out 13 ∧
      out.regs 0 = base + parent * limbs ∧ out.regs 5 = base + child * limbs ∧
      (∀ r, r ≠ 0 → r ≠ 5 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := { st with regs := Function.update st.regs 0 (base + parent * limbs) }
  let out := { mid with regs := Function.update mid.regs 5 (base + child * limbs) }
  have hpMul : parent * limbs < 2 ^ w := by omega
  have hcMul : child * limbs < 2 ^ w := by omega
  have hfirst : Runs w p ω
      (.assign 0 (.bin .add (.reg 20) (.bin .mul (.reg 25) (.reg 3)))) st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hb, hp, hl, hpMul, hsrc],
      rfl, rfl, rfl⟩
  have hsecond : Runs w p ω
      (.assign 5 (.bin .add (.reg 20) (.bin .mul (.reg 26) (.reg 3)))) mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hb, hc, hl, hcMul, hdst],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r hr₀ hr₅
  simp [out, mid, Function.update_of_ne, hr₀, hr₅]

/-- Write a child potential from the names of the two vertices. -/
@[expose] def writeNamedForestPotential (entry : ℕ) : Stmt :=
  forestPotentialAddresses ;; writeForestPotential entry

/-- The named write preserves the other slots and charges for address calculation. -/
theorem writeNamedForestPotential_runs
    {w h limbs precision base edgePtr zeroPtr heap entry : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 20 = base) (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    (parentValue edgeValue : ℤ)
    (hparent : treeRootPot F g parent = (parentValue : ℝ) / (2 : ℝ) ^ precision)
    (hedge : g edge.1 = (edgeValue : ℝ) / (2 : ℝ) ^ precision)
    (himpl : MeetsContract w p entry (writeCoreGradientCellContract w h parentValue
      (if edge.2 then edgeValue else 0) (if edge.2 then 0 else edgeValue)))
    (hr₃ : st.regs 3 = limbs) (hr₄ : st.regs 4 = heap)
    (hr₂₂ : st.regs 22 = zeroPtr)
    (hr₂₃ : st.regs 23 = if edge.2 then 1 else 0) (hr₂₄ : st.regs 24 = edgePtr)
    (hsrc : PathIntAt st.mem (base + parent * limbs) h limbs parentValue)
    (he : PathIntAt st.mem edgePtr h limbs edgeValue)
    (hz : PathIntAt st.mem zeroPtr h limbs 0)
    (hsRoom : (base + parent * limbs) + limbs ≤ heap) (heRoom : edgePtr + limbs ≤ heap)
    (hzRoom : zeroPtr + limbs ≤ heap) (hdRoom : (base + child * limbs) + limbs ≤ heap)
    (hzero : ZeroFrom st.mem heap) (hroom : heap + 3 * limbs < 2 ^ w) (hw : 2 < 2 ^ w)
    (hfit : Num.Fits h limbs (parentValue +
      ((if edge.2 then edgeValue else 0) - (if edge.2 then 0 else edgeValue)))) :
    ∃ out ret cost, Runs w p ω (writeNamedForestPotential entry) st .normal out cost ∧
      out.regs 4 = ret ∧ ret = heap + 3 * limbs ∧ ZeroFrom out.mem ret ∧
      Num.Valid out.mem (base + child * limbs) h limbs ∧ Num.fixVal out.mem (base + child * limbs) h limbs precision = treeRootPot F g child ∧
      (∀ a < heap, a < (base + child * limbs) ∨ (base + child * limbs) + limbs ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → out.regs r = st.regs r) ∧
      cost ≤ 129 * limbs + 139 := by
  have hsrcAddr : base + parent * limbs < 2 ^ w := by omega
  have hdstAddr : base + child * limbs < 2 ^ w := by omega
  obtain ⟨mid, haddr, hm₀, hm₅, hregs, hmem, _⟩ :=
    forestPotentialAddresses_runs (ω := ω) hb hr₃ hp hc hsrcAddr hdstAddr
  obtain ⟨out, ret, cost, hrun, hret, hnext, hzout, hv, hg, hframe, hwriteRegs, hcost⟩ :=
    writeForestPotential_runs (ω := ω) hforest hpath g parentValue edgeValue hparent hedge
      himpl hm₀ ((hregs 3 (by decide) (by decide)).trans hr₃)
      ((hregs 4 (by decide) (by decide)).trans hr₄) hm₅
      ((hregs 22 (by decide) (by decide)).trans hr₂₂)
      ((hregs 23 (by decide) (by decide)).trans hr₂₃)
      ((hregs 24 (by decide) (by decide)).trans hr₂₄)
      (hmem.symm ▸ hsrc) (hmem.symm ▸ he) (hmem.symm ▸ hz)
      hsRoom heRoom hzRoom hdRoom (hmem.symm ▸ hzero) hroom hw hfit
  refine ⟨out, ret, 13 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 13, cost, haddr, hrun, rfl⟩),
    hret, hnext, hzout, hv, hg, ?_,
    fun r hr => (hwriteRegs r hr).trans (hregs r (by omega) (by omega)), by omega⟩
  simpa only [hmem] using hframe

/-- The vertices already visited have their Definition 5.6 root potentials
in the corresponding fixed-point slots. -/
@[expose] def ForestPotentialsAt (mem : ℕ → ℕ) (base h limbs precision : ℕ)
    (F : MGraph) (g : ℕ → ℝ) (visited : Finset ℕ) : Prop :=
  ∀ v ∈ visited, Num.Valid mem (base + v * limbs) h limbs ∧
    Num.fixVal mem (base + v * limbs) h limbs precision = treeRootPot F g v

/-- A child write extends the visited set while preserving every earlier potential. -/
theorem ForestPotentialsAt.insert_of_write
    {mem out : ℕ → ℕ} {base h limbs precision heap child : ℕ}
    {F : MGraph} {g : ℕ → ℝ} {visited : Finset ℕ}
    (hvisited : ForestPotentialsAt mem base h limbs precision F g visited)
    (hfresh : child ∉ visited)
    (hroom : ∀ v ∈ visited, base + v * limbs + limbs ≤ heap)
    (hchild : Num.Valid out (base + child * limbs) h limbs ∧
      Num.fixVal out (base + child * limbs) h limbs precision = treeRootPot F g child)
    (hframe : ∀ a < heap, a < base + child * limbs ∨
      base + child * limbs + limbs ≤ a → out a = mem a) :
    ForestPotentialsAt out base h limbs precision F g (insert child visited) := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact hchild
  obtain ⟨hvalid, hpot⟩ := hvisited v hv
  have hagree : ∀ j < limbs, out (base + v * limbs + j) = mem (base + v * limbs + j) := by
    intro j hj
    apply hframe _ (by have := hroom v hv; omega)
    have hne : v ≠ child := fun eq => hfresh (eq ▸ hv)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsep := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt hlt)
      simp only [Nat.succ_mul] at hsep
      exact Or.inl (by omega)
    · have hsep := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt hgt)
      simp only [Nat.succ_mul] at hsep
      exact Or.inr (by omega)
  exact ⟨fun j hj => (hagree j hj) ▸ hvalid j hj,
    by rw [Num.fixVal, Num.intVal_congr hagree]; exact hpot⟩

/-- The zeroed table already represents all canonical roots within the vertex
name capacity. These are the starting vertices of the potential traversal. -/
theorem reserveForestPotentials_roots_runs {w heap vc limbs : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 4 = heap) (hv : st.regs 21 = vc) (hl : st.regs 3 = limbs)
    (hz : ZeroFrom st.mem heap) (hroom : heap + vc * limbs + limbs < 2 ^ w)
    (hforest : F.IsForest) (g : ℕ → ℝ) (h precision : ℕ)
    (roots : Finset ℕ) (hroots : ∀ r ∈ roots, r < vc ∧ compRoot F r = r) :
    ∃ out, Runs w p ω reserveForestPotentials st .normal out 14 ∧
      out.regs 20 = heap ∧ out.regs 22 = heap + vc * limbs ∧
      out.regs 4 = heap + vc * limbs + limbs ∧
      PathIntAt out.mem (out.regs 22) h limbs 0 ∧
      ForestPotentialsAt out.mem heap h limbs precision F g roots ∧
      ZeroFrom out.mem (out.regs 4) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨out, hrun, htable, hzero, hheap, hvalue, hpot, htail, _, hmem, hpos⟩ :=
    reserveForestPotentials_runs (ω := ω) hh hv hl hz hroom hforest g h precision
  refine ⟨out, hrun, htable, hzero, hheap, hvalue, ?_, htail, hmem, hpos⟩
  intro r hr
  obtain ⟨hrCap, hrRoot⟩ := hroots r hr
  simpa only [hrRoot] using hpot r (hrRoot.symm ▸ hrCap)

/-- A named child write advances the traversal invariant when its parent has been visited. -/
theorem writeNamedForestPotential_insert_runs
    {w h limbs precision base edgePtr zeroPtr heap entry : ℕ}
    {F : MGraph} {child parent : ℕ} {edge : ℕ × Bool}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hb : st.regs 20 = base) (hp : st.regs 25 = parent) (hc : st.regs 26 = child)
    (hforest : F.IsForest) (hpath : F.IsPath child parent [edge]) (g : ℕ → ℝ)
    {visited : Finset ℕ} (hvisited : ForestPotentialsAt st.mem base h limbs precision F g visited)
    (hpVisited : parent ∈ visited) (hcFresh : child ∉ visited)
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
    ∃ out ret cost, Runs w p ω (writeNamedForestPotential entry) st .normal out cost ∧
      out.regs 4 = ret ∧ ret = heap + 3 * limbs ∧ ZeroFrom out.mem ret ∧
      ForestPotentialsAt out.mem base h limbs precision F g (insert child visited) ∧
      (∀ a < heap, a < (base + child * limbs) ∨ (base + child * limbs) + limbs ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r = 3 ∨ 6 ≤ r → out.regs r = st.regs r) ∧
      cost ≤ 129 * limbs + 139 := by
  obtain ⟨hvalid, hpot⟩ := hvisited parent hpVisited
  obtain ⟨out, ret, cost, hrun, hret, hnext, htail, hv, hg, hframe, hwriteRegs, hcost⟩ :=
    writeNamedForestPotential_runs (ω := ω) hb hp hc hforest hpath g _ edgeValue
      hpot.symm hedge himpl hr₃ hr₄ hr₂₂ hr₂₃ hr₂₄ ⟨hvalid, rfl⟩ he hz
      (hslots parent hpVisited) heRoom hzRoom hdRoom hzero hroom hw hfit
  exact ⟨out, ret, cost, hrun, hret, hnext, htail,
    hvisited.insert_of_write hcFresh hslots ⟨hv, hg⟩ hframe, hframe, hwriteRegs, hcost⟩

/-- A half-edge incident to the parent specifies the reverse orientation for
the potential recurrence, which follows the edge from child to parent. -/
theorem forestHalfEdge_childPath {F : MGraph} (hforest : F.IsForest)
    {j parent : ℕ} (he : j / 2 ∈ F.E)
    (hparent : (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) :
    let edge := (j / 2, decide (j % 2 ≠ 0))
    F.src edge ∈ F.V ∧ F.IsPath (F.src edge) parent [edge] := by
  let edge := (j / 2, decide (j % 2 ≠ 0))
  have hd : F.dst edge = parent := by
    by_cases hj : j % 2 = 0
    · simpa [edge, MGraph.dst, hj] using hparent
    · simpa [edge, MGraph.dst, hj] using hparent
  have hv : F.src edge ∈ F.V := by
    by_cases hj : j % 2 = 0
    · simpa [edge, MGraph.src, hj] using (hforest.1 _ he).2
    · simpa [edge, MGraph.src, hj] using (hforest.1 _ he).1
  have hwalk : F.IsWalk (F.src edge) parent [edge] :=
    .cons he rfl (hd.symm ▸ MGraph.IsWalk.nil _)
  have hne : F.src edge ≠ parent := by
    intro eq
    have hcycle : F.IsCycle [edge] :=
      ⟨by simp, by simp, parent, eq ▸ hwalk⟩
    exact hforest.2 _ hcycle
  refine ⟨hv, hwalk, ?_⟩
  change [F.src edge, F.dst edge].Nodup
  rw [hd]
  exact List.nodup_cons.mpr ⟨fun hm => hne (List.mem_singleton.mp hm), List.nodup_singleton parent⟩

/-- Read the next incidence cursor. Register 27 holds the next-pointer array
base and register 28 the current zero-based half-edge name. -/
@[expose] def loadForestIncidenceNext : Stmt :=
  .assign 29 (.load (.bin .add (.reg 27) (.reg 28)))

/-- The adjacency read returns either the next one-based cursor or zero at
the end of the list. It preserves memory and the input registers. -/
theorem loadForestIncidenceNext_runs {w prev next head cap i : ℕ} {L : List ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hlist : IsDoublyLinkedList st.mem prev next head cap L) (hi : i < L.length)
    (hb : st.regs 27 = next) (hj : st.regs 28 = L[i])
    (hroom : next + L[i] < 2 ^ w) :
    ∃ out, Runs w p ω loadForestIncidenceNext st .normal out 5 ∧
      out.regs 29 = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1) ∧
      (∀ r, r ≠ 29 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let value := st.mem (next + L[i])
  let out := { st with regs := Function.update st.regs 29 value }
  have hrun : Runs w p ω loadForestIncidenceNext st .normal out 5 :=
    runs_assign_iff.mpr ⟨value, by simp [Expr.eval, BinOp.eval, hb, hj, hroom, value],
      rfl, rfl, rfl⟩
  exact ⟨out, hrun, by simpa [out, value] using (hlist.2.2.2 i hi).2,
    fun r hr => Function.update_of_ne hr _ _, rfl, rfl⟩

/-- Open the adjacency list for the named parent in register 25. Registers
30 and 31 hold the name-to-slot and incidence-head array bases. -/
@[expose] def loadForestIncidenceHead : Stmt :=
  .assign 29 (.load (.bin .add (.reg 31) (.load (.bin .add (.reg 30) (.reg 25)))))

/-- The first cursor comes from the internal slot of the named parent,
and zero marks an empty incidence list. -/
theorem loadForestIncidenceHead_runs {w a vc ec parent : ℕ} {F : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hgraph : DynGraphAt st.mem a vc ec F) (hv : parent ∈ F.V)
    (hp : st.regs 25 = parent) (hm : st.regs 30 = dgExtToIntBase a vc)
    (hh : st.regs 31 = dgIncHeadBase a vc)
    (hroom : a + dynGraphSize vc ec ≤ 2 ^ w) :
    ∃ out L, Runs w p ω loadForestIncidenceHead st .normal out 8 ∧
      IsDoublyLinkedList st.mem (dgHePrevBase a vc ec) (dgHeNextBase a vc ec)
        (dgIncHeadBase a vc + st.mem (dgExtToIntBase a vc + parent)) (2 * ec) L ∧
      (∀ j, j ∈ L ↔ j < 2 * ec ∧ j / 2 ∈ F.E ∧
        (if j % 2 = 0 then F.tail (j / 2) else F.head (j / 2)) = parent) ∧
      out.regs 29 = (match L with | [] => 0 | j :: _ => j + 1) ∧
      (∀ r, r ≠ 29 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let slot := st.mem (dgExtToIntBase a vc + parent)
  have hvCap := hgraph.2.1
  have hslot : slot ∈ F.V := hgraph.2.2.2.2.2.2.2.2.2.1 parent hv |>.1
  have hparentLt := hvCap parent hv
  have hslotLt := hvCap slot hslot
  have hin : dgExtToIntBase a vc + parent < 2 ^ w := by
    simp only [dgExtToIntBase, dynGraphSize] at *
    omega
  have hout : dgIncHeadBase a vc + slot < 2 ^ w := by
    simp only [dgIncHeadBase, dynGraphSize] at *
    omega
  obtain ⟨L, hlist, hmembers⟩ := dynGraphAt_incident hgraph hv
  let value := st.mem (dgIncHeadBase a vc + slot)
  let out := { st with regs := Function.update st.regs 29 value }
  have hrun : Runs w p ω loadForestIncidenceHead st .normal out 8 :=
    runs_assign_iff.mpr ⟨value, by simp [Expr.eval, BinOp.eval, hp, hm, hh, hin, hout, slot, value],
      rfl, rfl, rfl⟩
  exact ⟨out, L, hrun, hlist, hmembers, by change value = _; exact hlist.2.2.1,
    fun r hr => Function.update_of_ne hr _ _, rfl, rfl⟩

/-- Decode a nonzero incidence cursor into its half-edge name, direction
toward the parent, and edge name. -/
@[expose] def decodeForestIncidence : Stmt :=
  .assign 28 (.bin .sub (.reg 29) (.const 1)) ;;
  .assign 23 (.bin .mod (.reg 28) (.const 2)) ;;
  .assign 32 (.bin .div (.reg 28) (.const 2))

/-- A live cursor decodes in fourteen steps without changing memory. -/
theorem decodeForestIncidence_runs {w j : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hc : st.regs 29 = j + 1) (hj : j < 2 ^ w) (hw : 2 < 2 ^ w) :
    ∃ out, Runs w p ω decodeForestIncidence st .normal out 14 ∧
      out.regs 28 = j ∧ out.regs 23 = (if j % 2 ≠ 0 then 1 else 0) ∧
      out.regs 32 = j / 2 ∧
      (∀ r, r ≠ 28 → r ≠ 23 → r ≠ 32 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let first := { st with regs := Function.update st.regs 28 j }
  let second := { first with regs := Function.update first.regs 23 (j % 2) }
  let out := { second with regs := Function.update second.regs 32 (j / 2) }
  have hone : 1 < 2 ^ w := by omega
  have hmod : j % 2 < 2 ^ w := by omega
  have hdiv : j / 2 < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 28 (.bin .sub (.reg 29) (.const 1))) st .normal first 4 :=
    runs_assign_iff.mpr ⟨j, by simp [Expr.eval, BinOp.eval, hc, hone, hj], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 23 (.bin .mod (.reg 28) (.const 2))) first .normal second 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, first, hw, hmod], rfl, rfl, rfl⟩
  have hthird : Runs w p ω (.assign 32 (.bin .div (.reg 28) (.const 2))) second .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, second, first, Function.update_of_ne, hw, hdiv],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨first, 4, 9, hfirst,
      runs_seq_iff.mpr (Or.inr ⟨second, 4, 4, hsecond, hthird, rfl⟩), rfl⟩),
    by simp [out, second, first, Function.update_of_ne], ?_, by simp [out], ?_, rfl, rfl⟩
  · change j % 2 = _
    split <;> omega
  · intro r h28 h23 h32
    simp [out, second, first, Function.update_of_ne, h28, h23, h32]

end MinCostFlow.MinRatio
