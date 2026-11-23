module

public import MinCostFlow.MinRatio.ShiftModelPrefix
import WordRAM.Tactic
import MinCostFlow.MinRatio.PathCycleCoefficients
import MinCostFlow.MinRatio.TreeEditEndpoints

/-!
# Writing the gradients of the next Shift level

The gradient scan applies the forest potentials to each active edge.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- The fixed-point routine for a residual adjustment also computes one
core-gradient cell: subtract the tail potential from the head potential,
then add the original gradient (Definition 5.6, page 18). -/
theorem coreGradientCell_meetsContract {w h entry subtract add : ℕ} {p : Program}
    (gradient headPot tailPot : ℤ)
    (hp : p.HasAt entry [detectorRefreshBody subtract add])
    (hs : MeetsContract w p subtract (Num.subtractContract w h))
    (ha : MeetsContract w p add (Num.addContract w h)) :
    MeetsContract w p entry (detectorRefreshContract w h gradient headPot tailPot) :=
  detectorRefresh_meetsContract gradient headPot tailPot hp hs ha

/-- The routine's result block decodes to the next gradient at the
old precision, with no rounding step. -/
theorem coreGradientCell_readout {w h precision limbs source headPtr tailPtr heap ret : ℕ}
    {mem mem' : ℕ → ℕ} (G : MGraph) (forest : LSF) (g : ℕ → ℝ)
    (ng potential : ℕ → ℤ) (e : ℕ)
    (hg : g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (potential v : ℝ) / (2 : ℝ) ^ precision)
    (hout : (detectorRefreshContract w h (ng e) (potential (G.head e))
      (potential (G.tail e))).post [source, headPtr, tailPtr, limbs, heap] mem ret mem') :
    Num.Valid mem' (heap + 2 * limbs) h limbs ∧
      Num.fixVal mem' (heap + 2 * limbs) h limbs precision = coreGrad G forest g e := by
  obtain ⟨src, hp, tp, L, dst, hargs, _, hv, _, _⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  refine ⟨hv.1, ?_⟩
  rw [Num.fixVal, hv.2, coreGrad_dyadic G forest g ng potential precision hg hpot]
  congr 2
  omega

/-- A packed core-gradient cell can be copied back into its edge-name
slot. The disjoint copy allows the destination to precede the scratch heap. -/
theorem coreGradientCell_copy_readout {w h precision limbs dst scratch ret : ℕ}
    {mem mem' mem'' : ℕ → ℕ} (G : MGraph) (forest : LSF) (g : ℕ → ℝ)
    (ng potential : ℕ → ℤ) (e : ℕ) {source headPtr tailPtr heap : ℕ}
    (hg : g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (potential v : ℝ) / (2 : ℝ) ^ precision)
    (hout : (detectorRefreshContract w h (ng e) (potential (G.head e))
      (potential (G.tail e))).post [source, headPtr, tailPtr, limbs, heap] mem ret mem')
    (hcopy : (copyWordsContract w).post [heap + 2 * limbs, dst + e * limbs, limbs]
      mem' scratch mem'') :
    Num.Valid mem'' (dst + e * limbs) h limbs ∧
      Num.fixVal mem'' (dst + e * limbs) h limbs precision = coreGrad G forest g e := by
  obtain ⟨hv, he⟩ := coreGradientCell_readout G forest g ng potential e hg hpot hout
  obtain ⟨src, target, len, hargs, _, hwords, _⟩ := hcopy
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl⟩ := hargs
  have hcell : PathIntAt mem' (heap + 2 * limbs) h limbs
      (Num.intVal mem' (heap + 2 * limbs) h limbs) := ⟨hv, rfl⟩
  have hdst := hcell.congr hwords
  refine ⟨hdst.1, ?_⟩
  rw [Num.fixVal, hdst.2]
  exact he

/-- Evaluate a deeper gradient and copy it to the caller's edge slot.
The first five arguments are the arithmetic inputs and the sixth is the slot. -/
@[expose] def writeCoreGradientCell (arithmetic copy : ℕ) : Stmt :=
  .call 6 arithmetic [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 7 copy [.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 3)), .reg 5, .reg 3] ;;
  .ret (.reg 6)

/-- The edge slot lies below the scratch allocation. The call preserves
all other caller cells and returns the advanced scratch heap. -/
@[expose] def writeCoreGradientCellContract (w h : ℕ) (gradient headPot tailPot : ℤ) : Contract where
  pre args mem := ∃ source headPtr tailPtr limbs heap dst,
    args = [source, headPtr, tailPtr, limbs, heap, dst] ∧ dst + limbs ≤ heap ∧
    2 < 2 ^ w ∧ (detectorRefreshContract w h gradient headPot tailPot).pre
      [source, headPtr, tailPtr, limbs, heap] mem
  post args mem ret mem' := ∃ source headPtr tailPtr limbs heap dst,
    args = [source, headPtr, tailPtr, limbs, heap, dst] ∧ ret = heap + 3 * limbs ∧
    PathIntAt mem' dst h limbs (gradient + (headPot - tailPot)) ∧ ZeroFrom mem' ret ∧
    (∀ a < heap, a < dst ∨ dst + limbs ≤ a → mem' a = mem a)
  cost args _ := 129 * args.getD 3 0 + 110

/-- The two linked calls compute and store a gradient at the common
fixed-point precision (Definition 5.6, page 18). -/
theorem writeCoreGradientCell_meetsContract {w h entry arithmetic copy : ℕ} {p : Program}
    (gradient headPot tailPot : ℤ)
    (hp : p.HasAt entry [writeCoreGradientCell arithmetic copy])
    (ha : MeetsContract w p arithmetic (detectorRefreshContract w h gradient headPot tailPot))
    (hc : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (writeCoreGradientCellContract w h gradient headPot tailPot) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨source, headPtr, tailPtr, limbs, heap, dst, rfl, hdst, hw, harith⟩ := hpre
  have harithPre := harith
  obtain ⟨a, b, c, L, hp', hargs, _, _, _, _, _, _, _, _, hroom⟩ := harith
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hsw := hwords source (by simp)
  have hhw := hwords headPtr (by simp)
  have htw := hwords tailPtr (by simp)
  have hLw := hwords limbs (by simp)
  have hpw := hwords heap (by simp)
  have hdw := hwords dst (by simp)
  have htwice : 2 * limbs < 2 ^ w := by omega
  have hsrc : heap + 2 * limbs < 2 ^ w := by omega
  have hret : heap + 3 * limbs < 2 ^ w := hroom
  apply runs_start_le
  unfold writeCoreGradientCell
  refine runs_seq_call_le ha (vs := [source, headPtr, tailPtr, limbs, heap])
    (by eval_expr) (by wram_words) harithPre ?_
  intro next mem₁ pos₁ hpost
  obtain ⟨a, b, c, L, hp', hargs, hn, hv, hf, hz₁⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  have hnword : next < 2 ^ w := hn.symm ▸ hret
  refine runs_seq_call_le hc (vs := [heap + 2 * limbs, dst, limbs])
    (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨_, _, _, rfl, by omega, by omega, by omega, Or.inl (by omega)⟩
  · intro ignored mem₂ pos₂ hpost₂
    obtain ⟨a, b, L, hargs, _, hcopy, hframe⟩ := hpost₂
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl⟩ := hargs
    refine runs_ret_le (v := next) (by eval_expr) ?_ ?_
    · refine ⟨source, headPtr, tailPtr, limbs, heap, dst, rfl, hn, hv.congr hcopy, ?_, ?_⟩
      · intro a ha
        change next ≤ a at ha
        exact (hframe a (Or.inr (by omega))).trans (hz₁ a ha)
      · intro a ha houtside
        exact (hframe a houtside).trans (hf a ha)
    · simp only [writeCoreGradientCellContract, detectorRefreshContract, copyWordsContract,
        List.getD_cons_succ, List.getD_cons_zero, argsSize_cons, argsSize_nil, Expr.size_reg,
        Expr.size_const, Expr.size_bin]
      omega

/-- Writing one named edge slot adds it to the represented gradient table.
The fixed-point blocks of all previously prepared edge names are preserved. -/
theorem writeCoreGradientCell_extend {w h L precision base e source headPtr tailPtr heap ret : ℕ}
    {mem mem' : ℕ → ℕ} {done : Finset ℕ} (G : MGraph) (forest : LSF) (g : ℕ → ℝ)
    (ng potential : ℕ → ℤ)
    (hg : g e = (ng e : ℝ) / (2 : ℝ) ^ precision)
    (hpot : ∀ v, treeRootPot forest.T g v = (potential v : ℝ) / (2 : ℝ) ^ precision)
    (hready : EdgeValuesAt mem base h L precision done (coreGrad G forest g))
    (hroom : ∀ j ∈ done, base + j * L + L ≤ heap)
    (hout : (writeCoreGradientCellContract w h (ng e) (potential (G.head e))
      (potential (G.tail e))).post [source, headPtr, tailPtr, L, heap, base + e * L] mem ret mem') :
    EdgeValuesAt mem' base h L precision (insert e done) (coreGrad G forest g) := by
  obtain ⟨src, hp, tp, limbs, scratch, dst, hargs, _, hvalue, _, hframe⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
  intro j hj
  by_cases hje : j = e
  · subst j
    refine ⟨hvalue.1, ?_⟩
    rw [Num.fixVal, hvalue.2, coreGrad_dyadic G forest g ng potential precision hg hpot]
    congr 2
    omega
  · have hjdone := (Finset.mem_insert.mp hj).resolve_left hje
    obtain ⟨hv, he⟩ := hready j hjdone
    have hagree (k : ℕ) (hk : k < L) : mem' (base + j * L + k) = mem (base + j * L + k) := by
      apply hframe _ (by have := hroom j hjdone; omega)
      rcases lt_or_gt_of_ne hje with hjl | hjg
      · left
        have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hjl)
        rw [Nat.succ_mul] at hm
        omega
      · right
        have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hjg)
        rw [Nat.succ_mul] at hm
        omega
    exact ⟨fun k hk => hagree k hk ▸ hv k hk,
      (congrArg (fun z : ℤ => (z : ℝ) / (2 : ℝ) ^ precision) (Num.intVal_congr hagree)).trans he⟩

/-- Store one gradient for the first deeper level following Shift.
The output is indexed by its original edge name, as in Definition 5.7 (page 19). -/
theorem writeShiftGradientCell_extend {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i : ℕ) (hi : i < P.d)
    {w h limbs precision base e source headPtr tailPtr heap ret : ℕ}
    {mem mem' : ℕ → ℕ} {done : Finset ℕ} (ng potential : ℕ → ℤ) :
    let branch := (chain.bran i + 1) % P.k
    let forest := T.lsfs (T.restart (chain.scState i) branch) branch
    let current := chain.toTreeChain.chainGrad chain.g i
    let next := (algorithm1_shift T L P chain i).1.toTreeChain.chainGrad chain.g (i + 1)
    current e = (ng e : ℝ) / (2 : ℝ) ^ precision →
    (∀ v, treeRootPot forest.T current v = (potential v : ℝ) / (2 : ℝ) ^ precision) →
    EdgeValuesAt mem base h limbs precision done next →
    (∀ j ∈ done, base + j * limbs + limbs ≤ heap) →
    (writeCoreGradientCellContract w h (ng e) (potential ((chain.G i).head e))
      (potential ((chain.G i).tail e))).post
      [source, headPtr, tailPtr, limbs, heap, base + e * limbs] mem ret mem' →
    EdgeValuesAt mem' base h limbs precision (insert e done) next := by
  dsimp only
  rw [(shiftNextLevelNumbers T L P chain i hi).2]
  exact writeCoreGradientCell_extend (chain.G i) _ _ ng potential

/-- Visit the next sparsifier's live edge list. The cell body receives
the edge name in register 18 and the list index in register 19. -/
@[expose] def prepareShiftGradientTable (cell : Stmt) : Stmt :=
  forRange 19 (.const 0) (.reg 11)
    (.assign 18 (.load (.bin .add (.reg 10) (.reg 19))) ;; cell)

/-- The gradient loop reads only the list of live edges. The caller supplies
the cell triple, which must extend the represented gradient table for the
named edge and preserve the list. -/
theorem prepareShiftGradientTable_runs {w base : ℕ} {p : Program} {st : State}
    {cell : Stmt} {ω : ℕ → Bool} (edges : List ℕ) (Inv : ℕ → State → Prop)
    (cellCost : ℕ) (hw : 1 < 2 ^ w) (hbound : base + edges.length < 2 ^ w)
    (hin : Inv 0 { st with regs := Function.update st.regs 19 0 })
    (hindex : ∀ i s, i ≤ edges.length → Inv i s → s.regs 19 = i)
    (hstop : ∀ i s, i ≤ edges.length → Inv i s → s.regs 11 = edges.length)
    (hbase : ∀ i s, i < edges.length → Inv i s → s.regs 10 = base)
    (hlist : ∀ i s, i < edges.length → Inv i s → ListAt s.mem base edges)
    (hstep : ∀ i (hi : i < edges.length),
      Triple w p (fun s => ∃ before, Inv i before ∧
        s = { before with regs := Function.update before.regs 18 edges[i] }) cell
        (normalPost fun out => Inv (i + 1) { out with regs := Function.update out.regs 19 (i + 1) } ∧
          out.regs 19 = i) (fun _ => cellCost)) :
    ∃ out cost, Runs w p ω (prepareShiftGradientTable cell) st .normal out cost ∧
      Inv edges.length out ∧ cost ≤ (cellCost + 15) * edges.length + 7 := by
  let loadEdge := Stmt.assign 18 (.load (.bin .add (.reg 10) (.reg 19)))
  have hbody : ∀ i, 0 ≤ i → i < edges.length →
      Triple w p (Inv i) (loadEdge ;; cell)
        (normalPost fun out => Inv (i + 1) { out with regs := Function.update out.regs 19 (i + 1) } ∧
          out.regs 19 = i) (fun _ => cellCost + 6) := by
    intro i _ hi before bits hInv
    let mid := { before with regs := Function.update before.regs 18 edges[i] }
    have hload : Runs w p bits loadEdge before .normal mid 5 :=
      runs_assign_iff.mpr ⟨edges[i], by
        simp [Expr.eval, BinOp.eval, hbase i before hi hInv,
          hindex i before hi.le hInv, show base + i < 2 ^ w by omega,
          hlist i before hi hInv i hi], rfl, rfl, rfl⟩
    obtain ⟨o, out, c, hr, hp, hc⟩ := (hstep i hi).runs bits ⟨before, hInv, rfl⟩
    cases o with
    | returned _ => exact False.elim hp
    | normal =>
      exact ⟨.normal, out, 5 + c + 1,
        runs_seq_iff.mpr (Or.inr ⟨mid, 5, c, hload, hr, rfl⟩), hp, by change 5 + c + 1 ≤ cellCost + 6; omega⟩
  have hlo := Triple.forRange_const (p := p) (P := fun s => s = st) (Inv := Inv)
    (r := 19) (lo := .const 0) (hi := .reg 11) (cellCost + 6) 0 edges.length
    (Nat.zero_le _) hw (fun _ => by omega)
    (fun s hs => by subst s; exact ⟨by simp [Expr.eval], hin⟩)
    (fun i s _ hi h => hindex i s hi h)
    (fun i s _ hi h => by simp [Expr.eval, hstop i s hi h]) hbody
  obtain ⟨o, out, c, hr, hp, hc⟩ := hlo.runs ω rfl
  cases o with
  | returned _ => exact False.elim hp
  | normal =>
    exact ⟨out, c, hr, hp, by simpa [Expr.size, Nat.add_assoc, Nat.mul_comm] using hc⟩

/-- Read the live-edge list base and count from the caller-owned graph.
Register 6 holds the graph, and registers 10 and 11 receive the list and count. -/
@[expose] def readShiftGradientEdges : Stmt :=
  .assign 10 (.bin .add
    (.bin .add (.bin .add (.reg 6) (.const 4)) (.bin .mul (.const 7) (.load (.reg 6))))
    (.load (.bin .add (.reg 6) (.const 1)))) ;;
  .assign 11 (.load (.bin .add (.reg 6) (.const 3)))

/-- Obtain the list for the gradient loop in twenty steps. Its entries
are exactly the graph's live edge names, including for sparse name spaces. -/
theorem readShiftGradientEdges_runs {w base vc ec : ℕ} {p : Program} {st : State}
    {ω : ℕ → Bool} {G : MGraph}
    (hb : st.regs 6 = base) (hG : DynGraphAt st.mem base vc ec G)
    (hroom : base + dynGraphSize vc ec < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out edges, Runs w p ω readShiftGradientEdges st .normal out 20 ∧
      out.regs 10 = dgEListBase base vc ec ∧ out.regs 11 = edges.length ∧
      ListAt out.mem (out.regs 10) edges ∧ edges.toFinset = G.E ∧ edges.Nodup ∧
      dgEListBase base vc ec + edges.length < 2 ^ w ∧ out.mem = st.mem ∧ out.pos = st.pos ∧
      (∀ r, r ≠ 10 → r ≠ 11 → out.regs r = st.regs r) := by
  obtain ⟨_, _, hecap, hv, he, _, hm, _, _, _, _, _, ⟨edges, hlen, hnd, hnames, hlist, _⟩, _, _⟩ := hG
  have hv' : st.mem base = vc := by simpa [dgVCapOff] using hv
  have he' : st.mem (base + 1) = ec := by simpa [dgECapOff] using he
  have hm' : st.mem (base + 3) = G.m := by simpa [dgMOff] using hm
  have hsz : edges.length ≤ ec := by
    have hsub : G.E ⊆ Finset.range ec := fun e he => Finset.mem_range.mpr (hecap e he)
    rw [hlen]
    simpa [MGraph.m] using Finset.card_le_card hsub
  have hroom' : base + 4 + 7 * vc + 9 * ec < 2 ^ w := by
    unfold dynGraphSize at hroom
    omega
  let mid := { st with regs := Function.update st.regs 10 (dgEListBase base vc ec) }
  let out := { mid with regs := Function.update mid.regs 11 G.m }
  have hfirst : Runs w p ω (.assign 10 (.bin .add
      (.bin .add (.bin .add (.reg 6) (.const 4)) (.bin .mul (.const 7) (.load (.reg 6))))
      (.load (.bin .add (.reg 6) (.const 1))))) st .normal mid 14 := by
    refine runs_assign_iff.mpr ⟨dgEListBase base vc ec, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, BinOp.eval, hb, hv', he', dgEListBase, hw,
      show 4 < 2 ^ w by omega, show 1 < 2 ^ w by omega, show base + 1 < 2 ^ w by omega,
      show base + 4 < 2 ^ w by omega, show 7 * vc < 2 ^ w by omega,
      show base + 4 + 7 * vc < 2 ^ w by omega, show base + 4 + 7 * vc + ec < 2 ^ w by omega]
  have hsecond : Runs w p ω (.assign 11 (.load (.bin .add (.reg 6) (.const 3)))) mid .normal out 5 :=
    runs_assign_iff.mpr ⟨G.m, by
      simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hb, hm',
        show 3 < 2 ^ w by omega, show base + 3 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hbase : out.regs 10 = dgEListBase base vc ec := by simp [out, mid, Function.update_of_ne]
  refine ⟨out, edges, runs_seq_iff.mpr (Or.inr ⟨mid, 14, 5, hfirst, hsecond, rfl⟩),
    hbase, by simp [out, hlen], hbase.symm ▸ hlist, ?_, hnd, ?_, rfl, rfl, ?_⟩
  · ext e
    simpa using hnames e
  · unfold dgEListBase
    omega
  · intro r h10 h11
    simp [out, mid, Function.update_of_ne h10, Function.update_of_ne h11]

/-- Loop invariant for the deeper gradient table. The completed cells
are precisely the edge names in the visited list prefix. -/
@[expose] def shiftGradientTablePrefix (edges : List ℕ) (listBase table h limbs precision : ℕ)
    (gradient : ℕ → ℝ) (i : ℕ) (st : State) : Prop :=
  st.regs 19 = i ∧ st.regs 10 = listBase ∧ st.regs 11 = edges.length ∧
    ListAt st.mem listBase edges ∧
    EdgeValuesAt st.mem table h limbs precision (edges.take i).toFinset gradient

/-- A cell step that extends the table at the loaded edge name is enough
to prepare all live gradients. Its other state properties are threaded
through the loop as a caller invariant. -/
theorem prepareShiftGradientTable_edges_runs {w listBase table h limbs precision : ℕ}
    {p : Program} {st : State} {cell : Stmt} {ω : ℕ → Bool} {G : MGraph}
    (edges : List ℕ) (gradient : ℕ → ℝ) (Ready : ℕ → State → Prop) (cellCost : ℕ)
    (hnames : edges.toFinset = G.E) (hlength : edges.length = G.m)
    (hbase : st.regs 10 = listBase) (hlen : st.regs 11 = edges.length)
    (hlist : ListAt st.mem listBase edges)
    (hinit : Ready 0 { st with regs := Function.update st.regs 19 0 })
    (hw : 1 < 2 ^ w) (hbound : listBase + edges.length < 2 ^ w)
    (hcell : ∀ i (hi : i < edges.length),
      Triple w p (fun s => ∃ before,
        shiftGradientTablePrefix edges listBase table h limbs precision gradient i before ∧
        Ready i before ∧ s = { before with regs := Function.update before.regs 18 edges[i] }) cell
        (normalPost fun out =>
          out.regs 19 = i ∧ out.regs 10 = listBase ∧ out.regs 11 = edges.length ∧
          ListAt out.mem listBase edges ∧
          EdgeValuesAt out.mem table h limbs precision
            (insert edges[i] (edges.take i).toFinset) gradient ∧
          Ready (i + 1) { out with regs := Function.update out.regs 19 (i + 1) })
        (fun _ => cellCost)) :
    ∃ out cost, Runs w p ω (prepareShiftGradientTable cell) st .normal out cost ∧
      EdgeValuesAt out.mem table h limbs precision G.E gradient ∧
      Ready edges.length out ∧ cost ≤ (cellCost + 15) * G.m + 7 := by
  let Inv := fun i s =>
    shiftGradientTablePrefix edges listBase table h limbs precision gradient i s ∧ Ready i s
  have hin : Inv 0 { st with regs := Function.update st.regs 19 0 } := by
    exact ⟨⟨by simp, by simp [Function.update_of_ne, hbase],
      by simp [Function.update_of_ne, hlen], hlist, by simp [EdgeValuesAt]⟩, hinit⟩
  have hstep : ∀ i (hi : i < edges.length),
      Triple w p (fun s => ∃ before, Inv i before ∧
        s = { before with regs := Function.update before.regs 18 edges[i] }) cell
        (normalPost fun out => Inv (i + 1) { out with regs := Function.update out.regs 19 (i + 1) } ∧
          out.regs 19 = i) (fun _ => cellCost) := by
    intro i hi s bits hpre
    obtain ⟨before, ⟨hprefix, hready⟩, rfl⟩ := hpre
    obtain ⟨o, out, c, hr, hp, hc⟩ := (hcell i hi).runs bits ⟨before, hprefix, hready, rfl⟩
    cases o with
    | returned _ => exact False.elim hp
    | normal =>
      obtain ⟨hidx, hb, hn, hlist', htable, hready'⟩ := hp
      have hnames' : (edges.take (i + 1)).toFinset = insert edges[i] (edges.take i).toFinset := by
        rw [List.take_succ_eq_append_getElem hi]
        ext e
        simp only [List.mem_toFinset, List.mem_append, List.mem_singleton, Finset.mem_insert, or_comm]
      exact ⟨.normal, out, c, hr, ⟨⟨⟨by simp, by simp [Function.update_of_ne, hb],
        by simp [Function.update_of_ne, hn], hlist', hnames'.symm ▸ htable⟩, hready'⟩, hidx⟩, hc⟩
  obtain ⟨out, cost, hr, ⟨hprefix, hready⟩, hc⟩ :=
    prepareShiftGradientTable_runs (ω := ω) edges Inv cellCost hw hbound hin
      (fun _ _ _ h => h.1.1) (fun _ _ _ h => h.1.2.2.1)
      (fun _ _ _ h => h.1.2.1) (fun _ _ _ h => h.1.2.2.2.1) hstep
  have htable := hprefix.2.2.2.2
  rw [List.take_length, hnames] at htable
  exact ⟨out, cost, hr, htable, hready, hlength ▸ hc⟩

/-- Read and scan the copied sparsifier's live edges to prepare its
gradient table for the next level. -/
@[expose] def prepareShiftGradients (cell : Stmt) : Stmt :=
  readShiftGradientEdges ;; prepareShiftGradientTable cell

/-- The header and scan compose using the list supplied by the graph
layout, charging the cell cost plus fifteen steps per live edge. -/
theorem prepareShiftGradients_runs {w base vc ec table h limbs precision : ℕ}
    {p : Program} {st : State} {cell : Stmt} {ω : ℕ → Bool} {G : MGraph}
    (gradient : ℕ → ℝ) (Ready : ℕ → State → Prop) (cellCost : ℕ)
    (hb : st.regs 6 = base) (hG : DynGraphAt st.mem base vc ec G)
    (hroom : base + dynGraphSize vc ec < 2 ^ w) (hw : 7 < 2 ^ w)
    (hinit : ∀ mid, Runs w p ω readShiftGradientEdges st .normal mid 20 →
      Ready 0 { mid with regs := Function.update mid.regs 19 0 })
    (hcell : ∀ (edges : List ℕ), edges.toFinset = G.E → edges.Nodup → ∀ i (hi : i < edges.length),
      Triple w p (fun s => ∃ before,
        shiftGradientTablePrefix edges (dgEListBase base vc ec) table h limbs precision gradient i before ∧
        Ready i before ∧ s = { before with regs := Function.update before.regs 18 edges[i] }) cell
        (normalPost fun out =>
          out.regs 19 = i ∧ out.regs 10 = dgEListBase base vc ec ∧ out.regs 11 = edges.length ∧
          ListAt out.mem (dgEListBase base vc ec) edges ∧
          EdgeValuesAt out.mem table h limbs precision
            (insert edges[i] (edges.take i).toFinset) gradient ∧
          Ready (i + 1) { out with regs := Function.update out.regs 19 (i + 1) })
        (fun _ => cellCost)) :
    ∃ out cost, Runs w p ω (prepareShiftGradients cell) st .normal out cost ∧
      EdgeValuesAt out.mem table h limbs precision G.E gradient ∧
      Ready G.m out ∧ cost ≤ (cellCost + 15) * G.m + 28 := by
  obtain ⟨mid, edges, hr, he, hn, hlist, hnames, hnd, hbound, _, _, _⟩ :=
    readShiftGradientEdges_runs (ω := ω) hb hG hroom hw
  have hcount : edges.length = G.m := by
    rw [← List.toFinset_card_of_nodup hnd, hnames]
    rfl
  obtain ⟨out, c, hloop, htable, hready, hc⟩ :=
    prepareShiftGradientTable_edges_runs (ω := ω) edges gradient Ready cellCost hnames hcount
      he hn (he ▸ hlist) (hinit mid hr) (by omega) hbound (hcell edges hnames hnd)
  exact ⟨out, 20 + c + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 20, c, hr, hloop, rfl⟩),
    htable, hcount ▸ hready, by omega⟩

/-- Compute the old and new gradient slots for the edge in register 18.
Registers 13 and 14 hold the old and new table bases. -/
@[expose] def shiftGradientSlotArgs : Stmt :=
  .assign 0 (.bin .add (.reg 13) (.bin .mul (.reg 18) (.reg 3))) ;;
  .assign 5 (.bin .add (.reg 14) (.bin .mul (.reg 18) (.reg 3)))

/-- The two slot addresses fit the call ABI and cost thirteen steps. -/
theorem shiftGradientSlotArgs_runs {w src dst edge limbs : ℕ} {p : Program}
    {st : State} {ω : ℕ → Bool}
    (hs : st.regs 13 = src) (hd : st.regs 14 = dst)
    (he : st.regs 18 = edge) (hl : st.regs 3 = limbs)
    (hsw : src + edge * limbs < 2 ^ w) (hdw : dst + edge * limbs < 2 ^ w) :
    ∃ out, Runs w p ω shiftGradientSlotArgs st .normal out 13 ∧
      out.regs 0 = src + edge * limbs ∧ out.regs 5 = dst + edge * limbs ∧
      (∀ r, r ≠ 0 → r ≠ 5 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  have hmul : edge * limbs < 2 ^ w := by omega
  let mid := { st with regs := Function.update st.regs 0 (src + edge * limbs) }
  let out := { mid with regs := Function.update mid.regs 5 (dst + edge * limbs) }
  have hr : Runs w p ω (.assign 0 (.bin .add (.reg 13) (.bin .mul (.reg 18) (.reg 3))))
      st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hs, he, hl, hmul, hsw], rfl, rfl, rfl⟩
  have hr' : Runs w p ω (.assign 5 (.bin .add (.reg 14) (.bin .mul (.reg 18) (.reg 3))))
      mid .normal out 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, hd, he, hl, hmul, hdw, Function.update_of_ne], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 6, hr, hr', rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r hr₀ hr₅
  simp [out, mid, Function.update_of_ne hr₀, Function.update_of_ne hr₅]

@[expose] def shiftPotentialAddress (endpointReg : ℕ) : Expr :=
  .bin .add (.reg 20) (.bin .mul
    (.load (.bin .add (.reg 17) (.load (.bin .add (.reg endpointReg) (.reg 18))))) (.reg 3))

/-- Look up the head and tail gradient potentials by named endpoint.
Registers 15 and 16 hold the old graph's tail and head slot bases,
17 its inverse name base, and 20 the potential table base. -/
@[expose] def shiftGradientPotentialArgs : Stmt :=
  .assign 1 (shiftPotentialAddress 16) ;; .assign 2 (shiftPotentialAddress 15)

private theorem shiftPotentialAddress_eval {w edgeBase inverse potential e v limbs r : ℕ}
    {st : State} (hb : st.regs r = edgeBase) (hi : st.regs 17 = inverse)
    (hp : st.regs 20 = potential) (he : st.regs 18 = e) (hl : st.regs 3 = limbs)
    (h₁ : edgeBase + e < 2 ^ w) (h₂ : inverse + st.mem (edgeBase + e) < 2 ^ w)
    (hname : st.mem (inverse + st.mem (edgeBase + e)) = v) (hword : potential + v * limbs < 2 ^ w) :
    (shiftPotentialAddress r).eval w st = some (potential + v * limbs) := by
  have hmul : v * limbs < 2 ^ w := by omega
  simp [shiftPotentialAddress, Expr.eval, BinOp.eval, hb, hi, hp, he, hl, h₁, h₂, hname, hmul, hword]

/-- The endpoint lookups pass the head and tail blocks in the same
order as the core-gradient store, in twenty-five steps. -/
theorem shiftGradientPotentialArgs_runs {w base vc ec e potential limbs : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hG : DynGraphAt st.mem base vc ec G) (he : e ∈ G.E)
    (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hr₁₅ : st.regs 15 = dgETailSlotBase base vc ec)
    (hr₁₆ : st.regs 16 = dgEHeadSlotBase base vc ec)
    (hr₁₇ : st.regs 17 = dgIntToExtBase base vc)
    (hr₁₈ : st.regs 18 = e) (hr₂₀ : st.regs 20 = potential) (hr₃ : st.regs 3 = limbs)
    (hhead : potential + G.head e * limbs < 2 ^ w)
    (htail : potential + G.tail e * limbs < 2 ^ w) :
    ∃ out, Runs w p ω shiftGradientPotentialArgs st .normal out 25 ∧
      out.regs 1 = potential + G.head e * limbs ∧ out.regs 2 = potential + G.tail e * limbs ∧
      (∀ r, r ≠ 1 → r ≠ 2 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨hec, ht, hh, _, _, htn, hhn⟩ := TreeEditEndpointAt.of_graph hG he
  let mid := { st with regs := Function.update st.regs 1 (potential + G.head e * limbs) }
  let out := { mid with regs := Function.update mid.regs 2 (potential + G.tail e * limbs) }
  have hr : Runs w p ω (.assign 1 (shiftPotentialAddress 16)) st .normal mid 12 :=
    runs_assign_iff.mpr ⟨_, shiftPotentialAddress_eval hr₁₆ hr₁₇ hr₂₀ hr₁₈ hr₃
      (by unfold dgEHeadSlotBase dynGraphSize at *; omega)
      (by unfold dgIntToExtBase dynGraphSize at *; omega) hhn hhead, rfl, rfl, rfl⟩
  have hreg (r : ℕ) (hne : r ≠ 1) : mid.regs r = st.regs r := Function.update_of_ne hne _ _
  have hr' : Runs w p ω (.assign 2 (shiftPotentialAddress 15)) mid .normal out 12 :=
    runs_assign_iff.mpr ⟨_, shiftPotentialAddress_eval
      ((hreg 15 (by decide)).trans hr₁₅) ((hreg 17 (by decide)).trans hr₁₇)
      ((hreg 20 (by decide)).trans hr₂₀) ((hreg 18 (by decide)).trans hr₁₈)
      ((hreg 3 (by decide)).trans hr₃)
      (by unfold dgETailSlotBase dynGraphSize at *; omega)
      (by change dgIntToExtBase base vc + st.mem _ < _; unfold dgIntToExtBase dynGraphSize at *; omega)
      htn htail, rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 12, 12, hr, hr', rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl, rfl⟩
  intro r hn₁ hn₂
  simp [out, mid, Function.update_of_ne hn₁, Function.update_of_ne hn₂]

/-- Prepare the fixed-point call arguments from a live edge name. -/
@[expose] def shiftGradientArgs : Stmt :=
  shiftGradientSlotArgs ;; shiftGradientPotentialArgs

/-- All four fixed-point addresses are ready in 39 steps. The argument
limb count, scratch heap, and edge-list cursor are preserved. -/
theorem shiftGradientArgs_runs {w base vc ec e potential limbs src dst : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hG : DynGraphAt st.mem base vc ec G) (he : e ∈ G.E)
    (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hr₁₃ : st.regs 13 = src) (hr₁₄ : st.regs 14 = dst)
    (hr₁₅ : st.regs 15 = dgETailSlotBase base vc ec)
    (hr₁₆ : st.regs 16 = dgEHeadSlotBase base vc ec)
    (hr₁₇ : st.regs 17 = dgIntToExtBase base vc)
    (hr₁₈ : st.regs 18 = e) (hr₂₀ : st.regs 20 = potential) (hr₃ : st.regs 3 = limbs)
    (hsrc : src + e * limbs < 2 ^ w) (hdst : dst + e * limbs < 2 ^ w)
    (hhead : potential + G.head e * limbs < 2 ^ w)
    (htail : potential + G.tail e * limbs < 2 ^ w) :
    ∃ out, Runs w p ω shiftGradientArgs st .normal out 39 ∧
      out.regs 0 = src + e * limbs ∧ out.regs 5 = dst + e * limbs ∧
      out.regs 1 = potential + G.head e * limbs ∧ out.regs 2 = potential + G.tail e * limbs ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  obtain ⟨mid, hr, hs, hd, hregs, hm, hp⟩ :=
    shiftGradientSlotArgs_runs (ω := ω) hr₁₃ hr₁₄ hr₁₈ hr₃ hsrc hdst
  obtain ⟨out, hr', hh, ht, hregs', hm', hp'⟩ :=
    shiftGradientPotentialArgs_runs (ω := ω) (hm.symm ▸ hG) he hroom
      ((hregs 15 (by decide) (by decide)).trans hr₁₅)
      ((hregs 16 (by decide) (by decide)).trans hr₁₆)
      ((hregs 17 (by decide) (by decide)).trans hr₁₇)
      ((hregs 18 (by decide) (by decide)).trans hr₁₈)
      ((hregs 20 (by decide) (by decide)).trans hr₂₀)
      ((hregs 3 (by decide) (by decide)).trans hr₃) hhead htail
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 13, 25, hr, hr', rfl⟩),
    (hregs' 0 (by decide) (by decide)).trans hs, (hregs' 5 (by decide) (by decide)).trans hd,
    hh, ht, fun r h₀ h₁ h₂ h₅ => (hregs' r h₁ h₂).trans (hregs r h₀ h₅),
    hm'.trans hm, hp'.trans hp⟩

/-- Run one linked gradient write from the six prepared arguments.
The returned heap replaces register 4 for the next scanned edge. -/
@[expose] def callShiftGradientCell (entry : ℕ) : Stmt :=
  .call 4 entry [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5]

/-- A linked cell write preserves the other registers and adds seven
steps of call overhead to the verified arithmetic-and-copy bound. -/
theorem callShiftGradientCell_runs {w h entry src headPtr tailPtr limbs heap dst : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} (gradient headPot tailPot : ℤ)
    (himpl : MeetsContract w p entry (writeCoreGradientCellContract w h gradient headPot tailPot))
    (h0 : st.regs 0 = src) (h1 : st.regs 1 = headPtr) (h2 : st.regs 2 = tailPtr)
    (h3 : st.regs 3 = limbs) (h4 : st.regs 4 = heap) (h5 : st.regs 5 = dst)
    (hwords : ∀ a ∈ [src, headPtr, tailPtr, limbs, heap, dst], a < 2 ^ w)
    (hpre : (writeCoreGradientCellContract w h gradient headPot tailPot).pre
      [src, headPtr, tailPtr, limbs, heap, dst] st.mem) :
    ∃ out ret cost, Runs w p ω (callShiftGradientCell entry) st .normal out cost ∧
      out.regs 4 = ret ∧ (∀ r ≠ 4, out.regs r = st.regs r) ∧
      (writeCoreGradientCellContract w h gradient headPot tailPot).post
        [src, headPtr, tailPtr, limbs, heap, dst] st.mem ret out.mem ∧
      cost ≤ 129 * limbs + 117 := by
  obtain ⟨body, hbody, o, after, c, hrun, hpost, hc⟩ :=
    himpl [src, headPtr, tailPtr, limbs, heap, dst] st.mem st.pos ω hwords hpre
  let out := { after with regs := Function.update st.regs 4 o.value }
  have hargs : evalArgs w st [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5] =
      some [src, headPtr, tailPtr, limbs, heap, dst] := by
    simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5]
  refine ⟨out, o.value, 6 + c + 1, runs_call_iff.mpr ⟨_, body, o, after, c, hargs,
    hbody, hrun, rfl, rfl, rfl⟩, by simp [out], ?_, hpost, ?_⟩
  · intro r hr
    exact Function.update_of_ne hr _ _
  · change c ≤ 129 * limbs + 110 at hc
    omega

end MinCostFlow.MinRatio
