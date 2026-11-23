module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.NamedInstance
public import MinCostFlow.MinRatio.InitAssembly
public import MinCostFlow.MinRatio.InitSparsifierConcreteLength
public import MinCostFlow.MinRatio.InitHeader
public import MinCostFlow.LinkCut.PathProg.Account
public import MinCostFlow.DynSpanner.Program.DynGraphInit

/-!
# Packed graph input for min-ratio initialization

The solver supplies a graph header followed by the vertex names and edge
triples. The dynamic graph initializer reads these lists in place.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM IPM.Machine DynSpanner.Program

private theorem initGraphTriplesAt {mem : ℕ → ℕ} {base : ℕ}
    {edges : List (ℕ × ℕ × ℕ)}
    (h : ListAt mem base (edges.flatMap fun t => [t.1, t.2.1, t.2.2])) :
    ∀ i (hi : i < edges.length),
      mem (base + 3 * i) = edges[i].1 ∧
      mem (base + 3 * i + 1) = edges[i].2.1 ∧
      mem (base + 3 * i + 2) = edges[i].2.2 := by
  induction edges generalizing base with
  | nil => simp
  | cons e es ih =>
    intro i hi
    cases i with
    | zero =>
      exact ⟨by simpa using h 0 (by simp),
        by simpa using h 1 (by simp), by simpa using h 2 (by simp)⟩
    | succ i =>
      have ht : ListAt mem (base + 3) (es.flatMap fun t => [t.1, t.2.1, t.2.2]) := by
        rw [List.flatMap_cons, listAt_append] at h
        simpa using h.2
      have he := ih ht i (by simpa using hi)
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

/-- Packing the alpha words and dynamic graph adds a linear number of
cells. Power bounds on the incoming cursor, limb count, and graph sizes
therefore give a power bound on the cursor passed to the depth selector. -/
theorem initPackedGraphCursor_power_bound {B heap limbs n m dh dl dg : ℕ}
    (hB : 2 ≤ B) (hh : heap ≤ B ^ dh) (hl : limbs ≤ B ^ dl)
    (hn : n ≤ B ^ dg) (hm : m ≤ B ^ dg) :
    heap + (limbs + 1) + 6 + dynGraphSize n m ≤ B ^ (max (max dh dl) dg + 5) := by
  let e := max (max dh dl) dg
  have mono {a k : ℕ} (ha : a ≤ B ^ k) (hk : k ≤ e) : a ≤ B ^ e :=
    ha.trans (Nat.pow_le_pow_right (by omega) hk)
  have hh' := mono hh ((le_max_left dh dl).trans (le_max_left (max dh dl) dg))
  have hl' := mono hl ((le_max_right dh dl).trans (le_max_left (max dh dl) dg))
  have hn' := mono hn (le_max_right (max dh dl) dg)
  have hm' := mono hm (le_max_right (max dh dl) dg)
  have he : 1 ≤ B ^ e := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ 32 * B ^ e := by unfold dynGraphSize; omega
    _ = B ^ e * 32 := Nat.mul_comm _ _
    _ ≤ B ^ e * B ^ 5 :=
      Nat.mul_le_mul_left (B ^ e) (show 32 ≤ B ^ 5 from Nat.pow_le_pow_left hB 5)
    _ = _ := (pow_add B e 5).symm

/-- The two lists in the solver's Init input meet the dynamic graph
initializer's list precondition at a fresh heap. -/
theorem initGraphFromSolver_pre {w graph heap vc ec : ℕ} {mem : ℕ → ℕ} {G : MGraph}
    (hg : GraphAt mem graph G) (hv : G.IsValid)
    (hvc : ∀ v ∈ G.V, v < vc) (hec : ∀ e ∈ G.E, e < ec)
    (hbelow : graph + (graphWords G).length ≤ heap)
    (hz : ZeroFrom mem heap) (hword : 16 ≤ 2 ^ w) (hroom : heap + dynGraphSize vc ec < 2 ^ w) :
    let vs := G.V.sort (· ≤ ·)
    let es := (G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e))
    (dgInitFromListsContract w vc ec G vs es).pre
      [heap, vc, ec, G.n, graph + 2, G.m, graph + 2 + G.n] mem := by
  intro vs es
  have hvlen : vs.length = G.n := by simp [vs, MGraph.n]
  have helen : es.length = G.m := by simp [es, MGraph.m]
  have hf : es.flatMap (fun t => [t.1, t.2.1, t.2.2]) =
      (G.E.sort (· ≤ ·)).flatMap (fun e => [e, G.tail e, G.head e]) := by
    simp [es, List.flatMap_map]
  have hlists : ListAt mem (graph + 2) (vs ++ es.flatMap fun t => [t.1, t.2.1, t.2.2]) := by
    change ListAt mem graph ([G.V.card, G.E.card] ++
      (vs ++ (G.E.sort (· ≤ ·)).flatMap fun e => [e, G.tail e, G.head e])) at hg
    rw [← hf, listAt_append] at hg
    exact hg.2
  obtain ⟨hvs, hes⟩ := listAt_append.mp hlists
  rw [hvlen] at hes
  have hlen : (graphWords G).length = 2 + G.n + 3 * G.m := by
    have haux (xs : List ℕ) : (xs.flatMap fun e => [e, G.tail e, G.head e]).length = 3 * xs.length := by
      induction xs with
      | nil => simp
      | cons x xs ih => simp [ih, Nat.mul_succ, Nat.add_comm]; omega
    simp [graphWords, haux, MGraph.m, MGraph.n]; omega
  refine ⟨heap, G.n, graph + 2, G.m, graph + 2 + G.n, rfl, hword, hroom, hz,
    hv, hvc, hec, hvlen, hvs, ?_, ?_, helen, ?_, initGraphTriplesAt hes, ?_, ?_, ?_⟩
  · intro v
    simp [vs]
  · intro i hi
    omega
  · simp [es, List.map_map, Function.comp_def]
  · intro t ht
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
    exact ⟨by simpa using he, rfl, rfl⟩
  · intro e he
    exact ⟨(e, G.tail e, G.head e), List.mem_map.mpr ⟨e, by simpa using he, rfl⟩, rfl⟩
  · intro i hi
    omega

/-- Pack the solver graph into fresh memory for the per-level tools.
The graph pointer is in register 69 and the available heap in register 7. -/
@[expose] def packInitSolverGraph (entry : ℕ) : Stmt :=
  .call 69 entry
    [.reg 7, .reg 93, .reg 94, .load (.reg 69),
      .bin .add (.reg 69) (.const 2),
      .load (.bin .add (.reg 69) (.const 1)),
      .bin .add (.bin .add (.reg 69) (.const 2)) (.load (.reg 69))]

/-- The shared dynamic graph procedure consumes the solver lists
directly and leaves the original input below the allocation. -/
theorem packInitSolverGraph_runs {w entry graph heap vc ec : ℕ}
    {mem : ℕ → ℕ} {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (hmem : st.mem = mem)
    (hbridge : MeetsContract w p entry
      (dgInitFromListsContract w vc ec G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hg : GraphAt mem graph G) (hv : G.IsValid)
    (hp : st.regs 69 = graph) (hh : st.regs 7 = heap)
    (hvreg : st.regs 93 = vc) (hereg : st.regs 94 = ec)
    (hvc : ∀ v ∈ G.V, v < vc) (hec : ∀ e ∈ G.E, e < ec)
    (hbelow : graph + (graphWords G).length ≤ heap)
    (hz : ZeroFrom mem heap) (hw : 16 ≤ 2 ^ w)
    (hroom : heap + dynGraphSize vc ec < 2 ^ w) :
    ∃ out cost, Runs w p ω (packInitSolverGraph entry) st .normal out cost ∧
      out.regs 69 = heap ∧ DynGraphAt out.mem heap vc ec G ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (heap + dynGraphSize vc ec) ∧
      (∀ r ≠ 69, out.regs r = st.regs r) ∧ cost ≤ 130 * G.n + 490 * G.m + 119 := by
  have hn : mem graph = G.n := by
    simpa [graphWords, MGraph.n] using hg 0 (by simp [graphWords])
  have hm : mem (graph + 1) = G.m := by
    simpa [graphWords, MGraph.m] using hg 1 (by simp [graphWords])
  have hl : 2 + G.n ≤ (graphWords G).length := by
    simp [graphWords, MGraph.n]
    omega
  have haddr : graph + 2 + G.n < 2 ^ w := by omega
  have ht : vc + ec < 2 ^ w := by
    have hsize : vc + ec ≤ dynGraphSize vc ec := by unfold dynGraphSize; omega
    omega
  have hnw : G.n < 2 ^ w := by omega
  have hmw : G.m < 2 ^ w := by
    have he : G.E.card ≤ (Finset.range ec).card := Finset.card_le_card fun e he =>
      Finset.mem_range.mpr (hec e he)
    rw [Finset.card_range] at he
    change G.E.card < 2 ^ w
    omega
  let argv := [heap, vc, ec, G.n, graph + 2, G.m, graph + 2 + G.n]
  have ha : evalArgs w st
      [.reg 7, .reg 93, .reg 94, .load (.reg 69), .bin .add (.reg 69) (.const 2),
        .load (.bin .add (.reg 69) (.const 1)),
        .bin .add (.bin .add (.reg 69) (.const 2)) (.load (.reg 69))] = some argv := by
    simp [evalArgs, Expr.eval, BinOp.eval, argv, hmem, hn, hm, hp, hh, hvreg, hereg, haddr,
      show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
      show graph + 1 < 2 ^ w by omega, show graph + 2 < 2 ^ w by omega]
  have hwords : ∀ v ∈ argv, v < 2 ^ w := by
    intro v hv'
    simp [argv] at hv'
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hpre := initGraphFromSolver_pre hg hv hvc hec hbelow hz hw hroom
  obtain ⟨out, cost, ret, hr, hpost, hreg, hk, hc⟩ :=
    runs_call_of_meetsContract (r := 69) hbridge ha hwords (hmem.symm ▸ hpre) ω
  obtain ⟨base, nv, vp, ne, ep, heq, hval, hdg, hframe, hz'⟩ := hpost
  have hb : base = heap := by simpa [argv] using (List.cons.inj heq).1.symm
  rw [hb] at hval hdg hframe hz'
  simp [argsSize, Expr.size, dgInitFromListsContract, argv] at hc
  exact ⟨out, cost, hr, hreg.trans hval, hdg, fun a ha' => (hframe a (Or.inl ha')).trans (congrFun hmem a),
    hz', hk, by omega⟩

/-- Advance the Init heap past the packed dynamic graph. -/
@[expose] def advanceInitSolverGraphHeap : Stmt :=
  .assign 7 (.bin .add (.reg 7)
    (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 93)))
      (.bin .mul (.const 9) (.reg 94))))

/-- The new cursor is the end of the graph allocation. -/
theorem advanceInitSolverGraphHeap_runs {w heap vc ec : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 7 = heap) (hv : st.regs 93 = vc) (he : st.regs 94 = ec)
    (hw : 16 ≤ 2 ^ w) (hroom : heap + dynGraphSize vc ec < 2 ^ w) :
    ∃ out, Runs w p ω advanceInitSolverGraphHeap st .normal out 12 ∧
      out.regs 7 = heap + dynGraphSize vc ec ∧ out.mem = st.mem ∧
      (∀ r ≠ 7, out.regs r = st.regs r) := by
  let out := {st with regs := Function.update st.regs 7 (heap + dynGraphSize vc ec)}
  have hsize : 4 + 7 * vc + 9 * ec < 2 ^ w := by
    unfold dynGraphSize at hroom
    omega
  have hr : Runs w p ω advanceInitSolverGraphHeap st .normal out 12 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hh, hv, he, dynGraphSize, hsize,
        show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show 9 < 2 ^ w by omega,
        show 7 * vc < 2 ^ w by omega, show 9 * ec < 2 ^ w by omega,
        show 4 + 7 * vc < 2 ^ w by omega,
        show heap + (4 + 7 * vc + 9 * ec) < 2 ^ w from hroom],
      rfl, rfl, rfl⟩
  exact ⟨out, hr, by simp [out], rfl, fun r h => by simp [out, h]⟩

/-- Read the dense solver graph's vertex and edge capacities from its header. -/
@[expose] def stageInitSolverGraphSizes : Stmt :=
  .assign 92 (.load (.reg 69)) ;;
  .assign 93 (.reg 92) ;;
  .assign 94 (.load (.bin .add (.reg 69) (.const 1)))

/-- Staging the capacities preserves the numeric parameters and the solver input. -/
theorem stageInitSolverGraphSizes_runs {w graph : ℕ} {G : MGraph}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hg : st.regs 69 = graph) (hat : GraphAt st.mem graph G)
    (hroom : graph + 1 < 2 ^ w) :
    ∃ out, Runs w p ω stageInitSolverGraphSizes st .normal out 12 ∧
      out.regs 92 = G.n ∧ out.regs 93 = G.n ∧ out.regs 94 = G.m ∧
      (∀ r, r ≠ 92 → r ≠ 93 → r ≠ 94 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let s1 := { st with regs := Function.update st.regs 92 G.n }
  let s2 := { s1 with regs := Function.update s1.regs 93 G.n }
  let out := { s2 with regs := Function.update s2.regs 94 G.m }
  have hn : st.mem graph = G.n := by
    simpa [graphWords, MGraph.n] using hat 0 (by simp [graphWords])
  have hm : st.mem (graph + 1) = G.m := by
    simpa [graphWords, MGraph.m] using hat 1 (by simp [graphWords])
  have hr1 : Runs w p ω (.assign 92 (.load (.reg 69))) st .normal s1 3 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hg, hn], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 93 (.reg 92)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 94 (.load (.bin .add (.reg 69) (.const 1)))) s2 .normal out 5 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s2, s1, hg, hm, hroom, show 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 3, 8, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 5, hr2, hr3, rfl⟩), rfl⟩),
    by simp [out, s2, s1], by simp [out, s2], by simp [out],
    fun r h92 h93 h94 => by simp [out, s2, s1, Function.update_of_ne, h92, h93, h94], rfl, rfl⟩

/-- Pack the solver graph and advance the heap for subsequent Init
allocations. -/
@[expose] def prepareInitSolverGraph (entry : ℕ) : Stmt :=
  packInitSolverGraph entry ;; advanceInitSolverGraphHeap

/-- The packed graph and the new heap cursor are both ready for the
per-level tool calls. -/
theorem prepareInitSolverGraph_runs {w entry graph heap vc ec : ℕ}
    {mem : ℕ → ℕ} {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (hmem : st.mem = mem)
    (hbridge : MeetsContract w p entry
      (dgInitFromListsContract w vc ec G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hg : GraphAt mem graph G) (hv : G.IsValid)
    (hp : st.regs 69 = graph) (hh : st.regs 7 = heap)
    (hvreg : st.regs 93 = vc) (hereg : st.regs 94 = ec)
    (hvc : ∀ v ∈ G.V, v < vc) (hec : ∀ e ∈ G.E, e < ec)
    (hbelow : graph + (graphWords G).length ≤ heap)
    (hz : ZeroFrom mem heap) (hw : 16 ≤ 2 ^ w)
    (hroom : heap + dynGraphSize vc ec < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareInitSolverGraph entry) st .normal out cost ∧
      out.regs 69 = heap ∧ out.regs 7 = heap + dynGraphSize vc ec ∧ DynGraphAt out.mem heap vc ec G ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (heap + dynGraphSize vc ec) ∧
      (∀ r, r ≠ 69 → r ≠ 7 → out.regs r = st.regs r) ∧ cost ≤ 130 * G.n + 490 * G.m + 132 := by
  obtain ⟨mid, cost, hr₁, hg', hdg, hf, hz', hk₁, hc⟩ :=
    packInitSolverGraph_runs (ω := ω) hmem hbridge hg hv hp hh hvreg hereg hvc hec hbelow hz hw hroom
  obtain ⟨out, hr₂, hh', hm, hk₂⟩ :=
    advanceInitSolverGraphHeap_runs (p := p) (ω := ω)
      ((hk₁ 7 (by decide)).trans hh) ((hk₁ 93 (by decide)).trans hvreg)
      ((hk₁ 94 (by decide)).trans hereg) hw hroom
  exact ⟨out, cost + 13, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 12, hr₁, hr₂, rfl⟩),
    (hk₂ 69 (by decide)).trans hg', hh', hm.symm ▸ hdg,
    fun a ha => (congrFun hm a).trans (hf a ha), hm.symm ▸ hz',
    fun r h69 h7 => (hk₂ r h7).trans (hk₁ r h69), by omega⟩

/-- The solver's original indices fit in the initial dynamic graph's
capacities, which are the vertex and edge counts read from the header. -/
theorem namedInstance_initGraphBounds (I : Instance) (hI : I.IsValid) :
    (IPM.namedInstance I).IsValid ∧
      (∀ v ∈ (IPM.namedInstance I).V, v < (IPM.namedInstance I).n) ∧
      (∀ e ∈ (IPM.namedInstance I).E, e < (IPM.namedInstance I).m) := by
  refine ⟨IPM.namedInstance_valid I hI, ?_, ?_⟩
  · intro v hv
    simpa [MGraph.n, IPM.namedInstance] using (Finset.mem_range.mp hv)
  · intro e he
    rw [IPM.namedInstance_m]
    exact Finset.mem_range.mp he

/-- The solver names every edge of the augmented instance by its
index. The padded bound decoded from that graph uses the instance's
edge count, including all augmentation edges. -/
theorem namedInstance_initBaseEdgeBound (I : Instance) (threshold : ℕ) :
    max (IPM.namedInstance I).m threshold = max I.m threshold := by
  rw [IPM.namedInstance_m]

/-- Stage capacities and pack the dense solver graph in fresh memory. -/
@[expose] def prepareDenseInitSolverGraph (entry : ℕ) : Stmt :=
  stageInitSolverGraphSizes ;; prepareInitSolverGraph entry

/-- The dense graph fits in its staged capacities and leaves the earlier
Init parameters and memory live. -/
theorem prepareDenseInitSolverGraph_runs {w entry graph heap : ℕ}
    {G : MGraph} {p : Program} {ω : ℕ → Bool} {st : State}
    (hbridge : MeetsContract w p entry
      (dgInitFromListsContract w G.n G.m G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hg : GraphAt st.mem graph G) (hv : G.IsValid)
    (hp : st.regs 69 = graph) (hh : st.regs 7 = heap)
    (hvc : ∀ v ∈ G.V, v < G.n) (hec : ∀ e ∈ G.E, e < G.m)
    (hbelow : graph + (graphWords G).length ≤ heap)
    (hz : ZeroFrom st.mem heap) (hw : 16 ≤ 2 ^ w)
    (hroom : heap + dynGraphSize G.n G.m < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareDenseInitSolverGraph entry) st .normal out cost ∧
      out.regs 69 = heap ∧ out.regs 7 = heap + dynGraphSize G.n G.m ∧
      out.regs 92 = G.n ∧ out.regs 93 = G.n ∧ out.regs 94 = G.m ∧
      DynGraphAt out.mem heap G.n G.m G ∧
      (∀ a < heap, out.mem a = st.mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      (∀ r, r ≠ 69 → r ≠ 7 → r ≠ 92 → r ≠ 93 → r ≠ 94 → out.regs r = st.regs r) ∧
      cost ≤ 130 * G.n + 490 * G.m + 145 := by
  have hgraph : graph + 1 < 2 ^ w := by
    have hlen : 2 ≤ (graphWords G).length := by simp [graphWords]
    omega
  obtain ⟨mid, hr₁, hn, hvcReg, hecReg, hk₁, hm, _⟩ :=
    stageInitSolverGraphSizes_runs (p := p) (ω := ω) hp hg hgraph
  obtain ⟨out, cost, hr₂, hp', hh', hdg, hf, hz', hk₂, hc⟩ :=
    prepareInitSolverGraph_runs (ω := ω) hm hbridge hg hv
      ((hk₁ 69 (by decide) (by decide) (by decide)).trans hp)
      ((hk₁ 7 (by decide) (by decide) (by decide)).trans hh)
      hvcReg hecReg hvc hec hbelow hz hw hroom
  refine ⟨out, 12 + cost + 1, runs_seq_iff.mpr (Or.inr ⟨mid, 12, cost, hr₁, hr₂, by omega⟩),
    hp', hh', (hk₂ 92 (by decide) (by decide)).trans hn,
    (hk₂ 93 (by decide) (by decide)).trans hvcReg,
    (hk₂ 94 (by decide) (by decide)).trans hecReg, hdg, hf, hh'.symm ▸ hz', ?_, by omega⟩
  intro r h69 h7 h92 h93 h94
  exact (hk₂ r h69 h7).trans (hk₁ r h92 h93 h94)

/-- Prepare the barrier, stability parameters and quality for the
solver's seven-word graph-list Init interface. -/
@[expose] def prepareMinRatioSolverNumericParameters (alpha select quality : ℕ) : Stmt :=
  prepareMinRatioNumericParametersAt alpha select quality 1

/-- The solver graph's edge count supplies the numeric prefix with
the same size used by the dyadic model. -/
theorem prepareMinRatioSolverNumericParameters_runs
    {w h alpha select quality graph gradient lengths limbs precision V heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    {qualityExponent qualityCharge : ℕ → ℕ}
    (hquality : MeetsContract w p quality
      (IPM.Machine.solverQualityContract w qualityExponent qualityCharge))
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hG : GraphAt mem graph G)
    (hgraph : graph + 1 < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w)
    (hepsRoom : Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioSolverNumericParameters alpha select quality)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      out.regs 6 = IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 ∧
      out.regs 7 = heap + (limbs + 1) + 6 ∧
      out.regs 69 = graph ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.regs 72 = qualityExponent G.m ∧
      out.regs 73 = Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 =
        (1 / (2 : ℝ) ^ qualityExponent G.m) * Num.IPM.alphaPrime G.m V / 1024 ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + qualityCharge G.m + 20672 := by
  have hEdge : mem (graph + 1) = G.m := by
    simpa [graphWords, MGraph.m] using hG 1 (by simp [graphWords])
  exact prepareMinRatioNumericParametersAt_runs hquality halpha hselect hEdge hgraph
    hmw hVw hLw hPw hsize hcover hwidth hscale hw hpsi hz hroom hepsRoom

/-- Prepare the chain parameters and pack the incoming solver graph. -/
@[expose] def prepareMinRatioSolverGraph (alpha select quality pack : ℕ) : Stmt :=
  prepareMinRatioSolverNumericParameters alpha select quality ;; prepareDenseInitSolverGraph pack

/-- The Init prefix preserves the input and leaves the graph, barrier block
and fresh heap ready for per-level initialization. -/
theorem prepareMinRatioSolverGraph_runs
    {w h alpha select quality pack graph gradient lengths limbs precision V heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    {qualityExponent qualityCharge : ℕ → ℕ}
    (hquality : MeetsContract w p quality
      (IPM.Machine.solverQualityContract w qualityExponent qualityCharge))
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hG : GraphAt mem graph G)
    (hgraph : graph + 1 < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w)
    (hepsRoom : Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 < 2 ^ w)
    (hbridge : MeetsContract w p pack
      (dgInitFromListsContract w G.n G.m G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hvalid : G.IsValid) (hvc : ∀ v ∈ G.V, v < G.n) (hec : ∀ e ∈ G.E, e < G.m)
    (hbelow : graph + (graphWords G).length ≤ heap) (hw16 : 16 ≤ 2 ^ w)
    (hpack : heap + (limbs + 1) + 6 + dynGraphSize G.n G.m < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioSolverGraph alpha select quality pack)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      out.regs 6 = IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 ∧
      out.regs 7 = heap + (limbs + 1) + 6 + dynGraphSize G.n G.m ∧
      out.regs 69 = heap + (limbs + 1) + 6 ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.regs 72 = qualityExponent G.m ∧
      out.regs 73 = Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 =
        (1 / (2 : ℝ) ^ qualityExponent G.m) * Num.IPM.alphaPrime G.m V / 1024 ∧
      out.regs 92 = G.n ∧ out.regs 93 = G.n ∧ out.regs 94 = G.m ∧
      DynGraphAt out.mem (heap + (limbs + 1) + 6) G.n G.m G ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + qualityCharge G.m + 130 * G.n + 490 * G.m + 20818 := by
  obtain ⟨mid, c, hr, hm, hV, hL, hP, hh, hΨ, hret, hg, hgrad, hlen, hq, he,
    heps, hframe, hfree, ha, hv, hval, hc⟩ :=
    prepareMinRatioSolverNumericParameters_runs (ω := ω) (gradient := gradient)
      (lengths := lengths) (pos := pos) hquality halpha hselect hG hgraph
      hmw hVw hLw hPw hsize hcover hwidth hscale hw hpsi hz hroom hepsRoom
  have hG' : GraphAt mid.mem graph G := by
    intro i hi
    exact (hframe _ (by omega)).trans (hG i hi)
  obtain ⟨out, c', hr', hp', hh', hn, hvc', hec', hdg, hf, hz', hkeep, hc'⟩ :=
    prepareDenseInitSolverGraph_runs (ω := ω) hbridge hG' hvalid hg hret hvc hec
      (by omega) (hret ▸ hfree) hw16 hpack
  have keep (r : ℕ) (h69 : r ≠ 69) (h7 : r ≠ 7) (h92 : r ≠ 92)
      (h93 : r ≠ 93) (h94 : r ≠ 94) := hkeep r h69 h7 h92 h93 h94
  refine ⟨out, c + c' + 1, runs_seq_iff.mpr (Or.inr ⟨mid, c, c', hr, hr', rfl⟩),
    (keep 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm,
    (keep 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hV,
    (keep 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL,
    (keep 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hP,
    (keep 4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh,
    ?_, hh', hp', ?_, ?_, ?_, ?_, ?_, hn, hvc', hec', hdg, ?_, hz', ?_, ?_, ?_, by omega⟩
  · rwa [keep 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rwa [keep 70 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rwa [keep 71 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rwa [keep 72 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rwa [keep 73 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · rwa [keep 73 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact fun a ha' => (hf a (by omega)).trans (hframe a ha')
  · exact (hf heap (by omega)).trans ha
  · intro i hi
    rw [hf _ (by omega)]
    exact hv i hi
  · have hagree : ∀ i < limbs, out.mem (heap + 1 + i) = mid.mem (heap + 1 + i) :=
      fun i hi => hf _ (by omega)
    rw [Num.fixVal, Num.intVal_congr hagree]
    exact hval

/-- Pass the allocated heap cursor and fixed-point format to the
bucket and threshold calculations. -/
@[expose] def stageInitThresholdWorkspace : Stmt :=
  .assign 67 (.reg 2) ;;
  .assign 68 (.reg 3) ;;
  .assign 98 (.reg 7)

/-- The threshold calculations start at the end of the packed graph
with the format read from the solver's Init arguments. -/
theorem stageInitThresholdWorkspace_runs {w limbs precision heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hL : st.regs 2 = limbs) (hP : st.regs 3 = precision) (hh : st.regs 7 = heap) :
    ∃ out, Runs w p ω stageInitThresholdWorkspace st .normal out 8 ∧
      out.regs 67 = limbs ∧ out.regs 68 = precision ∧ out.regs 98 = heap ∧
      (∀ r, r ≠ 67 → r ≠ 68 → r ≠ 98 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let s1 := {st with regs := Function.update st.regs 67 limbs}
  let s2 := {s1 with regs := Function.update s1.regs 68 precision}
  let out := {s2 with regs := Function.update s2.regs 98 heap}
  have hr1 : Runs w p ω (.assign 67 (.reg 2)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hL], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 68 (.reg 3)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, hP], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 98 (.reg 7)) s2 .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1, hh], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 5, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 2, hr2, hr3, rfl⟩), rfl⟩),
    by simp [out, s2, s1], by simp [out, s2], by simp [out],
    fun r h67 h68 h98 => by simp [out, s2, s1, Function.update_of_ne, h67, h68, h98], rfl, rfl⟩

/-- Prepare the solver graph and stage the workspace for the threshold calculation. -/
@[expose] def prepareMinRatioSolverThresholdInputs (alpha select quality pack : ℕ) : Stmt :=
  prepareMinRatioSolverGraph alpha select quality pack ;; stageInitThresholdWorkspace

/-- The threshold prefix starts with the packed graph, numeric parameters
and an empty workspace after the graph. -/
theorem prepareMinRatioSolverThresholdInputs_runs
    {w h alpha select quality pack graph gradient lengths limbs precision V heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ} {G : MGraph}
    {qualityExponent qualityCharge : ℕ → ℕ}
    (hquality : MeetsContract w p quality
      (IPM.Machine.solverQualityContract w qualityExponent qualityCharge))
    (halpha : MeetsContract w p alpha (Num.IPM.alphaContract w h))
    (hselect : MeetsContract w p select (IPM.Machine.precisionSelectionContract w))
    (hG : GraphAt mem graph G)
    (hgraph : graph + 1 < 2 ^ w)
    (hmw : G.m < 2 ^ w) (hVw : V < 2 ^ w) (hLw : limbs < 2 ^ w) (hPw : precision < 2 ^ w)
    (hsize : 2 ≤ G.m * V) (hcover : Num.IPM.alphaExponent G.m V + 3 ≤ precision)
    (hwidth : precision + 2 ≤ h * limbs) (hscale : Num.IPM.alphaScale G.m V + 1 < 2 ^ w)
    (hw : IPM.Machine.ipmParameterWordBits G.m V ≤ w)
    (hpsi : IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) + IPM.Machine.slackRangeExponent G.m V + 6 < 2 ^ w)
    (hz : ZeroFrom mem heap) (hroom : heap + (limbs + 1) + 6 < 2 ^ w)
    (hepsRoom : Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 < 2 ^ w)
    (hbridge : MeetsContract w p pack
      (dgInitFromListsContract w G.n G.m G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hvalid : G.IsValid) (hvc : ∀ v ∈ G.V, v < G.n) (hec : ∀ e ∈ G.E, e < G.m)
    (hbelow : graph + (graphWords G).length ≤ heap) (hw16 : 16 ≤ 2 ^ w)
    (hpack : heap + (limbs + 1) + 6 + dynGraphSize G.n G.m < 2 ^ w) :
    ∃ out cost, Runs w p ω (prepareMinRatioSolverThresholdInputs alpha select quality pack)
        (startState [graph, gradient, lengths, limbs, precision, V, heap] mem pos) .normal out cost ∧
      out.regs 0 = G.m ∧ out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      out.regs 4 = heap ∧
      out.regs 6 = IPM.Machine.ipmQualityRangeExponent G.m V (qualityExponent G.m) +
        IPM.Machine.slackRangeExponent G.m V + 6 ∧
      out.regs 7 = heap + (limbs + 1) + 6 + dynGraphSize G.n G.m ∧
      out.regs 69 = heap + (limbs + 1) + 6 ∧ out.regs 70 = gradient ∧ out.regs 71 = lengths ∧
      out.regs 72 = qualityExponent G.m ∧
      out.regs 73 = Num.IPM.alphaExponent G.m V + qualityExponent G.m + 10 ∧
      1 / (2 : ℝ) ^ out.regs 73 =
        (1 / (2 : ℝ) ^ qualityExponent G.m) * Num.IPM.alphaPrime G.m V / 1024 ∧
      out.regs 67 = limbs ∧ out.regs 68 = precision ∧ out.regs 98 = out.regs 7 ∧
      out.regs 92 = G.n ∧ out.regs 93 = G.n ∧ out.regs 94 = G.m ∧
      DynGraphAt out.mem (heap + (limbs + 1) + 6) G.n G.m G ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (out.regs 7) ∧
      out.mem heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid out.mem (heap + 1) h limbs ∧
      Num.fixVal out.mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 ∧
      cost ≤ 20028 * (G.m.size + V.size) + qualityCharge G.m + 130 * G.n + 490 * G.m + 20827 := by
  obtain ⟨mid, c, hr, hm, hV, hL, hP, hh, hΨ, hret, hg, hgrad, hlen, hq, he,
    heps, hn, hv, hE, hdg, hf, hz', ha, hav, hval, hc⟩ :=
    prepareMinRatioSolverGraph_runs (ω := ω) (gradient := gradient)
      (lengths := lengths) (pos := pos) hquality halpha hselect hG hgraph
      hmw hVw hLw hPw hsize hcover hwidth hscale hw hpsi hz hroom hepsRoom
      hbridge hvalid hvc hec hbelow hw16 hpack
  obtain ⟨out, hr', h67, h68, h98, hkeep, hmem, _⟩ :=
    stageInitThresholdWorkspace_runs (w := w) (p := p) (ω := ω) hL hP hret
  refine ⟨out, c + 9, runs_seq_iff.mpr (Or.inr ⟨mid, c, 8, hr, hr', by omega⟩), ?_⟩
  have keep (r : ℕ) (h67 : r ≠ 67 := by decide) (h68 : r ≠ 68 := by decide)
      (h98 : r ≠ 98 := by decide) := hkeep r h67 h68 h98
  simp only [keep 0, keep 1, keep 2, keep 3, keep 4, keep 6, keep 7, keep 69,
    keep 70, keep 71, keep 72, keep 73, keep 92, keep 93, keep 94, hmem]
  exact ⟨hm, hV, hL, hP, hh, hΨ, hret, hg, hgrad, hlen, hq, he, heps,
    h67, h68, h98.trans hret.symm, hn, hv, hE, hdg, hf, hz', ha, hav, hval, by omega⟩

/-- The integer bucket and the integral path factors use unit scale.
Save the barrier pointer without constructing the solver's multiword scale. -/
@[expose] def stageCertifiedInitUnitScale : Stmt :=
  .assign 101 (.reg 4) ;; .assign 4 (.const 1)

/-- Staging the unit scale preserves the barrier pointer and solver format. -/
theorem stageCertifiedInitUnitScale_runs {w alphaPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 4 = alphaPtr) (hw : 1 < 2 ^ w) :
    ∃ out, Runs w p ω stageCertifiedInitUnitScale st .normal out 5 ∧
      out.regs 4 = 1 ∧ out.regs 101 = alphaPtr ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 4 → r ≠ 101 → out.regs r = st.regs r) := by
  let mid := {st with regs := Function.update st.regs 101 alphaPtr}
  let out := {mid with regs := Function.update mid.regs 4 1}
  have hsave : Runs w p ω (.assign 101 (.reg 4)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, ha], rfl, rfl, rfl⟩
  have hscale : Runs w p ω (.assign 4 (.const 1)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hw], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hsave, hscale, rfl⟩),
    by simp [out], by simp [out, mid], rfl,
    fun r h4 h101 => by simp [out, mid, h4, h101]⟩

/-- Save the barrier pointer before using register 4 for the scale of
the bucket calculation. -/
@[expose] def stageInitBucketScale : Stmt :=
  .assign 101 (.reg 4) ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 68))

/-- A precision that fits the word scale gives the bucket calculator
its exact scale and preserves the barrier pointer in register 101. -/
theorem stageInitBucketScale_runs {w precision alphaPtr : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 4 = alphaPtr) (hP : st.regs 68 = precision) (hwidth : precision < w) :
    ∃ out, Runs w p ω stageInitBucketScale st .normal out 7 ∧
      out.regs 4 = 2 ^ precision ∧ out.regs 101 = alphaPtr ∧
      (∀ r, r ≠ 4 → r ≠ 101 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := {st with regs := Function.update st.regs 101 alphaPtr}
  let out := {mid with regs := Function.update mid.regs 4 (2 ^ precision)}
  have hpow : 2 ^ precision < 2 ^ w := Nat.pow_lt_pow_right (by decide) hwidth
  have hone : 1 < 2 ^ w := Nat.one_le_two_pow.trans_lt hpow
  have hr₁ : Runs w p ω (.assign 101 (.reg 4)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, ha], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 4 (.bin .shiftLeft (.const 1) (.reg 68))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, mid, hP, hone, hpow, Nat.shiftLeft_eq], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 4, hr₁, hr₂, rfl⟩),
    by simp [out], by simp [out, mid],
    fun r h4 h101 => by simp [out, mid, Function.update_of_ne, h4, h101], rfl, rfl⟩

/-- Save the solver penalty and numeric format before evaluating the bucket. -/
@[expose] def saveSolverInitArguments : Stmt :=
  .assign 102 (.reg 1) ;;
  .assign 103 (.reg 2) ;;
  .assign 104 (.reg 3)

/-- Saving the arguments leaves the threshold table and cursor intact. -/
theorem saveSolverInitArguments_runs {w V limbs precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hV : st.regs 1 = V) (hL : st.regs 2 = limbs) (hP : st.regs 3 = precision) :
    ∃ out, Runs w p ω saveSolverInitArguments st .normal out 8 ∧
      out.regs 102 = V ∧ out.regs 103 = limbs ∧ out.regs 104 = precision ∧
      (∀ r, r ≠ 102 → r ≠ 103 → r ≠ 104 → out.regs r = st.regs r) ∧ out.mem = st.mem := by
  let s1 := {st with regs := Function.update st.regs 102 V}
  let s2 := {s1 with regs := Function.update s1.regs 103 limbs}
  let out := {s2 with regs := Function.update s2.regs 104 precision}
  have hr1 : Runs w p ω (.assign 102 (.reg 1)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hV], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 103 (.reg 2)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, hL], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 104 (.reg 3)) s2 .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1, hP], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 5, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 2, hr2, hr3, rfl⟩), rfl⟩),
    by simp [out, s2, s1], by simp [out, s2], by simp [out],
    fun r h1 h2 h3 => by simp [out, s2, s1, Function.update_of_ne, h1, h2, h3], rfl⟩

/-- Restore the barrier pointer and adopt the threshold phase's heap
cursor before allocating the handle and building the levels. -/
@[expose] def finishInitThresholdWorkspace : Stmt :=
  .assign 4 (.reg 101) ;;
  .assign 7 (.reg 99)

/-- Releasing the threshold workspace registers leaves the allocated
table and its free-memory boundary intact. -/
theorem finishInitThresholdWorkspace_runs {w alphaPtr heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (ha : st.regs 101 = alphaPtr) (hh : st.regs 99 = heap) (hz : ZeroFrom st.mem heap) :
    ∃ out, Runs w p ω finishInitThresholdWorkspace st .normal out 5 ∧
      out.regs 4 = alphaPtr ∧ out.regs 7 = heap ∧ ZeroFrom out.mem heap ∧
      (∀ r, r ≠ 4 → r ≠ 7 → out.regs r = st.regs r) ∧
      out.mem = st.mem ∧ out.pos = st.pos := by
  let mid := {st with regs := Function.update st.regs 4 alphaPtr}
  let out := {mid with regs := Function.update mid.regs 7 heap}
  have hr₁ : Runs w p ω (.assign 4 (.reg 101)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, ha], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 7 (.reg 99)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, hh], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 2, 2, hr₁, hr₂, rfl⟩),
    by simp [out, mid], by simp [out], hz,
    fun r h4 h7 => by simp [out, mid, Function.update_of_ne, h4, h7], rfl, rfl⟩

/-- Restore the input penalty and numeric format from the saved Init
registers after the numerical routines use registers 1 through 3. -/
@[expose] def restoreSolverInitArguments : Stmt :=
  .assign 1 (.reg 102) ;;
  .assign 2 (.reg 103) ;;
  .assign 3 (.reg 104)

/-- Restoring the arguments leaves the threshold table and cursor intact. -/
theorem restoreSolverInitArguments_runs {w V limbs precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hV : st.regs 102 = V) (hL : st.regs 103 = limbs) (hP : st.regs 104 = precision) :
    ∃ out, Runs w p ω restoreSolverInitArguments st .normal out 8 ∧
      out.regs 1 = V ∧ out.regs 2 = limbs ∧ out.regs 3 = precision ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → out.regs r = st.regs r) ∧ out.mem = st.mem ∧ out.pos = st.pos := by
  let s1 := {st with regs := Function.update st.regs 1 V}
  let s2 := {s1 with regs := Function.update s1.regs 2 limbs}
  let out := {s2 with regs := Function.update s2.regs 3 precision}
  have hr1 : Runs w p ω (.assign 1 (.reg 102)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hV], rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 2 (.reg 103)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s1, hL], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 3 (.reg 104)) s2 .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, s2, s1, hP], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨s1, 2, 5, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, 2, hr2, hr3, rfl⟩), rfl⟩),
    by simp [out, s2, s1], by simp [out, s2], by simp [out],
    fun r h1 h2 h3 => by simp [out, s2, s1, Function.update_of_ne, h1, h2, h3], rfl, rfl⟩

/-- Compute Detect's find and expose scratch reservations from the
runtime limb count. Both operations use the path-tree scratch arena. -/
@[expose] def stageSolverDetectSpace : Stmt :=
  .assign 78 (.bin .add (.bin .mul (.const 80) (.reg 103)) (.const 260)) ;;
  .assign 79 (.reg 78)

/-- The reservations use the saved numeric format and leave the
threshold table and the heap cursor intact. -/
theorem stageSolverDetectSpace_runs {w limbs : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hL : st.regs 103 = limbs) (hroom : 80 * limbs + 260 < 2 ^ w) :
    ∃ out, Runs w p ω stageSolverDetectSpace st .normal out 9 ∧
      out.regs 78 = 20 * (4 * limbs + 8) + 100 ∧ out.regs 79 = out.regs 78 ∧
      (∀ r, r ≠ 78 → r ≠ 79 → out.regs r = st.regs r) ∧ out.mem = st.mem := by
  let mid := {st with regs := Function.update st.regs 78 (80 * limbs + 260)}
  let out := {mid with regs := Function.update mid.regs 79 (80 * limbs + 260)}
  have hr₁ : Runs w p ω
      (.assign 78 (.bin .add (.bin .mul (.const 80) (.reg 103)) (.const 260))) st .normal mid 6 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, hL, hroom, show 80 < 2 ^ w by omega,
        show 260 < 2 ^ w by omega, show 80 * limbs < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω (.assign 79 (.reg 78)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid], rfl, rfl, rfl⟩
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 6, 2, hr₁, hr₂, rfl⟩),
    by simp [out, mid]; omega, by simp [out, mid],
    fun r h78 h79 => by simp [out, mid, Function.update_of_ne, h78, h79], rfl⟩

/-- The Init reservations cover the path-tree find and expose
allocations and the full expose output record. -/
theorem solverDetectSpace_bounds (limbs n : ℕ) (findArgs exposeArgs : List ℕ) :
    let space := 20 * (4 * limbs + 8) + 100
    LinkCut.PathProg.pathAlloc limbs 6 n findArgs ≤ space ∧
      LinkCut.PathProg.pathAlloc limbs 4 n exposeArgs ≤ space ∧ 2 + 4 * limbs ≤ space := by
  simp [LinkCut.PathProg.pathAlloc, LinkCut.PathProg.treeLimbs]
  omega

/-- After threshold computation, allocate the shared Init handle from
the advanced heap and store the restored barrier pointer. -/
@[expose] def allocateSolverInitHeader : Stmt :=
  stageSolverDetectSpace ;;
  (restoreSolverInitArguments ;; (finishInitThresholdWorkspace ;; allocateMinRatioInitHeader))

/-- The solver header starts beyond the threshold workspace, preserves
the allocated table and records the chain and fixed-point parameters. -/
theorem allocateSolverInitHeader_runs
    {w heap m V depth branch psi alphaPtr quality epsilon limbs precision : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hh : st.regs 99 = heap) (ha : st.regs 101 = alphaPtr)
    (hm : st.regs 0 = m) (hV : st.regs 102 = V) (hd : st.regs 75 = depth)
    (hb : st.regs 76 = branch) (hpsi : st.regs 6 = psi)
    (hq : st.regs 72 = quality) (he : st.regs 73 = epsilon)
    (hL : st.regs 103 = limbs) (hP : st.regs 104 = precision)
    (hspace : 80 * limbs + 260 < 2 ^ w)
    (hz : ZeroFrom st.mem heap) (hroom : heap + 17 < 2 ^ w) :
    let space := 20 * (4 * limbs + 8) + 100
    ∃ out, Runs w p ω allocateSolverInitHeader st .normal out 104 ∧
      out.regs 74 = heap ∧ out.regs 77 = heap + 17 ∧
      ChainInitParametersAt out.mem heap m V depth branch psi alphaPtr quality epsilon ∧
      MinRatioNumericHeaderAt out.mem heap limbs precision space space ∧
      (∀ a < heap + 5, out.mem a = st.mem a) ∧ ZeroFrom out.mem (heap + 17) ∧
      (∀ r, r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 7 → r ≠ 74 → r ≠ 77 → r ≠ 78 → r ≠ 79 → out.regs r = st.regs r) ∧
      (∀ j, st.regs 83 + j < heap →
        out.mem (out.regs 83 + j) = st.mem (st.regs 83 + j)) := by
  dsimp only
  obtain ⟨staged, hrSpace, h78, h79, hstage, hstageMem⟩ :=
    stageSolverDetectSpace_runs (w := w) (p := p) (ω := ω) hL hspace
  have stagedKeep (r : ℕ) (h78 : r ≠ 78 := by decide) (h79 : r ≠ 79 := by decide) :=
    hstage r h78 h79
  obtain ⟨restored, hr₀, hV', hL', hP', hrestore, hm₀, hpos₀⟩ :=
    restoreSolverInitArguments_runs (w := w) (p := p) (ω := ω) ((stagedKeep 102).trans hV) ((stagedKeep 103).trans hL) ((stagedKeep 104).trans hP)
  have saved (r : ℕ) (h1 : r ≠ 1 := by decide) (h2 : r ≠ 2 := by decide)
      (h3 : r ≠ 3 := by decide) := hrestore r h1 h2 h3
  obtain ⟨ready, hr₁, ha', hh', hz', hk, hmem, hpos⟩ :=
    finishInitThresholdWorkspace_runs (w := w) (p := p) (ω := ω) ((saved 101).trans ((stagedKeep 101).trans ha)) ((saved 99).trans ((stagedKeep 99).trans hh)) ((hm₀.trans hstageMem).symm ▸ hz)
  have keep (r : ℕ) (h4 : r ≠ 4 := by decide) (h7 : r ≠ 7 := by decide) := hk r h4 h7
  obtain ⟨out, hr₂, hhandle, hheap, hchain, hnum, hf, hz'', hk', hpos'⟩ :=
    allocateMinRatioInitHeader_runs (ω := ω) hh' ((keep 0).trans ((saved 0).trans ((stagedKeep 0).trans hm))) ((keep 1).trans hV')
      ((keep 75).trans ((saved 75).trans ((stagedKeep 75).trans hd))) ((keep 76).trans ((saved 76).trans ((stagedKeep 76).trans hb))) ((keep 6).trans ((saved 6).trans ((stagedKeep 6).trans hpsi))) ha'
      ((keep 72).trans ((saved 72).trans ((stagedKeep 72).trans hq))) ((keep 73).trans ((saved 73).trans ((stagedKeep 73).trans he))) ((keep 2).trans hL') ((keep 3).trans hP')
      ((keep 78).trans ((saved 78).trans h78)) ((keep 79).trans ((saved 79).trans (h79.trans h78))) hz' hroom
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨staged, 9, 94, hrSpace,
    runs_seq_iff.mpr (Or.inr ⟨restored, 8, 85, hr₀,
      runs_seq_iff.mpr (Or.inr ⟨ready, 5, 79, hr₁, hr₂, rfl⟩), rfl⟩), rfl⟩),
    hhandle, hheap, hchain, hnum, fun a h => (hf a h).trans (congrFun (hmem.trans (hm₀.trans hstageMem)) a), hz'',
    fun r h1 h2 h3 h4 h7 h74 h77 h78 h79 =>
      (hk' r h74 h77).trans ((hk r h4 h7).trans ((saved r h1 h2 h3).trans (stagedKeep r h78 h79))), ?_⟩
  intro j hj
  have htable : out.regs 83 = st.regs 83 :=
    (hk' 83 (by decide) (by decide)).trans ((keep 83).trans ((saved 83).trans (stagedKeep 83)))
  rw [htable]
  exact (hf _ (by omega)).trans (congrFun (hmem.trans (hm₀.trans hstageMem)) _)

/-- Allocate the header and enter the level initializer only after
the runtime check certifies the threshold table. -/
@[expose] def continueSolverInit (levels inconclusive : Stmt) : Stmt :=
  .cond (.bin .eq (.reg 10) (.const 1))
    (allocateSolverInitHeader ;; levels) inconclusive

/-- Certification permits the level initializer to use the allocated header. -/
theorem continueSolverInit_certified_runs {w headerCost levelCost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st header out : State} {levels inconclusive : Stmt}
    (hcert : st.regs 10 = 1) (hw : 1 < 2 ^ w)
    (hh : Runs w p ω allocateSolverInitHeader st .normal header headerCost)
    (hl : Runs w p ω levels header .normal out levelCost) :
    Runs w p ω (continueSolverInit levels inconclusive) st .normal out
      (headerCost + levelCost + 5) := by
  have hcond : Expr.eval w st (.bin .eq (.reg 10) (.const 1)) = some 1 := by
    simp [Expr.eval, BinOp.eval, hcert, hw]
  exact runs_cond_iff.mpr ⟨1, headerCost + levelCost + 1, hcond,
    runs_seq_iff.mpr (Or.inr ⟨header, headerCost, levelCost, hh, hl, rfl⟩), by
      simp [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega⟩

/-- An inconclusive check runs the supplied continuation without
entering header allocation or level initialization. -/
theorem continueSolverInit_inconclusive_runs {w cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {levels inconclusive : Stmt} {outcome : Outcome}
    (hcert : st.regs 10 ≠ 1) (hw : 1 < 2 ^ w)
    (hr : Runs w p ω inconclusive st outcome out cost) :
    Runs w p ω (continueSolverInit levels inconclusive) st outcome out (cost + 4) := by
  have hcond : Expr.eval w st (.bin .eq (.reg 10) (.const 1)) = some 0 := by
    simp [Expr.eval, BinOp.eval, hcert, hw]
  exact runs_cond_iff.mpr ⟨0, cost, hcond, by simpa using hr, by
    simp [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega⟩

/-- Scratch writes above the packed graph preserve both the dynamic
graph and the alpha data needed by level construction. -/
theorem initPackedGraphAlpha_of_frame
    {mem mem' : ℕ → ℕ} {G : MGraph} {heap limbs h precision V : ℕ}
    (hG : DynGraphAt mem (heap + (limbs + 1) + 6) G.n G.m G)
    (hExp : mem heap = Num.IPM.alphaExponent G.m V)
    (hValid : Num.Valid mem (heap + 1) h limbs)
    (hAlpha : Num.fixVal mem (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8)
    (hframe : ∀ a < heap + (limbs + 1) + 6 + dynGraphSize G.n G.m, mem' a = mem a) :
    DynGraphAt mem' (heap + (limbs + 1) + 6) G.n G.m G ∧
      mem' heap = Num.IPM.alphaExponent G.m V ∧ Num.Valid mem' (heap + 1) h limbs ∧
      Num.fixVal mem' (heap + 1) h limbs precision = Num.IPM.alphaPrime G.m V / 8 := by
  have hagree (i : ℕ) (hi : i < limbs) : mem' (heap + 1 + i) = mem (heap + 1 + i) :=
    hframe _ (by omega)
  refine ⟨hG.of_agree (fun a _ ha => hframe a ha), (hframe _ (by omega)).trans hExp,
    fun i hi => (hagree i hi).trans_lt (hValid i hi), ?_⟩
  rw [Num.fixVal, Num.intVal_congr hagree]
  exact hAlpha

end MinCostFlow.MinRatio
