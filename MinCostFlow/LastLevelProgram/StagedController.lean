module

public import MinCostFlow.LastLevelProgram.StagedControllerLoop

public import MinCostFlow.LastLevelProgram.StagedBranchAppend
public import MinCostFlow.LastLevelProgram.StagedWideInputs
public import MinCostFlow.LastLevelProgram.CanonicalModel
import MinCostFlow.DynSpanner.Program.DynGraphInit
import Mathlib.Data.Nat.Size

/-!
# Staged collection controller

The controller for Definition 5.8 (pages 19–20) initializes the weight
table, runs the rounds, and publishes the collection at the caller handle.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num SparseCore Scaling.Machine DynSpanner.Program

/-- The installed depth covers every vertex and fits both the numeric
row counter and the logarithmic round budget. -/
theorem controllerLevels_bounds (n w : ℕ) (hword : n+1 < 2^w) :
    n ≤ 2^(Nat.clog 2 n+1) ∧ Nat.clog 2 n+1 < 2^w ∧
      Nat.clog 2 n ≤ (n+2).size := by
  have hn : Nat.clog 2 n ≤ n :=
    (Nat.clog_le_iff_le_pow (by decide)).2 Nat.lt_two_pow_self.le
  refine ⟨(Nat.le_pow_clog (b := 2) (by decide) n).trans ?_,by omega,?_⟩
  · exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  · exact (Nat.clog_le_iff_le_pow (by decide)).2
      ((show n ≤ n+2 by omega).trans (Nat.lt_size_self _).le)

/-- The numeric round sees the controller's lifting depth, host format,
weight stride, update scale, and original edge table addresses. -/
theorem publishedRoundArgs_numericRegisters (st : State) (mem : ℕ → ℕ) (pos : ℕ) :
    let entered := startState ((List.range 70).map (st.regs ∘ roundControllerRegister)) mem pos
    entered.regs 14 = st.regs 86 ∧ entered.regs 19 = st.regs 91 ∧
    entered.regs 23 = st.regs 95 ∧ entered.regs 27 = st.regs 99 ∧
    entered.regs 28 = st.regs 100 ∧ entered.regs 32 = st.regs 104 ∧
    entered.regs 35 = st.regs 107 ∧ entered.regs 40 = st.regs 150 ∧ entered.regs 41 = st.regs 113 ∧
    entered.regs 42 = st.regs 114 ∧ entered.regs 43 = st.regs 115 ∧
    entered.regs 44 = st.regs 116 ∧ entered.regs 55 = st.regs 127 ∧
    entered.regs 56 = st.regs 3 ∧ entered.regs 57 = st.regs 2 ∧
    entered.regs 59 = st.regs 131 ∧ entered.regs 61 = st.regs 133 ∧
    entered.regs 62 = st.regs 134 := by
  simp [startState,roundControllerRegister,List.getD]

/-- Guest staging preserves the numeric controller words and installs the
incoming cursor and the two copies of the current weight pointer. -/
theorem stagedController_numericRegisters (st staged : State) (pos : ℕ)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (h8 : staged.regs 8 = st.mem (st.regs 0-1))
    (h31 : staged.regs 31 = st.mem (st.regs 0-1)) :
    staged.regs 5 = st.regs 0 ∧
    staged.regs 8 = st.mem (st.regs 0-1) ∧ staged.regs 31 = st.mem (st.regs 0-1) ∧
    staged.regs 14 = st.regs 86 ∧
    staged.regs 19 = st.regs 91 ∧
    staged.regs 23 = st.regs 95 ∧
    staged.regs 27 = st.regs 99 ∧
    staged.regs 28 = st.regs 100 ∧
    staged.regs 32 = st.regs 104 ∧
    staged.regs 35 = st.regs 107 ∧
    staged.regs 40 = st.regs 150 ∧
    staged.regs 41 = st.regs 113 ∧
    staged.regs 42 = st.regs 114 ∧
    staged.regs 43 = st.regs 115 ∧
    staged.regs 44 = st.regs 116 ∧
    staged.regs 55 = st.regs 127 ∧
    staged.regs 56 = st.regs 3 ∧ staged.regs 57 = st.regs 2 ∧
    staged.regs 59 = st.regs 131 ∧ staged.regs 61 = st.regs 133 ∧
    staged.regs 62 = st.regs 134 := by
  obtain ⟨h14,h19,h23,h27,h28,h32,h35,h40,h41,h42,h43,h44,h55,h56,h57,h59,h61,h62⟩ :=
    publishedRoundArgs_numericRegisters st st.mem pos
  exact ⟨hcursor,h8,h31,
    (hkeep 14 (by decide) (by decide) (by decide) (by decide)).trans h14,
    (hkeep 19 (by decide) (by decide) (by decide) (by decide)).trans h19,
    (hkeep 23 (by decide) (by decide) (by decide) (by decide)).trans h23,
    (hkeep 27 (by decide) (by decide) (by decide) (by decide)).trans h27,
    (hkeep 28 (by decide) (by decide) (by decide) (by decide)).trans h28,
    (hkeep 32 (by decide) (by decide) (by decide) (by decide)).trans h32,
    (hkeep 35 (by decide) (by decide) (by decide) (by decide)).trans h35,
    (hkeep 40 (by decide) (by decide) (by decide) (by decide)).trans h40,
    (hkeep 41 (by decide) (by decide) (by decide) (by decide)).trans h41,
    (hkeep 42 (by decide) (by decide) (by decide) (by decide)).trans h42,
    (hkeep 43 (by decide) (by decide) (by decide) (by decide)).trans h43,
    (hkeep 44 (by decide) (by decide) (by decide) (by decide)).trans h44,
    (hkeep 55 (by decide) (by decide) (by decide) (by decide)).trans h55,
    (hkeep 56 (by decide) (by decide) (by decide) (by decide)).trans h56,
    (hkeep 57 (by decide) (by decide) (by decide) (by decide)).trans h57,
    (hkeep 59 (by decide) (by decide) (by decide) (by decide)).trans h59,
    (hkeep 61 (by decide) (by decide) (by decide) (by decide)).trans h61,
    (hkeep 62 (by decide) (by decide) (by decide) (by decide)).trans h62⟩

/-- The staged selector sees the graph sizes, the live weight pointer,
and the separate guest and host formats from the controller. -/
theorem stagedController_selectorArgs {w : ℕ} (st staged : State) (pos : ℕ) (H : MGraph)
    (guestL sim stride P Q hostL : ℕ)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = hostL) :
    evalArgs w staged convertedGuestCallArgs =
      some (stagedGuestArgs H guestL sim (st.regs 0) (st.mem (st.regs 0-1)) stride P Q ++
        List.replicate 7 0 ++ [hostL]) := by
  have keep r (h₁ : r ≠ 5) (h₂ : r ≠ 8) (h₃ : r ≠ 31) (h₄ : r ≠ 70) := hkeep r h₁ h₂ h₃ h₄
  apply convertedGuestCallArgs_eval H guestL sim _ _ stride P Q hostL
    _ _ _ _ hcursor hweight _ _ _ _ (Nat.two_pow_pos _)
  · simpa [startState,roundControllerRegister,List.getD,hn] using keep 0 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hm] using keep 1 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hguest] using keep 2 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hsim] using keep 3 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hstride] using keep 9 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hP] using keep 10 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hQ] using keep 11 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD,hhost] using keep 19 (by decide) (by decide) (by decide) (by decide)

/-- The selector can pack the current weight blocks into the fresh
suffix of the staged guest input. Only the live host blocks are read. -/
theorem stagedController_selectorMemory
    {w vCap eCap L P caller base count handle bound j guestL Q stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstride : L ≤ stride)
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a →
      staged.mem a = st.mem a)
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hP : P+guestL < 2^w) (hQ : Q < 2^w)
    (hm : H.m < 2^w) (hroom : st.regs 0+queryOriginals H guestL < 2^w)
    (hpos : ∀ e ∈ H.E, 0 ≤ weights P ρ query j e)
    (hfit : ∀ e ∈ H.E, Fits 1 guestL (queryNumerator Q (weights P ρ query j e))) :
    let src := st.mem (st.regs 0-1)
    let dst := st.regs 0+queryWeights H guestL
    (packGuestStridedContract w).pre [src,dst,stride,L,P,Q,guestL,H.m] staged.mem ∧
    ZeroFrom staged.mem dst ∧
    ∀ i < H.m, queryNumerator Q (fixVal staged.mem (src+i*stride) 4 L P) =
      queryNumerator Q (weights P ρ query j (edgeName H i)) := by
  intro src dst
  have hs' := hs
  obtain ⟨_,_,_,_,_,hzero,_,_,_,_⟩ := hs'
  obtain ⟨hend,hweights⟩ := stagedController_stagedWeights st staged hs
    (fun a ha => hframe a (Or.inl ha))
  have hsep i (hi : i < H.m) : src+i*stride+L ≤ dst := by
    have hb := Nat.mul_le_mul_right stride (show i ≤ H.m-1 by omega)
    change src+(H.m-1)*stride+L ≤ st.regs 0 at hend
    dsimp [dst]
    omega
  refine ⟨packGuestStrided_pre_of_weights H staged.mem (weights P ρ query j)
    src dst stride L P Q guestL hw hL hP hQ hm hstride hsep ?_ hweights hpos hfit,?_,?_⟩
  · simpa [dst,queryOriginals,Nat.add_assoc] using hroom
  · intro a ha
    exact (hframe a (Or.inr ha)).trans (hzero a ((Nat.le_add_right _ _).trans ha))
  · intro i hi
    exact congrArg (queryNumerator Q) (hweights i hi).2

/-- Numeric output supplies the address registers used by branch append.
Installing those registers retains the numeric memory and allocation end. -/
theorem stagedController_appendLayout {w n m L heap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (hn : st.regs 0 = n) (hm : st.regs 1 = m) (hL : st.regs 19 = L)
    (hh : st.regs 20 = heap) (hnWord : n < 2^w)
    (hmPos : 0 < m) (hLPos : 0 < L) (hw : 1 < 2^w) :
    let start := heap+(n-1)*L
    let afterStretch := start+m*edgeStretchSpace L
    let stop := afterStretch+m*narrowWeightSpace L
    st.regs 16 = stop → ZeroFrom st.mem stop → stop < 2^w →
    ∃ ready cost, Runs w p ω installStagedOutputLayout st .normal ready cost ∧
      ready.mem = st.mem ∧ ready.regs 16 = stop ∧ ZeroFrom ready.mem stop ∧
      ready.regs 36 = start+edgeStretchSpace L-L ∧ ready.regs 37 = edgeStretchSpace L ∧
      ready.regs 38 = afterStretch+narrowWeightSpace L-L ∧ ready.regs 39 = narrowWeightSpace L ∧
      (∀ r, r ∉ ([36,37,38,39] : List ℕ) → ready.regs r = st.regs r) ∧
      cost ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9 := by
  intro start afterStretch stop hstop hzero hfit
  obtain ⟨ready,cost,hr,hmem,h36,h37,h38,h39,hkeep,hcost⟩ :=
    installStagedOutputLayout_runs (ω := ω) st n m L heap hn hm hL hh hnWord hmPos hLPos hw hfit
  exact ⟨ready,cost,hr,hmem,(hkeep 16 (by decide)).trans hstop,hmem.symm ▸ hzero,
    h36,h37,h38,h39,hkeep,hcost⟩

/-- The numeric postcondition supplies the two arrays at the addresses
installed for branch append. -/
theorem stagedController_appendArrays {w h Q : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G T H : MGraph) (len : ℕ → ℤ)
    (adj parents edges depths queue n levels dist lengths L heap tails heads P old stride denom j : ℕ)
    (scale : ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (args : List ℕ) (mem : ℕ → ℕ)
    (hn : st.regs 0 = n) (hm : st.regs 1 = G.m) (hl : st.regs 19 = L)
    (hh : st.regs 20 = heap) (hmEq : H.m = G.m)
    (hnWord : n < 2^w) (hmPos : 0 < G.m) (hLPos : 0 < L) (hw : 1 < 2^w)
    (hpost : (stretchWeightRoundContract w h Q G T H 0 len adj parents edges depths queue n
      levels dist lengths L heap tails heads P old stride denom j scale query).post
      args mem (st.regs 16) st.mem)
    (hfit : heap+(n-1)*L+G.m*edgeStretchSpace L+G.m*narrowWeightSpace L < 2^w) :
    let start := heap+(n-1)*L
    let afterStretch := start+G.m*edgeStretchSpace L
    let stop := afterStretch+G.m*narrowWeightSpace L
    ∃ ready cost, Runs w p ω installStagedOutputLayout st .normal ready cost ∧
      ready.mem = st.mem ∧ ready.regs 16 = stop ∧ ZeroFrom ready.mem stop ∧
      ready.regs 36 = start+edgeStretchSpace L-L ∧ ready.regs 37 = edgeStretchSpace L ∧
      ready.regs 38 = afterStretch+narrowWeightSpace L-L ∧ ready.regs 39 = narrowWeightSpace L ∧
      (∀ r, r ∉ ([36,37,38,39] : List ℕ) → ready.regs r = st.regs r) ∧
      (∀ i < H.m, Valid st.mem (roundStretchAddr start L i) h L ∧
        fixVal st.mem (roundStretchAddr start L i) h L P =
          query (weights P (scale : ℝ) query j) (edgeName H i)) ∧
      (∀ i < H.m, Valid st.mem (roundWeightAddr afterStretch L i) h L ∧
        fixVal st.mem (roundWeightAddr afterStretch L i) h L P =
          weights P (scale : ℝ) query (j+1) (edgeName H i)) ∧
      cost ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9 := by
  obtain ⟨hret,hzero,_,hblocks,_⟩ := hpost
  rw [hmEq] at hret
  obtain ⟨ready,cost,hr,hmem,hend,hz,h36,h37,h38,h39,hkeep,hcost⟩ :=
    stagedController_appendLayout (ω := ω) st hn hm hl hh hnWord hmPos hLPos hw
      hret (hret ▸ hzero) hfit
  exact ⟨ready,cost,hr,hmem,hend,hz,h36,h37,h38,h39,hkeep,
    fun i hi => (hblocks i hi).2,fun i hi => (hblocks i hi).1,hcost⟩

/-- The original vertex list remains available to branch initialization
after any writes above the original graph block. -/
theorem stagedController_originalVertices {g vCap eCap limit : ℕ}
    {G : MGraph} {mem out : ℕ → ℕ}
    (hg : DynGraphAt mem g vCap eCap G) (hlimit : g+dynGraphSize vCap eCap ≤ limit)
    (hframe : ∀ a < limit, out a = mem a) :
    ∃ vs : List ℕ, vs.length = G.n ∧ vs.Nodup ∧
      (∀ v, v ∈ vs ↔ v ∈ G.V) ∧ ListAt out (dgVListBase g vCap) vs ∧
      dgVListBase g vCap+vs.length ≤ limit := by
  obtain ⟨_,hcap,_,_,_,_,_,_,⟨vs,hlen,hnd,hV,hlist,_⟩,_⟩ := hg
  have hv : vs.length ≤ vCap := by
    simpa using hnd.length_le_of_subset (l₂ := List.range vCap)
      (fun v hv => List.mem_range.mpr (hcap v ((hV v).mp hv)))
  have hspan : dgVListBase g vCap+vs.length ≤ limit := by
    unfold dgVListBase dynGraphSize at *
    omega
  exact ⟨vs,hlen,hnd,hV,hlist.congr (fun a _ ha => hframe a (ha.trans_le hspan)),hspan⟩

/-- The numeric call preserves the two representative name tables and the
original graph's vertex list for branch publication. -/
theorem stagedController_branchNames {G H T : MGraph}
    {g vCap eCap names vertices cursor base dest count : ℕ}
    {mem staged out : ℕ → ℕ}
    (hg : DynGraphAt mem g vCap eCap G)
    (hgraph : g+dynGraphSize vCap eCap ≤ cursor)
    (hnames : names+H.m ≤ cursor) (hvertices : vertices+H.n ≤ cursor)
    (hstage : ∀ a < cursor, staged a = mem a)
    (htree : retainedStagedTreeAt H T base dest count staged out)
    (hbase : cursor ≤ base)
    (hedges : ∀ i < H.m, mem (names+i) = edgeName H i)
    (hverts : ∀ i < H.n, mem (vertices+i) = vertexName H i) :
    (∀ i < H.m, staged (names+i) = edgeName H i) ∧
    (∀ i < H.n, staged (vertices+i) = vertexName H i) ∧
    ∃ vs : List ℕ, vs.length = G.n ∧ vs.Nodup ∧
      (∀ v, v ∈ vs ↔ v ∈ G.V) ∧ ListAt out (dgVListBase g vCap) vs ∧
      dgVListBase g vCap+vs.length ≤ cursor := by
  refine ⟨fun i hi => (hstage _ (by omega)).trans (hedges i hi),
    fun i hi => (hstage _ (by omega)).trans (hverts i hi), ?_⟩
  exact stagedController_originalVertices hg hgraph
    (fun a ha => (retainedStagedTreeAt_frame htree hbase a ha).trans (hstage a ha))

/-- The branch record writer sees the same retained tree after the
address setup and the unit allocation. -/
theorem stagedController_branchTree {H T : MGraph}
    {base dest count stop : ℕ} {mem : ℕ → ℕ} {numeric layout unit : State}
    (htree : retainedStagedTreeAt H T base dest count mem numeric.mem)
    (hlayout : layout.mem = numeric.mem)
    (hunit : ∀ a < stop, unit.mem a = layout.mem a)
    (hbase : base ≤ stop) (hdest : dest+H.n ≤ stop) :
    retainedStagedTreeAt H T base dest count mem unit.mem :=
  retainedStagedTreeAt_congr htree hbase hdest
    (fun a ha => (hunit a ha).trans (congrFun hlayout a))

/-- Reuse the original graph's vertex list when restoring the selected
tree to a branch graph. All of the input graph's vertices are copied. -/
theorem stagedController_branchGraph_runs {w entry write bOps bEdge bSplit bBatch : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G T : MGraph) (ℓ : ℕ → ℝ)
    (guestL staging cursor count names vertices records g vCap eCap : ℕ)
    (mem staged : ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (j : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hp : p.procs[entry]? = some (branchEdgeRecordsBody write))
    (hwrite : p.procs[write]? = some writeBranchEdgeRecordBody)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hops : p.HasAt bOps dgOpsProcs)
    (hw : 16 ≤ 2^w) (hG : G.IsValid)
    (hg : DynGraphAt mem g vCap eCap G) (hgEnd : g+dynGraphSize vCap eCap ≤ records)
    (hframe : ∀ a < records, st.mem a = mem a)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hRecords : st.regs 16 = records) (hNames : st.regs 28 = names)
    (hStaging : st.regs 5 = staging) (hVertices : st.regs 40 = vertices)
    (hCursor : st.regs 12 = cursor) (hCount : st.regs 13 = count)
    (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (h43 : st.regs 43 = G.n) (h44 : st.regs 44 = dgVListBase g vCap)
    (hwords : ∀ x ∈ [vCap,eCap,G.n,dgVListBase g vCap], x < 2^w)
    (hz : ZeroFrom st.mem records) :
    let H := representativeGraph G ℓ
    let dest := cursor+1+H.m
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    oracle H (LSF.safeLen H ℓ) (weights P (roundedScale C H) query j) = restoreTreeNames H T →
    st.regs 1 = H.m →
    retainedStagedTreeAt H T (staging+queryWeights H guestL) dest count staged st.mem →
    (∀ i ∈ T.E, i < H.m) →
    names+H.m ≤ staging+queryWeights H guestL → vertices+H.n ≤ staging+queryWeights H guestL →
    (∀ i < H.m, staged (names+i) = edgeName H i ∧
      staged (staging+i) = (indexedGraph H).tail i ∧
      staged (staging+(H.m+i)) = (indexedGraph H).head i) →
    (∀ v < H.n, staged (vertices+v) = vertexName H v) →
    staging+queryWeights H guestL ≤ dest → dest+H.n ≤ records →
    records+3*H.n < 2^w → records+3*count+4+dynGraphSize vCap eCap < 2^w →
    ∃ out cost, Runs w p ω
      (stagedBranchGraphBody entry (bBatch+dgIdxInitFromLists)) st .normal out cost ∧
      DynGraphAt out.mem (records+3*count+4) vCap eCap branch.T ∧
      DynGraphAt out.mem (records+3*count+4) vCap eCap branch.F.F ∧
      componentRoots G = branch.F.R ∧
      (∀ u < vCap, out.mem (records+3*count+4+dynGraphSize vCap eCap+u) = 0) ∧
      ZeroFrom out.mem (records+3*count+4+dynGraphSize vCap eCap) ∧
      (∀ a < records, out.mem a = st.mem a) ∧
      (∀ r, r ≠ 45 → r ≠ 46 → out.regs r = st.regs r) ∧
      cost ≤ 130*G.n+563*count+139 := by
  intro H dest P query branch hmodel hm htree hindex hnames hvertices hedges hverts hsep hdest hroom hfull
  obtain ⟨vs,hlen,_,hset,hlist,hspan⟩ := stagedController_originalVertices hg hgEnd hframe
  have hvCap : vCap < 2^w := hwords _ (by simp)
  have heCap : eCap < 2^w := hwords _ (by simp)
  obtain ⟨out,cost,hr,hgraph,hzero,hprefix,hregs,hcost⟩ :=
    stagedBranchGraph_runs (ω := ω) st G T ℓ
      guestL staging cursor count names vertices records staged hp
      (writeBranchEdgeRecord_meetsContract hwrite) (by omega) hG
    (fun v hv => Nat.lt_trans (hV v hv) hvCap) (fun e he => Nat.lt_trans (hE e he) heCap)
    hRecords hNames hStaging hVertices hCursor hCount hm htree hindex hnames hvertices
    hedges hverts hsep hdest vs vCap eCap (dgVListBase g vCap) h41 h42 (h43.trans hlen.symm)
    h44 hset hV hE hlist hspan hw (by simpa only [hlen] using hwords) hz hroom hfull
    (fun _ => dgInitFromLists_meetsContract hbatch hedge hops)
  obtain ⟨hT,hF,hroots,hrootZero⟩ :=
    stagedBranchGraph_publish_payload oracle C G T ℓ j (records+3*count+4) vCap eCap
      out.mem hnl hmodel hgraph hzero
  exact ⟨out,cost,hr,hT,hF,hroots,hrootZero,hzero,hprefix,hregs,by simpa only [hlen] using hcost⟩

/-- All compact stretch blocks are below the unit allocation and the
branch graph. They can be read in place by the named scatter. -/
theorem stagedController_branchStretchInputs {H : MGraph}
    {h L P start addresses : ℕ} {mem out : ℕ → ℕ} {value : ℕ → ℝ}
    (hspan : start+H.m*edgeStretchSpace L ≤ addresses)
    (hframe : ∀ a < start+H.m*edgeStretchSpace L, out a = mem a)
    (hvalues : ∀ i < H.m, Valid mem (roundStretchAddr start L i) h L ∧
      fixVal mem (roundStretchAddr start L i) h L P = value (edgeName H i)) :
    ∀ i < H.m,
      let src := start+edgeStretchSpace L-L+i*edgeStretchSpace L
      src+L ≤ addresses ∧ Valid out src h L ∧ fixVal out src h L P = value (edgeName H i) := by
  intro i hi
  dsimp only
  rw [← stagedStretchAddr_eq]
  have hend := (stagedNumericOutput_blockEnds start H.m L i hi).1
  have hkeep (k : ℕ) (hk : k < L) : out (roundStretchAddr start L i+k) =
      mem (roundStretchAddr start L i+k) := hframe _ (by omega)
  obtain ⟨hv,hval⟩ := hvalues i hi
  exact ⟨hend.trans hspan,fun k hk => (hkeep k hk).trans_lt (hv k hk),
    by simpa only [fixVal,intVal_congr hkeep] using hval⟩

/-- The restored graph and freshly allocated unit preserve every
publication input below the numeric allocation end. -/
theorem stagedController_publicationFrame {numeric layout unit graph : State}
    {numericEnd records : ℕ} (hEnd : numericEnd ≤ records)
    (hLayout : layout.mem = numeric.mem)
    (hUnit : ∀ a < numericEnd, unit.mem a = layout.mem a)
    (hGraph : ∀ a < records, graph.mem a = unit.mem a) :
    ∀ a < numericEnd, graph.mem a = numeric.mem a := by
  intro a ha
  exact (hGraph a (ha.trans_le hEnd)).trans ((hUnit a ha).trans (congrFun hLayout a))

/-- The original names, stretch indices, and compact vertex names
are still available in the restored graph state. -/
theorem stagedController_publicationTables {G H T : MGraph}
    {cursor stagingEnd dest count numericEnd records names indices vertices : ℕ}
    {mem staged : ℕ → ℕ} {numeric layout unit graph : State}
    (ℓ : ℕ → ℝ)
    (hstage : ∀ a < cursor, staged a = mem a)
    (htree : retainedStagedTreeAt H T stagingEnd dest count staged numeric.mem)
    (hcursor : cursor ≤ stagingEnd) (hnum : cursor ≤ numericEnd)
    (hEnd : numericEnd ≤ records) (hLayout : layout.mem = numeric.mem)
    (hUnit : ∀ a < numericEnd, unit.mem a = layout.mem a)
    (hGraph : ∀ a < records, graph.mem a = unit.mem a)
    (hnamesEnd : names+G.m ≤ cursor) (hindicesEnd : indices+G.m ≤ cursor)
    (hverticesEnd : vertices+H.n ≤ cursor)
    (hnames : ∀ i < G.m, mem (names+i) = edgeName G i)
    (hindices : ∀ i < G.m, mem (indices+i) = branchStretchIndex G ℓ (edgeName G i))
    (hvertices : ∀ i < H.n, mem (vertices+i) = vertexName H i) :
    (∀ i < G.m, graph.mem (names+i) = edgeName G i) ∧
    (∀ i < G.m, graph.mem (indices+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
    ∀ i < H.n, graph.mem (vertices+i) = vertexName H i := by
  have hframe := stagedController_publicationFrame hEnd hLayout hUnit hGraph
  have hkeep a (ha : a < cursor) : graph.mem a = mem a :=
    (hframe a (ha.trans_le hnum)).trans
      ((retainedStagedTreeAt_frame htree hcursor a ha).trans (hstage a ha))
  exact ⟨fun i hi => (hkeep _ (by omega)).trans (hnames i hi),
    fun i hi => (hkeep _ (by omega)).trans (hindices i hi),
    fun i hi => (hkeep _ (by omega)).trans (hvertices i hi)⟩

/-- Combine the three branch append phases with the frame needed
to retain the numeric weight blocks and earlier collection slots. -/
theorem stagedController_appendPhases {w unit restore init scatter publish : ℕ}
    {p : Program} {ω : ℕ → Bool} {st afterUnit graph out : State}
    {cu cg co numericEnd records stop slot : ℕ}
    (hu : Runs w p ω (stagedAfterRoundUnitBody unit) st .normal afterUnit cu)
    (hg : Runs w p ω (stagedBranchGraphBody restore init) afterUnit .normal graph cg)
    (ho : Runs w p ω (stagedBranchOutputBody scatter publish) graph .normal out co)
    (hEnd : numericEnd ≤ records)
    (huFrame : ∀ a < numericEnd, afterUnit.mem a = st.mem a)
    (hgFrame : ∀ a < records, graph.mem a = afterUnit.mem a)
    (hoFrame : ∀ a, a < numericEnd ∨ stop ≤ a → a ≠ slot → out.mem a = graph.mem a)
    (huWeight : afterUnit.regs 38 = st.regs 38)
    (hgWeight : graph.regs 38 = afterUnit.regs 38)
    (hoWeight : out.regs 38 = graph.regs 38) :
    Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      st .normal out (cu+cg+co+2) ∧
    (∀ a < numericEnd, a ≠ slot → out.mem a = st.mem a) ∧
    out.regs 38 = st.regs 38 := by
  have htail := runs_seq_iff.mpr (Or.inr ⟨graph,cg,co,hg,ho,rfl⟩)
  refine ⟨runs_seq_iff.mpr (Or.inr ⟨afterUnit,cu,cg+co+1,hu,htail,by omega⟩),?_,
    hoWeight.trans (hgWeight.trans huWeight)⟩
  intro a ha hne
  exact (hoFrame a (Or.inl ha) hne).trans
    ((hgFrame a (ha.trans_le hEnd)).trans (huFrame a ha))

/-- A published branch with packed weights advances the controller
invariant to caller-width stride. -/
theorem stagedController_packedAppendPost
    {H : MGraph} {vCap eCap h L P caller base count handle bound j start stop budget oldStride : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem numeric : ℕ → ℕ} (st out : State) (args : List ℕ) (input : ℕ → ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      oldStride E branches ρ query mem j st)
    (hm : 0 < H.m) (hj : j < count) (hstart : st.regs 0 ≤ start)
    (hstop : start+H.m*L ≤ stop) (hbound : stop+1 ≤ bound)
    (hnumeric : ∀ a < st.regs 0, numeric a = st.mem a)
    (happend : ∀ a < start+H.m*L, a ≠ base+1+j → out.mem a = numeric a)
    (hzero : ZeroFrom out.mem stop)
    (hspan : BranchWithin out.mem (out.mem (base+1+j)) (base+1+count) stop vCap eCap L E)
    (hbranch : MinRatio.LSFAt out.mem (out.mem (base+1+j)) vCap eCap h L caller E (branches j))
    (hvalues : ∀ i < H.m, Valid numeric (start+i*L) h L ∧
      fixVal numeric (start+i*L) h L P = weights P ρ query (j+1) (edgeName H i))
    (hweight : out.regs 38 = start) :
    let Next := stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      L E branches ρ query mem (j+1)
    (stagedControllerRoundContract st Next j budget).post args input (stop+1)
      (Function.update out.mem stop (out.regs 38)) := by
  have hsCopy := hs
  obtain ⟨_,_,_,htable,_,_,_,hprefix,_,_⟩ := hsCopy
  have hp := CollectionPrefix.of_agree hprefix htable (fun a _ ha => hnumeric a ha)
  obtain ⟨hptr,hend,hfresh,hframe,hprefix',hweights⟩ :=
    stagedPackedRound_memory H ρ query hm hj htable hstart hp hstop happend hzero hspan hbranch hvalues
  intro Next pos
  rw [hweight]
  apply stagedRoundStateAtStride_next pos hs (by omega) hbound hfresh _ hprefix' _ hweights
  · intro a ha
    exact (hframe a (by omega) (by omega)).trans (hnumeric a (by omega))
  · rw [hptr,Nat.add_sub_cancel]
    exact hend

/-- A published branch and the new weight pointer establish the
controller contract's postcondition at every return position. -/
theorem stagedController_appendPost
    {H : MGraph} {vCap eCap h L P caller base count handle bound j start stop budget : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem staged numeric : ℕ → ℕ} (st out : State) (args : List ℕ) (input : ℕ → ℕ)
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st)
    (hm : 0 < H.m) (hj : j < count) (hstart : st.regs 0 ≤ start)
    (hstop : start+H.m*narrowWeightSpace L ≤ stop) (hbound : stop+1 ≤ bound)
    (hstage : ∀ a < st.regs 0, staged a = st.mem a)
    (hnumeric : ∀ a < st.regs 0, numeric a = staged a)
    (happend : ∀ a < start+H.m*narrowWeightSpace L, a ≠ base+1+j → out.mem a = numeric a)
    (hzero : ZeroFrom out.mem stop)
    (hspan : BranchWithin out.mem (out.mem (base+1+j)) (base+1+count) stop vCap eCap L E)
    (hbranch : MinRatio.LSFAt out.mem (out.mem (base+1+j)) vCap eCap h L caller E (branches j))
    (hvalues : ∀ i < H.m, Valid numeric (roundWeightAddr start L i) h L ∧
      fixVal numeric (roundWeightAddr start L i) h L P = weights P ρ query (j+1) (edgeName H i))
    (hweight : out.regs 38 = start+narrowWeightSpace L-L) :
    let Next := stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem (j+1)
    (stagedControllerRoundContract st Next j budget).post args input (stop+1)
      (Function.update out.mem stop (out.regs 38)) := by
  have hsCopy := hs
  obtain ⟨_,_,_,htable,_,_,_,hprefix,_,_⟩ := hsCopy
  obtain ⟨hgrowth,_,hweightEnd,hfresh,_,hframe,hprefix',hweights⟩ :=
    stagedPublishedRound_memory H ρ query hm hj htable hprefix hstart hstop
      hstage hnumeric happend hzero hspan hbranch hvalues
  intro Next pos
  rw [hweight]
  exact stagedRoundState_next pos hs hgrowth.le hbound hfresh hframe hprefix' hweightEnd hweights

/-- The append phases preserve the round invariant after writing
the returned weight pointer. The publication pointer identifies the
new branch in both the footprint and the model layout. -/
theorem stagedController_publishedPost
    {H T : MGraph} {vCap eCap h L P caller base count handle bound j start stop budget
      stagingEnd dest treeCount branchPtr : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged numeric layout out : State) (args : List ℕ)
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st)
    (hm : 0 < H.m) (hj : j < count) (hstart : st.regs 0 ≤ start)
    (hstop : start+H.m*narrowWeightSpace L ≤ stop) (hbound : stop+1 ≤ bound)
    (hstage : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (htree : retainedStagedTreeAt H T stagingEnd dest treeCount staged.mem numeric.mem)
    (hcursor : st.regs 0 ≤ stagingEnd)
    (hLayout : layout.mem = numeric.mem)
    (happend : ∀ a < start+H.m*narrowWeightSpace L, a ≠ base+1+j → out.mem a = layout.mem a)
    (hzero : ZeroFrom out.mem stop) (hptr : out.mem (base+1+j) = branchPtr)
    (hspan : BranchWithin out.mem branchPtr (base+1+count) stop vCap eCap L E)
    (hbranch : MinRatio.LSFAt out.mem branchPtr vCap eCap h L caller E (branches j))
    (hvalues : ∀ i < H.m, Valid numeric.mem (roundWeightAddr start L i) h L ∧
      fixVal numeric.mem (roundWeightAddr start L i) h L P = weights P ρ query (j+1) (edgeName H i))
    (hweight : out.regs 38 = start+narrowWeightSpace L-L) :
    let Next := stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem (j+1)
    (stagedControllerRoundContract st Next j budget).post args st.mem (stop+1)
      (Function.update out.mem stop (out.regs 38)) :=
  stagedController_appendPost st out args st.mem hs hm hj hstart hstop hbound hstage
    (retainedStagedTreeAt_frame htree hcursor)
    (fun a ha hs => (happend a ha hs).trans (congrFun hLayout a)) hzero
    (hptr.symm ▸ hspan) (hptr.symm ▸ hbranch) hvalues hweight

/-- The named scatter reads the unit block from the unit allocation
and the compact stretch blocks from the earlier numeric allocation. -/
theorem stagedController_scatterSources {H : MGraph}
    {h L P start numericEnd records addresses : ℕ} {numeric layout unit graph : State}
    {value : ℕ → ℝ}
    (hStretchEnd : start+H.m*edgeStretchSpace L ≤ numericEnd)
    (hunitEnd : numericEnd+2*L ≤ records) (haddress : records ≤ addresses)
    (hLayout : layout.mem = numeric.mem)
    (hUnit : ∀ a < numericEnd, unit.mem a = layout.mem a)
    (hGraph : ∀ a < records, graph.mem a = unit.mem a)
    (hValid : Valid unit.mem (numericEnd+L) h L)
    (hValue : fixVal unit.mem (numericEnd+L) h L P = 1)
    (hvalues : ∀ i < H.m, Valid numeric.mem (roundStretchAddr start L i) h L ∧
      fixVal numeric.mem (roundStretchAddr start L i) h L P = value (edgeName H i)) :
    numericEnd+L+L ≤ addresses ∧ Valid graph.mem (numericEnd+L) h L ∧
    fixVal graph.mem (numericEnd+L) h L P = 1 ∧
    ∀ i < H.m,
      let src := start+edgeStretchSpace L-L+i*edgeStretchSpace L
      src+L ≤ addresses ∧ Valid graph.mem src h L ∧
        fixVal graph.mem src h L P = value (edgeName H i) := by
  have hEnd : numericEnd ≤ records := by omega
  have hframe := stagedController_publicationFrame hEnd hLayout hUnit hGraph
  have hkeep k (hk : k < L) : graph.mem (numericEnd+L+k) = unit.mem (numericEnd+L+k) :=
    hGraph _ (by omega)
  exact ⟨by omega,fun k hk => (hkeep k hk).trans_lt (hValid k hk),
    by simpa only [fixVal,intVal_congr hkeep] using hValue,
    stagedController_branchStretchInputs (hStretchEnd.trans (hEnd.trans haddress))
      (fun a ha => hframe a (ha.trans_le hStretchEnd)) hvalues⟩

/-- The unit and graph initialization preserve a packed stretch table
and supply the constant block used for loops. -/
theorem stagedController_packedScatterSources {H : MGraph}
    {h L P start numericEnd records addresses : ℕ} {packed unit graph : State}
    {value : ℕ → ℝ}
    (hStretchEnd : start+H.m*L ≤ numericEnd)
    (hunitEnd : numericEnd+2*L ≤ records) (haddress : records ≤ addresses)
    (hUnit : ∀ a < numericEnd, unit.mem a = packed.mem a)
    (hGraph : ∀ a < records, graph.mem a = unit.mem a)
    (hValid : Valid unit.mem (numericEnd+L) h L)
    (hValue : fixVal unit.mem (numericEnd+L) h L P = 1)
    (hvalues : ∀ i < H.m, Valid packed.mem (start+i*L) h L ∧
      fixVal packed.mem (start+i*L) h L P = value (edgeName H i)) :
    numericEnd+L+L ≤ addresses ∧ Valid graph.mem (numericEnd+L) h L ∧
    fixVal graph.mem (numericEnd+L) h L P = 1 ∧
    ∀ i < H.m, (start+i*L)+L ≤ addresses ∧ Valid graph.mem (start+i*L) h L ∧
      fixVal graph.mem (start+i*L) h L P = value (edgeName H i) := by
  have hkeep k (hk : k < L) : graph.mem (numericEnd+L+k) = unit.mem (numericEnd+L+k) :=
    hGraph _ (by omega)
  refine ⟨by omega,fun k hk => (hkeep k hk).trans_lt (hValid k hk),
    by simpa only [fixVal,intVal_congr hkeep] using hValue,?_⟩
  intro i hi
  have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hmul
  have hframe k (hk : k < L) : graph.mem (start+i*L+k) = packed.mem (start+i*L+k) :=
    (hGraph _ (by omega)).trans (hUnit _ (by omega))
  exact ⟨by omega,fun k hk => (hframe k hk).trans_lt ((hvalues i hi).1 k hk),
    by simpa only [fixVal,intVal_congr hframe] using (hvalues i hi).2⟩

/-- Allocate the constant stretch for loops and restore the selected
tree in the immediately following branch records. -/
theorem stagedController_unitGraph_runs
    {w unit entry write bOps bEdge bSplit bBatch h L : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G T : MGraph) (ℓ : ℕ → ℝ)
    (guestL staging cursor count names vertices numericEnd g vCap eCap : ℕ)
    (mem staged : ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (j : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hp : p.procs[entry]? = some (branchEdgeRecordsBody write))
    (hwrite : p.procs[write]? = some writeBranchEdgeRecordBody)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hops : p.HasAt bOps dgOpsProcs)
    (hunit : MeetsContract w p unit (denominatorContract w h))
    (hw : 16 ≤ 2^w)
    (hg : DynGraphAt mem g vCap eCap G) (hgEnd : g+dynGraphSize vCap eCap ≤ numericEnd)
    (hframe : ∀ a < g+dynGraphSize vCap eCap, st.mem a = mem a)
    (hEnd : st.regs 16 = numericEnd) (hL : st.regs 55 = L)
    (hNames : st.regs 28 = names) (hStaging : st.regs 5 = staging)
    (hVertices : st.regs 40 = vertices) (hCursor : st.regs 12 = cursor) (hCount : st.regs 13 = count)
    (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (h43 : st.regs 43 = G.n) (h44 : st.regs 44 = dgVListBase g vCap)
    (hwords : ∀ x ∈ [vCap,eCap,G.n,dgVListBase g vCap], x < 2^w)
    (hz : ZeroFrom st.mem numericEnd) :
    let H := representativeGraph G ℓ
    let dest := cursor+1+H.m
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    let records := numericEnd+2*L
    let roots := records+3*count+4+dynGraphSize vCap eCap
    st.regs 23 = P → P < 2^w → 2 * (2 : ℝ)^P < Num.capacity h L →
    oracle H (LSF.safeLen H ℓ) (weights P (roundedScale C H) query j) = restoreTreeNames H T →
    st.regs 1 = H.m →
    retainedStagedTreeAt H T (staging+queryWeights H guestL) dest count staged st.mem →
    (∀ i ∈ T.E, i < H.m) →
    names+H.m ≤ staging+queryWeights H guestL → vertices+H.n ≤ staging+queryWeights H guestL →
    (∀ i < H.m, staged (names+i) = edgeName H i ∧
      staged (staging+i) = (indexedGraph H).tail i ∧
      staged (staging+(H.m+i)) = (indexedGraph H).head i) →
    (∀ v < H.n, staged (vertices+v) = vertexName H v) →
    staging+queryWeights H guestL ≤ dest → dest+H.n ≤ numericEnd →
    records+3*H.n < 2^w → roots < 2^w →
    ∃ ready out cu cg,
      Runs w p ω (stagedAfterRoundUnitBody unit) st .normal ready cu ∧
      Runs w p ω (stagedBranchGraphBody entry (bBatch+dgIdxInitFromLists)) ready .normal out cg ∧
      DynGraphAt out.mem (records+3*count+4) vCap eCap branch.T ∧
      DynGraphAt out.mem (records+3*count+4) vCap eCap branch.F.F ∧
      componentRoots G = branch.F.R ∧ ZeroFrom out.mem roots ∧
      Valid ready.mem (numericEnd+L) h L ∧ fixVal ready.mem (numericEnd+L) h L P = 1 ∧
      (∀ a < numericEnd, ready.mem a = st.mem a) ∧
      (∀ a < records, out.mem a = ready.mem a) ∧
      out.regs 16 = records ∧ out.regs 60 = numericEnd+L ∧
      (∀ r, r ≠ 16 → r ≠ 45 → r ≠ 46 → r ≠ 60 → r ≠ 67 → out.regs r = st.regs r) ∧
      cu+cg ≤ 56*L+75+(130*G.n+563*count+139) := by
  intro H dest P query branch records roots hP hPword hwidth hmodel hm htree hindex hnames
    hverSpan hedges hverts hsep hdest hroom hroots
  obtain ⟨ready,cu,hu,hunitPtr,hrecords,hvalid,hval,huFrame,hzero,hureg,hcu⟩ :=
    stagedAfterRoundUnit_runs (ω := ω) st L P numericEnd hunit hL hP hEnd (by omega) hPword
      (B := 1) le_rfl (by simpa using hwidth) hz (by dsimp [records] at hroom; omega)
  have keep r (h₁ : r ≠ 16) (h₂ : r ≠ 60) (h₃ : r ≠ 67) := hureg r h₁ h₂ h₃
  -- The entire original graph lies below the unit block.
  have hg' : DynGraphAt ready.mem g vCap eCap G :=
    hg.of_agree (fun a _ ha =>
      (huFrame a (ha.trans_le hgEnd)).trans (hframe a ha))
  obtain ⟨out,cg,hr,hT,hF,hR,_,hz',hgFrame,hregs,hcg⟩ :=
    stagedController_branchGraph_runs (ω := ω) ready G T ℓ guestL staging cursor count names vertices
      records g vCap eCap ready.mem staged oracle C j hnl hp hwrite hbatch hedge hops hw hg.1
      hg' (by dsimp [records]; omega) (fun _ _ => rfl) hg.2.1 hg.2.2.1 hrecords
      ((keep 28 (by decide) (by decide) (by decide)).trans hNames)
      ((keep 5 (by decide) (by decide) (by decide)).trans hStaging)
      ((keep 40 (by decide) (by decide) (by decide)).trans hVertices)
      ((keep 12 (by decide) (by decide) (by decide)).trans hCursor)
      ((keep 13 (by decide) (by decide) (by decide)).trans hCount)
      ((keep 41 (by decide) (by decide) (by decide)).trans h41)
      ((keep 42 (by decide) (by decide) (by decide)).trans h42)
      ((keep 43 (by decide) (by decide) (by decide)).trans h43)
      ((keep 44 (by decide) (by decide) (by decide)).trans h44)
      hwords hzero hmodel ((keep 1 (by decide) (by decide) (by decide)).trans hm)
      (retainedStagedTreeAt_congr htree (hsep.trans (Nat.le_add_right _ _ |>.trans hdest))
        hdest huFrame) hindex hnames hverSpan hedges hverts hsep
      (hdest.trans (by dsimp [records]; omega)) hroom hroots
  exact ⟨ready,out,cu,cg,hu,hr,hT,hF,hR,hz',hvalid,hval,huFrame,hgFrame,
    (hregs 16 (by decide) (by decide)).trans hrecords,
    (hregs 60 (by decide) (by decide)).trans hunitPtr,
    fun r h₁ h₂ h₃ h₄ h₅ => (hregs r h₂ h₃).trans (keep r h₁ h₄ h₅),by omega⟩


/-- Run a last-level round with widened numeric scratch and compact
caller-width outputs, then return the cursor after the weight descriptor. -/
def stagedPackedRoundBody
    (select dedup copy packLengths packWeights prepare adjacency numeric pack
      unit restore init scatter publish : ℕ) : Stmt :=
  stagedPublishedRoundWith copy unit restore init scatter publish
    (.seq (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
      (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric))
    (publishableWideOutputs pack)

/-- The staged packed round body uses no `rand` statement. -/
theorem stagedPackedRoundBody_noRand
    (select dedup copy packLengths packWeights prepare adjacency numeric pack
      unit restore init scatter publish : ℕ) :
    (stagedPackedRoundBody select dedup copy packLengths packWeights prepare adjacency numeric pack
      unit restore init scatter publish).NoRand := by
  have haddr : ∀ rs es, (stagedAddressAssignments rs es).NoRand := by
    intro rs
    induction rs with
    | nil => intro es; simp [stagedAddressAssignments, Stmt.NoRand]
    | cons r rs ih =>
      intro es
      cases es with
      | nil => simp [stagedAddressAssignments, Stmt.NoRand]
      | cons e es => simp [stagedAddressAssignments, Stmt.NoRand, ih es]
  simp only [stagedPackedRoundBody, stagedPublishedRoundWith, loadStagedRoundWeights,
    stageNextGuestPrefix, stagedTreeSelectionBody, dedupStagedTreeBody,
    prepareAndRunWideStagedNumericBody, prepareWideStagedNumericBody,
    installWideStagedNumericLayout, installStagedNumericLayoutFrom, stagedWideInputsBody,
    stagedNumericBodyFrom, publishableWideOutputs, installWideStagedOutputLayout,
    installStagedOutputLayoutFrom, preparePackedStagedOutputs, packStagedWideOutputs,
    installPackedStagedOutputLayout, stagedBranchAppendBody, stagedAfterRoundUnitBody,
    stagedStretchUnitBody, stagedBranchGraphBody, stagedBranchOutputBody,
    installStagedBranchPayloadLayout, stagedStretchPublishBody, stagedBranchStretchBody,
    stagedRoundWeightCursor, Stmt.NoRand, haddr, and_self]

/-- Link the verified phases and write the compact weight base at the
returned cursor boundary. -/
theorem stagedPackedRoundBody_runs
    {w select dedup copy packLengths packWeights prepare adjacency numeric pack
      unit restore init scatter publish stop weight cs ct cn cp cb : ℕ}
    {p : Program} {ω : ℕ → Bool} {st staged selected computed packed published : State}
    (hs : Runs w p ω (.seq loadStagedRoundWeights (stageNextGuestPrefix copy))
      st .normal staged cs)
    (ht : Runs w p ω (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
      staged .normal selected ct)
    (hn : Runs w p ω
      (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric)
      selected .normal computed cn)
    (hp : Runs w p ω (publishableWideOutputs pack) computed .normal packed cp)
    (hb : Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      packed .normal published cb)
    (hstop : published.regs 54 = stop) (hweight : published.regs 38 = weight)
    (hroom : stop+1 < 2^w) (hz : ZeroFrom published.mem stop) :
    ∃ out, Runs w p ω
      (stagedPackedRoundBody select dedup copy packLengths packWeights prepare adjacency numeric pack
        unit restore init scatter publish)
      st (.returned (stop+1)) out (cs+ct+cn+cp+cb+13) ∧
      out.mem = Function.update published.mem stop weight := by
  obtain ⟨out,hr,hmem,_,_,_⟩ :=
    stagedRoundWeightCursor_runs (p := p) (ω := ω) published stop weight hstop hweight hroom hz
  have hnumeric := runs_seq_iff.mpr (Or.inr ⟨selected,ct,cn,ht,hn,rfl⟩)
  have happend := runs_seq_iff.mpr (Or.inr ⟨published,cb,8,hb,hr,rfl⟩)
  have hlayout := runs_seq_iff.mpr (Or.inr ⟨packed,cp,cb+9,hp,happend,rfl⟩)
  have hround := runs_seq_iff.mpr (Or.inr ⟨computed,ct+cn+1,cp+(cb+9)+1,hnumeric,hlayout,rfl⟩)
  exact ⟨out,runs_seq_iff.mpr (Or.inr ⟨staged,cs,_,hs,hround,by omega⟩),hmem⟩

/-- Link the installed published round at a reachable controller state.
Its premise is the numeric run and branch append on the
staged input. -/
theorem stagedPackedControllerRound_link
    {w entry select dedup copy packLengths packWeights prepare adjacency numeric pack unit restore init scatter publish
      vCap eCap h L P caller base count handle bound guestL sim src j budget stride : ℕ}
    {p : Program} {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} (st : State) (Next : State → Prop)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hbase : src+queryWeights H guestL = base) (hw : 1 < 2^w)
    (hheap : queryHeap H guestL < 2^w) (hfit : bound+queryWeights H guestL < 2^w)
    (he : p.procs[entry]? = some
      (stagedPackedRoundBody select dedup copy packLengths packWeights prepare adjacency numeric pack
        unit restore init scatter publish))
    (hcopy : MeetsContract w p copy (copyWordsContract w)) :
    let C := stagedControllerRoundContract st Next j budget
    (∀ args mem pos ω, (∀ x ∈ args, x < 2^w) → C.pre args mem →
      ∀ staged, staged.regs 5 = st.regs 0 →
        staged.regs 8 = st.mem (st.regs 0-1) → staged.regs 31 = st.mem (st.regs 0-1) → staged.regs 70 = 0 →
        (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
          staged.regs r = (startState args mem pos).regs r) →
        (∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = mem (src+i)) →
        (∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = mem a) →
      ∃ mid ready out cn cl cb stop weights,
        Runs w p ω
          (.seq (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
            (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric))
          staged .normal mid cn ∧
        Runs w p ω (publishableWideOutputs pack) mid .normal ready cl ∧
        Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
          ready .normal out cb ∧
        out.regs 54 = stop ∧ out.regs 38 = weights ∧ stop+1 < 2^w ∧
        ZeroFrom out.mem stop ∧
        C.post args mem (stop+1) (Function.update out.mem stop weights) ∧
        cn+cl+cb+21+17*queryWeights H guestL+14+
          argsSize [.reg 69,.reg 5,
            (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
          ≤ C.cost args mem) →
    MeetsContract w p entry C := by
  intro C hrun
  obtain ⟨hstage,hload⟩ :=
    stagedControllerRoundContract_setup (budget := budget) st Next hs hn hm hguest hsim hsrc
      hbase hw hheap hfit
  apply stagedPublishedRoundWith_meetsContract he C H guestL sim src hcopy hstage hload
  intro args input pos ω hwords hpre staged inputWeights cursor hcursor hweight h5 h8 h31 h70 hkeep hcopied hframe
  have hpre' := hpre
  change args = _ ∧ input = st.mem at hpre'
  obtain ⟨rfl,rfl⟩ := hpre'
  have hc := (publishedRoundArgs_startState st st.mem pos).2.2
  have heq : cursor = st.regs 0 := hcursor.symm.trans hc
  rw [heq] at h5 hweight hcopied hframe
  rw [← hweight] at h8 h31
  exact hrun _ _ pos ω hwords hpre staged h5 h8 h31 h70 hkeep hcopied hframe

end MinCostFlow.LastLevelProgram
