module

public import MinCostFlow.LastLevelProgram.PackedInitializer
import MinCostFlow.LastLevelProgram.StagedPackedNumeric
import Mathlib.Data.Nat.Size

/-!
# Running the packed representative initializer

Definition 5.8 (pages 19–20) prepares the representative graph once,
then rebuilds the collection using the live round contracts.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num DynSpanner.Program

/-- The scalar scans around guest format packing depend only on graph
dimensions and the fixed integer scale constant. -/
@[expose] def packedFormatScalarCost (d n m : ℕ) : ℕ :=
  argsSize collectionGuestFormatArgs+40*(Nat.log 2 (n+2)+1)+
    40*((1024*d).size+3*(m+1).size)+
    40*(Nat.log 2 (4*m+2)+Nat.log 2 (16*m+6)+2)+169

set_option maxRecDepth 2048 in
/-- Charge the packed format scan and length conversion at the reserved
guest width, with a separate charge for scalar setup. -/
theorem packedRuntime_formatCost_le
    (C : ℝ) (G : MGraph) (ℓ : ℕ → ℝ) (L N cf : ℕ) (hG : G.IsValid)
    (hN : N ≤ representativeGuestWidthBound ⌈max 1 C⌉₊ L G.m) :
    let H := representativeGraph G ℓ
    cf ≤ argsSize collectionGuestFormatArgs+
      (((98*L+92)+(80*N+37))*H.m+40*(2*H.m).size+145)+
      40*(Nat.log 2 (H.n+2)+1)+40*weightPrecision C H+
      40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+169 →
    cf ≤ representativeGuestSetupMultiplier ⌈max 1 C⌉₊ L G.m*(G.m+1)+
      packedFormatScalarCost ⌈max 1 C⌉₊ G.n G.m := by
  intro H hf
  let d := ⌈max 1 C⌉₊
  let B := representativeGuestWidthBound d L G.m
  change N ≤ B at hN
  have hsub := representativeGraph_subgraph hG ℓ
  have hm : H.m ≤ G.m := Finset.card_le_card hsub.2.1
  have hn : H.n ≤ G.n := Finset.card_le_card hsub.1
  have hgrid : weightPrecision C H ≤ (1024*d).size+3*(G.m+1).size :=
    (representativeGraph_weightPrecision_le C G ℓ).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3
        (Nat.size_le_size (Nat.succ_le_succ hm))) _)
  have hmain := Nat.mul_le_mul
    (show (98*L+92)+(80*N+37) ≤ 98*L+80*B+129 by omega) hm
  have hsize := Nat.size_le_size (Nat.mul_le_mul_left 2 hm)
  have hmain' : ((98*L+92)+(80*N+37))*H.m+40*(2*H.m).size+145 ≤
      representativeGuestSetupMultiplier d L G.m*(G.m+1) := by
    unfold representativeGuestSetupMultiplier
    change _ ≤ (98*L+80*B+40*(2*G.m).size+274)*(G.m+1)
    rw [Nat.mul_succ]
    have hcost := Nat.mul_le_mul_right G.m
      (show 98*L+80*B+129 ≤ 98*L+80*B+40*(2*G.m).size+274 by omega)
    omega
  have hlogN := Nat.log_mono_right (b := 2) (Nat.add_le_add_right hn 2)
  have hlogM := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hm) 2)
  have hlogM' := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (Nat.mul_le_mul_left 16 hm) 6)
  change cf ≤ representativeGuestSetupMultiplier d L G.m*(G.m+1)+packedFormatScalarCost d G.n G.m
  unfold packedFormatScalarCost
  omega

/-- The non-loop bound includes the scalar format scans as well as the
controller, endpoint preparation, and packed guest calls. -/
noncomputable def packedNonLoopInitMultiplier (guest : Program) (c d : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativePackedRuntimeMultiplier guest c d K L n m+(packedFormatScalarCost d n m+argsSize packedControllerInputArgs+4)

/-- Include the dispatcher scan in the non-loop initialization charge. -/
@[expose] noncomputable def packedNonLoopDispatchMultiplier (guest : Program) (c d : ℕ)
    (K : ℝ) (L n m : ℕ) : ℕ :=
  representativePackedDispatchMultiplier guest c d K L n m+(packedFormatScalarCost d n m+argsSize packedControllerInputArgs+4)

/-- The dispatcher scan and scalar setup fit the non-loop contract cost. -/
theorem packedNonLoopDispatchCost_le (guest : Program) (c : ℕ) (K C : ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (G : MGraph) (L cost : ℕ) (hne : (SparseCore.nonLoopEdges G).Nonempty) :
    let d := ⌈max 1 C⌉₊
    let budget := (fixedPointLastLevelTool oracle C).cost G+1
    cost ≤ packedNonLoopInitMultiplier guest c d K L G.n G.m*budget →
    cost+29*G.m+80 ≤ packedNonLoopDispatchMultiplier guest c d K L G.n G.m*budget := by
  intro d budget hcost
  have hbase := representativePackedDispatchCost_le guest c K C oracle G L
    (representativePackedRuntimeMultiplier guest c d K L G.n G.m*budget) hne le_rfl
  let A := packedFormatScalarCost d G.n G.m+argsSize packedControllerInputArgs+4
  let R := representativePackedRuntimeMultiplier guest c d K L G.n G.m
  let S := representativePackedDispatchMultiplier guest c d K L G.n G.m
  change R*budget+29*G.m+80 ≤ S*budget at hbase
  change cost ≤ (R+A)*budget at hcost
  change cost+29*G.m+80 ≤ (S+A)*budget
  rw [Nat.add_mul] at hcost ⊢
  omega

/-- The prepared table addresses lie below the collection base, so the
controller frame preserves them across every live round. -/
theorem packedInitializer_tableBounds (G : MGraph) (ℓ : ℕ → ℝ)
    (vCap eCap handle g : ℕ) (hG : G.IsValid)
    (hgraph : g+dynGraphSize vCap eCap ≤ handle) (guestWidth : ℕ) :
    let H := representativeGraph G ℓ
    let src := handle+11*G.m+vCap+1
    let base := src+queryWeights H guestWidth
    g+dynGraphSize vCap eCap ≤ base ∧
      handle+7*G.m+H.n ≤ base ∧ handle+4*G.m+G.m ≤ base ∧
      handle+G.m ≤ base ∧ handle+2*G.m+H.m ≤ base := by
  intro H src base
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hn : H.n ≤ 2*H.m := representativeGraph_n_le_twice_m G ℓ
  have hbase : src ≤ base := Nat.le_add_right _ _
  dsimp only [src] at hbase
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

/-- Recover the graph and branch publication tables from the prepared
prefix at a live round cursor. -/
theorem packedInitializer_liveAppendTables
    {g vCap eCap L P caller count handle bound j N : ℕ}
    (G : MGraph) (ℓ : ℕ → ℝ) (input : ℕ → ℕ)
    (ready current staged : State) (branches : ℕ → LSF) (ρ : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ)
    (hgraph : DynGraphAt input g vCap eCap G)
    (hgraphEnd : g+dynGraphSize vCap eCap ≤ handle)
    (hframe : ∀ a < handle, ready.mem a = input a) :
    let H := representativeGraph G ℓ
    let base := handle+11*G.m+vCap+1+queryWeights H N
    let vertices := handle+7*G.m
    let indices := handle+4*G.m
    let names := handle
    let repNames := handle+2*G.m
    stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound
      L G.E branches ρ query ready.mem j current →
    (∀ i < H.n, ready.mem (vertices+i) = vertexName H i) →
    (∀ i < G.m, ready.mem (indices+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, ready.mem (names+i) = edgeName G i) →
    (∀ i < H.m, ready.mem (repNames+i) = edgeName H i) →
    (∀ a < current.regs 0, staged.mem a = current.mem a) →
    (∀ i < H.m, staged.mem (current.regs 0+i) = (indexedGraph H).tail i) →
    (∀ i < H.m, staged.mem (current.regs 0+(H.m+i)) = (indexedGraph H).head i) →
    DynGraphAt current.mem g vCap eCap G ∧
    g+dynGraphSize vCap eCap ≤ current.regs 0 ∧
    vertices+H.n ≤ current.regs 0 ∧ indices+G.m ≤ current.regs 0 ∧
    names+G.m ≤ current.regs 0 ∧
    (∀ i < H.n, current.mem (vertices+i) = vertexName H i) ∧
    (∀ i < G.m, current.mem (indices+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
    (∀ i < G.m, current.mem (names+i) = edgeName G i) ∧
    repNames+H.m ≤ current.regs 0+queryWeights H N ∧
    vertices+H.n ≤ current.regs 0+queryWeights H N ∧
    (∀ i < H.m, staged.mem (repNames+i) = edgeName H i ∧
      staged.mem (current.regs 0+i) = (indexedGraph H).tail i ∧
      staged.mem (current.regs 0+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.n, staged.mem (vertices+i) = vertexName H i) := by
  intro H base vertices indices names repNames hs hv hi hn hr hst ht hh
  obtain ⟨hgEnd,hvEnd,hiEnd,hnEnd,hrEnd⟩ :=
    packedInitializer_tableBounds G ℓ vCap eCap handle g hgraph.1 hgraphEnd N
  have hg := representativeGraph_frame hgraph (fun a _ ha => hframe a (ha.trans_le hgraphEnd))
  have hbase : base ≤ current.regs 0 :=
    (Nat.le_add_right base 1).trans ((Nat.le_add_right _ count).trans hs.2.2.2.1)
  obtain ⟨hg',hv',hi',hn',hrEnd',hvEnd',hedges,hverts⟩ :=
    packedController_appendTables (guestL := N) ℓ hs hg hgEnd hvEnd hiEnd hnEnd
      hv hi hn hrEnd hr hst ht hh
  exact ⟨hg',hgEnd.trans hbase,hvEnd.trans hbase,hiEnd.trans hbase,hnEnd.trans hbase,
    hv',hi',hn',hrEnd',hvEnd',hedges,hverts⟩

/-- Publish the branch for a live controller state after arithmetic and
compaction, using the caller tables preserved below the collection. -/
theorem packedInitializer_liveAppend_runs
    {w g vCap eCap L caller handle bound N j budget sim levels : ℕ} {guest : Program} {ω : ℕ → Bool}
    (G T : MGraph) (ℓ : ℕ → ℝ) (input : ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (c : ℕ)
    (ready current staged selected packed : State) (pos start cursor count : ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (hg : DynGraphAt input g vCap eCap G) (hgEnd : g+dynGraphSize vCap eCap ≤ handle)
    (hframe : ∀ a < handle, ready.mem a = input a)
    (hw : 16 ≤ 2^w) (hbits : 14 ≤ w) (hL : 0 < L) :
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let ρ := roundedScale C H
    let query := stretchQuery oracle H ℓ P
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let base := handle+11*G.m+vCap+1+queryWeights H N
    let stage := current.regs 0
    let finish := start+H.m*L+H.m*L
    let ptr := finish+2*L+3*count
    let stop := ptr+4+dynGraphSize vCap eCap+vCap+2+eCap+eCap*L+eCap*L
    let D := ⌈max 1 C⌉₊
    let step := stagedPackedRoundSpace H guest D N sim levels L P H.n vCap eCap
    stagedRoundStateAtStride H vCap eCap 4 L P caller base s.1 handle bound L
      G.E s.2 ρ query ready.mem j current →
    j < s.1 → P < 2^w → 2*(2 : ℝ)^P < capacity 4 L →
    (∀ i < H.n, ready.mem (handle+7*G.m+i) = vertexName H i) →
    (∀ i < G.m, ready.mem (handle+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, ready.mem (handle+i) = edgeName G i) →
    (∀ i < H.m, ready.mem (handle+2*G.m+i) = edgeName H i) →
    (∀ a < stage, staged.mem a = current.mem a) →
    (∀ i < H.m, staged.mem (stage+i) = (indexedGraph H).tail i) →
    (∀ i < H.m, staged.mem (stage+(H.m+i)) = (indexedGraph H).head i) →
    (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (current.regs ∘ roundControllerRegister))
        current.mem pos).regs r) →
    (∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r) →
    (∀ r, r ≠ 15 → r ≠ 16 →
      r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34,36,37,38,39] : List ℕ) →
      packed.regs r = selected.regs r) →
    selected.regs 1 = H.m → selected.regs 5 = stage → selected.regs 12 = cursor →
    selected.regs 13 = count → selected.regs 19 = L → selected.regs 23 = P →
    selected.regs 28 = handle+2*G.m →
    current.regs 150 = handle+7*G.m → current.regs 113 = vCap → current.regs 114 = eCap →
    current.regs 115 = G.n → current.regs 116 = dgVListBase g vCap →
    current.regs 127 = L → current.regs 2 = j →
    current.regs 131 = handle+4*G.m → current.regs 133 = G.m → current.regs 134 = handle →
    packed.regs 36 = start → packed.regs 37 = L → packed.regs 38 = start+H.m*L →
    packed.regs 16 = finish → ZeroFrom packed.mem finish →
    oracle H (LSF.safeLen H ℓ) (weights P ρ query j) = restoreTreeNames H T →
    retainedStagedTreeAt H T (stage+queryWeights H N) (cursor+1+H.m)
      count staged.mem packed.mem →
    (∀ i ∈ T.E, i < H.m) →
    stage+queryWeights H N ≤ cursor+1+H.m → cursor+1+H.m+H.n ≤ finish →
    (∀ i < H.m, Valid packed.mem (start+i*L) 4 L ∧
      fixVal packed.mem (start+i*L) 4 L P = query (weights P ρ query j) (edgeName H i)) →
    cursor = stage+queryOriginals H N+2^paddedGuestWidth guest D H.n H.m sim (queryHeap H N) →
    (let K := L+(P+levels+7)/4
     let dest := cursor+1+H.m
     let adj := dest+H.n+stagedTraversalReserve H.n levels
     let tails := adj+H.n+6*H.n
     let heap := tails+2*H.m+H.m*K+H.m*K+2*K+H.n*K
     start = heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K) →
    count ≤ H.n → bound < 2^w → stage+(s.1-j)*step ≤ bound →
    (∀ i < H.m, Valid packed.mem (start+H.m*L+i*L) 4 L ∧
      fixVal packed.mem (start+H.m*L+i*L) 4 L P =
        weights P ρ query (j+1) (edgeName H i)) →
    let Next := fun next =>
      stagedRoundStateAtStride H vCap eCap 4 L P caller base s.1 handle bound L
        G.E s.2 ρ query ready.mem (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound
    let args := (List.range 70).map (current.regs ∘ roundControllerRegister)
    ∃ out cost, Runs w (packedLastLevelProgram guest ⌈max 1 C⌉₊ c) ω
        (stagedBranchAppendBody 164 172 14 174 179) packed .normal out cost ∧
      out.regs 54 = stop ∧ out.regs 38 = start+H.m*L ∧ ZeroFrom out.mem stop ∧
      stop+1 < 2^w ∧
      (stagedControllerRoundContract current Next j budget).post args current.mem (stop+1)
        (Function.update out.mem stop (start+H.m*L)) ∧
      cost ≤ stagedAppendModelCost G L count := by
  intro H P ρ query s base stage finish ptr stop D step hs hj hP hunit
    hv hi hn hr hstage ht hh hstaged hselected hpacked h1 h5 h12 h13 h19 h23 h28 h40 h41 h42 h43 h44 h55 h57
    h59 h61 h62 h36 h37 h38 h16 hz hmodel htree hindex hsep hdest hvalues hcursor hstartEq hcount hword hreserve hweights Next args
  obtain ⟨hgraph,hgraphEnd,hvEnd,hiEnd,hnEnd,hvertices,hindices,hnames,hrEnd,hvStage,hedges,hverts⟩ :=
    packedInitializer_liveAppendTables (N := N) G ℓ input ready current staged s.2 ρ query
      hg hgEnd hframe hs hv hi hn hr hstage ht hh
  let scale := integerScale ⌈max 1 C⌉₊ H
  have hscale : (scale : ℝ) = ρ := rfl
  have hcast : ((scale : ℤ) : ℝ) = ρ := (Int.cast_natCast scale).trans hscale
  obtain ⟨_,_,hbound,hstop,hnext⟩ :=
    packedNumeric_appendStop H guest D N sim levels L P count vCap eCap
      stage cursor j s.1 bound w hcursor hj hcount hword hreserve
  rw [← hstartEq] at hbound hstop hnext
  have hstart : stage ≤ start+H.m*L := by
    have hc : stage ≤ cursor :=
      (Nat.le_add_right stage _).trans ((Nat.le_add_right _ _).trans_eq hcursor.symm)
    omega
  obtain ⟨hp40,hp41,hp42,hp43,hp44,hp55,hp56,hp57,hp59,hp61,hp62⟩ :=
    packedController_appendRegisters current staged selected packed pos hstaged hselected hpacked
  have happend := packedLastLevelProgram_append_runs (caller := caller) (guest := guest) (d := ⌈max 1 C⌉₊) (c := c)
    (ω := ω) packed oracle C G ℓ count base j s.1 (handle+7*G.m) (handle+4*G.m)
    start handle g N stage cursor (handle+2*G.m) scale current.mem staged.mem
    hne hg.1 hconn hw
    ((hpacked 13 (by decide) (by decide) (by decide)).trans h13)
    (hp41.trans h41) (hp42.trans h42) (hp59.trans h59) (hp55.trans h55)
    (hp56.trans hs.2.1) (hp57.trans h57) (hp40.trans h40) (hp61.trans h61) (hp62.trans h62)
    ((hpacked 19 (by decide) (by decide) (by decide)).trans h19) hL hbits
    hgraph hgraphEnd hstage ((hpacked 28 (by decide) (by decide) (by decide)).trans h28)
    ((hpacked 5 (by decide) (by decide) (by decide)).trans h5)
    ((hpacked 12 (by decide) (by decide) (by decide)).trans h12)
    (hp43.trans h43) (hp44.trans h44) T
    ((hpacked 1 (by decide) (by decide) (by decide)).trans h1) hstop h36 h37 h38 hs.2.2.2.1 hj
    h16 hz hiEnd hnEnd hvEnd hvertices hindices hnames ((hpacked 23 (by decide) (by decide) (by decide)).trans h23) hP hunit hscale hmodel htree
    hindex hrEnd hvStage hedges hverts hsep hdest (by simpa only [hcast] using hvalues)
  have hm : 0 < H.m := by
    obtain ⟨e,he⟩ := hne
    exact Finset.card_pos.mpr ⟨_,(representativeGraph_shortest (ℓ := ℓ) he).1⟩
  have hstopGe : start+H.m*L+H.m*L ≤ stop := by dsimp only [stop,ptr,finish]; omega
  obtain ⟨out,cost,hr,h54,h38,hroom,hzero,hpost,hcost⟩ :=
    stagedPackedAppendModel_roundPost (budget := budget) (stagingEnd := stage+queryWeights H N)
      current staged packed args hs hm hj hstart hstopGe hbound hnext hword hstage htree
      (Nat.le_add_right _ _) hweights happend
  rw [h38] at hpost
  exact ⟨out,cost,hr,h54,h38,hzero,hroom,hpost,hcost⟩

/-- Execute numeric compaction and publish the live branch. The compact
weights and branch become the next controller invariant. -/
theorem packedInitializer_numericAppend_runs
    {w g vCap eCap L handle bound N j budget sim levels multiplier stretchPrecision src : ℕ} {guest : Program} {ω : ℕ → Bool}
    (G T : MGraph) (fmt : Format w) (allocation : ℕ → List ℕ → ℕ) (input : ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C γ : ℝ) (c : ℕ)
    (ready current staged selected : State) (pos : ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (hg : DynGraphAt input g vCap eCap G) (hgEnd : g+dynGraphSize vCap eCap ≤ handle)
    (hframe : ∀ a < handle, ready.mem a = input a)
    (hw : 16 ≤ 2^w) (hbits : 14 ≤ w)
    (hOracle : LSF.HasLSSTSpec oracle C) :
    let ℓ := MinRatio.readEdgeValues input src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let ρ := roundedScale C H
    let query := stretchQuery oracle H ℓ P
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let base := handle+11*G.m+vCap+1+queryWeights H N
    let stage := current.regs 0
    let D := ⌈max 1 C⌉₊
    let width := paddedGuestWidth guest D H.n H.m sim (queryHeap H N)
    let cursor := stage+queryOriginals H N+2^width
    let count := selected.regs 13
    let dest := cursor+1+H.m
    let K := L+(P+levels+7)/4
    let adj := dest+H.n+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let heap := tails+2*H.m+H.m*K+H.m*K+2*K+H.n*K
    let start := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
    let finish := start+H.m*L+H.m*L
    let ptr := finish+2*L+3*count
    let stop := ptr+4+dynGraphSize vCap eCap+vCap+2+eCap+eCap*L+eCap*L
    let step := stagedPackedRoundSpace H guest D N sim levels L P H.n vCap eCap
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,handle] input →
    stagedRoundStateAtStride H vCap eCap 4 L P fmt.precision base s.1 handle bound L
      G.E s.2 ρ query ready.mem j current →
    j < s.1 → P < 2^w → H.n ≤ 2^(levels+1) →
    (∀ i < H.n, ready.mem (handle+7*G.m+i) = vertexName H i) →
    (∀ i < G.m, ready.mem (handle+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, ready.mem (handle+i) = edgeName G i) →
    (∀ i < H.m, ready.mem (handle+2*G.m+i) = edgeName H i) →
    (∀ a < stage, staged.mem a = current.mem a) →
    (∀ i < H.m, staged.mem (stage+i) = (indexedGraph H).tail i) →
    (∀ i < H.m, staged.mem (stage+(H.m+i)) = (indexedGraph H).head i) →
    (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (current.regs ∘ roundControllerRegister))
        current.mem pos).regs r) →
    (∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r) →
    selected.regs 0 = H.n → selected.regs 1 = H.m → selected.regs 5 = stage →
    selected.regs 12 = cursor → selected.regs 14 = levels → selected.regs 19 = L →
    selected.regs 23 = P → selected.regs 27 = src → selected.regs 28 = handle+2*G.m →
    selected.regs 31 = current.mem (stage-1) → selected.regs 32 = L →
    selected.regs 35 = integerScale D H →
    (∀ r, selected.regs r < 2^w) →
    current.regs 150 = handle+7*G.m → current.regs 113 = vCap → current.regs 114 = eCap →
    current.regs 115 = G.n → current.regs 116 = dgVListBase g vCap →
    current.regs 127 = L → current.regs 2 = j →
    current.regs 131 = handle+4*G.m → current.regs 133 = G.m → current.regs 134 = handle →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (weights P ρ query j ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) (weights P ρ query j) = restoreTreeNames H T →
    selectedTreeAt H T (stage+queryWeights H N) dest count staged.mem selected.mem →
    count ≤ H.n → bound < 2^w → stage+(s.1-j)*step ≤ bound →
    (∀ i < H.m, current.mem (stage-1)+i*L+L ≤ stage+queryWeights H N ∧
      Valid staged.mem (current.mem (stage-1)+i*L) 4 L) →
    (∀ i < H.m, fixVal staged.mem (current.mem (stage-1)+i*L) 4 L P =
      weights P ρ query j (edgeName H i)) →
    let Next := fun next =>
      stagedRoundStateAtStride H vCap eCap 4 L P fmt.precision base s.1 handle bound L
        G.E s.2 ρ query ready.mem (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound
    let args := (List.range 70).map (current.regs ∘ roundControllerRegister)
    let p := packedLastLevelProgram guest D c
    ∃ computed packed out cn cp cb,
      Runs w p ω (prepareAndRunWideStagedNumericBody 74 162 163 164 165 58)
        selected .normal computed cn ∧
      Runs w p ω (publishableWideOutputs 168) computed .normal packed cp ∧
      Runs w (packedLastLevelProgram guest ⌈max 1 C⌉₊ c) ω
        (stagedBranchAppendBody 164 172 14 174 179) packed .normal out cb ∧
      out.regs 54 = stop ∧ out.regs 38 = start+H.m*L ∧ ZeroFrom out.mem stop ∧
      stop+1 < 2^w ∧
      (stagedControllerRoundContract current Next j budget).post args current.mem (stop+1)
        (Function.update out.mem stop (start+H.m*L)) ∧
      cn ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor K levels*(H.m+1)+13+
        (stagedScratchWidthExpr.size+
          argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
            [.reg 64])+37+34*H.m+(2*((30*K+90)*H.m+20)+56*K+72))+1 ∧
      cp ≤ 2*((35*L+60)*H.m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 ∧
      cb ≤ stagedAppendModelCost G L count := by
  intro ℓ H P ρ query s base stage D width cursor count dest K adj tails heap start finish ptr stop step
    hgrid hpre hs hj hP hlevels hv hi hn hr hstage ht hh hstaged hselected h0 h1 h5 h12 h14 h19
    h23 h27 h28 h31 h32 h35 hwords h40 h41 h42 h43 h44 h55 h57 h59 h61 h62 htree hmodel
    hsel hcount hbound hreserve hweights hvalue Next args p
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest D c
  have hround := (packedRepresentativeInitializerModule_entries hgeneral).2.2.2.2.2.2.2
  obtain ⟨_,harith,hbuffer,_,_⟩ := packedRoundModule_entries (packedSelectedRoundModule_entries hround).1
  have hcountEq : s.1 = H.m := by simp only [s,fixedPointLastLevelTool,ite_eq_left hne,H]
  have hj' : j < H.m := hcountEq ▸ hj
  have hhandle : handle ≤ stage := by
    have hbase := hs.2.2.2.1
    dsimp only [base,stage] at *
    omega
  have hcaller (a : ℕ) (ha : a < handle) : staged.mem a = input a := by
    have hbase : handle ≤ base := by dsimp only [base]; omega
    exact (hstage a (ha.trans_le hhandle)).trans
      ((hs.2.2.2.2.2.2.1 a (ha.trans_le hbase)).trans (hframe a ha))
  have hnEnd : handle+2*G.m+H.m ≤ stage+queryWeights H N := by
    have hcard : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hg.1 ℓ).2.1
    have hge := hs.2.2.2.1
    dsimp only [base,stage] at *
    omega
  have hnames (i : ℕ) (hi' : i < H.m) : staged.mem (handle+2*G.m+i) = edgeName H i := by
    have hcard : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hg.1 ℓ).2.1
    have hb : handle+2*G.m+i < base := by dsimp only [base]; omega
    have hc : base ≤ stage := by have := hs.2.2.2.1; omega
    exact (hstage _ (hb.trans_le hc)).trans ((hs.2.2.2.2.2.2.1 _ hb).trans (hr i hi'))
  obtain ⟨computed,packed,cn,cp,hnr,hpr,h16,h36,h37,h38,_,hpacked,hzero,_,hsep,
    hdest,_,hretained,hstretch,hnextWeight,hcn,hcp⟩ :=
    packedController_selectedNumeric_runs (ω := ω) fmt allocation oracle C γ G T input staged selected
      stage N width levels (handle+2*G.m) (current.mem (stage-1)) bound sim j hOracle hne hconn
      hbits (by omega) harith hbuffer hgrid hpre hj' hbound hlevels rfl
      (by rw [← hcountEq]; exact hreserve) htree hmodel hsel h12 h0 h1 h5 h14 h19 h23 h27 h28
      h31 h32 h35 hwords ht hh hnEnd hnames hhandle hcaller hweights hvalue
  obtain ⟨hL,_,hunit,_,_,_,_⟩ :=
    packedNumeric_capacity_of_finer_runtimePre fmt allocation oracle C G input levels hne hgrid hpre
  have hindex := (packedNumeric_treeBounds G T ℓ (weights P ρ query j) γ hg.1 hne hconn htree).2.2.2.2.2.2
  obtain ⟨out,cb,hb,h54,h38',hz,hroom,hpost,hcb⟩ :=
    packedInitializer_liveAppend_runs (ω := ω) (guest := guest) (N := N) (sim := sim)
      (levels := levels) (budget := budget) G T ℓ input oracle C c ready current staged selected packed
      pos start cursor count hne hconn hg hgEnd hframe hw hbits hL hs hj hP hunit hv hi hn hr
      hstage ht hh hstaged hselected hpacked h1 h5 h12 rfl h19 h23 h28 h40 h41 h42 h43 h44 h55 h57
      h59 h61 h62 h36 h37 h38 h16 hzero hmodel hretained hindex hsep (h16 ▸ hdest)
      hstretch rfl rfl hcount hbound hreserve hnextWeight
  exact ⟨computed,packed,out,cn,cp,cb,hnr,hpr,hb,h54,h38',hz,hroom,hpost,hcn,hcp,hcb⟩

/-- The live round selects its tree, updates the weights, and publishes
the branch within the controller's per-round budget. -/
theorem packedInitializer_liveRound_runs
    {w g vCap eCap L handle bound j multiplier stretchPrecision src : ℕ} {guest : Program} {ω : ℕ → Bool}
    (G T : MGraph) (fmt : Format w) (input : ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C K γ : ℝ) (c guestCost : ℕ)
    (ready current staged : State) (pos : ℕ)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (hGn : G.n ≤ G.m+1)
    (hg : DynGraphAt input g vCap eCap G) (hgEnd : g+dynGraphSize vCap eCap ≤ handle)
    (hframe : ∀ a < handle, ready.mem a = input a)
    (hw : 16 ≤ 2^w) (hbits : 14 ≤ w)
    (hOracle : LSF.HasLSSTSpec oracle C) :
    let ℓ := MinRatio.readEdgeValues input src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let ρ := roundedScale C H
    let query := stretchQuery oracle H ℓ P
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let stage := current.regs 0
    let D := ⌈max 1 C⌉₊
    let len := LSF.safeLen H ℓ
    let N := roundQueryLimbs C H len
    let Q := roundQueryPrecision C H len
    let sim := WideWord.lsstLSimMin c H.n H.m N 1
    let levels := Nat.clog 2 H.n
    let guestBase := handle+11*G.m+vCap+1
    let base := guestBase+queryWeights H N
    let budget := representativePackedRoundMultiplier guest c D K L G.n G.m*(G.m+1)
    let allocation := packedRuntimeAllocation G guest C c L vCap eCap
    let width := paddedGuestWidth guest D H.n H.m sim (queryHeap H N)
    let step := stagedPackedRoundSpace H guest D N sim levels L P H.n vCap eCap
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,handle] input →
    stagedRoundStateAtStride H vCap eCap 4 L P fmt.precision base s.1 handle bound L
      G.E s.2 ρ query ready.mem j current →
    j < s.1 → handle+(MinRatio.lastLevelRuntimeMachineContract fmt L
      (fixedPointLastLevelTool oracle C) G vCap eCap multiplier stretchPrecision allocation).initSpace
        [g,src,L,fmt.precision,handle] input < 2^w →
    (∀ i < H.n, ready.mem (handle+7*G.m+i) = vertexName H i) →
    (∀ i < G.m, ready.mem (handle+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, ready.mem (handle+i) = edgeName G i) →
    (∀ i < H.m, ready.mem (handle+2*G.m+i) = edgeName H i) →
    (∀ a, a < stage ∨ stage+queryWeights H N ≤ a → staged.mem a = current.mem a) →
    (∀ i < queryWeights H N, staged.mem (stage+i) = current.mem (guestBase+i)) →
    (∀ i < H.m, ready.mem (guestBase+i) = (indexedGraph H).tail i ∧
      ready.mem (guestBase+(H.m+i)) = (indexedGraph H).head i) →
    (∀ i < H.m, ListAt ready.mem (guestBase+queryLengths H+i*N)
      (encodeLimbs 1 N (queryNumerator Q (len (edgeName H i))))) →
    (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (current.regs ∘ roundControllerRegister))
        current.mem pos).regs r) →
    staged.regs 5 = stage → staged.regs 8 = current.mem (stage-1) →
    staged.regs 31 = current.mem (stage-1) →
    (∀ r, staged.regs r < 2^w) → (∀ r, current.regs r < 2^w) →
    current.regs 72 = H.n → current.regs 73 = H.m →
    current.regs 74 = N → current.regs 75 = sim →
    current.regs 81 = L → current.regs 82 = P → current.regs 83 = Q →
    current.regs 86 = levels → current.regs 91 = L → current.regs 95 = P →
    current.regs 99 = src → current.regs 100 = handle+2*G.m →
    current.regs 104 = L → current.regs 107 = integerScale D H →
    current.regs 150 = handle+7*G.m → current.regs 113 = vCap → current.regs 114 = eCap →
    current.regs 115 = G.n → current.regs 116 = dgVListBase g vCap →
    current.regs 127 = L → current.regs 2 = j →
    current.regs 131 = handle+4*G.m → current.regs 133 = G.m → current.regs 134 = handle →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (weights P ρ query j ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) (weights P ρ query j) = restoreTreeNames H T →
    bound < 2^w → stage+(s.1-j)*step ≤ bound →
    (guestCost : ℝ) ≤ 16000*((H.m+H.n+1 : ℕ) : ℝ)*
      WideWord.lsstOverheadFactor guest c K H.n H.m N →
    (stage+queryOriginals H N+1+2^width ≤ 2^w →
      MeetsContract w (packedLastLevelProgram guest D c) 187
        (convertedTreeSelectorContract w guest D H T N sim stage guestCost
          (current.mem (stage-1)) L L P Q (queryNumerator Q ∘ len)
          (queryNumerator Q ∘ weights P ρ query j))) →
    let Next := fun next =>
      stagedRoundStateAtStride H vCap eCap 4 L P fmt.precision base s.1 handle bound L
        G.E s.2 ρ query ready.mem (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound
    let args := (List.range 70).map (current.regs ∘ roundControllerRegister)
    let p := packedLastLevelProgram guest D c
    ∃ computed packed out cn cp cb stop weightsAddr,
      Runs w p ω (.seq (stagedTreeSelectionBody 187 186 convertedGuestCallArgs)
        (prepareAndRunWideStagedNumericBody 74 162 163 164 165 58))
        staged .normal computed cn ∧
      Runs w p ω (publishableWideOutputs 168) computed .normal packed cp ∧
      Runs w p ω (stagedBranchAppendBody 164 172 14 174 179) packed .normal out cb ∧
      out.regs 54 = stop ∧ out.regs 38 = weightsAddr ∧ stop+1 < 2^w ∧
      ZeroFrom out.mem stop ∧
      (stagedControllerRoundContract current Next j budget).post args current.mem (stop+1)
        (Function.update out.mem stop weightsAddr) ∧
      cn+cp+cb+21+17*queryWeights H N+14+
        argsSize [.reg 69,.reg 5,
          (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤ budget := by
  intro ℓ H P ρ query s stage D len N Q sim levels guestBase base budget allocation width step hgrid hpre hs hj
    hspace hv hi hn hr hframeStage hcopy hendpoints hlengths hstaged h5 h8 h31 hsw hcw h72 h73 h74 h75
    h81 h82 h83 h86 h91 h95 h99 h100 h104 h107 h150 h113 h114 h115 h116 h127 h2 h131 h133 h134
    htree hmodel hbound hreserve hguestCost hcall Next args p
  have hcountEq : s.1 = H.m := by simp only [s,fixedPointLastLevelTool,ite_eq_left hne,H]
  have hj' : j < H.m := hcountEq ▸ hj
  obtain ⟨hready,hvalid,_,hm,hconnected,_,_,hL,hprec⟩ :=
    packedInitializer_liveSelectorInputs (j := j) fmt guest c oracle C G input hOracle hne hconn
      hgrid hpre hspace hj'
  obtain ⟨selected,cs,hrun,htreeAt,h12,hcount,hselectedWords,hselected,h0,h1,h5',ht,hh,hcs⟩ :=
    packedLastLevelProgram_treeSelection_runs (ω := ω) current staged pos len C hready rfl rfl hs
      le_rfl hstaged h5 h8 h72 h73 h74 h75 h81 h82 h83 h91 hbound hcw hcopy hframeStage rfl
      (fun i hi => (hendpoints i hi).1) (fun i hi => (hendpoints i hi).2) hlengths
      hw hL hprec guest D c hsw (fun he _ => hcall he) hvalid hconnected γ htree hj hreserve
  obtain ⟨h14,h19,h23,h27,h28,h31',h32,h35⟩ :=
    packedController_selectedNumericRegisters current staged selected pos hstaged hselected h31
  have hlevels : H.n ≤ 2^(levels+1) := by
    have h := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1
      (show Nat.clog 2 H.n ≤ levels+1 from Nat.le_succ _)
    exact h
  have hpword : P < 2^w := (Nat.le_add_right P N).trans_lt hprec
  have htreeAt' : selectedTreeAt H T (stage+queryWeights H N)
      (stage+queryOriginals H N+2^width+1+H.m) (selected.regs 13) staged.mem selected.mem := by
    simpa only [Nat.add_assoc, Nat.add_comm 1] using htreeAt
  have hscale : (integerScale D H : ℝ) = ρ := rfl
  obtain ⟨_,_,_,hweights,hvalue⟩ :=
    stagedController_numericWeights (guestL := N) current staged hs le_rfl
      (fun a ha => hframeStage a (Or.inl ha)) hscale h104 hcw
  have hscale' : (((integerScale D H : ℕ) : ℤ) : ℝ) = ρ :=
    (Int.cast_natCast _).trans hscale
  rw [hscale'] at hvalue
  obtain ⟨computed,packed,out,cn,cp,cb,hnr,hpr,hbr,h54,h38,hzero,hroom,hpost,hcn,hcp,hcb⟩ :=
    packedInitializer_numericAppend_runs (ω := ω) (guest := guest) (budget := budget) (N := N)
      (sim := sim) (levels := levels) G T fmt allocation input oracle C γ c ready current staged selected
      pos hne hconn hg hgEnd hframe hw hbits hOracle hgrid hpre hs hj hpword hlevels hv hi hn hr
      (fun a ha => hframeStage a (Or.inl ha)) ht hh hstaged hselected h0 h1 h5' h12
      (h14.trans h86) (h19.trans h91) (h23.trans h95) (h27.trans h99) (h28.trans h100)
      h31' (h32.trans h104) (h35.trans h107) hselectedWords
      h150 h113 h114 h115 h116 h127 h2 h131 h133 h134 htree hmodel htreeAt' hcount
      hbound hreserve hweights hvalue
  have hgridFit := (packedNumeric_capacity_of_finer_runtimePre fmt allocation oracle C G input levels
    hne hgrid hpre).2.1
  have hcost := representativePackedLinkCost_of_initPre fmt (fixedPointLastLevelTool oracle C)
    allocation guest c C K G input (selected.regs 13) guestCost cs cn cp cb hg.1 hGn hne
    hgridFit hpre hm hcount hguestCost hcs hcn hcp hcb
  exact ⟨computed,packed,out,cs+cn+1,cp,cb,_,_,
    runs_seq_iff.mpr (Or.inr ⟨selected,cs,cn,hrun,hnr,rfl⟩),hpr,hbr,h54,h38,
    hroom,hzero,hpost,hcost⟩

/-- Verify the installed round operation on the controller invariant.
The call stages the guest prefix before running selection and publication. -/
theorem packedInitializer_liveRound_meetsContract
    {w g vCap eCap L handle bound j multiplier stretchPrecision src : ℕ} {guest : Program}
    (G T : MGraph) (fmt : Format w) (input : ℕ → ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C K γ : ℝ) (c guestCost : ℕ)
    (ready current : State)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (hGn : G.n ≤ G.m+1)
    (hg : DynGraphAt input g vCap eCap G) (hgEnd : g+dynGraphSize vCap eCap ≤ handle)
    (hframe : ∀ a < handle, ready.mem a = input a)
    (hw : 16 ≤ 2^w) (hbits : 14 ≤ w)
    (hOracle : LSF.HasLSSTSpec oracle C) :
    let ℓ := MinRatio.readEdgeValues input src 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let ρ := roundedScale C H
    let query := stretchQuery oracle H ℓ P
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let stage := current.regs 0
    let D := ⌈max 1 C⌉₊
    let len := LSF.safeLen H ℓ
    let N := roundQueryLimbs C H len
    let Q := roundQueryPrecision C H len
    let sim := WideWord.lsstLSimMin c H.n H.m N 1
    let levels := Nat.clog 2 H.n
    let guestBase := handle+11*G.m+vCap+1
    let base := guestBase+queryWeights H N
    let budget := representativePackedRoundMultiplier guest c D K L G.n G.m*(G.m+1)
    let allocation := packedRuntimeAllocation G guest C c L vCap eCap
    let width := paddedGuestWidth guest D H.n H.m sim (queryHeap H N)
    let step := stagedPackedRoundSpace H guest D N sim levels L P H.n vCap eCap
    P ≤ stretchPrecision →
    (MinRatio.lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C)
      G vCap eCap multiplier stretchPrecision allocation).initPre [g,src,L,fmt.precision,handle] input →
    stagedRoundStateAtStride H vCap eCap 4 L P fmt.precision base s.1 handle bound L
      G.E s.2 ρ query ready.mem j current →
    j < s.1 → handle+(MinRatio.lastLevelRuntimeMachineContract fmt L
      (fixedPointLastLevelTool oracle C) G vCap eCap multiplier stretchPrecision allocation).initSpace
        [g,src,L,fmt.precision,handle] input < 2^w →
    (∀ i < H.n, ready.mem (handle+7*G.m+i) = vertexName H i) →
    (∀ i < G.m, ready.mem (handle+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, ready.mem (handle+i) = edgeName G i) →
    (∀ i < H.m, ready.mem (handle+2*G.m+i) = edgeName H i) →
    (∀ i < H.m, ready.mem (guestBase+i) = (indexedGraph H).tail i ∧
      ready.mem (guestBase+(H.m+i)) = (indexedGraph H).head i) →
    (∀ i < H.m, ListAt ready.mem (guestBase+queryLengths H+i*N)
      (encodeLimbs 1 N (queryNumerator Q (len (edgeName H i))))) →
    (∀ r, current.regs r < 2^w) →
    queryHeap H N < 2^w → bound+queryWeights H N < 2^w →
    current.regs 141 = guestBase →
    current.regs 72 = H.n → current.regs 73 = H.m →
    current.regs 74 = N → current.regs 75 = sim →
    current.regs 81 = L → current.regs 82 = P → current.regs 83 = Q →
    current.regs 86 = levels → current.regs 91 = L → current.regs 95 = P →
    current.regs 99 = src → current.regs 100 = handle+2*G.m →
    current.regs 104 = L → current.regs 107 = integerScale D H →
    current.regs 150 = handle+7*G.m → current.regs 113 = vCap → current.regs 114 = eCap →
    current.regs 115 = G.n → current.regs 116 = dgVListBase g vCap →
    current.regs 127 = L → current.regs 2 = j →
    current.regs 131 = handle+4*G.m → current.regs 133 = G.m → current.regs 134 = handle →
    LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (weights P ρ query j ∘ edgeName H) γ T →
    oracle H (LSF.safeLen H ℓ) (weights P ρ query j) = restoreTreeNames H T →
    bound < 2^w → stage+(s.1-j)*step ≤ bound →
    (guestCost : ℝ) ≤ 16000*((H.m+H.n+1 : ℕ) : ℝ)*
      WideWord.lsstOverheadFactor guest c K H.n H.m N →
    (stage+queryOriginals H N+1+2^width ≤ 2^w →
      MeetsContract w (packedLastLevelProgram guest D c) 187
        (convertedTreeSelectorContract w guest D H T N sim stage guestCost
          (current.mem (stage-1)) L L P Q (queryNumerator Q ∘ len)
          (queryNumerator Q ∘ weights P ρ query j))) →
    let Next := fun next =>
      stagedRoundStateAtStride H vCap eCap 4 L P fmt.precision base s.1 handle bound L
        G.E s.2 ρ query ready.mem (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound
    MeetsContract w (packedLastLevelProgram guest D c) 57
      (stagedControllerRoundContract current Next j budget) := by
  intro ℓ H P ρ query s stage D len N Q sim levels guestBase base budget allocation width step hgrid hpre hs hj
    hspace hv hi hn hr hendpoints hlengths hcw hheap hfit h141 h72 h73 h74 h75 h81 h82 h83 h86 h91 h95 h99
    h100 h104 h107 h150 h113 h114 h115 h116 h127 h2 h131 h133 h134
    htree hmodel hbound hreserve hguestCost hcall Next
  apply packedLastLevelProgram_round_meetsContract current Next hs h72 h73 h74 h75
    (src := guestBase) (D := D) (c := c) (guest := guest) (stride := L) h141 rfl
    (show 1 < 2^w from (by decide : 1 < 16).trans_le hw) hheap hfit hbound hcw
  intro pos ω staged h5 h8 h31 hstaged hcopy hframeStage hsw
  obtain ⟨computed,packed,out,cn,cp,cb,stop,weightsAddr,hnr,hpr,hbr,h54,h38,hroom,hzero,hpost,hcost⟩ :=
    packedInitializer_liveRound_runs (ω := ω) (guest := guest) G T fmt input oracle C K γ c
      guestCost ready current staged pos hne hconn hGn hg hgEnd hframe hw hbits hOracle
      hgrid hpre hs hj hspace hv hi hn hr hframeStage hcopy hendpoints hlengths hstaged
      h5 h8 h31 hsw hcw h72 h73 h74 h75 h81 h82 h83 h86 h91 h95 h99 h100 h104 h107
      h150 h113 h114 h115 h116 h127 h2 h131 h133 h134 htree hmodel hbound hreserve
      hguestCost hcall
  exact ⟨computed,packed,out,cn,cp,cb,stop,weightsAddr,hnr,hpr,hbr,h54,h38,hroom,hzero,hpost,hcost⟩

/-- Join the five input preparation phases to the collection controller
at the fixed non-loop entry with the canonical selector. -/
theorem packedLastLevelProgram_nonLoop_runs
    {w g vCap eCap L P multiplier c : ℕ} {guest : Program} {ω : ℕ → Bool}
    (fmt : Format w) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C K : ℝ)
    (G : MGraph) (mem : ℕ → ℕ) (lengths handle pos : ℕ)
    (hc : 1 ≤ c) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b)
    (hGn : G.n ≤ G.m+1) (hOracle : LSF.HasLSSTSpec oracle C)
    (hzero : ZeroFrom mem handle) :
    let d := ⌈max 1 C⌉₊
    let p := packedLastLevelProgram guest d c
    let tool := fixedPointLastLevelTool oracle C
    let alloc := packedRuntimeAllocation G guest C c L vCap eCap
    let D := MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc
    let args := [g,lengths,L,fmt.precision,handle]
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let H := representativeGraph G ℓ
    let grid := weightPrecision C H
    let N := roundQueryLimbs C H (LSF.safeLen H ℓ)
    let Q := roundQueryPrecision C H (LSF.safeLen H ℓ)
    let sim := WideWord.lsstLSimMin c H.n H.m N 1
    let s := tool.build G ℓ
    let ρ := roundedScale C H
    let query := stretchQuery oracle H ℓ grid
    grid ≤ P → D.initPre args mem → handle+D.initSpace args mem < 2^w →
    (∀ j < H.m,
      let v := weights grid ρ query j
      ∃ T : MGraph, ∃ guestCost : ℕ, ∃ γ : ℝ,
        oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T ∧
        LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
          (v ∘ edgeName H) γ T ∧
        (guestCost : ℝ) ≤ 16000*((H.m+H.n+1 : ℕ) : ℝ)*
          WideWord.lsstOverheadFactor guest c K H.n H.m N ∧
        ∀ staging weightSrc,
          staging+queryOriginals H N+1+
            2^paddedGuestWidth guest d H.n H.m sim (queryHeap H N) ≤ 2^w →
          MeetsContract w p 187 (convertedTreeSelectorContract w guest d H T N sim staging guestCost
            weightSrc L L grid Q (queryNumerator Q ∘ LSF.safeLen H ℓ) (queryNumerator Q ∘ v))) →
    ∃ ret out cost, Runs w p ω
      (packedRepresentativeInitializerBody guest 19 d c 0 14) (startState args mem pos) (.returned ret) out cost ∧
      handle+1+s.1 ≤ ret ∧
      CollectionPrefix out.mem handle s.1 s.1 ret vCap eCap 4 L fmt.precision G.E s.2 ∧
      ret ≤ handle+D.initSpace args mem ∧ ZeroFrom out.mem ret ∧
      (∀ a < handle, out.mem a = mem a) ∧
      cost ≤ packedNonLoopInitMultiplier guest c d K L G.n G.m*(tool.cost G+1) := by
  intro d p tool alloc D args ℓ H grid N Q sim s ρ query
    hgrid hpre hspace hselector
  let levels := Nat.clog 2 H.n
  let src := handle+11*G.m+vCap+1
  let base := src+queryWeights H N
  let budget := representativePackedRoundMultiplier guest c d K L G.n G.m*(G.m+1)
  let step := stagedPackedRoundSpace H guest d N sim levels L grid H.n vCap eCap
  let bound := base+stagedPackedCollectionSpace H guest d N sim levels L grid H.m vCap eCap
  obtain ⟨hm,haddr,hheap,_,hsep,hreserve,hfit,hbound⟩ :=
    packedRuntimeAllocation_controllerBounds fmt oracle G guest C c mem hne hconn hpre hspace
  obtain ⟨hbits,_,hscalar⟩ :=
    packedRuntimeAllocation_nonLoop_words fmt tool G guest C c mem hne hpre hspace
  obtain ⟨_,_,hunit,_,_,_,_⟩ :=
    packedNumeric_capacity_of_finer_runtimePre fmt alloc oracle C G mem levels hne hgrid hpre
  obtain ⟨prepared,named,indexed,formatted,ready,prep,cn,ci,cf,cl,
    hp,hn,hi,hf,hl,h86,_,hQ,hN,hsim,hP,h107,_,hends,hencoded,hz,hframe,_,
    h72,h73,hL,hsrc,h151,h113,h114,h115,h116,h131,h133,h134,h150,h99,h100,h145,
    hnames,hindices,hrepNames,hvertices,hprepCost,hindexCost,hlevelCost,hformatCost⟩ :=
    packedInitializer_prepare_runs (guest := guest) (ω := ω) fmt oracle C G mem lengths handle pos
      hc hne hconn hzero hpre hspace
  have hcount : s.1 = H.m := by simp only [s,tool,fixedPointLastLevelTool,ite_eq_left hne,H]
  have hword : bound < 2^w :=
    (show bound ≤ bound+queryWeights H N from Nat.le_add_right _ _).trans_lt hfit
  have hw : 1 < 2^w := (show 1 < 2^14 by decide).trans_le
    (Nat.pow_le_pow_right (by decide) hbits)
  let rebuildBudget := collectionHeaderAddress.size+20+
    (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+
      ((argsSize publishedRoundArgs+budget+10)*s.1+7)+(17*(s.1+1)+19)+17)
  obtain ⟨hg,hgEnd,_⟩ := runtimeEndpoints_inputs_of_initPre fmt tool alloc G mem hpre
  have hlen : lengths ≤ handle := by
    obtain ⟨g',len',h',heq,_,_,hbase,_⟩ := hpre
    dsimp only [args] at heq
    simp only [List.cons.injEq,and_true,true_and] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    obtain ⟨g',len',h',heq,_,_,hspan,_,_⟩ := hbase
    simp only [List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    exact (Nat.le_add_right _ _).trans hspan
  have haddr' : src < 2^w := (Nat.le_add_right src (queryLengths H)).trans_lt haddr
  have hreadyBits := packedControllerInput_words G H grid ready hg hgEnd hlen haddr' hscalar
    h72 h73 hN hsim hQ h86 hP h99 h100 h107 h113 h114 h115 h116 hL h131 h133 h134 hsrc h145 h150 h151
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest d c
  have hentry := packedRepresentativeInitializerModule_controller hgeneral
  let Post := fun ret out => handle+1+s.1 ≤ ret ∧ ret ≤ bound ∧
    CollectionPrefix out handle s.1 s.1 ret vCap eCap 4 L fmt.precision G.E s.2 ∧
    ZeroFrom out ret ∧ (∀ a < handle, out a = mem a)
  have hcontroller (entered : State) (hemem : entered.mem = ready.mem)
      (_ : entered.pos = ready.pos)
      (he : ∀ r ∈ packedControllerInputRegisters, entered.regs r = ready.regs r)
      (hewords : ∀ r, entered.regs r < 2^w) :
      ∃ ret out cost, Runs w p ω (stagedCompactCollectionThen 54 55 57 74)
        entered (.returned ret) out cost ∧ Post ret out.mem ∧ cost ≤ rebuildBudget := by
    have hrebuild :=
      packedLastLevelProgram_controller_runs (guest := guest) (ω := ω) (D := d) (c := c)
        (vCap := vCap) (eCap := eCap) (caller := fmt.precision) (budget := budget) (step := step)
        entered G ℓ oracle C ρ query (by omega) hne hw
        ((he _ (by decide)).trans hL) ((he _ (by decide)).trans hP)
        ((he _ (by decide)).trans h151) ((he _ (by decide)).trans hN)
        ((he _ (by decide)).trans hsim) ((he _ (by decide)).trans hsrc) hword hunit
        ((he _ (by decide)).trans h72) ((he _ (by decide)).trans h73)
        hm hheap (by rw [hcount]; exact hsep) (hemem.symm ▸ hz)
        (by rw [hcount]; exact hreserve) hewords (by
          intro regs h81 h82 h91 h104 hkeep j hj current hs hreserveCurrent hcurrent hretained h2
          have hj' : j < H.m := hcount ▸ hj
          obtain ⟨T,guestCost,γ,hmodel,htree,hcost,hcall⟩ := hselector j hj'
          have keep (r : ℕ) (hr : 4 ≤ r) (hlist : r ∉ ([1,3,81,82,91,104] : List ℕ)) :=
            (hretained r hr).trans (hkeep r hlist)
          obtain ⟨hg,hgEnd,_⟩ :=
            runtimeEndpoints_inputs_of_initPre fmt tool alloc G mem hpre
          have hmc := packedInitializer_liveRound_meetsContract (guest := guest) G T fmt mem oracle C K γ c
            guestCost ready current hne hconn hGn hg hgEnd hframe ((show 16 ≤ 2^14 by decide).trans (Nat.pow_le_pow_right (by decide) hbits)) hbits hOracle
            hgrid hpre (by simpa only [hemem] using hs) hj hspace hvertices hindices hnames hrepNames hends hencoded
            hcurrent hheap hfit ((keep 141 (by decide) (by decide)).trans ((he 141 (by decide)).trans hsrc))
            ((keep 72 (by decide) (by decide)).trans ((he 72 (by decide)).trans h72))
            ((keep 73 (by decide) (by decide)).trans ((he 73 (by decide)).trans h73))
            ((keep 74 (by decide) (by decide)).trans ((he 74 (by decide)).trans hN))
            ((keep 75 (by decide) (by decide)).trans ((he 75 (by decide)).trans hsim))
            ((hretained 81 (by decide)).trans h81) ((hretained 82 (by decide)).trans h82)
            ((keep 83 (by decide) (by decide)).trans ((he 83 (by decide)).trans hQ))
            ((keep 86 (by decide) (by decide)).trans ((he 86 (by decide)).trans h86)) ((hretained 91 (by decide)).trans h91)
            ((keep 95 (by decide) (by decide)).trans ((he 95 (by decide)).trans hP))
            ((keep 99 (by decide) (by decide)).trans ((he 99 (by decide)).trans h99))
            ((keep 100 (by decide) (by decide)).trans ((he 100 (by decide)).trans h100))
            ((hretained 104 (by decide)).trans h104)
            ((keep 107 (by decide) (by decide)).trans ((he 107 (by decide)).trans h107))
            ((keep 150 (by decide) (by decide)).trans ((he 150 (by decide)).trans h150))
            ((keep 113 (by decide) (by decide)).trans ((he 113 (by decide)).trans h113))
            ((keep 114 (by decide) (by decide)).trans ((he 114 (by decide)).trans h114))
            ((keep 115 (by decide) (by decide)).trans ((he 115 (by decide)).trans h115))
            ((keep 116 (by decide) (by decide)).trans ((he 116 (by decide)).trans h116))
            ((keep 127 (by decide) (by decide)).trans ((he 127 (by decide)).trans hL)) h2
            ((keep 131 (by decide) (by decide)).trans ((he 131 (by decide)).trans h131))
            ((keep 133 (by decide) (by decide)).trans ((he 133 (by decide)).trans h133))
            ((keep 134 (by decide) (by decide)).trans ((he 134 (by decide)).trans h134))
            htree hmodel hword hreserveCurrent hcost (hcall _ _)
          simpa only [hemem] using hmc)
    obtain ⟨o,out,cost,hr,⟨ret,rfl,hlo,hhi,hprefix,hz,hf⟩,hcost⟩ := hrebuild
    exact ⟨ret,out,cost,hr,⟨hlo,hhi,hprefix,hz,fun a ha =>
      (hf a ha).trans ((congrFun hemem a).trans (hframe a ha))⟩,hcost⟩
  obtain ⟨ret,finished,cc,hrc,hpost,hcc⟩ :=
    packedControllerCall_runs (ω := ω) (result := 160) ready _ hentry hreadyBits Post rebuildBudget hcontroller
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ :=
    representativeRuntimeInitWith_runs (startState args mem pos) prepared named indexed formatted ready
      prep cn ci cf cl (rebuildBudget+argsSize packedControllerInputArgs+4)
      (fun o out => o = .returned ret ∧ Post ret out.mem) hp hn hi hf hl
      ⟨.returned ret,finished,cc,hrc,⟨rfl,hpost⟩,hcc⟩
  obtain ⟨rfl,hlo,hret,hprefix,hz',hf'⟩ := hpost
  refine ⟨ret,out,cost,hr,hlo,hprefix,hret.trans hbound,hz',hf',?_⟩
  obtain ⟨hgraph,_,_⟩ :=
    runtimeEndpoints_inputs_of_initPre fmt tool alloc G mem hpre
  obtain ⟨hwidth,hlevels⟩ :=
    representativePackedCost_dimensions_of_initPre fmt tool alloc C G mem hne hpre
  change N ≤ representativeGuestWidthBound d L G.m at hwidth
  change levels ≤ (G.n+2).size at hlevels
  change cf ≤ argsSize collectionGuestFormatArgs+
    (((98*L+92)+(80*N+37))*H.m+40*(2*H.m).size+145)+
    40*(Nat.log 2 (H.n+2)+1)+40*grid+
    40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+169 at hformatCost
  have hformat := packedRuntime_formatCost_le C G ℓ L N cf hgraph.1 hwidth hformatCost
  have hlevel : cl ≤ 40*(G.n+2).size+22 := hlevelCost.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 40 hlevels) 22)
  let loop := (argsSize publishedRoundArgs+budget+10)*H.m+7
  have hloop : loop ≤ (representativePackedRoundMultiplier guest c d K L G.n G.m+
      (argsSize publishedRoundArgs+10)+7)*(tool.cost G+1) := by
    have hr := representativePackedLoopCost_le guest c d K C oracle G ℓ L hne
    change (argsSize publishedRoundArgs+budget+10)*SparseCore.lastMWUK H+7 ≤ _ at hr
    have hiter : loop ≤ (argsSize publishedRoundArgs+budget+10)*SparseCore.lastMWUK H+7 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (lastMWUK_ge_edges H)) _
    exact hiter.trans (by simpa only [Nat.add_assoc] using hr)
  have hreb : rebuildBudget ≤ collectionHeaderAddress.size+20+
        (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loop+
          (17*(H.m+1)+19)+17) := by
    dsimp only [rebuildBudget,loop]
    rw [hcount]
  have hbaseCost := packedRuntime_initCost_le guest c K C oracle G ℓ L prep cn ci
    (representativeGuestSetupMultiplier d L G.m*(G.m+1)) cl loop rebuildBudget hne hgraph.1
    hm hprepCost hindexCost le_rfl hloop hlevel hreb
  let extra := packedFormatScalarCost d G.n G.m+argsSize packedControllerInputArgs+4
  have hextra : extra ≤ extra*(tool.cost G+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change cf ≤ representativeGuestSetupMultiplier d L G.m*(G.m+1)+packedFormatScalarCost d G.n G.m at hformat
  change _ ≤ representativePackedRuntimeMultiplier guest c d K L G.n G.m*(tool.cost G+1)
    at hbaseCost
  change cost ≤ (representativePackedRuntimeMultiplier guest c d K L G.n G.m+extra)*(tool.cost G+1)
  rw [Nat.add_mul]
  dsimp only [extra] at hextra ⊢
  omega

/-- The dispatcher runs the fixed non-loop initializer after scanning
the graph. Its additional cost is charged to the non-loop multiplier. -/
theorem packedLastLevelProgram_nonLoop_dispatch_runs
    {w g vCap eCap L : ℕ} {guest : Program} {ω : ℕ → Bool}
    (fmt : Format w) (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C K : ℝ)
    (G : MGraph) (mem : ℕ → ℕ) (c lengths handle pos : ℕ)
    (Post : ℕ → (ℕ → ℕ) → Prop)
    (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hgraphEnd : g+dynGraphSize vCap eCap < 2^w) :
    let d := ⌈max 1 C⌉₊
    let p := packedLastLevelProgram guest d c
    let args := [g,lengths,L,fmt.precision,handle]
    let budget := (fixedPointLastLevelTool oracle C).cost G+1
    (∀ start, ∃ limit out cost, Runs w p ω
      (packedRepresentativeInitializerBody guest 19 d c 0 14) (startState args mem start) (.returned limit) out cost ∧
      Post limit out.mem ∧ cost ≤ packedNonLoopInitMultiplier guest c d K L G.n G.m*budget) →
    ∃ limit out cost, Runs w p ω (dispatchRuntimeInit 17 19)
      (startState args mem pos) (.returned limit) out cost ∧
      Post limit out.mem ∧ cost ≤ packedNonLoopDispatchMultiplier guest c d K L G.n G.m*budget := by
  intro d p args budget hinit
  obtain ⟨_,_,_,_,_,hgeneral⟩ := packedLastLevelProgram_entries guest d c
  have hbody := (packedRepresentativeInitializerModule_entries hgeneral).1
  let upper := packedNonLoopInitMultiplier guest c d K L G.n G.m*budget
  obtain ⟨limit,out,cost,hr,hpost,hcost⟩ :=
    dispatchRuntimeInit_runs (ω := ω) (p := p) (loopOnly := 17) (general := 19)
      mem lengths L fmt.precision handle pos upper Post hG hw hgraphEnd (by
        intro start
        simp only [ite_eq_left hne]
        obtain ⟨limit,out,cost,hr,hpost,hcost⟩ := hinit start
        exact ⟨_,limit,out,cost,hbody,hr,hpost,hcost⟩)
  exact ⟨limit,out,cost,hr,hpost,hcost.trans
    (packedNonLoopDispatchCost_le guest c K C oracle G L upper hne le_rfl)⟩

/-- The cited tree procedure gives one fixed program and tool for all
connected non-loop inputs. The dispatcher
returns the realized collection within its allocation and cost bound. -/
theorem packedLastLevelProgram_nonLoop_withCanonical :
    ∃ (guest : Program) (c : ℕ) (K Cf : ℝ)
      (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph),
      let C := graphCanonicalConstant K Cf
      let d := ⌈max 1 C⌉₊
      let p := packedLastLevelProgram guest d c
      let tool := fixedPointLastLevelTool oracle C
      tool.IsSpec (SparseCore.lastLevelParams (128 * max 1 C)) ∧
      ∀ {w L vCap eCap : ℕ} (fmt : Format w) (G : MGraph) (g lengths handle : ℕ)
        (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        let P := (1024*d).size+3*(G.m+1).size
        let multiplier := packedNonLoopDispatchMultiplier guest c d K L G.n G.m
        let alloc := packedRuntimeAllocation G guest C c L vCap eCap
        let D := MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P alloc
        let args := [g,lengths,L,fmt.precision,handle]
        let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
        let s := tool.build G ℓ
        (SparseCore.nonLoopEdges G).Nonempty →
        (∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) → G.n ≤ G.m+1 →
        (∀ a ∈ args, a < 2^w) →
        D.initPre args mem → ZeroFrom mem handle → handle+D.initSpace args mem < 2^w →
        ∃ ret out cost, Runs w p ω (dispatchRuntimeInit 17 19)
          (startState args mem pos) (.returned ret) out cost ∧
          (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).rep
            handle s ret out.mem ∧ D.initPost args mem s out.mem ∧
          ret ≤ handle+D.initSpace args mem ∧ ZeroFrom out.mem ret ∧
          (∀ a < handle, out.mem a = mem a) ∧ cost ≤ multiplier*(tool.cost G+1) := by
  obtain ⟨guest,c,K,Cf,oracle,hc,hOracle,hSpec,hselector⟩ :=
    packedLastLevelProgram_withCanonicalSelector
  refine ⟨guest,c,K,Cf,oracle,hSpec,?_⟩
  intro w L vCap eCap fmt G g lengths handle mem pos ω P multiplier alloc D args ℓ s
    hne hconn hGn _ hpre hzero hspace
  let C := graphCanonicalConstant K Cf
  let d := ⌈max 1 C⌉₊
  let tool := fixedPointLastLevelTool oracle C
  let H := representativeGraph G ℓ
  let Post := fun ret out =>
    handle+1+s.1 ≤ ret ∧
    CollectionPrefix out handle s.1 s.1 ret vCap eCap 4 L fmt.precision G.E s.2 ∧
    ret ≤ handle+D.initSpace args mem ∧ ZeroFrom out ret ∧ (∀ a < handle, out a = mem a)
  obtain ⟨hg,hgEnd,_⟩ := runtimeEndpoints_inputs_of_initPre fmt tool alloc G mem hpre
  obtain ⟨hbits,_,_⟩ := packedRuntimeAllocation_nonLoop_words fmt tool G guest C c mem hne hpre hspace
  have hw : 16 ≤ 2^w := (show 16 ≤ 2^14 by decide).trans (Nat.pow_le_pow_right (by decide) hbits)
  have hgFit : g+dynGraphSize vCap eCap < 2^w :=
    hgEnd.trans_lt ((Nat.le_add_right _ _).trans_lt hspace)
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hg.1 ℓ).2.1
  have hgrid : weightPrecision C H ≤ P :=
    (representativeGraph_weightPrecision_le C G ℓ).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3 (Nat.size_le_size (Nat.succ_le_succ hm))) _)
  obtain ⟨ret,out,cost,hr,hpost,hcost⟩ :=
    packedLastLevelProgram_nonLoop_dispatch_runs (guest := guest) (ω := ω) (L := L)
      fmt oracle C K G mem c lengths handle pos Post hne hg hw hgFit (by
        intro start
        obtain ⟨ret,out,cost,hr,hlo,hprefix,hhi,hz,hframe,hcost⟩ :=
          packedLastLevelProgram_nonLoop_runs (guest := guest) (ω := ω) fmt oracle C K G mem
            lengths handle start hc hne hconn hGn hOracle hzero hgrid hpre hspace (by
              intro j hj v
              obtain ⟨hready,_,hn,hm,_,_,_,_,_⟩ :=
                packedInitializer_liveSelectorInputs (j := j) fmt guest c oracle C G mem
                  hOracle hne hconn hgrid hpre hspace hj
              obtain ⟨T,cost,heq,htree,hcost,hcall⟩ :=
                hselector H (LSF.safeLen H ℓ) v hn hm hready
              refine ⟨T,cost,_,heq,htree,hcost,?_⟩
              intro staging weightSrc hroom
              rw [← graphCanonicalIntegerConstant_eq K Cf] at hroom ⊢
              exact hcall w staging weightSrc L L (weightPrecision C H) hroom)
        exact ⟨ret,out,cost,hr,⟨hlo,hprefix,hhi,hz,hframe⟩,hcost⟩)
  have hformat : fmt.limbBits = 4 := hpre.choose_spec.choose_spec.choose_spec.2.1
  obtain ⟨hrep,hinit⟩ := lastLevelRuntime_initPost_of_prefix (Q := P) (multiplier := multiplier)
    fmt tool G alloc mem out.mem hformat hpost.1 hpost.2.1
  exact ⟨ret,out,cost,hr,hrep,hinit,hpost.2.2.1,hpost.2.2.2.1,hpost.2.2.2.2,hcost⟩

end MinCostFlow.LastLevelProgram
