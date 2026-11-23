module

public import MinCostFlow.LastLevelProgram.CanonicalModel
public import MinCostFlow.LastLevelProgram.StagedRoundInputs
public import MinCostFlow.LastLevelProgram.StagedAppendModel
import MinCostFlow.LastLevelProgram.OutputCapacity
import MinCostFlow.LastLevelProgram.UnitWeights
public import MinCostFlow.LastLevelProgram.StagedRebuildProof
import MinCostFlow.LastLevelProgram.ConnectedLSST
import MinCostFlow.LastLevelProgram.RepresentativeScan
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# Widened last-level arithmetic and packed output

Definition 5.8 (pages 19–20) prepares the selected tree and computes
both output tables before appending a branch.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Instantiate the reserved-space bounds at the cursor returned by
tree selection, in the address order used by the packed numeric call. -/
theorem packedNumeric_wordBounds (H : MGraph) (guest : Program)
    (D guestL sim levels L P j rounds vCap eCap staging bound w cursor : ℕ)
    (hL : 0 < L) (hm : 0 < H.m)
    (hcursor : cursor = staging+queryOriginals H guestL+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL))
    (hj : j < rounds)
    (hreserve : staging+(rounds-j)*
      stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap ≤ bound)
    (hbound : bound < 2^w) :
    let K := L+(P+levels+7)/4
    let dest := cursor+1+H.m
    let parents := dest+H.n
    let adj := parents+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let old := tails+2*H.m+H.m*K
    let dist := old+H.m*K+2*K
    let heap := dist+H.n*K
    let stop := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
    P+levels+7 < 2^w ∧ levels+1 < 2^w ∧ K < 2^w ∧ heap < 2^w ∧
      stop+H.m*L+H.m*L < 2^w := by
  intro K dest parents adj tails old dist heap stop
  obtain ⟨hspace,_⟩ := stagedRoundReservation_step hj hreserve
  obtain ⟨hp,hrows⟩ := stagedPackedRoundSpace_precisionWords H guest D guestL sim levels
    L P H.n vCap eCap staging bound w hL hm hspace hbound
  obtain ⟨_,_,_,hk,hh,hpacked,_⟩ := stagedPackedRoundSpace_bounds H guest D guestL sim
    levels L P H.n vCap eCap staging bound w hspace hbound
  have hd : dest = staging+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL)+H.m := by
    dsimp only [dest]
    rw [hcursor]
    omega
  refine ⟨hp,hrows,hk,?_,?_⟩
  · dsimp only [heap,dist,old,tails,adj,parents]
    rw [hd]
    exact hh
  · dsimp only [stop,heap,dist,old,tails,adj,parents]
    rw [hd]
    exact hpacked

/-- Prepare widened inputs, build the tree incidence lists, and pack the
arithmetic outputs back into the caller's four-bit format. -/
@[expose] def packedRoundBufferModule (b arithmetic : ℕ) : List Stmt :=
  [packWideValuesBody (arithmetic+32),packWideWeightsBody (arithmetic+32),
   denominatorBody (b+7) (b+8),selectedAdjacencyBody (b+4),
   pushTreeEdgeBody (b+5),pushTreeIncidenceBody,
   packGuestWeightsBody (b+8),storeWordBody 4] ++ Num.shiftLeftModule (b+8) 4

/-- The buffer module supplies the helper calls at the offsets used by
widened arithmetic preparation and publication. -/
theorem packedRoundBufferModule_entries {p : Program} {b arithmetic : ℕ}
    (hp : p.HasAt b (packedRoundBufferModule b arithmetic)) :
    p.procs[b]? = some (packWideValuesBody (arithmetic+32)) ∧
    p.procs[b+1]? = some (packWideWeightsBody (arithmetic+32)) ∧
    p.procs[b+2]? = some (denominatorBody (b+7) (b+8)) ∧
    p.procs[b+3]? = some (selectedAdjacencyBody (b+4)) ∧
    p.procs[b+4]? = some (pushTreeEdgeBody (b+5)) ∧
    p.procs[b+5]? = some pushTreeIncidenceBody ∧
    p.procs[b+6]? = some (packGuestWeightsBody (b+8)) ∧
    p.procs[b+7]? = some (storeWordBody 4) ∧
    p.HasAt (b+8) (Num.shiftLeftModule (b+8) 4) := by
  have entryAt (i : ℕ) (hi : i < 8) :=
    hp.get (i := i) (hi.trans_le (by
      change 8 ≤ (packedRoundBufferModule b arithmetic).length
      rw [packedRoundBufferModule,List.length_append]
      exact Nat.le_add_right 8 _))
  exact ⟨entryAt 0 (by decide),entryAt 1 (by decide),entryAt 2 (by decide),
    entryAt 3 (by decide),entryAt 4 (by decide),entryAt 5 (by decide),
    entryAt 6 (by decide),entryAt 7 (by decide),Num.hasAt_append_right hp⟩

/-- Run widened preparation, traversal, and output packing from the selected tree. -/
theorem selectedWideNumeric_publish_runs
    {w Q arithmetic buffer : ℕ}
    {p : Program} {ω : ℕ → Bool} (guest : Program) (st selected : State) (G T H : MGraph)
    (staging guestL width levels src names weightSrc stride L P scale count D sim j rounds vCap eCap bound : ℕ)
    (hwidth : width = paddedGuestWidth guest D G.n G.m sim (queryHeap G guestL))
    (hj : j < rounds) (hbound : bound < 2^w)
    (hreserve : staging+(rounds-j)*stagedPackedRoundSpace G guest D guestL sim levels
      L P G.n vCap eCap ≤ bound)
    (htree : selectedTreeAt G T (staging+queryWeights G guestL)
      (staging+queryOriginals G guestL+1+2^width+G.m) (selected.regs 13) st.mem selected.mem)
    (hcursor : selected.regs 12 = staging+queryOriginals G guestL+2^width)
    (harith : p.HasAt arithmetic (packedRoundArithmeticModule arithmetic))
    (hbuffer : p.HasAt buffer (packedRoundBufferModule buffer arithmetic))
    (hbits : 10 ≤ w) (hn : 0 < G.n)
    (h0 : selected.regs 0 = G.n) (h1 : selected.regs 1 = G.m) (h5 : selected.regs 5 = staging)
    (h14 : selected.regs 14 = levels) (h19 : selected.regs 19 = L)
    (h23 : selected.regs 23 = P) (h27 : selected.regs 27 = src) (h28 : selected.regs 28 = names)
    (h31 : selected.regs 31 = weightSrc) (h32 : selected.regs 32 = stride) (h35 : selected.regs 35 = scale)
    (hwords : ∀ r, selected.regs r < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hhead : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (ℓ v : ℕ → ℝ) (γ : ℝ)
    (hw : 6 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (hTree : LSF.IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (hE : T.E.card ≤ G.n) (hV : T.V.card ≤ G.n) (hnm : G.n ≤ G.m+1)
    (heq : H.m = G.m) (hlevels : G.n ≤ 2^(levels+1))
    (len : ℕ → ℤ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hCaller : 0 < L) (hmPos : 0 < G.m) (h13 : selected.regs 13 = count)
    (sBound wBound : ℝ)
    (hs : ∀ i < H.m, let s := query (weights P ((scale : ℤ) : ℝ) query j) (edgeName H i)
      0 ≤ s ∧ s ≤ sBound)
    (hwt : ∀ i < H.m, let v := weights P ((scale : ℤ) : ℝ) query (j+1) (edgeName H i)
      0 ≤ v ∧ v ≤ wBound)
    (hsFit : 2*(2 : ℝ)^P*sBound < capacity 4 L)
    (hwFit : 2*(2 : ℝ)^P*wBound < capacity 4 L)
    (hLenFit : ∀ i < G.m, 0 < len i ∧ Fits 4 L (len i))
    (hLen : ∀ i < G.m, intVal st.mem (src+edgeName G i*L) 4 L = len i)
    (hWeight : ∀ i < H.m, fixVal st.mem (weightSrc+i*stride) 4 L P =
      weights P ((scale : ℤ) : ℝ) query j (edgeName H i)) :

    let K := L+(P+levels+7)/4
    let dest := selected.regs 12+1+G.m
    let parents := dest+G.n
    let edges := parents+(levels+1)*G.n
    let depths := edges+G.n
    let queue := depths+G.n
    let adj := parents+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let heads := tails+G.m
    let lengths := tails+2*G.m
    let old := lengths+G.m*K
    let denom := old+G.m*K+K
    let dist := old+G.m*K+2*K
    let heap := dist+G.n*K
    let C := stretchWeightRoundContract w 4 Q (indexedGraph G).toMGraph T H 0 len
      adj parents edges depths queue G.n levels dist lengths K heap tails heads P
      old K denom j (scale : ℤ) query
    let base := staging+queryWeights G guestL
    names+G.m ≤ base → (∀ i < G.m, st.mem (names+i) = edgeName G i) →
    (∀ e ∈ G.E, src+e*L+L ≤ base ∧ Num.Valid st.mem (src+e*L) 4 L) →
    (∀ i < G.m, weightSrc+i*stride+L ≤ base ∧ Num.Valid st.mem (weightSrc+i*stride) 4 L) →
    Num.Fits 4 K (scale : ℤ) → Num.Fits 4 K ((scale : ℤ)*(2 : ℤ)^P) →
    let stop := heap+(G.n-1)*K+G.m*edgeStretchSpace K+G.m*narrowWeightSpace K
    (stop < 2^w → MeetsContract w p arithmetic C) →
    ∃ computed packed cn cp,
      Runs w p ω (prepareAndRunWideStagedNumericBody (arithmetic+16) buffer (buffer+1) (buffer+2) (buffer+3) arithmetic) selected .normal computed cn ∧
      Runs w p ω (publishableWideOutputs (buffer+6)) computed .normal packed cp ∧
      packed.regs 16 = stop+G.m*L+G.m*L ∧
      packed.regs 36 = stop ∧ packed.regs 37 = L ∧
      packed.regs 38 = stop+G.m*L ∧ packed.regs 39 = L ∧
      (∀ r, r ≠ 15 → r ≠ 16 → r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34,36,37,38,39] : List ℕ) → packed.regs r = selected.regs r) ∧
      ZeroFrom packed.mem (stop+G.m*L+G.m*L) ∧ (∀ a < staging+queryWeights G guestL, packed.mem a = st.mem a) ∧
      staging+queryWeights G guestL ≤ dest ∧ dest+G.n ≤ packed.regs 16 ∧ staging ≤ stop ∧
      retainedStagedTreeAt G T (staging+queryWeights G guestL) dest count st.mem packed.mem ∧
      (∀ i < H.m, Valid packed.mem (stop+i*L) 4 L ∧
        fixVal packed.mem (stop+i*L) 4 L P =
          query (weights P ((scale : ℤ) : ℝ) query j) (edgeName H i)) ∧
      (∀ i < H.m, Valid packed.mem (stop+G.m*L+i*L) 4 L ∧
        fixVal packed.mem (stop+G.m*L+i*L) 4 L P =
          weights P ((scale : ℤ) : ℝ) query (j+1) (edgeName H i)) ∧
      cn ≤ argsSize (stagedAdjacencyArgs (.reg 0) (.reg 1) (.reg 5) (.reg 12)
        (stagedTraversalReserveExpr (.reg 0) (.reg 14)) (.reg 13)) +
        argsSize (stagedNumericArgsFrom 24)+112*count+stagedNumericFactor K levels*(G.m+1)+13+
        (stagedScratchWidthExpr.size+
          argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
            [.reg 64])+37+34*G.m+(2*((30*K+90)*G.m+20)+56*K+72))+1 ∧
      cp ≤ 2*((35*L+60)*G.m+17)+argsSize packedStagedOutputArgs+
        argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 24) (.reg 20))+21 := by
  intro K dest parents edges depths queue adj records tails heads lengths old denom dist heap C base
    hnEnd hnames hlengths hweights hscale hdenom stop hlink
  obtain ⟨hc,_,_,_,hx,_,_,_,_⟩ := packedRoundArithmeticModule_helpers harith
  obtain ⟨hl,hwg,hd,he,hi,hpush,hpack,hstore,hshift⟩ := packedRoundBufferModule_entries hbuffer
  obtain ⟨hprec,hRows,hkw,hheap,hroom⟩ :=
    packedNumeric_wordBounds G guest D guestL sim levels L P j rounds vCap eCap
      staging bound w (selected.regs 12) hCaller hmPos (hwidth ▸ hcursor) hj hreserve hbound
  have hstop : stop < 2^w := (Nat.le_add_right _ _).trans_lt
    ((Nat.le_add_right _ _).trans_lt hroom)
  have hC := hlink hstop
  obtain ⟨ready,cprep,hprep,hblocks,hdenv,hdene,hzero,h21,h22,h18,h26,h25,h17,h20,h24,
    hkeep,htail,hhead',hretain,hclear,_,hprefix,hcprep⟩ :=
    prepareWideStagedNumeric_of_selection (ω := ω) st selected G T staging guestL width levels
      src names weightSrc stride L P scale htree hcursor (copyWords_meetsContract hc) hl hwg hd hx hstore hshift
      hbits (by decide) (by omega) hn h0 h1 h5 h14 h19 h23 h27 h28 h31 h32 h35 hwords hprec ht hhead
      hkw hheap hnEnd hnames hlengths hweights hscale hdenom
  obtain ⟨hlen',hwgt'⟩ := widenedNumericArrays len (scale : ℤ) query heq hblocks hLen hWeight
  have hsep : staging+queryWeights G guestL ≤ dest :=
    (selectedTree_wideScratch (levels := levels) htree hcursor).2.1
  obtain ⟨computed,packed,cn,cp,hnRun,hpRun,h16,h36,h37,h38,h39,hregs,hfresh,hframe,htree',hs',hw',hcn,hcp⟩ :=
    preparedWideNumeric_publish_runs (ω := ω) ready G T H guestL staging (selected.regs 12)
      levels count L st.mem ℓ v γ he
      (pushTreeEdge_meetsContract hi (pushTreeIncidence_meetsContract hpush))
      (by omega) hv hconn hTree ht hhead
      ((hkeep 0 (by decide)).trans h0) ((hkeep 1 (by decide)).trans h1)
      ((hkeep 5 (by decide)).trans h5) (hkeep 12 (by decide))
      ((hkeep 14 (by decide)).trans h14) ((hkeep 13 (by decide)).trans h13) hn
      P j len (scale : ℤ) query ((hkeep 23 (by decide)).trans h23) hCaller hmPos hE hV hnm
      heq hlevels hRows (by omega) hpack hshift hbits ((hkeep 19 (by decide)).trans h19)
      (h19 ▸ hwords 19) (h0 ▸ hwords 0) (h1 ▸ hwords 1)
      sBound wBound hs hwt hsFit hwFit hLenFit h24 hC h17 h18 h20 h21 h22 h26 h25
      (h13 ▸ hretain) hsep hclear htail hhead' hlen' hdenv hdene hwgt' hzero hroom
  have htreeEnd : dest+G.n ≤ stop := calc
    _ ≤ adj := Nat.le_add_right _ _
    _ ≤ records := Nat.le_add_right _ _
    _ ≤ tails := Nat.le_add_right _ _
    _ ≤ lengths := Nat.le_add_right _ _
    _ ≤ old := Nat.le_add_right _ _
    _ ≤ dist := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    _ ≤ heap := Nat.le_add_right _ _
    _ ≤ stop := (Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  refine ⟨computed,packed,cprep+cn+1,cp,
    runs_seq_iff.mpr (Or.inr ⟨ready,cprep,cn,hprep,hnRun,rfl⟩),
    hpRun,h16,h36,h37,h38,h39,?_,hfresh,?_,hsep,?_,?_,htree',hs',hw',?_,hcp⟩
  · intro r h15 h16 hrs
    exact (hregs r h15 h16 (fun h => hrs (by simp_all))).trans
      (hkeep r (fun h => hrs (by simp_all)))
  · intro a ha
    exact (hframe a (ha.trans_le (hsep.trans (Nat.le_add_right _ _)))).trans (hprefix a ha)
  · exact h16.symm ▸ htreeEnd.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  · exact ((Nat.le_add_right _ _).trans hsep).trans
      ((Nat.le_add_right dest G.n).trans htreeEnd)
  · rw [Nat.add_comm cprep cn]
    exact Nat.add_le_add_right (Nat.add_le_add hcn hcprep) 1

/-- The tree selector changes only the cursor and the retained edge
count. Both words fit when its allocation and the vertex count fit. -/
theorem selectedNumericWords {w base dest : ℕ} {G T : MGraph} {st selected : State}
    (htree : selectedTreeAt G T base dest (selected.regs 13) st.mem selected.mem)
    (hkeep : ∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = st.regs r)
    (hwords : ∀ r, st.regs r < 2^w) (hcursor : selected.regs 12 < 2^w) (hn : G.n < 2^w) :
    selected.regs 13 ≤ G.n ∧ ∀ r, selected.regs r < 2^w := by
  obtain ⟨kept,hcount,hsize,_⟩ := htree
  have hc : selected.regs 13 ≤ G.n := hcount ▸ hsize
  refine ⟨hc,?_⟩
  intro r
  by_cases h12 : r = 12
  · exact h12 ▸ hcursor
  by_cases h13 : r = 13
  · exact h13 ▸ hc.trans_lt hn
  exact (hkeep r h12 h13).trans_lt (hwords r)

/-- Attach the tree selection run to the numeric run that consumes
its selected tree and leaves the packed publication as a separate phase. -/
theorem selectedWideNumeric_link
    {w select dedup copy packLengths packWeights prepare adjacency numeric pack cs cn cp : ℕ}
    {p : Program} {ω : ℕ → Bool} {st selected computed packed : State}
    (hs : Runs w p ω (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
      st .normal selected cs)
    (hn : Runs w p ω
      (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric)
      selected .normal computed cn)
    (hp : Runs w p ω (publishableWideOutputs pack) computed .normal packed cp) :
    Runs w p ω
      (.seq (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
        (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric))
      st .normal computed (cs+cn+1) ∧
    Runs w p ω (publishableWideOutputs pack) computed .normal packed cp :=
  ⟨runs_seq_iff.mpr (Or.inr ⟨selected,cs,cn,hs,hn,rfl⟩),hp⟩

/-- The append cursor computed from the numeric output uses exactly
the retained tree's share of the controller reservation. The saved
weight descriptor and all later rounds fit in the remaining space. -/
theorem packedNumeric_appendStop (H : MGraph) (guest : Program)
    (D guestL sim levels L P treeCount vCap eCap staging cursor j rounds bound w : ℕ)
    (hcursor : cursor = staging+queryOriginals H guestL+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL))
    (hj : j < rounds) (hcount : treeCount ≤ H.n) (hbound : bound < 2^w)
    (hreserve : staging+(rounds-j)*stagedPackedRoundSpace H guest D guestL sim levels
      L P H.n vCap eCap ≤ bound) :
    let K := L+(P+levels+7)/4
    let dest := cursor+1+H.m
    let adj := dest+H.n+stagedTraversalReserve H.n levels
    let tails := adj+H.n+6*H.n
    let heap := tails+2*H.m+H.m*K+H.m*K+2*K+H.n*K
    let start := heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K
    let afterStretch := start+H.m*L
    let numericEnd := afterStretch+H.m*L
    let ptr := numericEnd+2*L+3*treeCount
    let tree := ptr+4
    let roots := tree+DynSpanner.Program.dynGraphSize vCap eCap
    let addresses := roots+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    let step := stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap
    afterStretch+H.m*L ≤ stop ∧
    stop+1 ≤ staging+step ∧ stop+1 ≤ bound ∧ stop < 2^w ∧
      stop+1+(rounds-(j+1))*step ≤ bound := by
  intro K dest adj tails heap start afterStretch numericEnd ptr tree roots addresses stop step
  have he : stop = staging+stagedPackedRoundSpace H guest D guestL sim levels
      L P treeCount vCap eCap-1 := by
    dsimp only [stop,addresses,roots,tree,ptr,numericEnd,afterStretch,start,heap,tails,adj,dest,K,
      stagedPackedRoundSpace]
    rw [hcursor]
    omega
  refine ⟨?_,?_⟩
  · dsimp only [stop,addresses,roots,tree,ptr,numericEnd]
    omega
  rw [he]
  exact stagedPackedAppend_reservation H guest D guestL sim levels L P vCap eCap
    staging j rounds treeCount bound w hj hcount hbound hreserve

/-- Link the packed round phases and return the next controller
invariant at the new weight descriptor. -/
theorem stagedPackedRound_linkPhases
    {w select dedup copy packLengths packWeights prepare adjacency numeric pack
      unit restore init scatter publish cs cn cp guestL D sim levels cursor scale : ℕ} {p guest : Program} {ω : ℕ → Bool}
    {H T : MGraph} {vCap eCap h L P caller base count handle bound j start stop budget
      dest treeCount appendBudget step oldStride : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged selected computed packed : State) (args : List ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound oldStride E branches ρ query mem j st)
    (hm : 0 < H.m) (hj : j < count)
    (hcursorEq : cursor = st.regs 0+queryOriginals H guestL+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL))
    (hcount : treeCount ≤ H.n)
    (hstep : step = stagedPackedRoundSpace H guest D guestL sim levels L P H.n vCap eCap)
    (hreserve : st.regs 0+(count-j)*step ≤ bound)
    (hstopEq : stop =
      start+H.m*L+2*L+3*treeCount+4+DynSpanner.Program.dynGraphSize vCap eCap+vCap+2+
        eCap+eCap*L+eCap*L)
    (hstartEq :
      let K := L+(P+levels+7)/4
      let dest := cursor+1+H.m
      let adj := dest+H.n+stagedTraversalReserve H.n levels
      let tails := adj+H.n+6*H.n
      let heap := tails+2*H.m+H.m*K+H.m*K+2*K+H.n*K
      start = heap+(H.n-1)*K+H.m*edgeStretchSpace K+H.m*narrowWeightSpace K+H.m*L)
    (hword : bound < 2^w)
    (hstage : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (htree : retainedStagedTreeAt H T (st.regs 0+queryWeights H guestL)
      dest treeCount staged.mem packed.mem)
    (hscale : (scale : ℝ) = ρ)
    (hvalues : ∀ i < H.m, Valid packed.mem (start+i*L) h L ∧
      fixVal packed.mem (start+i*L) h L P = weights P ((scale : ℤ) : ℝ) query (j+1) (edgeName H i))
    (happend : stop < 2^w → ∃ out cost branchPtr,
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      packed .normal out cost ∧ out.regs 54 = stop ∧ out.regs 38 = start ∧
      ZeroFrom out.mem stop ∧ out.mem (base+1+j) = branchPtr ∧
      BranchWithin out.mem branchPtr (base+1+count) stop vCap eCap L E ∧
      MinRatio.LSFAt out.mem branchPtr vCap eCap h L caller E (branches j) ∧
      (∀ a < start+H.m*L, a ≠ base+1+j → out.mem a = packed.mem a) ∧
      cost ≤ appendBudget)
    (hselect : Runs w p ω (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
      staged .normal selected cs)
    (hnumeric : Runs w p ω
      (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric)
      selected .normal computed cn)
    (hpacking : Runs w p ω (publishableWideOutputs pack) computed .normal packed cp)
    (hcost : cs+cn+1+cp+appendBudget+21+17*queryWeights H guestL+14+
      argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤ budget) :
    let Next := fun st' =>
      stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound L E branches ρ query mem (j+1) st' ∧
      st'.regs 0+(count-(j+1))*step ≤ bound
    ∃ mid ready out cn' cp' cb stop' weightsAddr,
      Runs w p ω
        (.seq (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
          (prepareAndRunWideStagedNumericBody copy packLengths packWeights prepare adjacency numeric))
        staged .normal mid cn' ∧
      Runs w p ω (publishableWideOutputs pack) mid .normal ready cp' ∧
      Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
        ready .normal out cb ∧ out.regs 54 = stop' ∧ out.regs 38 = weightsAddr ∧
      stop'+1 < 2^w ∧ ZeroFrom out.mem stop' ∧
      (stagedControllerRoundContract st Next j budget).post args st.mem (stop'+1)
        (Function.update out.mem stop' weightsAddr) ∧
      cn'+cp'+cb+21+17*queryWeights H guestL+14+
        argsSize [.reg 69,.reg 5,
          (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] ≤ budget := by
  intro Next
  rw [Int.cast_natCast,hscale] at hvalues
  obtain ⟨hstop,_,hbound,hwordStop,hnext⟩ :=
    packedNumeric_appendStop H guest D guestL sim levels L P treeCount vCap eCap
      (st.regs 0) cursor j count bound w hcursorEq hj hcount hword (hstep ▸ hreserve)
  have hstart : st.regs 0 ≤ start := by
    have hc : st.regs 0 ≤ cursor := hcursorEq.symm ▸
      (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    rw [hstartEq]
    omega
  have hstop' : start+H.m*L ≤ stop := by rwa [hstopEq,hstartEq]
  have hbound' : stop+1 ≤ bound := by rwa [hstopEq,hstartEq]
  have hwordStop' : stop < 2^w := by rwa [hstopEq,hstartEq]
  have hnext' : stop+1+(count-(j+1))*step ≤ bound := by rwa [hstopEq,hstartEq,hstep]
  obtain ⟨appendOut,appendCost,branchPtr,hrApp,h54App,h38App,hzeroApp,hptr,hspan,hbranch,hframe,hcbApp⟩ :=
    happend hwordStop'
  obtain ⟨hn,hp⟩ := selectedWideNumeric_link hselect hnumeric hpacking
  obtain ⟨out,cb,hb,h54,h38,hroom,hzero,hpost,hcb⟩ :=
    stagedPackedAppendModel_roundPost (budget := budget) st staged packed args hs hm hj hstart hstop'
      hbound' hnext' hword hstage htree (Nat.le_add_right _ _) hvalues ⟨appendOut,appendCost,hrApp,h54App,h38App,hzeroApp,hptr,hspan,hbranch,hframe,hcbApp⟩
  rw [h38] at hpost
  exact ⟨computed,packed,out,cs+cn+1,cp,cb,stop,start,hn,hp,hb,h54,h38,hroom,hzero,hpost,by omega⟩

/-- Every staged register fits the machine word. The weight pointer
comes from inside the allocation, and copying the guest prefix returns zero. -/
theorem packedStagedWords {w vCap eCap h L P caller base count handle bound j stride pos : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} {st staged : State}
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      stride E branches ρ query mem j st)
    (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (h5 : staged.regs 5 = st.regs 0)
    (h8 : staged.regs 8 = st.mem (st.regs 0-1))
    (h31 : staged.regs 31 = st.mem (st.regs 0-1))
    (h70 : staged.regs 70 = 0)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r) :
    ∀ r, staged.regs r < 2^w := by
  obtain ⟨_,_,_,_,hcur,_,_,_,hspan,_⟩ := hs
  have hptr : st.mem (st.regs 0-1) < 2^w := by omega
  intro r
  by_cases h₅ : r = 5
  · exact h₅ ▸ h5 ▸ hwords 0
  by_cases h₈ : r = 8
  · exact h₈ ▸ h8 ▸ hptr
  by_cases h₃₁ : r = 31
  · exact h₃₁ ▸ h31 ▸ hptr
  by_cases h₇₀ : r = 70
  · exact h₇₀ ▸ h70 ▸ Nat.two_pow_pos _
  rw [hkeep r h₅ h₈ h₃₁ h₇₀]
  simp only [startState,List.getD,List.getElem?_map]
  cases (List.range 70)[r]? <;> simp [hwords]

/-- The linked round receives the controller's memory and argument
vector. Its staging frame and register bounds follow from that precondition. -/
theorem packedStagedController_inputs
    {w vCap eCap h L P caller base count handle bound j stride pos budget guestL : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem input : ℕ → ℕ} {st staged : State}
    (Next : State → Prop) (args : List ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound
      stride E branches ρ query mem j st)
    (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (hpre : (stagedControllerRoundContract st Next j budget).pre args input)
    (h5 : staged.regs 5 = st.regs 0)
    (h8 : staged.regs 8 = st.mem (st.regs 0-1))
    (h31 : staged.regs 31 = st.mem (st.regs 0-1))
    (h70 : staged.regs 70 = 0)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
       staged.regs r = (startState args input pos).regs r)
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a →
      staged.mem a = input a) :
    (∀ r, staged.regs r < 2^w) ∧ (∀ a < st.regs 0, staged.mem a = st.mem a) := by
  obtain ⟨rfl,rfl⟩ := hpre
  exact ⟨packedStagedWords hs hbound hwords h5 h8 h31 h70 hkeep,
    fun a ha => hframe a (Or.inl ha)⟩

/-- Selection preserves the numeric arguments forwarded by the
controller, including the runtime length and weight formats. -/
theorem packedNumeric_registers {st staged selected : State} {pos : ℕ}
    (hstage : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hselect : ∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 31 = st.mem (st.regs 0-1)) :
    selected.regs 5 = st.regs 0 ∧
    selected.regs 31 = st.mem (st.regs 0-1) ∧
    ∀ r ∈ ([0,1,14,19,23,27,28,32,35] : List ℕ),
      selected.regs r = st.regs (roundControllerRegister r) := by
  refine ⟨(hselect 5 (by decide) (by decide)).trans hcursor,
    (hselect 31 (by decide) (by decide)).trans hweight,?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [hselect _ (by decide) (by decide),
      hstage _ (by decide) (by decide) (by decide) (by decide)] <;>
    rfl

/-- The append phase reads the tree cursor and count from selection
and its other arguments from the controller call. -/
theorem packedAppendRegisters {st staged selected packed : State} {pos : ℕ}
    (hstage : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hselect : ∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = staged.regs r)
    (hpack : ∀ r, r ≠ 15 → r ≠ 16 →
      r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34,36,37,38,39] : List ℕ) →
        packed.regs r = selected.regs r) :
    packed.regs 12 = selected.regs 12 ∧ packed.regs 13 = selected.regs 13 ∧
    packed.regs 5 = st.regs 0 ∧
    (∀ r ∈ ([1,19,23,28,40,41,42,43,44,55,56,57,59,61,62] : List ℕ),
      packed.regs r = st.regs (roundControllerRegister r)) := by
  refine ⟨hpack 12 (by decide) (by decide) (by decide),
    hpack 13 (by decide) (by decide) (by decide),
    (hpack 5 (by decide) (by decide) (by decide)).trans
      ((hselect 5 (by decide) (by decide)).trans hcursor),?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [hpack _ (by decide) (by decide) (by decide),
      hselect _ (by decide) (by decide),hstage _ (by decide) (by decide) (by decide) (by decide)] <;>
    rfl

/-- Run the converted selector and retain the compact tree and its
word-sized cursor and count for widened preparation. -/
theorem packedTreeSelection_runs
    {w select dedup D guestL sim staging guestCost src stride hostL P Q : ℕ}
    {p guest : Program} {ω : ℕ → Bool} (st : State) (G T : MGraph)
    (len wt : ℕ → ℤ) (ℓ v : ℕ → ℝ) (γ : ℝ) (args : List ℕ)
    (hq : MeetsContract w p select
      (convertedTreeSelectorContract w guest D G T guestL sim staging guestCost src stride hostL P Q len wt))
    (he : evalArgs w st convertedGuestCallArgs = some args) (hargs : ∀ x ∈ args, x < 2^w)
    (hready : convertedSelectorReady w G guestL sim staging src stride P Q hostL len wt args st.mem)
    (htree : LSF.IsLSST (indexedGraph G).toMGraph ℓ v γ T)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = guestL)
    (hs : st.regs 3 = sim) (ha : st.regs 5 = staging)
    (hdedup : p.procs[dedup]? = some dedupSelectedTreeBody)
    (hw : 1 < 2^w) (hv : (indexedGraph G).Valid)
    (hconn : ∀ a ∈ (indexedGraph G).toMGraph.V, ∀ b ∈ (indexedGraph G).toMGraph.V,
      (indexedGraph G).toMGraph.Connected a b)
    (hwords : ∀ r, st.regs r < 2^w) :
    let base := staging+queryOriginals G guestL+1
    let width := paddedGuestWidth guest D G.n G.m sim (queryHeap G guestL)
    let marks := base+2^width
    let dest := marks+G.m
    dest+G.n < 2^w → G.n+1 < 2^w →
    ∃ selected cost, Runs w p ω (stagedTreeSelectionBody select dedup convertedGuestCallArgs)
      st .normal selected cost ∧
      selectedTreeAt G T (staging+queryWeights G guestL) dest (selected.regs 13) st.mem selected.mem ∧
      selected.regs 12 = staging+queryOriginals G guestL+2^width ∧
      selected.regs 13 ≤ G.n ∧ (∀ r, selected.regs r < 2^w) ∧
      (∀ r, r ≠ 12 → r ≠ 13 → selected.regs r = st.regs r) ∧
      cost ≤ argsSize convertedGuestCallArgs + convertedTreeSelectorCost w guest D G guestL sim guestCost +
        argsSize (stagedDedupArgs (.reg 0) (.reg 1) (.reg 2) (.reg 3) (.reg 5) (.reg 12)) +
        40*G.n+17 := by
  intro base width marks dest hroom hword
  have hd := dedupSelectedTree_meetsContract G ℓ v γ
    (base+queryOriginals G guestL) (base+queryBridges G guestL) (base+queryHeader G guestL)
    marks dest staging (staging+G.m) hdedup hw hv hconn
  obtain ⟨selected,cost,hr,htree',hcursor,hkeep,hcost⟩ :=
    stagedTreeSelection_runs (ω := ω) st guest D G T guestL sim staging ℓ v γ
      convertedGuestCallArgs args _ _ hq he hargs hready htree ht hh hn hm hL hs ha hd hroom hword
  have hc : selected.regs 12 < 2^w := by
    change selected.regs 12 = staging+queryOriginals G guestL+2^width at hcursor
    rw [hcursor]
    dsimp only [dest,marks,base] at hroom
    omega
  obtain ⟨hcount,hreg⟩ := selectedNumericWords htree' hkeep hwords hc
    ((Nat.lt_succ_self _).trans hword)
  exact ⟨selected,cost,hr,htree',hcursor,hcount,hreg,hkeep,hcost⟩

/-- The packed round links selection, widened arithmetic, and branch
publication. The canonical selector and graph initializer are shared
with the surrounding program. -/
@[expose] def packedRoundModule (b select initGraph : ℕ) : List Stmt :=
  [stagedPackedRoundBody select (b+129) (b+17) (b+105) (b+106) (b+107)
    (b+108) (b+1) (b+111) (b+107) (b+115) initGraph (b+117) (b+122)] ++
  (packedRoundArithmeticModule (b+1) ++
    (packedRoundBufferModule (b+105) (b+1) ++
      (packedBranchModule (b+115) (b+17) ++ [dedupSelectedTreeBody])))

/-- Installing the round provides each group of procedures at the
address called by the body. -/
theorem packedRoundModule_entries {p : Program} {b select initGraph : ℕ}
    (hp : p.HasAt b (packedRoundModule b select initGraph)) :
    p.procs[b]? = some (stagedPackedRoundBody select (b+129) (b+17) (b+105) (b+106) (b+107)
      (b+108) (b+1) (b+111) (b+107) (b+115) initGraph (b+117) (b+122)) ∧
    p.HasAt (b+1) (packedRoundArithmeticModule (b+1)) ∧
    p.HasAt (b+105) (packedRoundBufferModule (b+105) (b+1)) ∧
    p.HasAt (b+115) (packedBranchModule (b+115) (b+17)) ∧
    p.procs[b+129]? = some dedupSelectedTreeBody := by
  unfold packedRoundModule at hp
  have harith := Num.hasAt_append_right hp
  have hbuffer : p.HasAt (b+105)
      (packedRoundBufferModule (b+105) (b+1) ++
        (packedBranchModule (b+115) (b+17) ++ [dedupSelectedTreeBody])) := by
    suffices h : p.HasAt (b+1+(packedRoundArithmeticModule (b+1)).length)
        (packedRoundBufferModule (b+105) (b+1) ++
          (packedBranchModule (b+115) (b+17) ++ [dedupSelectedTreeBody])) by
      rwa [packedRoundArithmeticModule_length] at h
    exact Num.hasAt_append_right harith
  have hbranch : p.HasAt (b+115) (packedBranchModule (b+115) (b+17) ++ [dedupSelectedTreeBody]) :=
    Num.hasAt_append_right hbuffer
  have hdedup : p.HasAt (b+129) [dedupSelectedTreeBody] := Num.hasAt_append_right hbranch
  exact ⟨hp.head, Num.hasAt_append_left harith, Num.hasAt_append_left hbuffer,
    Num.hasAt_append_left hbranch, hdedup.head⟩

/-- Install the tree selector immediately after the packed round that
calls it. The graph initializer is supplied by the enclosing program. -/
@[expose] def packedSelectedRoundModule (guest : Program) (D b initGraph : ℕ) : List Stmt :=
  packedRoundModule b (b+130) initGraph ++ packedTreeSelectorModule guest D (b+130)

/-- A single procedure block provides both the entry and its selector. -/
theorem packedSelectedRoundModule_entries {p guest : Program} {D b initGraph : ℕ}
    (hp : p.HasAt b (packedSelectedRoundModule guest D b initGraph)) :
    p.HasAt b (packedRoundModule b (b+130) initGraph) ∧
      p.HasAt (b+130) (packedTreeSelectorModule guest D (b+130)) := by
  have hlen : (packedRoundModule b (b+130) initGraph).length = 130 := by
    simp only [packedRoundModule, List.length_append, packedRoundArithmeticModule_length]
    rfl
  unfold packedSelectedRoundModule at hp
  exact ⟨Num.hasAt_append_left hp, hlen ▸ Num.hasAt_append_right hp⟩

/-- Initialize the collection header and compact unit weights using
the copy and four-bit encoder already installed with the round. -/
@[expose] def packedInitialWeightsModule (b round : ℕ) : List Stmt :=
  [initCollectionBody, stagedInitialWeightSetup (round+107) (b+2),
    stridedUnitWeightBody (round+17)]

/-- Installation supplies the header and weight initialization contracts. -/
theorem packedInitialWeightsModule_contracts {p guest : Program} {w P b round D initGraph : ℕ}
    (hp : p.HasAt b (packedInitialWeightsModule b round))
    (hr : p.HasAt round (packedSelectedRoundModule guest D round initGraph))
    (hw : 10 ≤ w) (B : ℝ) :
    MeetsContract w p b (initCollectionContract w) ∧
      MeetsContract w p (b+1) (stagedInitialWeightContract w 4 P B) := by
  obtain ⟨hr',_⟩ := packedSelectedRoundModule_entries hr
  obtain ⟨_,ha,hb,_,_⟩ := packedRoundModule_entries hr'
  have hcopy := copyWords_meetsContract (w := w) (packedRoundArithmeticModule_helpers ha).1
  obtain ⟨_,_,hunit,_,_,_,_,hstore,hshift⟩ := packedRoundBufferModule_entries hb
  have hword : 16 < 2^w := (show 16 < 2^10 by decide).trans_le
    (Nat.pow_le_pow_right (by decide) hw)
  have hencode := denominator_meetsContract (by decide : 0 < 4) hw hunit
    (storeWord_meetsContract (by omega) (show Num.base 4 < 2^w from hword) hstore) hshift
  exact ⟨initCollection_meetsContract hp.head,
    stagedInitialWeightSetup_meetsContract B (hp.get (i := 1) (show 1 < 3 by decide))
      hencode (stridedUnitWeight_meetsContract (hp.get (i := 2) (show 2 < 3 by decide)) hcopy)⟩

/-- Run the compact collection controller from the installed header,
unit-weight, and round modules. Each live round supplies its contract
at the current state. -/
theorem packedCompactController_of_rounds
    {w init round D initGraph vCap eCap L P caller guestL sim src handle bound budget step : ℕ}
    {p guest : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C ρ : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ)
    (hp : p.HasAt init (packedInitialWeightsModule init round))
    (hr : p.HasAt round (packedSelectedRoundModule guest D round initGraph))
    (hbits : 10 ≤ w)
    (hnl : (SparseCore.nonLoopEdges G).Nonempty) (hw : 1 < 2^w)
    (hL : st.regs 127 = L) (hP : st.regs 95 = P) (h151 : st.regs 151 = handle)
    (hguestL : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hfit : bound < 2^w)
    (hwidth : 2*(2 : ℝ)^P < capacity 4 L) :
    let H := representativeGraph G ℓ
    let base := src+queryWeights H guestL
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let Inv := stagedRoundStateAtStride H vCap eCap 4 L P caller base s.1 handle bound L G.E s.2 ρ query st.mem
    let loopCost := (argsSize publishedRoundArgs+budget+10)*s.1+7
    st.regs 72 = H.n → st.regs 73 = H.m → 0 < H.m → queryHeap H guestL < 2^w →
    handle+1+s.1 ≤ base → ZeroFrom st.mem base →
    base+1+s.1+2*L+H.m*L+1+s.1*step ≤ bound →
    (∀ r, st.regs r < 2^w) →
    (∀ prepared : State, prepared.regs 81 = L → prepared.regs 82 = P →
      prepared.regs 91 = L → prepared.regs 104 = L →
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → prepared.regs r = st.regs r) →
      ∀ j < s.1, ∀ current : State, Inv j current →
        current.regs 0+(s.1-j)*step ≤ bound →
        (∀ r, current.regs r < 2^w) →
        (∀ r, 4 ≤ r → current.regs r = prepared.regs r) →
        current.regs 2 = j →
        MeetsContract w p round
          (stagedControllerRoundContract current
            (fun next => Inv (j+1) next ∧ next.regs 0+(s.1-(j+1))*step ≤ bound)
            j budget)) →
    ∃ o out cost, Runs w p ω (stagedCompactCollectionThen init (init+1) round (round+17)) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+s.1 ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle s.1 s.1 limit vCap eCap 4 L caller G.E s.2 ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ collectionHeaderAddress.size+20+
        (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
          (17*(s.1+1)+19)+17) := by
  obtain ⟨hi,hweights⟩ := packedInitialWeightsModule_contracts (P := P) hp hr hbits (1 : ℝ)
  obtain ⟨hround,_⟩ := packedSelectedRoundModule_entries hr
  obtain ⟨_,ha,_,_,_⟩ := packedRoundModule_entries hround
  have hcopy := copyWords_meetsContract (w := w) (packedRoundArithmeticModule_helpers ha).1
  exact stagedCompactController_of_rounds st G ℓ oracle C ρ 1 query hi hweights hcopy
    hnl hw hL hP h151 hguestL hsim hsrc hfit le_rfl (by simpa only [mul_one] using hwidth)

end MinCostFlow.LastLevelProgram
