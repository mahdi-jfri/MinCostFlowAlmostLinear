module

public import MinCostFlow.LastLevelProgram.StagedController
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Publishing the restored branch

The append round in Definition 5.8 (pages 19–20) restores the tree, writes
the named stretch blocks, and publishes the new collection pointer.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num SparseCore DynSpanner.Program

/-- Cost of initializing, restoring, and publishing one branch. -/
@[expose] def stagedAppendModelCost (G : MGraph) (L count : ℕ) : ℕ :=
  56*L+75+(130*G.n+563*count+139)+argsSize (stagedBranchPayloadArgs (.reg 55))+
    20+2*((17*L+92)*G.m+51)+129

/-- The append cost is linear in the number of original edges and the
caller limb count when the graph is connected and the round count is at most twice its edge count. -/
theorem stagedAppendModelCost_le (G : MGraph) (L count : ℕ)
    (hn : G.n ≤ G.m+1) (hc : count ≤ 2*G.m) :
    stagedAppendModelCost G L count ≤ (90*L+2200)*(G.m+1) := by
  have ha : argsSize (stagedBranchPayloadArgs (.reg 55)) ≤ 300 := by decide
  have hv := Nat.mul_le_mul_left 130 hn
  have hcount := Nat.mul_le_mul_left 563 hc
  have hm := Nat.le_succ G.m
  have hlimb : 56*L ≤ 56*L*(G.m+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hscan := Nat.mul_le_mul_left (34*L) hm
  change 34*L*G.m ≤ 34*L*(G.m+1) at hscan
  have hs : 34*L*(G.m+1)+56*L*(G.m+1) = 90*L*(G.m+1) := by ring
  unfold stagedAppendModelCost
  simp only [Nat.add_mul, Nat.mul_add, ← Nat.mul_assoc] at ⊢
  simp only [Nat.mul_add, ← Nat.mul_assoc] at hv hcount hlimb hscan hs
  norm_num at ⊢
  omega

/-- The round count in Definition 5.8 (pages 19–20) is at most twice
the number of retained edges, so publication fits the original edge budget. -/
theorem stagedAppendModelCost_model_le (G : MGraph) (ℓ : ℕ → ℝ) (L : ℕ)
    (hG : G.IsValid) (hn : G.n ≤ G.m+1) :
    stagedAppendModelCost G L (lastMWUK (representativeGraph G ℓ)) ≤
      (90*L+2200)*(G.m+1) := by
  apply stagedAppendModelCost_le G L _ hn
  let H := representativeGraph G ℓ
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hlog : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hfloor : lastMWUK H ≤ 2*H.m := by
    unfold lastMWUK
    apply Nat.floor_le_of_le
    push_cast
    exact mul_le_of_le_one_right (by positivity) hlog
  exact hfloor.trans (Nat.mul_le_mul_left 2 hm)

/-- Finish append from the verified unit and graph phases. The weight
pointer is the one installed before allocating either branch payload. -/
theorem stagedAppendModel_runs
    {w unit restore write bOps bEdge bSplit bBatch scatter publish translate scatterCopy copyBlock copy writeSource
      root serialize descriptor finish header publishSlot vCap eCap h L caller floor : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (count collection j vertices indices heap names : ℕ)
    (g guestL staging cursor repNames : ℕ) (original staged : ℕ → ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (hG : G.IsValid)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hw : 16 ≤ 2^w)
    (h13 : st.regs 13 = count) (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (h59 : st.regs 59 = indices) (h55 : st.regs 55 = L)
    (h56 : st.regs 56 = collection) (h57 : st.regs 57 = j)
    (h40 : st.regs 40 = vertices) (h61 : st.regs 61 = G.m) (h62 : st.regs 62 = names)
    (h19 : st.regs 19 = L) (h20 : st.regs 20 = heap) (hLPos : 0 < L)
    (hunit : MeetsContract w p unit (denominatorContract w h))
    (hrestore : p.procs[restore]? = some (branchEdgeRecordsBody write))
    (hwriteRecord : p.procs[write]? = some writeBranchEdgeRecordBody)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hops : p.HasAt bOps dgOpsProcs)
    (hgraph : DynGraphAt original g vCap eCap G)
    (hgraphEnd : g+dynGraphSize vCap eCap ≤ staging)
    (hstageFrame : ∀ a < staging, staged a = original a)
    (h28 : st.regs 28 = repNames) (h5 : st.regs 5 = staging) (h12 : st.regs 12 = cursor)
    (h43 : st.regs 43 = G.n) (h44 : st.regs 44 = dgVListBase g vCap)
    (hgraphWords : ∀ x ∈ [vCap,eCap,G.n,dgVListBase g vCap], x < 2^w)
    (T : MGraph)
    (hscatter : p.procs[scatter]? = some (namedStretchBody translate scatterCopy))
    (htranslate : p.procs[translate]? = some (stretchSourceBody writeSource))
    (hwrite : p.procs[writeSource]? = some writeStretchSourceBody)
    (hscatterCopy : p.procs[scatterCopy]? = some (scatterBranchStretchBody copyBlock))
    (hcopyBlock : p.procs[copyBlock]? = some (copyBranchStretchBody copy))
    (hcopy : p.HasAt copy [copyWords])
    (hpublish : p.procs[publish]? = some (publishRootedBranchBody root serialize))
    (hroot : p.procs[root]? = some writeRootBitBody)
    (hserialize : p.procs[serialize]? = some (serializeBranchBody descriptor finish))
    (hdescriptor : p.procs[descriptor]? = some writeStretchDescriptorBody)
    (hfinish : p.procs[finish]? = some (finishBranchBody header publishSlot))
    (hheader : p.procs[header]? = some writeBranchHeaderBody)
    (hslotWriter : p.procs[publishSlot]? = some publishBranchBody) :
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    let start := heap+(H.n-1)*L
    let afterStretch := start+H.m*edgeStretchSpace L
    let numericEnd := afterStretch+H.m*narrowWeightSpace L
    let records := numericEnd+2*L
    let ptr := records+3*count
    let tree := ptr+4
    let roots := tree+dynGraphSize vCap eCap
    let addresses := roots+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    st.regs 0 = H.n → st.regs 1 = H.m → stop < 2^w →
    floor ≤ numericEnd → st.regs 16 = numericEnd → ZeroFrom st.mem numericEnd →
    collection+1+j < ptr →
    indices+G.m ≤ staging → names+G.m ≤ staging → vertices+H.n ≤ staging →
    (∀ i < H.n, original (vertices+i) = vertexName H i) →
    (∀ i < G.m, original (indices+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, original (names+i) = edgeName G i) →
    G.m ≤ eCap →
    st.regs 23 = P → P < 2^w → 2*(2 : ℝ)^P < Num.capacity h L →
    oracle H (LSF.safeLen H ℓ) (weights P (roundedScale C H) query j) = restoreTreeNames H T →
    retainedStagedTreeAt H T (staging+queryWeights H guestL) (cursor+1+H.m) count staged st.mem →
    (∀ i ∈ T.E, i < H.m) →
    repNames+H.m ≤ staging+queryWeights H guestL → vertices+H.n ≤ staging+queryWeights H guestL →
    (∀ i < H.m, staged (repNames+i) = edgeName H i ∧
      staged (staging+i) = (indexedGraph H).tail i ∧
      staged (staging+(H.m+i)) = (indexedGraph H).head i) →
    (∀ v < H.n, staged (vertices+v) = vertexName H v) →
    staging+queryWeights H guestL ≤ cursor+1+H.m → cursor+1+H.m+H.n ≤ numericEnd →
    (∀ i < H.m, Valid st.mem (roundStretchAddr start L i) h L ∧
      fixVal st.mem (roundStretchAddr start L i) h L P =
        query (weights P (roundedScale C H) query j) (edgeName H i)) →
    ∃ layout out cl cost,
      Runs w p ω installStagedOutputLayout st .normal layout cl ∧ layout.mem = st.mem ∧
      cl ≤ argsSize (stagedOutputArgs (.reg 0) (.reg 1) (.reg 19) (.reg 20))+9 ∧
      Runs w p ω (stagedBranchAppendBody unit restore (bBatch+dgIdxInitFromLists) scatter publish)
        layout .normal out cost ∧ out.regs 54 = stop ∧
      out.regs 38 = afterStretch+narrowWeightSpace L-L ∧
      ZeroFrom out.mem stop ∧ out.mem (collection+1+j) = ptr ∧
      BranchWithin out.mem ptr floor stop vCap eCap L G.E ∧
      MinRatio.LSFAt out.mem ptr vCap eCap h L caller G.E branch ∧
      (∀ a < numericEnd, a ≠ collection+1+j → out.mem a = st.mem a) ∧
      cost ≤ stagedAppendModelCost G L count := by
  intro H P query branch start afterStretch numericEnd records ptr tree roots addresses stop hn hm hfit hfloor hEnd hzero hslot hi hnEnd hvEnd hvnames
    hindices hnames hmCap hP hPword hwidth hmodel htree hindex hrepEnd hvertEnd hedges hverts hsep hdest
    hvalues
  have hfRoots : roots < 2^w := by dsimp [stop,addresses] at hfit; omega
  have hnWord : H.n < 2^w := by
    dsimp [roots,tree,ptr,records,dynGraphSize] at hfRoots
    omega
  have hnumWord : numericEnd < 2^w := by omega
  have hend : afterStretch ≤ numericEnd := Nat.le_add_right _ _
  have hstageEnd : staging ≤ numericEnd := by
    have h₁ : staging ≤ staging+queryWeights H guestL := Nat.le_add_right _ _
    omega
  have horiginal a (ha : a < staging) : st.mem a = original a :=
    (retainedStagedTreeAt_frame htree (Nat.le_add_right _ _) a ha).trans (hstageFrame a ha)
  have hnumFit : numericEnd+2*L < 2^w := by
    dsimp [roots,tree,ptr,records] at hfRoots
    omega
  have heCap : eCap < 2^w := by
    dsimp [stop,addresses] at hfit
    omega
  have hL : L < 2^w := by omega
  obtain ⟨e,he⟩ := hnl
  obtain ⟨heRep,_,_⟩ := representativeGraph_shortest (ℓ := ℓ) he
  have hmPos : 0 < H.m := Finset.card_pos.mpr ⟨_,heRep⟩
  obtain ⟨layout,cl,hLayout,hLayoutMem,h16L,hzeroL,h36,h37,h38,h39,hkeep,hcl⟩ :=
    stagedController_appendLayout (ω := ω) st hn hm h19 h20 hnWord hmPos hLPos (by omega)
      hEnd hzero hnumWord
  have keeps r (hr : r ∉ ([36,37,38,39] : List ℕ)) := hkeep r hr
  have hnPos : 0 < H.n := by
    have hn := representativeGraph_two_le_n G ℓ hmPos
    change 2 ≤ H.n at hn
    omega
  have hv : vertices < numericEnd := by omega
  have hstretch : edgeStretchSpace L ≤ H.m*edgeStretchSpace L :=
    Nat.le_mul_of_pos_left _ hmPos
  have hstride : edgeStretchSpace L < 2^w := by
    have h := (show afterStretch ≤ numericEnd from Nat.le_add_right _ _)
    dsimp [afterStretch] at h
    omega
  have hsrc : start+edgeStretchSpace L-L < 2^w := by
    have h := (show afterStretch ≤ numericEnd from Nat.le_add_right _ _)
    dsimp [afterStretch] at h
    omega
  have hnCap : H.n ≤ vCap := by
    have hsub : H.V ⊆ Finset.range vCap := fun u hu =>
      Finset.mem_range.mpr (hV u ((representativeGraph_subgraph hG ℓ).1 hu))
    change H.V.card ≤ vCap
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hroom : records+3*H.n < 2^w := by
    dsimp [roots,tree,ptr] at hfRoots
    unfold dynGraphSize at hfRoots
    omega
  have hphases := stagedController_unitGraph_runs (ω := ω) layout G T ℓ guestL staging cursor count
    repNames vertices numericEnd g vCap eCap original staged oracle C j ⟨e,he⟩ hrestore hwriteRecord
    hbatch hedge hops hunit hw hgraph (hgraphEnd.trans hstageEnd)
    (fun a ha => (congrFun hLayoutMem a).trans (horiginal a (ha.trans_le hgraphEnd))) h16L
    ((keeps 55 (by decide)).trans h55) ((keeps 28 (by decide)).trans h28)
    ((keeps 5 (by decide)).trans h5) ((keeps 40 (by decide)).trans h40)
    ((keeps 12 (by decide)).trans h12) ((keeps 13 (by decide)).trans h13)
    ((keeps 41 (by decide)).trans h41) ((keeps 42 (by decide)).trans h42)
    ((keeps 43 (by decide)).trans h43) ((keeps 44 (by decide)).trans h44)
    hgraphWords hzeroL ((keeps 23 (by decide)).trans hP) hPword hwidth hmodel
    ((keeps 1 (by decide)).trans hm) (hLayoutMem.symm ▸ htree) hindex hrepEnd
    hvertEnd hedges hverts hsep hdest hroom hfRoots
  obtain ⟨afterUnit,graph,cu,cg,hu,hg,hT,hF,hR,hz,hvalid,hval,huFrame,hgFrame,h16,h60,hregs,hbudget⟩ :=
    hphases
  have keep r (h₁ : r ≠ 16) (h₂ : r ≠ 45) (h₃ : r ≠ 46) (h₄ : r ≠ 60) (h₅ : r ≠ 67) :=
    hregs r h₁ h₂ h₃ h₄ h₅
  have hframe' a (ha : a < numericEnd) : graph.mem a = st.mem a :=
    (hgFrame a (by omega)).trans ((huFrame a ha).trans (congrFun hLayoutMem a))
  have ha : records ≤ addresses := by dsimp [addresses,roots,tree,ptr]; omega
  obtain ⟨huEnd,hvalid',hval',hvalues'⟩ :=
    stagedController_scatterSources (numeric := st) (layout := layout) (graph := graph)
      (unit := afterUnit) hend le_rfl ha hLayoutMem huFrame hgFrame hvalid hval hvalues
  obtain ⟨out,co,ho,hptr,hframe,hzero,hspan,hbranch,hstop,hweight,hcost⟩ :=
    stagedBranchOutput_model_runs (ω := ω) (caller := caller) (floor := floor) (oldEnd := numericEnd)
      graph oracle C G ℓ records count collection j vertices indices (start+edgeStretchSpace L-L)
      (edgeStretchSpace L) (numericEnd+L) ⟨e,he⟩ h16
      ((keep 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 13 (by decide)).trans h13))
      ((keep 41 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 41 (by decide)).trans h41))
      ((keep 42 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 42 (by decide)).trans h42)) (by omega)
      hG hconn hV (by omega) hfloor (by dsimp [records]; omega) hE
      ((keep 59 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 59 (by decide)).trans h59))
      ((keep 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 1 (by decide)).trans hm))
      ((keep 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h36)
      ((keep 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h37) h60
      ((keep 61 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 61 (by decide)).trans h61))
      ((keep 55 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 55 (by decide)).trans h55))
      ((keep 56 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 56 (by decide)).trans h56))
      ((keep 57 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 57 (by decide)).trans h57))
      ((keep 40 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 40 (by decide)).trans h40))
      names ((keep 62 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((keeps 62 (by decide)).trans h62))
      hscatter htranslate hwrite hscatterCopy hcopyBlock hcopy hpublish hroot
      hserialize hdescriptor hfinish hheader hslotWriter
      (fun i hi' => by
        change i < H.n at hi'
        exact (hframe' _ (by omega)).trans ((horiginal _ (by omega)).trans (hvnames i hi')))
      hslot (by have : numericEnd ≤ addresses := by dsimp [records] at ha; omega
                exact hv.trans_le this) hfit hz hT hF hR (hmCap.trans_lt heCap) hsrc hstride hL
      (by dsimp [records] at ha; omega) (by dsimp [records] at ha; omega)
      hmCap heCap.le (fun i hi' => (hframe' _ (by omega)).trans ((horiginal _ (by omega)).trans (hindices i hi')))
      (fun i hi' => (hframe' _ (by omega)).trans ((horiginal _ (by omega)).trans (hnames i hi'))) huEnd hvalid' hval' hvalues'
  have htail := runs_seq_iff.mpr (Or.inr ⟨graph,cg,co,hg,ho,rfl⟩)
  refine ⟨layout,out,cl,cu+(cg+co+1)+1,hLayout,hLayoutMem,hcl,runs_seq_iff.mpr (Or.inr ⟨afterUnit,cu,_,hu,htail,rfl⟩),
    hstop,hweight.trans ((keep 38 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h38),hzero,hptr,hspan,hbranch,?_,by unfold stagedAppendModelCost; omega⟩
  intro a hbelow hne
  exact (hframe a (Or.inl hbelow) hne).trans ((hgFrame a (by omega)).trans ((huFrame a hbelow).trans (congrFun hLayoutMem a)))

/-- The fixed branch procedures restore the named graph, scatter its
stretches, and publish its header and collection slot. -/
@[expose] def packedBranchModule (b copy : ℕ) : List Stmt :=
  [branchEdgeRecordsBody (b+1),
   writeBranchEdgeRecordBody,
   namedStretchBody (b+3) (b+5),
   stretchSourceBody (b+4),
   writeStretchSourceBody,
   scatterBranchStretchBody (b+6),
   copyBranchStretchBody copy,
   publishRootedBranchBody (b+8) (b+9),
   writeRootBitBody,
   serializeBranchBody (b+10) (b+11),
   writeStretchDescriptorBody,
   finishBranchBody (b+12) (b+13),
   writeBranchHeaderBody,
   publishBranchBody]

/-- Every branch operation is installed at its call address. -/
theorem packedBranchModule_entries {p : Program} {b copy : ℕ}
    (hp : p.HasAt b (packedBranchModule b copy)) :
    p.procs[b]? = some (branchEdgeRecordsBody (b+1)) ∧
    p.procs[b+1]? = some (writeBranchEdgeRecordBody) ∧
    p.procs[b+2]? = some (namedStretchBody (b+3) (b+5)) ∧
    p.procs[b+3]? = some (stretchSourceBody (b+4)) ∧
    p.procs[b+4]? = some (writeStretchSourceBody) ∧
    p.procs[b+5]? = some (scatterBranchStretchBody (b+6)) ∧
    p.procs[b+6]? = some (copyBranchStretchBody copy) ∧
    p.procs[b+7]? = some (publishRootedBranchBody (b+8) (b+9)) ∧
    p.procs[b+8]? = some (writeRootBitBody) ∧
    p.procs[b+9]? = some (serializeBranchBody (b+10) (b+11)) ∧
    p.procs[b+10]? = some (writeStretchDescriptorBody) ∧
    p.procs[b+11]? = some (finishBranchBody (b+12) (b+13)) ∧
    p.procs[b+12]? = some (writeBranchHeaderBody) ∧
    p.procs[b+13]? = some (publishBranchBody) := by
  have atIndex (i : ℕ) (hi : i < 14) := hp.get (i := i) hi
  exact ⟨atIndex 0 (by decide),atIndex 1 (by decide),atIndex 2 (by decide),
    atIndex 3 (by decide),atIndex 4 (by decide),atIndex 5 (by decide),
    atIndex 6 (by decide),atIndex 7 (by decide),atIndex 8 (by decide),
    atIndex 9 (by decide),atIndex 10 (by decide),atIndex 11 (by decide),
    atIndex 12 (by decide),atIndex 13 (by decide)⟩

/-- Append the model branch from compact caller-width stretch and weight tables. -/
theorem stagedPackedAppendModel_runs
    {w unit store shift branchEntry bOps bEdge bSplit bBatch copy vCap eCap h L caller : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (count collection j rounds vertices indices start names : ℕ)
    (g guestL staging cursor repNames scale : ℕ) (original staged : ℕ → ℕ)
    (hnl : (nonLoopEdges G).Nonempty) (hG : G.IsValid)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hw : 16 ≤ 2^w)
    (h13 : st.regs 13 = count) (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (h59 : st.regs 59 = indices) (h55 : st.regs 55 = L)
    (h56 : st.regs 56 = collection) (h57 : st.regs 57 = j)
    (h40 : st.regs 40 = vertices) (h61 : st.regs 61 = G.m) (h62 : st.regs 62 = names)
    (h19 : st.regs 19 = L) (hLPos : 0 < L)
    (hh : 0 < h) (hbits : 2*h+2 ≤ w) (hlimb : Num.base h < 2^w)
    (hunitBody : p.procs[unit]? = some (denominatorBody store shift))
    (hstore : p.procs[store]? = some (storeWordBody h))
    (hshift : p.HasAt shift (shiftLeftModule shift h))
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hops : p.HasAt bOps dgOpsProcs)
    (hgraph : DynGraphAt original g vCap eCap G)
    (hgraphEnd : g+dynGraphSize vCap eCap ≤ staging)
    (hstageFrame : ∀ a < staging, staged a = original a)
    (h28 : st.regs 28 = repNames) (h5 : st.regs 5 = staging) (h12 : st.regs 12 = cursor)
    (h43 : st.regs 43 = G.n) (h44 : st.regs 44 = dgVListBase g vCap)
    (T : MGraph)
    (hcopy : p.HasAt copy [copyWords])
    (hbranchEntry : p.HasAt branchEntry (packedBranchModule branchEntry copy)) :
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    let afterStretch := start+H.m*L
    let numericEnd := afterStretch+H.m*L
    let records := numericEnd+2*L
    let ptr := records+3*count
    let tree := ptr+4
    let roots := tree+dynGraphSize vCap eCap
    let addresses := roots+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    st.regs 1 = H.m → stop < 2^w →
    st.regs 36 = start → st.regs 37 = L → st.regs 38 = afterStretch →
    collection+1+rounds ≤ staging → j < rounds →
    st.regs 16 = numericEnd → ZeroFrom st.mem numericEnd →
    indices+G.m ≤ staging → names+G.m ≤ staging → vertices+H.n ≤ staging →
    (∀ i < H.n, original (vertices+i) = vertexName H i) →
    (∀ i < G.m, original (indices+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, original (names+i) = edgeName G i) →
    st.regs 23 = P → P < 2^w → 2*(2 : ℝ)^P < Num.capacity h L →
    (scale : ℝ) = roundedScale C H →
    oracle H (LSF.safeLen H ℓ) (weights P (roundedScale C H) query j) = restoreTreeNames H T →
    retainedStagedTreeAt H T (staging+queryWeights H guestL) (cursor+1+H.m) count staged st.mem →
    (∀ i ∈ T.E, i < H.m) →
    repNames+H.m ≤ staging+queryWeights H guestL → vertices+H.n ≤ staging+queryWeights H guestL →
    (∀ i < H.m, staged (repNames+i) = edgeName H i ∧
      staged (staging+i) = (indexedGraph H).tail i ∧
      staged (staging+(H.m+i)) = (indexedGraph H).head i) →
    (∀ v < H.n, staged (vertices+v) = vertexName H v) →
    staging+queryWeights H guestL ≤ cursor+1+H.m → cursor+1+H.m+H.n ≤ numericEnd →
    (∀ i < H.m, Valid st.mem (start+i*L) h L ∧
      fixVal st.mem (start+i*L) h L P =
        query (weights P ((scale : ℤ) : ℝ) query j) (edgeName H i)) →
    ∃ out cost,
      Runs w p ω (stagedBranchAppendBody unit branchEntry (bBatch+dgIdxInitFromLists) (branchEntry+2) (branchEntry+7))
        st .normal out cost ∧ out.regs 54 = stop ∧
      out.regs 38 = afterStretch ∧
      ZeroFrom out.mem stop ∧ out.mem (collection+1+j) = ptr ∧
      BranchWithin out.mem ptr (collection+1+rounds) stop vCap eCap L G.E ∧
      MinRatio.LSFAt out.mem ptr vCap eCap h L caller G.E branch ∧
      (∀ a < numericEnd, a ≠ collection+1+j → out.mem a = st.mem a) ∧
      cost ≤ stagedAppendModelCost G L count := by
  intro H P query branch afterStretch numericEnd records ptr tree roots addresses stop hm hfit h36 h37 h38 hcollection hj hEnd hzero hi hnEnd hvEnd hvnames
    hindices hnames hP hPword hwidth hscale hmodel htree hindex hrepEnd hvertEnd hedges hverts hsep hdest
    hvalues
  obtain ⟨hrestore,hwriteRecord,hscatter,htranslate,hwrite,hscatterCopy,hcopyBlock,
    hpublish,hroot,hserialize,hdescriptor,hfinish,hheader,hslotWriter⟩ :=
    packedBranchModule_entries hbranchEntry
  rw [Int.cast_natCast,hscale] at hvalues
  have hfRoots : roots < 2^w := by dsimp [stop,addresses] at hfit; omega
  have hnumWord : numericEnd < 2^w := by omega
  have hend : afterStretch ≤ numericEnd := Nat.le_add_right _ _
  have hstageEnd : staging ≤ numericEnd := by
    have h₁ : staging ≤ staging+queryWeights H guestL := Nat.le_add_right _ _
    omega
  have hfloor : collection+1+rounds ≤ numericEnd := hcollection.trans hstageEnd
  have hslot : collection+1+j < ptr := by
    dsimp only [ptr,records]
    omega
  have hV := hgraph.2.1
  have hE := hgraph.2.2.1
  have hnCapOrig : G.n ≤ vCap := by
    have hs : G.V ⊆ Finset.range vCap := fun v hv => Finset.mem_range.mpr (hV v hv)
    simpa only [MGraph.n,Finset.card_range] using Finset.card_le_card hs
  have hmCap : G.m ≤ eCap := by
    have hs : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hE e he)
    simpa only [MGraph.m,Finset.card_range] using Finset.card_le_card hs
  have hgraphWords : ∀ x ∈ [vCap,eCap,G.n,dgVListBase g vCap], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold dynGraphSize at hgraphEnd
    have hvWord : vCap < 2^w := by omega
    have heWord : eCap < 2^w := by omega
    have hlistWord : dgVListBase g vCap < 2^w := by
      unfold dgVListBase
      omega
    rcases hx with rfl | rfl | rfl | rfl
    · exact hvWord
    · exact heWord
    · exact hnCapOrig.trans_lt hvWord
    · exact hlistWord
  have horiginal a (ha : a < staging) : st.mem a = original a :=
    (retainedStagedTreeAt_frame htree (Nat.le_add_right _ _) a ha).trans (hstageFrame a ha)
  have hnumFit : numericEnd+2*L < 2^w := by
    dsimp [roots,tree,ptr,records] at hfRoots
    omega
  have heCap : eCap < 2^w := by
    dsimp [stop,addresses] at hfit
    omega
  have hL : L < 2^w := by omega
  obtain ⟨e,he⟩ := hnl
  obtain ⟨heRep,_,_⟩ := representativeGraph_shortest (ℓ := ℓ) he
  have hmPos : 0 < H.m := Finset.card_pos.mpr ⟨_,heRep⟩
  have hnPos : 0 < H.n := (by decide : 0 < 2).trans_le (representativeGraph_two_le_n G ℓ hmPos)
  have hv : vertices < numericEnd := by omega
  have hsrc : start < 2^w := by dsimp [numericEnd,afterStretch] at hnumWord; omega
  have hnCap : H.n ≤ vCap := by
    have hsub : H.V ⊆ Finset.range vCap := fun u hu =>
      Finset.mem_range.mpr (hV u ((representativeGraph_subgraph hG ℓ).1 hu))
    change H.V.card ≤ vCap
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hroom : records+3*H.n < 2^w := by
    dsimp [roots,tree,ptr] at hfRoots
    unfold dynGraphSize at hfRoots
    omega
  have hunit := denominator_meetsContract hh hbits hunitBody
    (storeWord_meetsContract (by omega) hlimb hstore) hshift
  have hphases := stagedController_unitGraph_runs (ω := ω) st G T ℓ guestL staging cursor count
    repNames vertices numericEnd g vCap eCap original staged oracle C j ⟨e,he⟩ hrestore hwriteRecord
    hbatch hedge hops hunit hw hgraph (hgraphEnd.trans hstageEnd)
    (fun a ha => horiginal a (ha.trans_le hgraphEnd)) hEnd
    h55 h28
    h5 h40
    h12 h13
    h41 h42
    h43 h44
    hgraphWords hzero hP hPword hwidth hmodel
    hm htree hindex hrepEnd
    hvertEnd hedges hverts hsep hdest hroom hfRoots
  obtain ⟨afterUnit,graph,cu,cg,hu,hg,hT,hF,hR,hz,hvalid,hval,huFrame,hgFrame,h16,h60,hregs,hbudget⟩ :=
    hphases
  have keep r (h₁ : r ≠ 16) (h₂ : r ≠ 45) (h₃ : r ≠ 46) (h₄ : r ≠ 60) (h₅ : r ≠ 67) :=
    hregs r h₁ h₂ h₃ h₄ h₅
  have hframe' a (ha : a < numericEnd) : graph.mem a = st.mem a :=
    (hgFrame a (by omega)).trans (huFrame a ha)
  have ha : records ≤ addresses := by dsimp [addresses,roots,tree,ptr]; omega
  obtain ⟨huEnd,hvalid',hval',hvalues'⟩ :=
    stagedController_packedScatterSources (packed := st) (graph := graph)
      (unit := afterUnit) hend le_rfl ha huFrame hgFrame hvalid hval hvalues
  obtain ⟨out,co,ho,hptr,hframe,hzero,hspan,hbranch,hstop,hweight,hcost⟩ :=
    stagedBranchOutput_model_runs (ω := ω) (caller := caller) (floor := collection+1+rounds) (oldEnd := numericEnd)
      graph oracle C G ℓ records count collection j vertices indices start
      L (numericEnd+L) ⟨e,he⟩ h16
      ((keep 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13)
      ((keep 41 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h41)
      ((keep 42 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h42) (by omega)
      hG hconn hV (by omega) hfloor (by dsimp [records]; omega) hE
      ((keep 59 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h59)
      ((keep 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm)
      ((keep 36 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h36)
      ((keep 37 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h37) h60
      ((keep 61 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h61)
      ((keep 55 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h55)
      ((keep 56 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h56)
      ((keep 57 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h57)
      ((keep 40 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h40)
      names ((keep 62 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h62)
      hscatter htranslate hwrite hscatterCopy hcopyBlock hcopy hpublish hroot
      hserialize hdescriptor hfinish hheader hslotWriter
      (fun i hi' => by
        change i < H.n at hi'
        exact (hframe' _ (by omega)).trans ((horiginal _ (by omega)).trans (hvnames i hi')))
      hslot (by have : numericEnd ≤ addresses := by dsimp [records] at ha; omega
                exact hv.trans_le this) hfit hz hT hF hR (hmCap.trans_lt heCap) hsrc hL hL
      (by dsimp [records] at ha; omega) (by dsimp [records] at ha; omega)
      hmCap heCap.le (fun i hi' => (hframe' _ (by omega)).trans ((horiginal _ (by omega)).trans (hindices i hi')))
      (fun i hi' => (hframe' _ (by omega)).trans ((horiginal _ (by omega)).trans (hnames i hi'))) huEnd hvalid' hval' hvalues'
  have htail := runs_seq_iff.mpr (Or.inr ⟨graph,cg,co,hg,ho,rfl⟩)
  refine ⟨out,cu+(cg+co+1)+1,runs_seq_iff.mpr (Or.inr ⟨afterUnit,cu,_,hu,htail,rfl⟩),
    hstop,hweight.trans ((keep 38 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h38),hzero,hptr,hspan,hbranch,?_,by unfold stagedAppendModelCost; omega⟩
  intro a hbelow hne
  exact (hframe a (Or.inl hbelow) hne).trans ((hgFrame a (by omega)).trans (huFrame a hbelow))

/-- A bound on the final cursor covers the intermediate numeric
allocations and the fresh descriptor word after the published branch. -/
theorem stagedAppendModel_allocationBounds (H : MGraph)
    (L count vCap eCap heap bound w : ℕ) :
    let start := heap+(H.n-1)*L
    let afterStretch := start+H.m*edgeStretchSpace L
    let numericEnd := afterStretch+H.m*narrowWeightSpace L
    let records := numericEnd+2*L
    let ptr := records+3*count
    let tree := ptr+4
    let roots := tree+dynGraphSize vCap eCap
    let addresses := roots+vCap+2
    let stop := addresses+eCap+eCap*L+eCap*L
    stop+1 ≤ bound → bound < 2^w →
    afterStretch < 2^w ∧ numericEnd ≤ stop ∧ stop < 2^w := by
  intro start afterStretch numericEnd records ptr tree roots addresses stop hfit hword
  have hn : numericEnd ≤ stop := by
    dsimp only [stop,addresses,roots,tree,ptr,records]
    omega
  exact ⟨(Nat.le_add_right _ _).trans_lt (hn.trans_lt (by omega)),hn,by omega⟩

end MinCostFlow.LastLevelProgram
