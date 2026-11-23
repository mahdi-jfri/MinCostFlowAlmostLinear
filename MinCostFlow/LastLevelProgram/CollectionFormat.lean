module

public import MinCostFlow.LastLevelProgram.StretchIndexScan
public import MinCostFlow.LastLevelProgram.StagedBranchAppend
public import MinCostFlow.LastLevelProgram.PackEdgeLoop
public import MinCostFlow.LastLevelProgram.PackVertexLoop
public import MinCostFlow.LastLevelProgram.RepresentativeRebuildInput
public import MinCostFlow.MinRatio.LastLevelContract
import Mathlib.Tactic
import WordRAM.Tactic

/-!
# Runtime formats for the last-level collection

Definition 5.8 (pages 19–20) rebuilds the collection from the graph
and its lengths. The update grid and the guest format are computed
before the collection loop, with the caller's length format passed
in runtime registers.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord Num DynSpanner.Program SparseCore Scaling.Machine

/-- Scatter the prepared vertex slots into the inverse index table.
The endpoint pass uses the same destination pointer. -/
def collectionVertexIndexArgs : List Expr :=
  [.reg 148,.reg 146,.reg 72]

/-- Index preparation records the compact representative ranks without
writing outside the inverse table. -/
theorem collectionVertexIndex_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G H : MGraph) (src dst : ℕ)
    (hs : st.regs 148 = src) (hd : st.regs 146 = dst) (hn : st.regs 72 = H.n)
    (hc : MeetsContract w p entry (packVertexIndexContract w g vCap eCap G H))
    (hw : ∀ a ∈ [src,dst,H.n], a < 2^w)
    (hpre : (packVertexIndexContract w g vCap eCap G H).pre [src,dst,H.n] st.mem) :
    ∃ out cost, Runs w p ω (.call 149 entry collectionVertexIndexArgs) st .normal out cost ∧
      (∀ v ∈ H.V, out.mem (dst+st.mem (dgExtToIntBase g vCap+v)) = vertexIndex H v) ∧
      (∀ a, a < dst ∨ dst+vCap ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 149 → out.regs r = st.regs r) ∧ cost ≤ 17*H.n+14 := by
  have ha : evalArgs w st collectionVertexIndexArgs = some [src,dst,H.n] := by
    simp [collectionVertexIndexArgs,evalArgs,Expr.eval,hs,hd,hn]
  obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 149) hc ha hw hpre ω
  obtain ⟨s,d,he,_,hindex,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl⟩ := he
  change cost ≤ 3+(17*H.n+10)+1 at hcost
  exact ⟨out,cost,hr,hindex,hframe,hregs,by omega⟩

/-- If the inverse table follows the dynamic graph and the name list,
index preparation establishes the complete endpoint packing premise. -/
theorem collectionEndpoint_pre_of_vertexIndex
    {w g vCap eCap : ℕ} {G H : MGraph} {mem out : ℕ → ℕ}
    (index names base : ℕ)
    (hG : DynGraphAt mem g vCap eCap G) (hsub : G.IsSubgraph H) (hvalid : H.IsValid)
    (hw : 1 < 2^w) (hn : H.n ≤ 2^w)
    (hg : g+dynGraphSize vCap eCap ≤ index) (hnames : names+H.m ≤ index)
    (hindex : index+vCap ≤ base) (hroom : base+queryLengths H < 2^w)
    (hnamesAt : ∀ i < H.m, mem (names+i) = edgeName H i)
    (hslots : ∀ v ∈ H.V, out (index+mem (dgExtToIntBase g vCap+v)) = vertexIndex H v)
    (hframe : ∀ a < index, out a = mem a) :
    (packEdgeContract w g vCap eCap G H).pre
      [dgETailSlotBase g vCap eCap,dgEHeadSlotBase g vCap eCap,index,names,base,base+H.m,H.m]
      out := by
  have hgraph : g+dynGraphSize vCap eCap ≤ base :=
    hg.trans ((Nat.le_add_right _ _).trans hindex)
  have hn' : names+H.m ≤ base := hnames.trans ((Nat.le_add_right _ _).trans hindex)
  have hG' := hG.of_agree (mem' := out) (fun a _ ha => hframe a (ha.trans_le hg))
  refine ⟨index,names,base,base+H.m,rfl,hG',hsub,hvalid,hw,hn,hgraph,hindex,hn',le_rfl,
    by unfold queryLengths at hroom; omega,?_,?_⟩
  · intro i hi
    exact (hframe _ (by omega)).trans (hnamesAt i hi)
  · intro v hv
    have hvc := hG.2.1 v (hsub.1 hv)
    rw [hframe (dgExtToIntBase g vCap+v) (by
      unfold dgExtToIntBase
      unfold dynGraphSize at hg
      omega)]
    exact hslots v hv

/-- Pack indexed representative endpoints at the start of the
persistent guest prefix. The source graph uses the caller's layout. -/
def collectionEndpointArgs : List Expr :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let region := add (add (.reg 0) (.const 4)) (mul (.const 7) (.reg 113))
  [add region (mul (.const 3) (.reg 114)),add region (mul (.const 4) (.reg 114)),
    .reg 146,.reg 100,.reg 141,add (.reg 141) (.reg 73),.reg 73]

/-- The dynamic graph footprint bounds the source addresses and the
prefix allocation bounds the destinations. -/
theorem collectionEndpointArgs_eval {w : ℕ} (st : State)
    (g vCap eCap index names base m : ℕ)
    (hg : st.regs 0 = g) (hv : st.regs 113 = vCap) (he : st.regs 114 = eCap)
    (hi : st.regs 146 = index) (hn : st.regs 100 = names)
    (hb : st.regs 141 = base) (hm : st.regs 73 = m)
    (hw : 7 < 2^w) (hgraph : g+dynGraphSize vCap eCap < 2^w)
    (hprefix : base+m < 2^w) :
    evalArgs w st collectionEndpointArgs =
      some [dgETailSlotBase g vCap eCap,dgEHeadSlotBase g vCap eCap,index,names,base,base+m,m] := by
  change g+(4+7*vCap+9*eCap) < 2^w at hgraph
  have h3 : 3 < 2^w := by omega
  have h4 : 4 < 2^w := by omega
  have hvg : 7*vCap < 2^w := by omega
  have hge3 : 3*eCap < 2^w := by omega
  have hge4 : 4*eCap < 2^w := by omega
  have hstart : g+4 < 2^w := by omega
  have hregion : g+4+7*vCap < 2^w := by omega
  have ht : g+4+7*vCap+3*eCap < 2^w := by omega
  have hh : g+4+7*vCap+4*eCap < 2^w := by omega
  simp only [collectionEndpointArgs,evalArgs,Expr.eval,BinOp.eval,hg,hv,he,hi,hn,hb,hm,
    hw,h3,h4,hvg,hge3,hge4,hstart,hregion,ht,hh,hprefix,ite_eq_left,
    dgETailSlotBase,dgEHeadSlotBase]

/-- Invoke representative endpoint packing and leave the original
graph and length tables intact below the guest prefix. -/
theorem collectionEndpoints_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (G H : MGraph) (index names base : ℕ)
    (hg : st.regs 0 = g) (hv : st.regs 113 = vCap) (he : st.regs 114 = eCap)
    (hi : st.regs 146 = index) (hn : st.regs 100 = names)
    (hb : st.regs 141 = base) (hm : st.regs 73 = H.m)
    (hw : 7 < 2^w) (hgraph : g+dynGraphSize vCap eCap < 2^w)
    (hprefix : base+H.m < 2^w)
    (hc : MeetsContract w p entry (packEdgeContract w g vCap eCap G H)) :
    let args := [dgETailSlotBase g vCap eCap,dgEHeadSlotBase g vCap eCap,
      index,names,base,base+H.m,H.m]
    (∀ a ∈ args, a < 2^w) → (packEdgeContract w g vCap eCap G H).pre args st.mem →
    ∃ out cost, Runs w p ω (.call 147 entry collectionEndpointArgs) st .normal out cost ∧
      (∀ i < H.m, out.mem (base+i) = (indexedGraph H).tail i ∧
        out.mem (base+(H.m+i)) = (indexedGraph H).head i) ∧
      (∀ a, a < base ∨ base+queryLengths H ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 147 → out.regs r = st.regs r) ∧
      cost ≤ argsSize collectionEndpointArgs+70*H.m+11 := by
  intro args hwords hpre
  have hargs := collectionEndpointArgs_eval st g vCap eCap index names base H.m
    hg hv he hi hn hb hm hw hgraph hprefix
  obtain ⟨out,cost,ret,hrun,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 147) hc hargs hwords hpre ω
  obtain ⟨ix,na,tl,hd,heq,_,hends,hframe⟩ := hpost
  simp only [List.cons.injEq,true_and,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl⟩ := heq
  change cost ≤ argsSize collectionEndpointArgs+(70*H.m+10)+1 at hcost
  refine ⟨out,cost,hrun,?_,?_,hregs,by omega⟩
  · intro i hi'
    simpa only [Nat.add_assoc] using hends i hi'
  · intro a h
    unfold queryLengths at h
    exact hframe a (by omega) (by omega)

/-- Build the inverse vertex table before packing the guest endpoints. -/
def collectionIndexAndEndpoints (vertices endpoints : ℕ) : Stmt :=
  .seq (.call 149 vertices collectionVertexIndexArgs)
    (.call 147 endpoints collectionEndpointArgs)

/-- Both passes preserve the input graph and write only the inverse
vertex table and the compact endpoint arrays. -/
theorem collectionIndexAndEndpoints_runs {w vertices endpoints g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G H : MGraph)
    (slots index names base : ℕ)
    (hg : st.regs 0 = g) (hv : st.regs 113 = vCap) (he : st.regs 114 = eCap)
    (hs : st.regs 148 = slots) (hi : st.regs 146 = index) (hn : st.regs 100 = names)
    (hb : st.regs 141 = base) (hm : st.regs 73 = H.m) (hnv : st.regs 72 = H.n)
    (hG : DynGraphAt st.mem g vCap eCap G) (hsub : G.IsSubgraph H) (hvalid : H.IsValid)
    (hw : 7 < 2^w) (hnFit : H.n < 2^w)
    (hslots : slots+H.n < 2^w) (hslotsSep : slots+H.n ≤ index)
    (hgraph : g+dynGraphSize vCap eCap ≤ index) (hnames : names+H.m ≤ index)
    (hindex : index+vCap ≤ base) (hroom : base+queryLengths H < 2^w)
    (hnamesAt : ∀ i < H.m, st.mem (names+i) = edgeName H i)
    (hslotsAt : ∀ i < H.n, st.mem (slots+i) = st.mem (dgExtToIntBase g vCap+vertexName H i))
    (hc : MeetsContract w p vertices (packVertexIndexContract w g vCap eCap G H))
    (hp : MeetsContract w p endpoints (packEdgeContract w g vCap eCap G H)) :
    ∃ out cost, Runs w p ω (collectionIndexAndEndpoints vertices endpoints) st .normal out cost ∧
      (∀ i < H.m, out.mem (base+i) = (indexedGraph H).tail i ∧
        out.mem (base+(H.m+i)) = (indexedGraph H).head i) ∧
      (∀ a, a < index ∨ base+queryLengths H ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 147 → r ≠ 149 → out.regs r = st.regs r) ∧
      cost ≤ 17*H.n+argsSize collectionEndpointArgs+70*H.m+26 := by
  have hiFit : index+vCap < 2^w := hindex.trans_lt ((Nat.le_add_right _ _).trans_lt hroom)
  have hwords : ∀ a ∈ [slots,index,H.n], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨mid,cv,hr,hslots',hframe,hregs,hcv⟩ :=
    collectionVertexIndex_runs (ω := ω) st G H slots index hs hi hnv hc hwords
      ⟨slots,index,rfl,hG,hsub,by omega,hslots,hiFit,Or.inl hslotsSep,hslotsAt⟩
  have hpre := collectionEndpoint_pre_of_vertexIndex index names base hG hsub hvalid
    (by omega) hnFit.le hgraph hnames hindex hroom hnamesAt hslots'
    (fun a ha => hframe a (Or.inl ha))
  have hwords' : ∀ a ∈ [dgETailSlotBase g vCap eCap,dgEHeadSlotBase g vCap eCap,
      index,names,base,base+H.m,H.m], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      unfold queryLengths at hroom <;>
      unfold dynGraphSize at hgraph <;>
      (try simp only [dgETailSlotBase,dgEHeadSlotBase]) <;> omega
  obtain ⟨out,cp,hpRun,hends,hframe',hregs',hcp⟩ :=
    collectionEndpoints_runs (ω := ω) mid G H index names base
      ((hregs _ (by decide)).trans hg) ((hregs _ (by decide)).trans hv)
      ((hregs _ (by decide)).trans he) ((hregs _ (by decide)).trans hi)
      ((hregs _ (by decide)).trans hn) ((hregs _ (by decide)).trans hb)
      ((hregs _ (by decide)).trans hm) hw (by omega)
      (by unfold queryLengths at hroom; omega) hp hwords' hpre
  exact ⟨out,cv+cp+1,runs_seq_iff.mpr (Or.inr ⟨mid,cv,cp,hr,hpRun,rfl⟩),hends,
    fun a ha => (hframe' a (ha.imp_left (by omega))).trans
      (hframe a (ha.imp_right (by omega))),
    fun r hr' hr'' => (hregs' r hr').trans (hregs r hr''),by omega⟩

/-- Compute the update grid, pack guest lengths, then set the simulation width. -/
def collectionFormatBody (scale precision format sim : ℕ) (D c : Expr) : Stmt :=
  .seq (collectionWeightScale scale precision D)
    (.seq (collectionGuestFormat format collectionGuestFormatArgs) (collectionSimulationWidth sim c))

/-- The runtime format pipeline links the three verified procedures.
It exposes the packed lengths and the registers used by each round. -/
theorem collectionFormat_runs {w scale precision format sim cap names lengths L P dst src : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (H : MGraph) (C : ℝ)
    (name : ℕ → ℕ) (D c : Expr) (c₀ : ℕ)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hnames : st.regs 100 = names) (hlengths : st.regs 99 = lengths)
    (hL : st.regs 144 = L) (hP : st.regs 145 = P)
    (hdst : st.regs 142 = dst) (hsrc : st.regs 141 = src)
    (hD : D.eval w st = some ⌈max 1 C⌉₊)
    (hscale : MeetsContract w p scale (scaleWordContract w H))
    (hprecision : MeetsContract w p precision (precisionWordContract w))
    (hformat : MeetsContract w p format
      (setupAndPackGuestContract w cap names lengths L P dst (src+queryLengths H) H C name))
    (hsim : MeetsContract w p sim (guestSimulationWidthContract w H.n))
    (hscaleWords : ∀ a ∈ [H.n,H.m,⌈max 1 C⌉₊], a < 2^w)
    (hscalePre : (scaleWordContract w H).pre [H.n,H.m,⌈max 1 C⌉₊] st.mem)
    (hscalePos : 0 < integerScale ⌈max 1 C⌉₊ H)
    (hscaleFit : 2*integerScale ⌈max 1 C⌉₊ H+2 < 2^w)
    (hw : 2 < 2^w) (haddr : src+queryLengths H < 2^w) :
    let F := setupAndPackGuestContract w cap names lengths L P dst (src+queryLengths H) H C name
    let args := [names,lengths,L,P,H.m,weightPrecision C H,dst,src+queryLengths H]
    let len := fun e => if e ∈ H.E then Num.fixVal st.mem (lengths+e*L) 4 L P else 0
    let N := roundQueryLimbs C H len
    (∀ a ∈ args, a < 2^w) → F.pre args st.mem →
    (∀ a ∈ [H.m,N,c₀], a < 2^w) →
    (guestSimulationWidthContract w H.n).pre [H.m,N,c₀] st.mem →
    (∀ ready : State, ready.regs 73 = H.m → ready.regs 74 = N →
      ready.regs 95 = weightPrecision C H → c.eval w ready = some c₀) →
    ∃ out cost, Runs w p ω (collectionFormatBody scale precision format sim D c) st .normal out cost ∧
      F.post args st.mem (out.regs 74) out.mem ∧
      out.regs 83 = roundQueryPrecision C H len ∧ out.regs 74 = N ∧
      out.regs 75 = lsstLSimMin c₀ H.n H.m N 1 ∧ out.regs 95 = weightPrecision C H ∧
      out.regs 107 = integerScale ⌈max 1 C⌉₊ H ∧
      (∀ r, r ∉ ([74,75,83,95,107] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ D.size+c.size+argsSize collectionGuestFormatArgs+F.cost args st.mem+
        40*(Nat.log 2 (H.n+2)+1)+40*weightPrecision C H+
        40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+167 := by
  classical
  intro F args len N hfWords hfPre hsWords hsPre hce
  obtain ⟨scaled,cs,hrs,h107,h95,hmem,hregs,hcs⟩ :=
    collectionWeightScale_runs (ω := ω) st H C D hn hm hD hscale hprecision
      hscaleWords hscalePre hscalePos hscaleFit
  have keep (r : ℕ) (h107' : r ≠ 107) (h95' : r ≠ 95) := hregs r h107' h95'
  have ha := collectionGuestFormatArgs_eval scaled H names lengths L P (weightPrecision C H) dst src
    ((keep _ (by decide) (by decide)).trans hnames) ((keep _ (by decide) (by decide)).trans hlengths)
    ((keep _ (by decide) (by decide)).trans hL) ((keep _ (by decide) (by decide)).trans hP)
    ((keep _ (by decide) (by decide)).trans hm) h95
    ((keep _ (by decide) (by decide)).trans hdst) ((keep _ (by decide) (by decide)).trans hsrc) hw haddr
  obtain ⟨packed,cf,hrf,hpost,h83,hregs',hcf⟩ :=
    collectionGuestFormat_runs (ω := ω) scaled H C name collectionGuestFormatArgs
      ((keep _ (by decide) (by decide)).trans hdst) hformat args ha hfWords (hmem.symm ▸ hfPre)
  have hpost' : F.post args st.mem (packed.regs 74) packed.mem := hmem ▸ hpost
  have hN : packed.regs 74 = N := hpost'.1
  have hQ : packed.regs 83 = roundQueryPrecision C H len := h83.trans hpost'.2.1
  have hm' := (hregs' 73 (by decide) (by decide)).trans ((keep _ (by decide) (by decide)).trans hm)
  have hp' := (hregs' 95 (by decide) (by decide)).trans h95
  obtain ⟨out,cw,hrw,h75,hmem',hregs'',hcw⟩ :=
    collectionSimulationWidth_runs (ω := ω) packed c H.m N c₀ hm' hN
      (hce packed hm' hN hp') hsim hsWords hsPre
  have htail := runs_seq_iff.mpr (Or.inr ⟨packed,cf,cw,hrf,hrw,rfl⟩)
  refine ⟨out,cs+(cf+cw+1)+1,runs_seq_iff.mpr (Or.inr ⟨scaled,cs,_,hrs,htail,rfl⟩),
    ?_,(hregs'' _ (by decide)).trans hQ,(hregs'' _ (by decide)).trans hN,h75,
    (hregs'' _ (by decide)).trans hp', (hregs'' _ (by decide)).trans
      ((hregs' _ (by decide) (by decide)).trans h107),?_,?_⟩
  · rwa [hregs'' 74 (by decide),hmem']
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact (hregs'' r hr.2.1).trans ((hregs' r hr.1 hr.2.2.1).trans (keep r hr.2.2.2.2 hr.2.2.2.1))
  · dsimp only [F, args] at *
    rw [hmem] at hcf
    omega

/-- Copy the caller's length pointer and format words from the
five-word initialization interface into the controller registers. -/
def loadCollectionCallerFormat : Stmt :=
  stagedAddressAssignments [99,127,144,145] [.reg 1,.reg 2,.reg 2,.reg 3]

/-- Loading the caller format preserves the graph pointer and heap.
The caller width is also the width of the host numeric work arrays. -/
theorem loadCollectionCallerFormat_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (lengths L P : ℕ) (hl : st.regs 1 = lengths)
    (hL : st.regs 2 = L) (hP : st.regs 3 = P) :
    ∃ out cost, Runs w p ω loadCollectionCallerFormat st .normal out cost ∧
      out.regs 99 = lengths ∧ out.regs 127 = L ∧ out.regs 144 = L ∧ out.regs 145 = P ∧
      out.mem = st.mem ∧
      (∀ r, r ∉ ([99,127,144,145] : List ℕ) → out.regs r = st.regs r) ∧ cost ≤ 13 := by
  let rs := [99,127,144,145]
  let es : List Expr := [.reg 1,.reg 2,.reg 2,.reg 3]
  have he (mid : State) (hf : ∀ r, r ∉ rs → mid.regs r = st.regs r) :
      evalArgs w mid es = some [lengths,L,L,P] := by
    simp only [es,evalArgs,Expr.eval,(hf _ (by decide)).trans hl,
      (hf _ (by decide)).trans hL,(hf _ (by decide)).trans hP]
  obtain ⟨out,cost,hr,hm,hregs,hcost⟩ :=
    addressAssignments_runs (p := p) (ω := ω) st rs es [lengths,L,L,P] (by decide) he
  refine ⟨out,cost,hr,?_,?_,?_,?_,hm,?_,hcost⟩
  all_goals rw [hregs]
  all_goals simp [rs,Function.update]
  intro r h99 h127 h144 h145
  simp [h99,h127,h144,h145]

/-- Rebuild from a prepared representative graph. Runtime format
selection precedes the collection loop. -/
def rebuildFormattedCollectionBody (scale precision format sim init weights round : ℕ)
    (D c : Expr) : Stmt :=
  .seq (collectionFormatBody scale precision format sim D c)
    (stagedPreparedCollectionBody init weights round)

/-- Compose the formatted controller with the collection run. The
returned pointer and layout are the collection's machine readout. -/
theorem rebuildFormattedCollection_runs
    {w scale precision format sim init weights round : ℕ}
    {p : Program} {ω : ℕ → Bool} (st ready : State) (D c : Expr)
    (formatCost base vCap eCap h L caller budget : ℕ)
    (E : Finset ℕ) (branches : ℕ × (ℕ → LSF))
    (hf : Runs w p ω (collectionFormatBody scale precision format sim D c)
      st .normal ready formatCost)
    (hb : ∃ o out cost, Runs w p ω (stagedPreparedCollectionBody init weights round)
      ready o out cost ∧ o.value = base ∧
      MinRatio.LSFCollectionAt out.mem base vCap eCap h L caller E branches ∧ cost ≤ budget) :
    ∃ o out cost, Runs w p ω (rebuildFormattedCollectionBody
      scale precision format sim init weights round D c) st o out cost ∧
      o.value = base ∧ MinRatio.LSFCollectionAt out.mem base vCap eCap h L caller E branches ∧
      cost ≤ formatCost+budget+1 := by
  obtain ⟨o,out,cost,hr,hbase,hlayout,hcost⟩ := hb
  exact ⟨o,out,formatCost+cost+1,runs_seq_iff.mpr (Or.inr ⟨ready,formatCost,cost,hf,hr,rfl⟩),
    hbase,hlayout,by omega⟩

/-- Build the persistent guest prefix and rebuild the collection.
The graph tables and the caller format have already been loaded. -/
def rebuildIndexedCollectionBody (vertices endpoints scale precision format sim init weights round : ℕ)
    (D c : Expr) : Stmt :=
  .seq (collectionIndexAndEndpoints vertices endpoints)
    (rebuildFormattedCollectionBody scale precision format sim init weights round D c)

/-- The packed endpoints are available to the format and collection
passes, which write subsequent portions of the prefix. -/
theorem rebuildIndexedCollection_runs
    {w vertices endpoints scale precision format sim init weights round g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G H : MGraph)
    (slots index names src h L caller budget : ℕ) (D c : Expr)
    (branches : ℕ × (ℕ → LSF))
    (hg : st.regs 0 = g) (hv : st.regs 113 = vCap) (he : st.regs 114 = eCap)
    (hs : st.regs 148 = slots) (hi : st.regs 146 = index) (hn : st.regs 100 = names)
    (hb : st.regs 141 = src) (hm : st.regs 73 = H.m) (hnv : st.regs 72 = H.n)
    (hG : DynGraphAt st.mem g vCap eCap G) (hsub : G.IsSubgraph H) (hvalid : H.IsValid)
    (hw : 7 < 2^w) (hnFit : H.n < 2^w)
    (hslots : slots+H.n < 2^w) (hslotsSep : slots+H.n ≤ index)
    (hgraph : g+dynGraphSize vCap eCap ≤ index) (hnames : names+H.m ≤ index)
    (hindex : index+vCap ≤ src) (hroom : src+queryLengths H < 2^w)
    (hnamesAt : ∀ i < H.m, st.mem (names+i) = edgeName H i)
    (hslotsAt : ∀ i < H.n, st.mem (slots+i) = st.mem (dgExtToIntBase g vCap+vertexName H i))
    (hc : MeetsContract w p vertices (packVertexIndexContract w g vCap eCap G H))
    (hp : MeetsContract w p endpoints (packEdgeContract w g vCap eCap G H)) :
    let body := rebuildFormattedCollectionBody scale precision format sim init weights round D c
    (∀ ready : State,
      (∀ i < H.m, ready.mem (src+i) = (indexedGraph H).tail i ∧
        ready.mem (src+(H.m+i)) = (indexedGraph H).head i) →
      (∀ a, a < index ∨ src+queryLengths H ≤ a → ready.mem a = st.mem a) →
      (∀ r, r ≠ 147 → r ≠ 149 → ready.regs r = st.regs r) →
      ∃ o out cost, Runs w p ω body ready o out cost ∧
        MinRatio.LSFCollectionAt out.mem o.value vCap eCap h L caller G.E branches ∧ cost ≤ budget) →
    ∃ o out cost, Runs w p ω (rebuildIndexedCollectionBody vertices endpoints
      scale precision format sim init weights round D c) st o out cost ∧
      MinRatio.LSFCollectionAt out.mem o.value vCap eCap h L caller G.E branches ∧
      cost ≤ 17*H.n+argsSize collectionEndpointArgs+70*H.m+27+budget := by
  intro body hnext
  obtain ⟨ready,ce,hr,hends,hframe,hregs,hce⟩ :=
    collectionIndexAndEndpoints_runs (ω := ω) st G H slots index names src
      hg hv he hs hi hn hb hm hnv hG hsub hvalid hw hnFit hslots hslotsSep
      hgraph hnames hindex hroom hnamesAt hslotsAt hc hp
  obtain ⟨o,out,cost,hrun,hlayout,hcost⟩ := hnext ready hends hframe hregs
  exact ⟨o,out,ce+cost+1,runs_seq_iff.mpr (Or.inr ⟨ready,ce,cost,hr,hrun,rfl⟩),hlayout,by omega⟩

/-- Prepare the representative graph and pack its endpoints for the guest. -/
def prepareRuntimeEndpoints (key sort cmp dedup vertices endpoints : ℕ) : Stmt :=
  .seq (prepareRuntimeRepresentative key sort cmp dedup)
    (collectionIndexAndEndpoints vertices endpoints)

/-- Extract the original graph and the live caller length blocks used
by representative endpoint preparation. -/
theorem runtimeEndpoints_inputs_of_initPre
    {w L vCap eCap multiplier P g src heap : ℕ} (fmt : Format w)
    (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (mem : ℕ → ℕ)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [g,src,L,fmt.precision,heap] mem) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L fmt.precision G.E
    DynGraphAt mem g vCap eCap G ∧ g+dynGraphSize vCap eCap ≤ heap ∧
      ∀ e ∈ G.E, src+e*L+L ≤ heap ∧ Valid mem (src+e*L) 4 L ∧
        fixVal mem (src+e*L) 4 L fmt.precision = ℓ e ∧ 0 < ℓ e := by
  intro ℓ
  obtain ⟨g',src',heap',heq,hbits,_,hbase,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  obtain ⟨g',src',heap',heq,hgraph,hend,hspan,hvalid,hpos⟩ := hbase
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  refine ⟨hgraph,hend,fun e he => ⟨?_,?_,?_,?_⟩⟩
  · have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hgraph.2.2.1 e he))
    rw [Nat.succ_mul] at hmul
    omega
  · simpa only [hbits] using hvalid e he
  · simp only [ℓ,MinRatio.readEdgeValues,ite_eq_left he]
  · simpa only [hbits] using hpos e he

/-- The endpoint arrays, original graph, and caller format are ready for runtime
format selection. Preparation preserves memory outside its scratch region. -/
theorem prepareRuntimeEndpoints_runs
    {w key sort cmp dedup ops vertices endpoints g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (G : MGraph) (mem : ℕ → ℕ) (ℓ : ℕ → ℝ)
    (lengths L P heap pos : ℕ)
    (hkey : MeetsContract w p key (representativeKeyContract w g vCap eCap G))
    (hsort : p.HasAt sort (sortProcs sort))
    (hcmp : MeetsContract w p cmp (unsignedLessContract w 4))
    (hdedup : p.HasAt dedup (gtProcs sort ops))
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w) (hg : g+dynGraphSize vCap eCap ≤ heap)
    (hlen : ∀ e ∈ G.E, lengths+e*L+L ≤ heap ∧ Valid mem (lengths+e*L) 4 L ∧
      fixVal mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    let src := heap+11*G.m+vCap+1
    src+queryLengths (representativeGraph G ℓ) < 2^w →
    MeetsContract w p vertices (packVertexIndexContract w g vCap eCap G (representativeGraph G ℓ)) →
    MeetsContract w p endpoints (packEdgeContract w g vCap eCap G (representativeGraph G ℓ)) →
    ∃ out cost, Runs w p ω (prepareRuntimeEndpoints key sort cmp (dedup+gtIdxSortDedup)
        vertices endpoints) (startState [g,lengths,L,P,heap] mem pos) .normal out cost ∧
      DynGraphAt out.mem g vCap eCap G ∧
      (∀ i < (representativeGraph G ℓ).m, out.mem (src+i) = (indexedGraph (representativeGraph G ℓ)).tail i ∧
        out.mem (src+((representativeGraph G ℓ).m+i)) = (indexedGraph (representativeGraph G ℓ)).head i) ∧
      (∀ i < (representativeGraph G ℓ).m, out.mem (heap+2*G.m+i) = edgeName (representativeGraph G ℓ) i) ∧
      (∀ i < (representativeGraph G ℓ).n,
        out.mem (heap+7*G.m+i) = vertexName (representativeGraph G ℓ) i) ∧
      out.regs 0 = g ∧ out.regs 112 = g ∧ out.regs 113 = vCap ∧ out.regs 114 = eCap ∧
      out.regs 100 = heap+2*G.m ∧ out.regs 73 = (representativeGraph G ℓ).m ∧ out.regs 72 = (representativeGraph G ℓ).n ∧
      out.regs 99 = lengths ∧ out.regs 127 = L ∧ out.regs 144 = L ∧ out.regs 145 = P ∧
      out.regs 146 = heap+11*G.m ∧ out.regs 142 = heap+11*G.m+vCap ∧
      out.regs 141 = src ∧ out.regs 151 = heap ∧ out.regs 150 = heap+7*G.m ∧
      out.regs 115 = G.n ∧ out.regs 116 = dgVListBase g vCap ∧ out.regs 133 = G.m ∧
      out.regs 134 = heap ∧ out.regs 136 = heap+G.m ∧ out.regs 137 = dgEListBase g vCap eCap ∧
      out.regs 138 = heap+3*G.m ∧ out.regs 131 = heap+4*G.m ∧
      (∀ a, a < heap ∨ src+queryLengths (representativeGraph G ℓ) ≤ a → out.mem a = mem a) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
        250*(2*(representativeGraph G ℓ).m)*(Nat.log 2 (2*(representativeGraph G ℓ).m+1)+1)+114*(representativeGraph G ℓ).m+37*(representativeGraph G ℓ).n+
        200*(representativeGraph G ℓ).m*(Nat.log 2 ((representativeGraph G ℓ).m+1)+1)+argsSize collectionEndpointArgs+565 := by
  dsimp only
  intro hroom hc hp
  have hsub := representativeGraph_subgraph hG.1 ℓ
  have hm : (representativeGraph G ℓ).m ≤ G.m := Finset.card_le_card hsub.2.1
  have hn : (representativeGraph G ℓ).n ≤ 2*G.m :=
    (representativeGraph_n_le_twice_m G ℓ).trans (Nat.mul_le_mul_left 2 hm)
  obtain ⟨mid,c,hr,hgraph,hedges,hnames,hslots,h0,h112,h113,h114,h148,h100,h73,h72,
    h99,h127,h144,h145,h146,h142,h141,h151,h150,h115,h116,h133,h134,h136,h137,h138,h131,hframe,hcost⟩ :=
    prepareRuntimeRepresentative_runs (ω := ω) G mem ℓ lengths L P heap pos
      hkey hsort hcmp hdedup hG hw hcap hg (by omega) hlen
  obtain ⟨out,d,hr',hends,hframe',hkeep,hcost'⟩ :=
    collectionIndexAndEndpoints_runs (ω := ω) mid G (representativeGraph G ℓ) (heap+9*G.m) (heap+11*G.m)
      (heap+2*G.m) (heap+11*G.m+vCap+1) h0 h113 h114 h148 h146 h100 h141 h73 h72
      hgraph hsub (representativeGraph_valid G ℓ) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hroom hedges hslots hc hp
  have hgraph' := hgraph.of_agree (fun a _ ha => hframe' a (Or.inl (by omega)))
  refine ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hr',rfl⟩),
    hgraph',hends,fun i hi => (hframe' _ (Or.inl (by omega))).trans (hedges i hi),
    ?_,(hkeep 0 (by decide) (by decide)).trans h0,
    (hkeep 112 (by decide) (by decide)).trans h112,
    (hkeep 113 (by decide) (by decide)).trans h113,
    (hkeep 114 (by decide) (by decide)).trans h114,
    (hkeep 100 (by decide) (by decide)).trans h100,
    (hkeep 73 (by decide) (by decide)).trans h73,
    (hkeep 72 (by decide) (by decide)).trans h72,
    (hkeep 99 (by decide) (by decide)).trans h99,
    (hkeep 127 (by decide) (by decide)).trans h127,
    (hkeep 144 (by decide) (by decide)).trans h144,
    (hkeep 145 (by decide) (by decide)).trans h145,
    (hkeep 146 (by decide) (by decide)).trans h146,
    (hkeep 142 (by decide) (by decide)).trans h142,
    (hkeep 141 (by decide) (by decide)).trans h141,
    (hkeep 151 (by decide) (by decide)).trans h151,
    (hkeep 150 (by decide) (by decide)).trans h150,
    (hkeep 115 (by decide) (by decide)).trans h115,
    (hkeep 116 (by decide) (by decide)).trans h116,
    (hkeep 133 (by decide) (by decide)).trans h133,
    (hkeep 134 (by decide) (by decide)).trans h134,
    (hkeep 136 (by decide) (by decide)).trans h136,
    (hkeep 137 (by decide) (by decide)).trans h137,
    (hkeep 138 (by decide) (by decide)).trans h138,
    (hkeep 131 (by decide) (by decide)).trans h131,?_,?_⟩
  · intro i hi
    exact (hframe' _ (Or.inl (by omega))).trans (sortedVertexNames_at hnames i hi)
  · intro a ha
    exact (hframe' a (by omega)).trans (hframe a (by omega))
  · omega

/-- The representative pass only reads the original length blocks. After
packing, every retained edge still has its caller length in the same format. -/
theorem preparedRepresentativeLengths {G : MGraph} {mem out : ℕ → ℕ}
    {lengths L P heap eCap dst : ℕ} (ℓ : ℕ → ℝ)
    (hG : G.IsValid) (hcap : ∀ e ∈ G.E, e < eCap) (hdst : heap ≤ dst)
    (hframe : ∀ a < heap, out a = mem a)
    (hlen : ∀ e ∈ G.E, lengths+e*L+L ≤ heap ∧ Valid mem (lengths+e*L) 4 L ∧
      fixVal mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    ∀ e ∈ (representativeGraph G ℓ).E,
      e < eCap ∧ lengths+e*L+L ≤ dst ∧ Valid out (lengths+e*L) 4 L ∧
      fixVal out (lengths+e*L) 4 L P = ℓ e ∧ 0 < fixVal out (lengths+e*L) 4 L P := by
  intro e he
  have heG := (representativeGraph_subgraph hG ℓ).2.1 he
  obtain ⟨hbound,hvalid,hvalue,hpos⟩ := hlen e heG
  have hcell i (hi : i < L) : out (lengths+e*L+i) = mem (lengths+e*L+i) :=
    hframe _ (by omega)
  have hout : fixVal out (lengths+e*L) 4 L P = ℓ e := by
    simpa only [fixVal,intVal_congr hcell] using hvalue
  exact ⟨hcap e heG,hbound.trans hdst,fun i hi => (hcell i hi).trans_lt (hvalid i hi),
    hout,hout.symm ▸ hpos⟩

/-- The guest format calculation decodes exactly the safe length vector
used by the fixed-point round, including zero outside the representative graph. -/
theorem preparedRepresentative_safeLen {G : MGraph} {mem out : ℕ → ℕ}
    {lengths L P heap eCap dst : ℕ} (ℓ : ℕ → ℝ)
    (hG : G.IsValid) (hcap : ∀ e ∈ G.E, e < eCap) (hdst : heap ≤ dst)
    (hframe : ∀ a < heap, out a = mem a)
    (hlen : ∀ e ∈ G.E, lengths+e*L+L ≤ heap ∧ Valid mem (lengths+e*L) 4 L ∧
      fixVal mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    (fun e => if e ∈ (representativeGraph G ℓ).E then fixVal out (lengths+e*L) 4 L P else 0) =
      LSF.safeLen (representativeGraph G ℓ) ℓ := by
  funext e
  by_cases he : e ∈ (representativeGraph G ℓ).E
  · rw [ite_eq_left he,LSF.safeLen_eq_of_mem ℓ he]
    exact (preparedRepresentativeLengths ℓ hG hcap hdst hframe hlen e he).2.2.2.1
  · simp [LSF.safeLen,he]

/-- The prepared edge names and positive caller lengths establish the
guest format precondition once the scalar and allocation bounds hold. -/
theorem preparedGuestFormat_pre {w cap names lengths L P dst guest : ℕ}
    (mem : ℕ → ℕ) (H : MGraph) (C : ℝ)
    (hnames : ∀ i < H.m, mem (names+i) = edgeName H i)
    (hlen : ∀ e ∈ H.E, e < cap ∧ lengths+e*L+L ≤ dst ∧
      Num.Valid mem (lengths+e*L) 4 L ∧ 0 < Num.fixVal mem (lengths+e*L) 4 L P)
    (hw : 16 ≤ 2^w) (hP : P ≤ 4*L) (hm : 0 < H.m) (hmFit : 2*H.m+2 < 2^w)
    (hwords : 4*L+max P (weightPrecision C H)+(2*H.m).size+2 < 2^w)
    (hspan : names+H.m ≤ dst) (hlenSpan : lengths+cap*L ≤ guest) (hdst : dst < guest) :
    let len := fun e => if e ∈ H.E then Num.fixVal mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    Q < 2^w → N < 2^w → P+N < 2^w → guest+H.m*N < 2^w →
    (setupAndPackGuestContract w cap names lengths L P dst guest H C (edgeName H)).pre
      [names,lengths,L,P,H.m,weightPrecision C H,dst,guest] mem := by
  intro len Q N hQ hN hPN hfit
  have hguest : guest < 2^w := by omega
  have hsetup : (guestFormatSetupContract w names lengths L P dst H C (edgeName H)).pre
      [names,lengths,L,P,H.m,weightPrecision C H,dst] mem := by
    refine ⟨rfl,hw,hP,hm,hmFit,by omega,by omega,hwords,?_,?_⟩
    · intro e
      constructor
      · intro he
        let iso : Fin H.m ≃o H.E := H.E.orderIsoOfFin rfl
        let i := iso.symm ⟨e,he⟩
        refine ⟨i.val,i.isLt,?_⟩
        rw [edgeName,dite_eq_left i.isLt]
        exact congrArg Subtype.val (iso.apply_symm_apply ⟨e,he⟩)
      · rintro ⟨i,hi,rfl⟩
        exact edgeName_mem hi
    · intro i hi
      obtain ⟨_,hcell,hvalid,hpositive⟩ := hlen _ (edgeName_mem hi)
      have hden : (0 : ℝ) < (2 : ℝ)^P := pow_pos (by norm_num) _
      exact ⟨hnames i hi,by omega,hvalid,by
        exact_mod_cast (div_pos_iff_of_pos_right hden).mp hpositive⟩
  exact ⟨rfl,hsetup,hQ,hN,hPN,hdst,hlenSpan,by omega,hfit,Or.inr hspan,
    fun _ _ => rfl,fun e he => (hlen e he).1,fun e he => Or.inr (hlen e he).2.1⟩

/-- Constant controller words and the prepared tables suffice to start
the guest format pipeline. -/
theorem preparedCollectionFormat_runs
    {w scale precision format sim cap names lengths L P dst src d c₀ : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (H : MGraph) (C : ℝ)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hnames : st.regs 100 = names) (hlengths : st.regs 99 = lengths)
    (hL : st.regs 144 = L) (hP : st.regs 145 = P)
    (hdst : st.regs 142 = dst) (hsrc : st.regs 141 = src)
    (hD : d = ⌈max 1 C⌉₊) (hdPos : 1 ≤ d) (hdFit : d < 2^w)
    (hscale : MeetsContract w p scale (scaleWordContract w H))
    (hprecision : MeetsContract w p precision (precisionWordContract w))
    (hformat : MeetsContract w p format
      (setupAndPackGuestContract w cap names lengths L P dst (src+queryLengths H) H C (edgeName H)))
    (hsim : MeetsContract w p sim (guestSimulationWidthContract w H.n))
    (hnameTable : ∀ i < H.m, st.mem (names+i) = edgeName H i)
    (hlen : ∀ e ∈ H.E, e < cap ∧ lengths+e*L+L ≤ dst ∧
      Num.Valid st.mem (lengths+e*L) 4 L ∧ 0 < Num.fixVal st.mem (lengths+e*L) 4 L P)
    (hw : 16 < 2^w) (hwidth : P ≤ 4*L) (hmPos : 0 < H.m)
    (hnFit : H.n+4 < 2^w) (hmFit : 16*H.m+8 < 2^w)
    (hscalePos : 0 < integerScale d H) (hscaleFit : 2*integerScale d H+2 < 2^w)
    (hwords : 4*L+max P (weightPrecision C H)+(2*H.m).size+2 < 2^w)
    (hspan : names+H.m ≤ dst) (hlenSpan : lengths+cap*L ≤ src+queryLengths H)
    (hdstSpan : dst < src+queryLengths H) (hcPos : 1 ≤ c₀) (hcFit : c₀ < 2^w) :
    let len := fun e => if e ∈ H.E then Num.fixVal st.mem (lengths+e*L) 4 L P else 0
    let Q := roundQueryPrecision C H len
    let N := roundQueryLimbs C H len
    let F := setupAndPackGuestContract w cap names lengths L P dst (src+queryLengths H) H C (edgeName H)
    let args := [names,lengths,L,P,H.m,weightPrecision C H,dst,src+queryLengths H]
    Q < 2^w → N < 2^w → P+N < 2^w → src+queryLengths H+H.m*N < 2^w →
    lsstLSimMin c₀ H.n H.m N 1 < 2^w →
    ∃ out cost, Runs w p ω (collectionFormatBody scale precision format sim (.const d) (.const c₀))
        st .normal out cost ∧ F.post args st.mem (out.regs 74) out.mem ∧
      out.regs 83 = Q ∧ out.regs 74 = N ∧ out.regs 75 = lsstLSimMin c₀ H.n H.m N 1 ∧
      out.regs 95 = weightPrecision C H ∧ out.regs 107 = integerScale d H ∧
      (∀ r, r ∉ ([74,75,83,95,107] : List ℕ) → out.regs r = st.regs r) ∧
      cost ≤ argsSize collectionGuestFormatArgs+F.cost args st.mem+
        40*(Nat.log 2 (H.n+2)+1)+40*weightPrecision C H+
        40*(Nat.log 2 (4*H.m+2)+Nat.log 2 (16*H.m+6)+2)+169 := by
  intro len Q N F args hQ hN hPN hfit hsimFit
  have haddr : src+queryLengths H < 2^w := by omega
  have hp := preparedGuestFormat_pre st.mem H C hnameTable hlen hw.le hwidth hmPos
    (by omega) hwords hspan hlenSpan hdstSpan hQ hN hPN hfit
  have hgrid := Nat.le_max_right P (weightPrecision C H)
  have hpgrid := Nat.le_max_left P (weightPrecision C H)
  have hargs : ∀ a ∈ args, a < 2^w := by
    intro a ha
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rw [hD] at hdPos hdFit hscalePos hscaleFit ⊢
  have hsWords : ∀ a ∈ [H.n,H.m,⌈max 1 C⌉₊], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hsimWords : ∀ a ∈ [H.m,N,c₀], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨out,cost,hr,hpost,h83,h74,h75,h95,h107,hregs,hcost⟩ :=
    collectionFormat_runs (ω := ω) st H C (edgeName H) (.const ⌈max 1 C⌉₊)
      (.const c₀) c₀ hn hm hnames hlengths hL hP hdst hsrc
      (by simp [Expr.eval,hdFit]) hscale hprecision hformat hsim hsWords
      ⟨_,rfl,hdPos,hmPos,hnFit,by omega⟩ hscalePos hscaleFit (by omega) haddr hargs hp hsimWords
      ⟨H.m,N,c₀,rfl,hcPos,hw,hmFit,hsimFit⟩ (by intros; simp [Expr.eval,hcFit])
  refine ⟨out,cost,hr,hpost,h83,h74,h75,h95,h107,hregs,?_⟩
  dsimp only [F,args]
  simp only [Expr.size] at hcost
  omega

/-- The runtime preparation factor includes loading, selection, and packing. -/
def runtimeEndpointMultiplier (L m : ℕ) : ℕ :=
  representativeInputMultiplier L m + 256

/-- The endpoint pass costs at most the runtime preparation factor times the
original edge count plus one. -/
theorem runtimeEndpointCost_le (G : MGraph) (ℓ : ℕ → ℝ) (L : ℕ) (hG : G.IsValid) :
    let H := representativeGraph G ℓ
    200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
      250*(2*H.m)*(Nat.log 2 (2*H.m+1)+1)+114*H.m+37*H.n+
      200*H.m*(Nat.log 2 (H.m+1)+1)+argsSize collectionEndpointArgs+565 ≤
    runtimeEndpointMultiplier L G.m * (G.m+1) := by
  dsimp only
  have hm : (representativeGraph G ℓ).m ≤ G.m :=
    Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hn : (representativeGraph G ℓ).n ≤ 2*G.m :=
    (representativeGraph_n_le_twice_m G ℓ).trans (Nat.mul_le_mul_left 2 hm)
  have hbase := representativeInputCost_le G ℓ L hG
  dsimp only at hbase
  have hargs : argsSize collectionEndpointArgs ≤ 37 := by decide
  by_cases hm0 : G.m = 0
  · have he : (representativeGraph G ℓ).m = 0 := by omega
    have hv : (representativeGraph G ℓ).n = 0 := by omega
    simp only [hm0,he,hv,runtimeEndpointMultiplier,representativeInputMultiplier,Nat.zero_mul,
      Nat.mul_zero,Nat.zero_add,Nat.add_zero,Nat.mul_one]
    change argsSize collectionEndpointArgs+565 ≤ 900+41*L+524+256
    exact (Nat.add_le_add_right hargs 565).trans
      (Nat.le_trans (show 602 ≤ 900 by decide) (by omega))
  unfold runtimeEndpointMultiplier
  rw [Nat.add_mul, Nat.mul_add 256, Nat.mul_one]
  omega

/-- Packing the guest length blocks leaves both endpoint arrays in place
and keeps the space above the persistent guest prefix fresh. -/
theorem collectionFormat_packedPrefix
    {w cap names lengths L P dst src N heap : ℕ} {mem out : ℕ → ℕ}
    (H : MGraph) (C : ℝ) (name : ℕ → ℕ)
    (hpost : (setupAndPackGuestContract w cap names lengths L P dst
        (src+queryLengths H) H C name).post
      [names,lengths,L,P,H.m,weightPrecision C H,dst,src+queryLengths H] mem N out)
    (len : ℕ → ℝ)
    (hlen : (fun e => if e ∈ H.E then fixVal mem (lengths+e*L) 4 L P else 0) = len)
    (hdst : heap ≤ dst) (hsrc : dst < src)
    (hz : ZeroFrom mem (src+queryLengths H))
    (hends : ∀ i < H.m, mem (src+i) = (indexedGraph H).tail i ∧
      mem (src+(H.m+i)) = (indexedGraph H).head i) :
    (∀ i < H.m, out (src+i) = (indexedGraph H).tail i ∧
      out (src+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.m, ListAt out (src+queryLengths H+i*N)
      (encodeLimbs 1 N (queryNumerator (roundQueryPrecision C H len) (len (edgeName H i))))) ∧
    ZeroFrom out (src+queryWeights H N) ∧ (∀ a < heap, out a = mem a) := by
  obtain ⟨hN,_,hpacked,hframe⟩ := hpost
  change N = roundQueryLimbs C H
    (fun e => if e ∈ H.E then Num.fixVal mem (lengths+e*L) 4 L P else 0) at hN
  rw [← hN] at hframe hpacked
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    have ht := (hends i hi).1
    have hh := (hends i hi).2
    unfold queryLengths at hframe
    exact ⟨(hframe _ (by omega) (Or.inl (by omega))).trans ht,
      (hframe _ (by omega) (Or.inl (by omega))).trans hh⟩
  · simpa only [← hlen] using hpacked
  · intro a ha
    unfold queryWeights at ha
    exact (hframe a (by omega) (Or.inr (by omega))).trans (hz a (by omega))
  · intro a ha
    exact hframe a (by omega) (Or.inl (by omega))

/-- Reserve the binary-lifting depth in the controller slot corresponding
to round register 14. -/
def installControllerLevels (log : ℕ) : Stmt :=
  .call 86 log [.reg 72]

/-- The level setup reads only the representative vertex count. -/
theorem installControllerLevels_runs {w log n : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (hc : MeetsContract w p log (clogTwoContract w n))
    (hn : st.regs 72 = n) (hword : n+1 < 2^w) (hw : 2 < 2^w) :
    ∃ out cost, Runs w p ω (installControllerLevels log) st .normal out cost ∧
      out.regs 86 = Nat.clog 2 n ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 86 → out.regs r = st.regs r) ∧ cost ≤ 40*Nat.clog 2 n+22 := by
  have ha : evalArgs w st [.reg 72] = some [n] := by simp [evalArgs,Expr.eval,hn]
  obtain ⟨out,c,ret,hr,⟨hmem,hret⟩,hreg,hkeep,hcost⟩ :=
    runs_call_of_meetsContract (r := 86) hc ha (by simpa using (show n < 2^w by omega))
      ⟨rfl,hword,hw⟩ ω
  refine ⟨out,c,hr,hreg.trans hret,hmem,hkeep,?_⟩
  change c ≤ 1+(40*Nat.clog 2 n+20)+1 at hcost
  omega

/-- Sort the original edge names and materialize their stretch indices
in the reserved scratch below the compact vertex and endpoint arrays. -/
theorem runtimeStretchTables_runs {w copy sort entry key scan g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ) (heap : ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w)) (hs : p.HasAt sort (sortProcs sort))
    (hp : p.procs[entry]? = some (stretchIndexKeyTableBody key))
    (hk : p.procs[key]? = some representativeKeyBody)
    (hscan : p.procs[scan]? = some stretchIndexScanBody)
    (hg : DynGraphAt st.mem g vCap eCap G)
    (h112 : st.regs 112 = g) (h113 : st.regs 113 = vCap) (h114 : st.regs 114 = eCap)
    (h134 : st.regs 134 = heap) (h136 : st.regs 136 = heap+G.m)
    (h137 : st.regs 137 = dgEListBase g vCap eCap)
    (h100 : st.regs 100 = heap+2*G.m) (h138 : st.regs 138 = heap+3*G.m)
    (h131 : st.regs 131 = heap+4*G.m) (h133 : st.regs 133 = G.m)
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hgraph : g+dynGraphSize vCap eCap ≤ heap) (hfit : heap+5*G.m < 2^w) :
    let H := representativeGraph G ℓ
    st.regs 73 = H.m →
    (∀ i < H.m, st.mem (heap+2*G.m+i) = edgeName H i) →
    ∃ named out cn ci, Runs w p ω (prepareOriginalEdgeNames copy sort) st .normal named cn ∧
      Runs w p ω (prepareStretchIndices entry scan) named .normal out ci ∧
      (∀ i < G.m, out.mem (heap+i) = edgeName G i) ∧
      (∀ i < G.m, out.mem (heap+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
      (∀ a, a < heap ∨ (heap+2*G.m ≤ a ∧ a < heap+3*G.m) ∨
        heap+5*G.m ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 135 → r ≠ 139 → r ≠ 140 → out.regs r = st.regs r) ∧
      cn+ci ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+17*G.m+100+
        argsSize (stretchIndexKeyArgs 134 136 133)+argsSize (stretchIndexKeyArgs 100 138 73)+
        57*(G.m+H.m)+(26*H.m+48)*G.m := by
  intro H h73 hnames
  obtain ⟨edges,hlen,hnd,hmem,hlist,_⟩ := hg.2.2.2.2.2.2.2.2.2.2.2.2.1
  have heCap : eCap < 2^w := by unfold dynGraphSize at hgraph; omega
  have hsrc : dgEListBase g vCap eCap+G.m ≤ heap := by
    have hm : G.m ≤ eCap := by
      rw [← hlen]
      simpa using hnd.length_le_of_subset (l₂ := List.range eCap)
        (fun e he => List.mem_range.mpr (hg.2.2.1 e ((hmem e).mp he)))
    unfold dgEListBase dynGraphSize at *
    omega
  obtain ⟨named,cn,hr,hnames',hframe,hkeep,hcn⟩ :=
    prepareOriginalEdgeNames_runs (ω := ω) st G edges (dgEListBase g vCap eCap) heap (heap+G.m)
      hc hs h137 h134 h133 h136 hlen hnd hmem hlist
      (fun e he => Nat.lt_trans (hg.2.2.1 e he) heCap) hw hsrc le_rfl (by omega)
  have hg' := representativeGraph_frame hg (fun a _ ha => hframe a (Or.inl (ha.trans_le hgraph)))
  have keep r (hn : r ≠ 135) := hkeep r hn
  obtain ⟨out,ci,hi,hidx,hframe',hkeep',hci⟩ :=
    prepareStretchIndices_runs (ω := ω) named G ℓ heap hp hk hscan hg'
      ((keep 112 (by decide)).trans h112) ((keep 113 (by decide)).trans h113)
      ((keep 114 (by decide)).trans h114) ((keep 134 (by decide)).trans h134)
      ((keep 136 (by decide)).trans h136) ((keep 100 (by decide)).trans h100)
      ((keep 138 (by decide)).trans h138) ((keep 131 (by decide)).trans h131)
      ((keep 133 (by decide)).trans h133) hw hcap hgraph hfit hnames'
      ((keep 73 (by decide)).trans h73)
      (fun i hi => (hframe _ (Or.inr (by omega))).trans (hnames i hi))
  refine ⟨named,out,cn,ci,hr,hi,fun i hi => (hframe' _ (Or.inl (by omega))).trans (hnames' i hi),
    hidx,fun a ha => (hframe' a (by omega)).trans (hframe a (by omega)),
    fun r h₁ h₂ h₃ => (hkeep' r h₁ h₂ h₃).trans (hkeep r h₁),?_⟩
  change ci ≤ _+_+57*(G.m+H.m)+(26*H.m+48)*G.m+31 at hci
  omega

/-- Prepare the representative graph and numeric format before rebuilding. -/
def representativeRuntimeInitWith (key sort cmp dedup vertices endpoints scale precision format sim
    copy log keys scan d c : ℕ) (rebuild : Stmt) : Stmt :=
  .seq (prepareRuntimeEndpoints key sort cmp dedup vertices endpoints)
    (.seq (prepareOriginalEdgeNames copy sort)
      (.seq (prepareStretchIndices keys scan)
        (.seq (collectionFormatBody scale precision format sim (.const d) (.const c))
        (.seq (installControllerLevels log) rebuild))))

/-- Initialize a nonempty representative collection from the five runtime
words and publish its header at the caller's handle. -/
def representativeRuntimeInit (key sort cmp dedup vertices endpoints scale precision format sim
    init weights round copy log keys scan d c : ℕ) : Stmt :=
  representativeRuntimeInitWith key sort cmp dedup vertices endpoints scale precision format sim
    copy log keys scan d c (stagedPreparedCollectionThen init weights round (publishRuntimeCollection copy))

/-- Initialize a representative collection with widened scratch and compact output tables. -/
def representativePackedRuntimeInit (key sort cmp dedup vertices endpoints scale precision format sim
    init weights round copy log keys scan d c : ℕ) : Stmt :=
  representativeRuntimeInitWith key sort cmp dedup vertices endpoints scale precision format sim
    copy log keys scan d c (stagedCompactCollectionThen init weights round copy)

/-- Sequential composition of runtime preparation, format selection, and
the rebuild with publication retains the final heap and caller frame. -/
theorem representativeRuntimeInitWith_runs
    {w key sort cmp dedup vertices endpoints scale precision format sim copy log keys scan d c : ℕ}
    {rebuild : Stmt}
    {p : Program} {ω : ℕ → Bool} (st packed named indexed formatted ready : State)
    (prepCost namesCost indexCost formatCost levelCost rebuildBudget : ℕ) (Post : Outcome → State → Prop)
    (hp : Runs w p ω (prepareRuntimeEndpoints key sort cmp dedup vertices endpoints)
      st .normal packed prepCost)
    (hn : Runs w p ω (prepareOriginalEdgeNames copy sort) packed .normal named namesCost)
    (hi : Runs w p ω (prepareStretchIndices keys scan) named .normal indexed indexCost)
    (hf : Runs w p ω (collectionFormatBody scale precision format sim (.const d) (.const c))
      indexed .normal formatted formatCost)
    (hl : Runs w p ω (installControllerLevels log) formatted .normal ready levelCost)
    (hr : ∃ o out cost,
      Runs w p ω rebuild
        ready o out cost ∧ Post o out ∧ cost ≤ rebuildBudget) :
    ∃ o out cost, Runs w p ω (representativeRuntimeInitWith key sort cmp dedup vertices endpoints
        scale precision format sim copy log keys scan d c rebuild) st o out cost ∧
      Post o out ∧ cost ≤ prepCost+namesCost+indexCost+formatCost+levelCost+rebuildBudget+5 := by
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ := hr
  have hlast := runs_seq_iff.mpr (Or.inr ⟨ready,levelCost,cost,hl,hr,rfl⟩)
  have htail := runs_seq_iff.mpr (Or.inr ⟨formatted,formatCost,levelCost+cost+1,hf,hlast,rfl⟩)
  have hindexed := runs_seq_iff.mpr (Or.inr
    ⟨indexed,indexCost,formatCost+(levelCost+cost+1)+1,hi,htail,rfl⟩)
  have hnamed := runs_seq_iff.mpr (Or.inr ⟨named,namesCost,_,hn,hindexed,rfl⟩)
  exact ⟨o,out,prepCost+(namesCost+(indexCost+(formatCost+(levelCost+cost+1)+1)+1)+1)+1,
    runs_seq_iff.mpr (Or.inr ⟨packed,prepCost,_,hp,hnamed,rfl⟩),hpost,by omega⟩

/-- Sequential composition of runtime preparation, format selection, and
the rebuild with publication retains the final heap and caller frame. -/
theorem representativeRuntimeInit_runs
    {w key sort cmp dedup vertices endpoints scale precision format sim init weights round copy log keys scan d c : ℕ}
    {p : Program} {ω : ℕ → Bool} (st packed named indexed formatted ready : State)
    (prepCost namesCost indexCost formatCost levelCost rebuildBudget : ℕ) (Post : Outcome → State → Prop)
    (hp : Runs w p ω (prepareRuntimeEndpoints key sort cmp dedup vertices endpoints)
      st .normal packed prepCost)
    (hn : Runs w p ω (prepareOriginalEdgeNames copy sort) packed .normal named namesCost)
    (hi : Runs w p ω (prepareStretchIndices keys scan) named .normal indexed indexCost)
    (hf : Runs w p ω (collectionFormatBody scale precision format sim (.const d) (.const c))
      indexed .normal formatted formatCost)
    (hl : Runs w p ω (installControllerLevels log) formatted .normal ready levelCost)
    (hr : ∃ o out cost,
      Runs w p ω (stagedPreparedCollectionThen init weights round (publishRuntimeCollection copy))
        ready o out cost ∧ Post o out ∧ cost ≤ rebuildBudget) :
    ∃ o out cost, Runs w p ω (representativeRuntimeInit key sort cmp dedup vertices endpoints
        scale precision format sim init weights round copy log keys scan d c) st o out cost ∧
      Post o out ∧ cost ≤ prepCost+namesCost+indexCost+formatCost+levelCost+rebuildBudget+5 :=
  representativeRuntimeInitWith_runs st packed named indexed formatted ready
    prepCost namesCost indexCost formatCost levelCost rebuildBudget Post hp hn hi hf hl hr

/-- Connect representative preparation to the packed rebuild at the caller handle. -/
theorem representativePackedRuntimeInit_runs
    {w key sort cmp dedup vertices endpoints scale precision format sim init weights round copy log keys scan d c : ℕ}
    {p : Program} {ω : ℕ → Bool} (st packed named indexed formatted ready : State)
    (prepCost namesCost indexCost formatCost levelCost rebuildBudget : ℕ) (Post : Outcome → State → Prop)
    (hp : Runs w p ω (prepareRuntimeEndpoints key sort cmp dedup vertices endpoints)
      st .normal packed prepCost)
    (hn : Runs w p ω (prepareOriginalEdgeNames copy sort) packed .normal named namesCost)
    (hi : Runs w p ω (prepareStretchIndices keys scan) named .normal indexed indexCost)
    (hf : Runs w p ω (collectionFormatBody scale precision format sim (.const d) (.const c))
      indexed .normal formatted formatCost)
    (hl : Runs w p ω (installControllerLevels log) formatted .normal ready levelCost)
    (hr : ∃ o out cost,
      Runs w p ω (stagedCompactCollectionThen init weights round copy)
        ready o out cost ∧ Post o out ∧ cost ≤ rebuildBudget) :
    ∃ o out cost, Runs w p ω (representativePackedRuntimeInit key sort cmp dedup vertices endpoints
        scale precision format sim init weights round copy log keys scan d c) st o out cost ∧
      Post o out ∧ cost ≤ prepCost+namesCost+indexCost+formatCost+levelCost+rebuildBudget+5 :=
  representativeRuntimeInitWith_runs st packed named indexed formatted ready
    prepCost namesCost indexCost formatCost levelCost rebuildBudget Post hp hn hi hf hl hr

/-- Link preparation and collection publication with the caller frame and
the complete branch table required by runtime dispatch. -/
theorem representativePackedRuntimeInit_returnsPrefix
    {w key sort cmp dedup vertices endpoints scale precision format sim init weights round copy log keys scan d c : ℕ}
    {p : Program} {ω : ℕ → Bool} (st packed named indexed formatted ready : State)
    (prepCost namesCost indexCost formatCost levelCost rebuildBudget : ℕ)
    (hp : Runs w p ω (prepareRuntimeEndpoints key sort cmp dedup vertices endpoints)
      st .normal packed prepCost)
    (hn : Runs w p ω (prepareOriginalEdgeNames copy sort) packed .normal named namesCost)
    (hi : Runs w p ω (prepareStretchIndices keys scan) named .normal indexed indexCost)
    (hf : Runs w p ω (collectionFormatBody scale precision format sim (.const d) (.const c))
      indexed .normal formatted formatCost)
    (hl : Runs w p ω (installControllerLevels log) formatted .normal ready levelCost)
    {handle limit vCap eCap h L P : ℕ} {G : MGraph} {s : ℕ × (ℕ → LSF)}
    (hprep : ∀ a < handle, ready.mem a = st.mem a)
    (hr : ∃ o out cost,
      Runs w p ω (stagedCompactCollectionThen init weights round copy) ready o out cost ∧
      (∃ ret, o = .returned ret ∧ handle+1+s.1 ≤ ret ∧ ret ≤ limit ∧
        CollectionPrefix out.mem handle s.1 s.1 ret vCap eCap h L P G.E s.2 ∧
        ZeroFrom out.mem ret ∧ (∀ a < handle, out.mem a = ready.mem a)) ∧
      cost ≤ rebuildBudget) :
    ∃ ret out cost, Runs w p ω (representativePackedRuntimeInit key sort cmp dedup vertices endpoints
        scale precision format sim init weights round copy log keys scan d c) st (.returned ret) out cost ∧
      handle+1+s.1 ≤ ret ∧
      CollectionPrefix out.mem handle s.1 s.1 ret vCap eCap h L P G.E s.2 ∧
      ret ≤ limit ∧ ZeroFrom out.mem ret ∧ (∀ a < handle, out.mem a = st.mem a) ∧
      cost ≤ prepCost+namesCost+indexCost+formatCost+levelCost+rebuildBudget+5 := by
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ := representativePackedRuntimeInit_runs st packed named
    indexed formatted ready prepCost namesCost indexCost formatCost levelCost rebuildBudget _ hp hn hi hf hl hr
  obtain ⟨ret,rfl,hlo,hhi,hprefix,hzero,hframe⟩ := hpost
  exact ⟨ret,out,cost,hrun,hlo,hprefix,hhi,hzero,fun a ha => (hframe a ha).trans (hprep a ha),hcost⟩

/-- Run representative endpoint preparation from the runtime input
using the installed key, vertex-index, and endpoint procedures. -/
theorem prepareRuntimeEndpoints_of_initPre
    {w key sort cmp dedup ops vertices endpoints pack g vCap eCap L P multiplier : ℕ}
    {p : Program} {ω : ℕ → Bool} (fmt : Format w)
    (tool : Chain.LastLevelTool) (allocation : ℕ → List ℕ → ℕ)
    (G : MGraph) (mem : ℕ → ℕ) (lengths heap pos : ℕ)
    (hkey : p.procs[key]? = some representativeKeyBody)
    (hsort : p.HasAt sort (sortProcs sort))
    (hcmp : MeetsContract w p cmp (unsignedLessContract w 4))
    (hdedup : p.HasAt dedup (gtProcs sort ops))
    (hvertices : p.procs[vertices]? = some packVertexIndexBody)
    (hendpoints : p.procs[endpoints]? = some (packEdgeBody pack))
    (hpack : p.procs[pack]? = some packEndpointsBody)
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hpre : (MinRatio.lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier P
      allocation).initPre [g,lengths,L,fmt.precision,heap] mem) :
    let ℓ := MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E
    let src := heap+11*G.m+vCap+1
    src+queryLengths (representativeGraph G ℓ) < 2^w →
    ∃ out cost, Runs w p ω (prepareRuntimeEndpoints key sort cmp (dedup+gtIdxSortDedup)
        vertices endpoints) (startState [g,lengths,L,fmt.precision,heap] mem pos) .normal out cost ∧
      DynGraphAt out.mem g vCap eCap G ∧
      (∀ i < (representativeGraph G ℓ).m, out.mem (src+i) = (indexedGraph (representativeGraph G ℓ)).tail i ∧
        out.mem (src+((representativeGraph G ℓ).m+i)) = (indexedGraph (representativeGraph G ℓ)).head i) ∧
      (∀ i < (representativeGraph G ℓ).m, out.mem (heap+2*G.m+i) = edgeName (representativeGraph G ℓ) i) ∧
      (∀ i < (representativeGraph G ℓ).n,
        out.mem (heap+7*G.m+i) = vertexName (representativeGraph G ℓ) i) ∧
      out.regs 0 = g ∧ out.regs 112 = g ∧ out.regs 113 = vCap ∧ out.regs 114 = eCap ∧
      out.regs 100 = heap+2*G.m ∧ out.regs 73 = (representativeGraph G ℓ).m ∧ out.regs 72 = (representativeGraph G ℓ).n ∧
      out.regs 99 = lengths ∧ out.regs 127 = L ∧ out.regs 144 = L ∧ out.regs 145 = fmt.precision ∧
      out.regs 146 = heap+11*G.m ∧ out.regs 142 = heap+11*G.m+vCap ∧
      out.regs 141 = src ∧ out.regs 151 = heap ∧ out.regs 150 = heap+7*G.m ∧
      out.regs 115 = G.n ∧ out.regs 116 = dgVListBase g vCap ∧ out.regs 133 = G.m ∧
      out.regs 134 = heap ∧ out.regs 136 = heap+G.m ∧ out.regs 137 = dgEListBase g vCap eCap ∧
      out.regs 138 = heap+3*G.m ∧ out.regs 131 = heap+4*G.m ∧
      (∀ a, a < heap ∨ src+queryLengths (representativeGraph G ℓ) ≤ a → out.mem a = mem a) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
        250*(2*(representativeGraph G ℓ).m)*(Nat.log 2 (2*(representativeGraph G ℓ).m+1)+1)+114*(representativeGraph G ℓ).m+37*(representativeGraph G ℓ).n+
        200*(representativeGraph G ℓ).m*(Nat.log 2 ((representativeGraph G ℓ).m+1)+1)+argsSize collectionEndpointArgs+565 := by
  intro ℓ src hroom
  obtain ⟨hgraph,hgraphEnd,hlen⟩ := runtimeEndpoints_inputs_of_initPre fmt tool allocation G mem hpre
  exact prepareRuntimeEndpoints_runs G mem ℓ lengths L fmt.precision heap pos
    (representativeKey_meetsContract G hkey) hsort hcmp hdedup hgraph hw hcap hgraphEnd hlen
    hroom (packVertexIndex_meetsContract G _ hvertices) (packEdge_meetsContract G _ hendpoints hpack)

/-- Guest formatting preserves the caller prefix and leaves fresh
memory at the collection base after the guest length and weight tables. -/
theorem preparedCollectionFormat_boundary
    {w cap names lengths L P dst src handle ret : ℕ}
    {H : MGraph} {C : ℝ} {input formatted : ℕ → ℕ} {args : List ℕ}
    (hpost : (setupAndPackGuestContract w cap names lengths L P dst (src+queryLengths H)
      H C (edgeName H)).post args input ret formatted)
    (hdst : handle ≤ dst) (hguest : dst < src+queryLengths H)
    (hzero : ZeroFrom input (src+queryLengths H)) :
    (∀ a < handle, formatted a = input a) ∧
      ZeroFrom formatted (src+queryWeights H ret) := by
  obtain ⟨rfl,_,_,hframe⟩ := hpost
  refine ⟨fun a ha => hframe a (by omega) (Or.inl (by omega)),?_⟩
  intro a ha
  change src+(queryLengths H+H.m*_) ≤ a at ha
  have hend : src+queryLengths H ≤ a := by omega
  exact (hframe a (by omega) (Or.inr (by omega))).trans (hzero a hend)

end MinCostFlow.LastLevelProgram
