module

public import MinCostFlow.LastLevelProgram.StagedOutputAddresses
import Mathlib.Tactic

/-!
# Publishing staged round outputs

The Definition 5.8 rebuild (pages 19–20) scatters compact stretches by edge name and publishes the branch header.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord DynSpanner.Program SparseCore LSF MinRatio Num

/-- Scatter the compact stretch blocks into the branch's named numerator
array. The original edge index, unit block, edge count and names use
registers fifty-nine through sixty-two. -/
def stagedNamedStretchArgs : List Expr :=
  [.reg 59,.reg 1,.reg 36,.reg 37,.reg 60,.reg 51,.reg 61,.reg 62,.reg 52,.reg 55]

/-- The named scatter exposes the model branch stretch and preserves
the graph, root range, and all memory after the numerator array. -/
theorem stagedNamedStretch_runs {w entry h L P cap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (j indices src stride unit addresses names dst : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hi : st.regs 59 = indices) (hm : st.regs 1 = (representativeGraph G ℓ).m)
    (hs : st.regs 36 = src) (hst : st.regs 37 = stride) (hu : st.regs 60 = unit)
    (ha : st.regs 51 = addresses) (hcount : st.regs 61 = G.m)
    (hn : st.regs 62 = names) (hd : st.regs 52 = dst) (hl : st.regs 55 = L) :
    let H := representativeGraph G ℓ
    let prec := weightPrecision C H
    let query := stretchQuery oracle H ℓ prec
    let v := weights prec (roundedScale C H) query j
    let contract := namedStretchContract w h L P cap
      (branchStretchIndex G ℓ ∘ edgeName G) (edgeName G)
    let args := [indices,H.m,src,stride,unit,addresses,G.m,names,dst,L]
    MeetsContract w p entry contract →
    (∀ a ∈ args, a < 2^w) → contract.pre args st.mem →
    (∀ i < H.m, fixVal st.mem (src+i*stride) h L P = query v (edgeName H i)) →
    fixVal st.mem unit h L P = 1 →
    ∃ out cost, Runs w p ω (.call 63 entry stagedNamedStretchArgs) st .normal out cost ∧
      EdgeValuesAt out.mem dst h L P G.E ((fixedPointLastLevelTool oracle C).build G ℓ |>.2 j).wstr ∧
      (∀ a, a < addresses ∨ (addresses+G.m ≤ a ∧ a < dst) ∨ dst+cap*L ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 63 → out.regs r = st.regs r) ∧ cost ≤ (17*L+92)*G.m+51 := by
  intro H prec query v contract args hcall hwords hpre hrep hunit
  have he : evalArgs w st stagedNamedStretchArgs = some args := by
    simp [stagedNamedStretchArgs,args,H,evalArgs,Expr.eval,hi,hm,hs,hst,hu,ha,hcount,hn,hd,hl]
  obtain ⟨out,cost,ret,hrun,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 63) hcall he hwords hpre ω
  obtain ⟨ix,sen,sr,str,un,ad,m,na,ds,heq,_,hout,hframe⟩ := hpost
  simp only [args,List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change cost ≤ 10+((17*L+92)*G.m+40)+1 at hcost
  exact ⟨out,cost,hrun,
    branchStretch_of_namedOutput oracle C G ℓ j h L P src stride unit dst st.mem out.mem
      hnl hrep hunit hout,hframe,hregs,by omega⟩

/-- Reuse the named scatter with zero source stride to copy the unit
block into each live denominator slot. -/
def stagedNamedDenominatorArgs : List Expr :=
  [.reg 59,.reg 1,.reg 60,.const 0,.reg 60,.reg 51,.reg 61,.reg 62,.reg 53,.reg 55]

/-- Copying a fixed-point unit block works in the caller's limb format.
The scratch address table is rebuilt, so the earlier numerator pass
can reuse the same table. -/
theorem stagedNamedDenominator_runs {w entry h L P cap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (indices sentinel unit addresses names dst : ℕ)
    (hi : st.regs 59 = indices) (hm : st.regs 1 = sentinel)
    (hu : st.regs 60 = unit) (ha : st.regs 51 = addresses) (hc : st.regs 61 = G.m)
    (hn : st.regs 62 = names) (hd : st.regs 53 = dst) (hl : st.regs 55 = L)
    (hw : 0 < 2^w) :
    let contract := namedStretchContract w h L P cap
      (branchStretchIndex G ℓ ∘ edgeName G) (edgeName G)
    let args := [indices,sentinel,unit,0,unit,addresses,G.m,names,dst,L]
    MeetsContract w p entry contract →
    (∀ a ∈ args, a < 2^w) → contract.pre args st.mem →
    fixVal st.mem unit h L P = 1 →
    ∃ out cost, Runs w p ω (.call 64 entry stagedNamedDenominatorArgs) st .normal out cost ∧
      EdgeValuesAt out.mem dst h L P G.E (fun _ => 1) ∧
      (∀ a, a < addresses ∨ (addresses+G.m ≤ a ∧ a < dst) ∨ dst+cap*L ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 64 → out.regs r = st.regs r) ∧ cost ≤ (17*L+92)*G.m+51 := by
  intro contract args hcall hwords hpre hunit
  have he : evalArgs w st stagedNamedDenominatorArgs = some args := by
    simp [stagedNamedDenominatorArgs,args,evalArgs,Expr.eval,hi,hm,hu,ha,hc,hn,hd,hl,hw]
  obtain ⟨out,cost,ret,hrun,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 64) hcall he hwords hpre ω
  obtain ⟨ix,sen,sr,str,un,ad,m,na,ds,heq,_,hout,hframe⟩ := hpost
  simp only [args,List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  change cost ≤ 10+((17*L+92)*G.m+40)+1 at hcost
  refine ⟨out,cost,hrun,?_,hframe,hregs,by omega⟩
  intro e he
  obtain ⟨hi,heq⟩ := edgeIndex_live he
  rw [← heq]
  simpa [hunit] using hout (edgeIndex G e) hi

/-- Prepare both named arrays using the same compact edge tables. -/
def stagedBranchStretchBody (entry : ℕ) : Stmt :=
  .seq (.call 63 entry stagedNamedStretchArgs)
    (.call 64 entry stagedNamedDenominatorArgs)

/-- The two scans preserve the shared graph and leave both stretch
arrays available to the publisher. -/
theorem stagedBranchStretch_runs {w entry h L P cap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (j indices src stride unit addresses names num den : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hi : st.regs 59 = indices) (hm : st.regs 1 = (representativeGraph G ℓ).m)
    (hs : st.regs 36 = src) (hst : st.regs 37 = stride) (hu : st.regs 60 = unit)
    (ha : st.regs 51 = addresses) (hc : st.regs 61 = G.m)
    (hn : st.regs 62 = names) (hnum : st.regs 52 = num) (hden : st.regs 53 = den)
    (hl : st.regs 55 = L) (hw : 0 < 2^w)
    (huEnd : unit+L ≤ addresses) (huValid : Valid st.mem unit h L)
    (hsep : num+cap*L ≤ den) (hfit : den+cap*L < 2^w)
    (hedges : ∀ e ∈ G.E, e < cap) :
    let H := representativeGraph G ℓ
    let prec := weightPrecision C H
    let query := stretchQuery oracle H ℓ prec
    let v := weights prec (roundedScale C H) query j
    let contract := namedStretchContract w h L P cap
      (branchStretchIndex G ℓ ∘ edgeName G) (edgeName G)
    let args := [indices,H.m,src,stride,unit,addresses,G.m,names,num,L]
    MeetsContract w p entry contract →
    (∀ a ∈ args, a < 2^w) → contract.pre args st.mem →
    (∀ i < H.m, fixVal st.mem (src+i*stride) h L P = query v (edgeName H i)) →
    fixVal st.mem unit h L P = 1 →
    ∃ out cost, Runs w p ω (stagedBranchStretchBody entry) st .normal out cost ∧
      EdgeValuesAt out.mem num h L P G.E ((fixedPointLastLevelTool oracle C).build G ℓ |>.2 j).wstr ∧
      EdgeValuesAt out.mem den h L P G.E (fun _ => 1) ∧
      (∀ a, a < addresses ∨ den+cap*L ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 63 → r ≠ 64 → out.regs r = st.regs r) ∧ cost ≤ 2*((17*L+92)*G.m+51)+1 := by
  intro H prec query v contract args hcall hwords hpre hrep hunit
  obtain ⟨mid,cn,hrn,hnvals,hfn,hrnRegs,hcn⟩ :=
    stagedNamedStretch_runs (ω := ω) st oracle C G ℓ j indices src stride unit addresses names
      num hnl hi hm hs hst hu ha hc hn hnum hl hcall hwords hpre hrep hunit
  have hprefix (a : ℕ) (h : a < addresses) := hfn a (Or.inl h)
  have hDenPre := namedStretch_denominator_pre hpre hprefix huValid huEnd
    (show num ≤ den by omega) hfit
  have hDenWords (a : ℕ) (ha' : a ∈ [indices,H.m,unit,0,unit,addresses,G.m,names,den,L]) :
      a < 2^w := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hw | exact (Nat.le_add_right _ _).trans_lt hfit | exact hwords _ (by simp [args])
  have hUnitMid : fixVal mid.mem unit h L P = 1 := by
    unfold fixVal at *
    rw [intVal_congr (fun k hk => hprefix (unit+k) (by omega))]
    exact hunit
  obtain ⟨out,cd,hrd,hdvals,hfd,hrdRegs,hcd⟩ :=
    stagedNamedDenominator_runs (ω := ω) mid G ℓ indices H.m unit addresses names den
      ((hrnRegs _ (by decide)).trans hi) ((hrnRegs _ (by decide)).trans hm)
      ((hrnRegs _ (by decide)).trans hu) ((hrnRegs _ (by decide)).trans ha)
      ((hrnRegs _ (by decide)).trans hc) ((hrnRegs _ (by decide)).trans hn)
      ((hrnRegs _ (by decide)).trans hden) ((hrnRegs _ (by decide)).trans hl)
      hw hcall hDenWords hDenPre hUnitMid
  have hTable : addresses+G.m ≤ num := by
    obtain ⟨ix,se,sr,str,un,ad,sz,na,dst,heq,_,_,_,hh,_⟩ := hpre
    simp only [args,List.cons.injEq,and_true] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    exact hh
  refine ⟨out,cn+cd+1,runs_seq_iff.mpr (Or.inr ⟨mid,cn,cd,hrn,hrd,rfl⟩),
    ?_,hdvals,?_,?_,by omega⟩
  · intro e he
    have hmul := Nat.mul_le_mul_right L (hedges e he)
    rw [Nat.succ_mul] at hmul
    have hblock (k : ℕ) (hk : k < L) :
        out.mem (num+e*L+k) = mid.mem (num+e*L+k) :=
      hfd _ (Or.inr (Or.inl ⟨by omega,by omega⟩))
    obtain ⟨hv,hval⟩ := hnvals e he
    refine ⟨fun k hk => hblock k hk ▸ hv k hk,?_⟩
    unfold fixVal at *
    rw [intVal_congr hblock]
    exact hval
  · intro a h
    exact (hfd a (h.imp_right Or.inr)).trans (hfn a (h.imp_right fun _ => Or.inr (by omega)))
  · intro r hr63 hr64
    exact (hrdRegs r hr64).trans (hrnRegs r hr63)

/-- The root writer and publisher use the two shared graph pointers
and the staged payload registers. The first compact vertex name is
the root on a connected input. Register forty-four still points to the
original vertex list for graph initialization. -/
def stagedPublishArgs : List Expr :=
  [.reg 47,.reg 48,.reg 48,.reg 49,.reg 50,.reg 56,.reg 57,.reg 52,.reg 53,.reg 40]

/-- Once the branch payloads are in memory, publish their pointer while
preserving the rest of the previously allocated prefix. -/
theorem stagedPublish_runs
    {w entry vCap eCap h L P floor oldEnd newEnd : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ} {branch : LSF} {G : MGraph}
    (st : State) (base graph roots stretch collection j numerator denominator vertices : ℕ)
    (hp : MeetsContract w p entry
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G))
    (hb : st.regs 47 = base) (hg : st.regs 48 = graph) (hr : st.regs 49 = roots)
    (hs : st.regs 50 = stretch) (hc : st.regs 56 = collection) (hj : st.regs 57 = j)
    (hn : st.regs 52 = numerator) (hd : st.regs 53 = denominator)
    (hv : st.regs 40 = vertices) :
    let args := [base,graph,graph,roots,stretch,collection,j,numerator,denominator,vertices]
    (∀ a ∈ args, a < 2^w) →
    (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G).pre
      args st.mem →
    ∃ out cost, Runs w p ω (.call 58 entry stagedPublishArgs) st .normal out cost ∧
      out.regs 58 = 0 ∧ out.mem (collection+1+j) = base ∧
      (∀ a, a < oldEnd ∨ newEnd ≤ a → a ≠ collection+1+j → out.mem a = st.mem a) ∧
      BranchWithin out.mem base floor newEnd vCap eCap L E ∧
      LSFAt out.mem base vCap eCap h L P E branch ∧
      (∀ r, r ≠ 58 → out.regs r = st.regs r) ∧ cost ≤ 127 := by
  intro args hw hpre
  have ha : evalArgs w st stagedPublishArgs = some args := by
    simp [stagedPublishArgs,args,evalArgs,Expr.eval,hb,hg,hr,hs,hc,hj,hn,hd,hv]
  obtain ⟨out,cost,ret,hrun,hpost,hresult,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 58) hp ha hw hpre ω
  obtain ⟨ptr,coll,k,hptr,hcoll,hk,hret,hslot,hframe,hspan,hlayout⟩ := hpost
  simp [args] at hptr hcoll hk
  cases hptr
  cases hcoll
  cases hk
  exact ⟨out,cost,hrun,hresult.trans hret,hslot,hframe,hspan,hlayout,hregs,hcost⟩

/-- Publish the branch after writing both stretch arrays. -/
def stagedStretchPublishBody (scatter publish : ℕ) : Stmt :=
  .seq (stagedBranchStretchBody scatter) (.call 58 publish stagedPublishArgs)

/-- The stretch pass preserves the graph and the zero root bits needed
by the publisher. Only the new collection slot can change below the
previous allocation end. -/
theorem stagedStretchPublish_runs {w scatter publish vCap eCap h L P floor oldEnd : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ} {branch : LSF} {G : MGraph}
    (st mid : State) (cs records count collection j vertices : ℕ)
    (hv : G.V.Nonempty) (hname : st.mem vertices = vertexName G 0)
    (hvertex : firstVertex G.V < vCap) (hmodel : componentRoots G = branch.F.R)
    (hw : 1 < 2^w) (hfloor : floor ≤ oldEnd) (hbase : oldEnd ≤ records)
    (hedges : ∀ e ∈ E, e < eCap) :
    let base := records+3*count
    let graph := base+4
    let roots := graph+dynGraphSize vCap eCap
    let stretch := roots+vCap
    let addresses := stretch+2
    let num := addresses+eCap
    let den := num+eCap*L
    let stop := den+eCap*L
    collection+1+j < base → vertices < addresses → stop < 2^w →
    (∀ v < vCap, st.mem (roots+v) = 0) →
    DynGraphAt st.mem graph vCap eCap branch.T →
    DynGraphAt st.mem graph vCap eCap branch.F.F →
    Runs w p ω (stagedBranchStretchBody scatter) st .normal mid cs →
    (∀ a, a < addresses ∨ stop ≤ a → mid.mem a = st.mem a) →
    EdgeValuesAt mid.mem num h L P E branch.wstr →
    EdgeValuesAt mid.mem den h L P E (fun _ => 1) →
    (∀ r, r ≠ 63 → r ≠ 64 → mid.regs r = st.regs r) →
    st.regs 47 = base → st.regs 48 = graph → st.regs 49 = roots →
    st.regs 50 = stretch → st.regs 56 = collection → st.regs 57 = j →
    st.regs 52 = num → st.regs 53 = den → st.regs 40 = vertices →
    MeetsContract w p publish
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd stop E branch G) →
    ∃ out cost, Runs w p ω (stagedStretchPublishBody scatter publish) st .normal out cost ∧
      out.mem (collection+1+j) = base ∧
      (∀ a, a < oldEnd ∨ stop ≤ a → a ≠ collection+1+j → out.mem a = st.mem a) ∧
      BranchWithin out.mem base floor stop vCap eCap L E ∧
      LSFAt out.mem base vCap eCap h L P E branch ∧
      (∀ r, r ≠ 58 → r ≠ 63 → r ≠ 64 → out.regs r = st.regs r) ∧ cost ≤ cs+128 := by
  intro base graph roots stretch addresses num den stop hslot hvword hfit hz ht hf
    hsRun hframe hn hd hmidRegs hb hg hr hst hc hj hnum hden hvreg hp
  have hchain : oldEnd ≤ base ∧ base < addresses ∧ roots ≤ addresses ∧ addresses ≤ stop := by
    dsimp [base,graph,roots,stretch,addresses,num,den,stop]
    omega
  have hagree (a : ℕ) (_ : graph ≤ a) (ha : a < graph+dynGraphSize vCap eCap) :
      mid.mem a = st.mem a := hframe a (Or.inl (ha.trans_le hchain.2.2.1))
  have hpre := stagedBranchPayload_publish_pre records count collection j vertices
    hv ((hframe vertices (Or.inl hvword)).trans hname) hvertex hmodel hw hfloor hbase hedges
    hslot hfit (fun v hv' => (hframe (roots+v) (Or.inl (by dsimp [addresses,stretch]; omega))).trans (hz v hv'))
    (ht.of_agree hagree) (hf.of_agree hagree) hn hd
  have hwords : ∀ a ∈ [base,graph,graph,roots,stretch,collection,j,num,den,vertices],
      a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp [stop,den,num,addresses,stretch,roots,graph] at * <;> omega
  obtain ⟨out,cp,hRun,_,hptr,hprefix,hwithin,hlayout,hregs,hcost⟩ :=
    stagedPublish_runs (ω := ω) mid base graph roots stretch collection j num den vertices
      hp ((hmidRegs _ (by decide) (by decide)).trans hb)
      ((hmidRegs _ (by decide) (by decide)).trans hg)
      ((hmidRegs _ (by decide) (by decide)).trans hr)
      ((hmidRegs _ (by decide) (by decide)).trans hst)
      ((hmidRegs _ (by decide) (by decide)).trans hc)
      ((hmidRegs _ (by decide) (by decide)).trans hj)
      ((hmidRegs _ (by decide) (by decide)).trans hnum)
      ((hmidRegs _ (by decide) (by decide)).trans hden)
      ((hmidRegs _ (by decide) (by decide)).trans hvreg) hwords hpre
  exact ⟨out,cs+cp+1,runs_seq_iff.mpr (Or.inr ⟨mid,cs,cp,hsRun,hRun,rfl⟩),hptr,
    fun a ha hne => (hprefix a ha hne).trans (hframe a (by omega)),
    hwithin,hlayout,fun r h58 h63 h64 => (hregs r h58).trans (hmidRegs r h63 h64),by omega⟩

/-- Compute the output layout before scattering and publishing a branch. -/
def stagedBranchOutputBody (scatter publish : ℕ) : Stmt :=
  .seq installStagedBranchPayloadLayout (stagedStretchPublishBody scatter publish)

/-- The runtime layout does not modify memory. Its register frame
lets the stretch-and-publish phase reuse all compact inputs. -/
theorem stagedBranchOutput_runs {w scatter publish : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (records count vCap eCap L : ℕ)
    (hRecords : st.regs 16 = records) (hCount : st.regs 13 = count)
    (hv : st.regs 41 = vCap) (he : st.regs 42 = eCap)
    (hL : st.regs 55 = L) (hw : 9 < 2^w)
    {Q : State → Prop} (bound : ℕ) :
    let base := records+3*count
    let graph := base+4
    let roots := graph+dynGraphSize vCap eCap
    let stretch := roots+vCap
    let addresses := stretch+2
    let num := addresses+eCap
    let den := num+eCap*L
    let stop := den+eCap*L
    stop < 2^w →
    (∀ ready : State, ready.mem = st.mem →
      ready.regs 47 = base → ready.regs 48 = graph → ready.regs 49 = roots →
      ready.regs 50 = stretch → ready.regs 51 = addresses → ready.regs 52 = num →
      ready.regs 53 = den → ready.regs 54 = stop →
      (∀ r, r < 47 ∨ 54 < r → ready.regs r = st.regs r) →
      ∃ out cost, Runs w p ω (stagedStretchPublishBody scatter publish) ready .normal out cost ∧
        Q out ∧ cost ≤ bound) →
    ∃ out cost, Runs w p ω (stagedBranchOutputBody scatter publish) st .normal out cost ∧
      Q out ∧ cost ≤ argsSize (stagedBranchPayloadArgs (.reg 55))+18+bound := by
  intro base graph roots stretch addresses num den stop hfit hnext
  obtain ⟨ready,cl,hl,hm,hb,hg,hr,hs,ha,hn,hd,ht,hregs,hcl⟩ :=
    installStagedBranchPayloadLayout_runs (p := p) (ω := ω) st records count vCap eCap L
      hRecords hCount hv he hL hw hfit
  obtain ⟨out,cp,hp,hQ,hcp⟩ := hnext ready hm hb hg hr hs ha hn hd ht hregs
  exact ⟨out,cl+cp+1,runs_seq_iff.mpr (Or.inr ⟨ready,cl,cp,hl,hp,rfl⟩),hQ,by omega⟩

/-- Scatter the model stretches and publish the resulting branch in its
collection slot, with a linear scan cost in the live edge count. -/
theorem stagedBranchOutput_model_runs
    {w scatter publish translate scatterCopy copyBlock copy writeSource root serialize
      descriptor finish header publishSlot vCap eCap h L P caller floor oldEnd : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (records count collection j vertices indices src stride unit : ℕ)
    (hnl : (nonLoopEdges G).Nonempty)
    (hRecords : st.regs 16 = records) (hCount : st.regs 13 = count)
    (hvCap : st.regs 41 = vCap) (heCap : st.regs 42 = eCap)
    (hwLayout : 9 < 2^w)
    (hG : G.IsValid) (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hvcap : ∀ v ∈ G.V, v < vCap) (hw : 1 < 2^w)
    (hfloor : floor ≤ oldEnd) (hbase : oldEnd ≤ records) (hedges : ∀ e ∈ G.E, e < eCap)
    (hi : st.regs 59 = indices) (hm : st.regs 1 = (representativeGraph G ℓ).m)
    (hs : st.regs 36 = src) (hst : st.regs 37 = stride) (hu : st.regs 60 = unit)
    (he : st.regs 61 = G.m) (hl : st.regs 55 = L)
    (hc : st.regs 56 = collection) (hj : st.regs 57 = j) (hvreg : st.regs 40 = vertices)
    (names : ℕ) (hn : st.regs 62 = names)
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
    let query := stretchQuery oracle H ℓ (weightPrecision C H)
    let v := weights (weightPrecision C H) (roundedScale C H) query j
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    let base := records+3*count
    let graph := base+4
    let roots := graph+dynGraphSize vCap eCap
    let stretch := roots+vCap
    let addresses := stretch+2
    let num := addresses+eCap
    let den := num+eCap*L
    let stop := den+eCap*L
    (∀ i < H.n, st.mem (vertices+i) = vertexName H i) →
    collection+1+j < base → vertices < addresses → stop < 2^w → ZeroFrom st.mem roots →
    DynGraphAt st.mem graph vCap eCap branch.T → DynGraphAt st.mem graph vCap eCap branch.F.F →
    componentRoots G = branch.F.R →
    G.m < 2^w → src < 2^w → stride < 2^w → L < 2^w →
    indices+G.m ≤ addresses → names+G.m ≤ addresses → G.m ≤ eCap → eCap ≤ 2^w →
    (∀ i < G.m, st.mem (indices+i) = branchStretchIndex G ℓ (edgeName G i)) →
    (∀ i < G.m, st.mem (names+i) = edgeName G i) →
    unit+L ≤ addresses → Valid st.mem unit h L → fixVal st.mem unit h L P = 1 →
    (∀ i < H.m, src+i*stride+L ≤ addresses ∧ Valid st.mem (src+i*stride) h L ∧
      fixVal st.mem (src+i*stride) h L P = query v (edgeName H i)) →
    ∃ out cost, Runs w p ω (stagedBranchOutputBody scatter publish) st .normal out cost ∧
      out.mem (collection+1+j) = base ∧
      (∀ a, a < oldEnd ∨ stop ≤ a → a ≠ collection+1+j → out.mem a = st.mem a) ∧
      ZeroFrom out.mem stop ∧
      BranchWithin out.mem base floor stop vCap eCap L G.E ∧
      LSFAt out.mem base vCap eCap h L caller G.E branch ∧
      out.regs 54 = stop ∧ out.regs 38 = st.regs 38 ∧
      cost ≤ argsSize (stagedBranchPayloadArgs (.reg 55))+18+2*((17*L+92)*G.m+51)+129 := by
  intro H query v branch base graph roots stretch addresses num den stop
    hvnames hslot hvaddr hfit hrootZero ht hf hmodel hmWord hsrcWord hstrideWord hLWord
    hiEnd hnEnd hmCap hcap hindex hnames huEnd huValid huVal hrep
  let args := [indices,H.m,src,stride,unit,addresses,G.m,names,num,L]
  have hHWord : H.m < 2^w :=
    (Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1).trans_lt hmWord
  have hwords : ∀ a ∈ args, a < 2^w := by
    intro a ha'
    simp only [args,List.mem_cons,List.not_mem_nil,or_false] at ha'
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (dsimp [stop,den,num] at hfit ⊢; omega)
  let contract := namedStretchContract w h L P eCap
    (branchStretchIndex G ℓ ∘ edgeName G) (edgeName G)
  have hpre : contract.pre args st.mem :=
    namedStretch_pre_of_compact G ℓ st.mem indices src stride unit addresses names num
      hw hiEnd hnEnd (Nat.add_le_add_left hmCap _) (by
        dsimp [stop,den] at hfit
        omega) hcap hnames hedges huEnd huValid (hwords H.m (by simp [args]))
      hindex (fun i hi' => ⟨(hrep i hi').1,(hrep i hi').2.1⟩)
  have hscatterContract : MeetsContract w p scatter contract :=
    namedStretch_meetsContract _ _ hscatter
      (stretchSource_meetsContract _ htranslate (writeStretchSource_meetsContract hwrite))
      (fun _ _ _ _ => scatterBranchStretch_meetsContract _ _ hscatterCopy
        (copyBranchStretch_meetsContract hcopyBlock hcopy))
  obtain ⟨ready,cl,hlayout,hmem,hb,hg,hr,hstr,ha,hnum,hden,hstopReg,hkeep,hcl⟩ :=
    installStagedBranchPayloadLayout_runs (p := p) (ω := ω) st records count vCap eCap L
      hRecords hCount hvCap heCap hl hwLayout hfit
  have hk r (hr : r < 47 ∨ 54 < r) := hkeep r hr
  obtain ⟨mid,cs,hrs,hnv,hdv,hfrm,hregs,hcs⟩ :=
    stagedBranchStretch_runs (ω := ω) ready oracle C G ℓ j indices src stride unit addresses
      names num den hnl ((hk 59 (by decide)).trans hi) ((hk 1 (by decide)).trans hm)
      ((hk 36 (by decide)).trans hs) ((hk 37 (by decide)).trans hst)
      ((hk 60 (by decide)).trans hu) ha ((hk 61 (by decide)).trans he)
      ((hk 62 (by decide)).trans hn) hnum hden ((hk 55 (by decide)).trans hl) (by omega)
      huEnd (hmem.symm ▸ huValid) (le_refl _) hfit hedges hscatterContract hwords
      (hmem.symm ▸ hpre) (fun i hi' => hmem.symm ▸ (hrep i hi').2.2) (hmem.symm ▸ huVal)
  obtain ⟨e,he⟩ := hnl
  have hv : G.V.Nonempty := ⟨G.tail e,(hG e (Finset.mem_filter.mp he).1).1⟩
  have hV : H.V = G.V := representativeGraph_vertices_eq ℓ hG ⟨e,he⟩ hconn
  have hnV : 0 < H.n := by
    change 0 < H.V.card
    rw [hV]
    exact Finset.card_pos.mpr hv
  have hname : st.mem vertices = vertexName G 0 := by
    simpa only [Nat.add_zero, ← firstVertex_eq_vertexName_zero (hV.symm ▸ hv),
      ← firstVertex_eq_vertexName_zero hv,hV] using hvnames 0 hnV
  have hvertex : firstVertex G.V < vCap := by
    rw [firstVertex_eq_vertexName_zero hv]
    exact hvcap _ (vertexName_mem (Finset.card_pos.mpr hv))
  have hpub : MeetsContract w p publish
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd stop G.E branch G) :=
    publishRootedBranch_meetsContract hpublish (branchRoots_meetsContract hroot hv hconn)
      (serializeBranch_meetsContract hserialize (stretchDescriptor_meetsContract hdescriptor)
        (finishBranch_meetsContract hfinish (branchHeader_meetsContract hheader)
          (publishBranch_meetsContract hslotWriter)))
  have hz : ∀ u < vCap, st.mem (roots+u) = 0 :=
    fun u _ => hrootZero _ (Nat.le_add_right _ _)
  have hfresh : ZeroFrom st.mem stop := by
    intro a ha'
    apply hrootZero
    dsimp [stop,den,num,addresses,stretch] at ha'
    omega
  obtain ⟨out,cost,hRun,hptr,hprefix,hwithin,hLSF,hout,hcost⟩ :=
    stagedStretchPublish_runs ready mid cs records count collection j vertices
      hv (hmem.symm ▸ hname) hvertex hmodel hw hfloor hbase hedges hslot hvaddr hfit
      (hmem.symm ▸ hz) (hmem.symm ▸ ht) (hmem.symm ▸ hf) hrs
      hfrm hnv hdv hregs hb hg hr hstr ((hk 56 (by decide)).trans hc)
      ((hk 57 (by decide)).trans hj) hnum hden ((hk 40 (by decide)).trans hvreg) hpub
  have hstop : base ≤ stop := by
    dsimp [stop,den,num,addresses,stretch,roots,graph]
    omega
  have hzero : ZeroFrom out.mem stop := by
    intro a ha
    have hne : a ≠ collection+1+j := ne_of_gt (hslot.trans_le (hstop.trans ha))
    exact (hprefix a (Or.inr ha) hne).trans ((congrFun hmem a).trans (hfresh a ha))
  refine ⟨out,cl+cost+1,runs_seq_iff.mpr (Or.inr ⟨ready,cl,cost,hlayout,hRun,rfl⟩),
    hptr,fun a ha hne => (hprefix a ha hne).trans (congrFun hmem a),hzero,hwithin,lsfAt_changePrecision hLSF caller,
    (hout 54 (by decide) (by decide) (by decide)).trans hstopReg,
    (hout 38 (by decide) (by decide) (by decide)).trans (hk 38 (by decide)),by omega⟩

/-- In Definition 5.8 (pages 19–20), the branch tree and forest use the
same restricted graph, with the original vertex names restored. -/
theorem fixedPointBranch_sharedGraph
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G T : MGraph) (ℓ : ℕ → ℝ) (j : ℕ)
    (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let F : MGraph :=
      { V := G.V, E := (restoreTreeNames H T).E ∩ H.E, tail := G.tail, head := G.head }
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    oracle H (safeLen H ℓ) v = restoreTreeNames H T →
    branch.T = F ∧ branch.F.F = F ∧ branch.F.R = componentRoots G := by
  intro H P query v F branch he
  dsimp [branch,fixedPointLastLevelTool]
  simp only [hnl,ite_eq_left]
  change
    { V := G.V, E := (oracle H (safeLen H ℓ) v).E ∩ H.E, tail := G.tail, head := G.head } = F ∧
    { V := G.V, E := (oracle H (safeLen H ℓ) v).E ∩ H.E, tail := G.tail, head := G.head } = F ∧
    True
  rw [he]
  exact ⟨rfl,rfl,True.intro⟩

/-- The graph initializer supplies both graph pointers and the zero
root range consumed by the branch publisher. -/
theorem stagedBranchGraph_publish_payload
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (C : ℝ) (G T : MGraph) (ℓ : ℕ → ℝ) (j graph vCap eCap : ℕ)
    (mem : ℕ → ℕ) (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let P := weightPrecision C H
    let query := stretchQuery oracle H ℓ P
    let v := weights P (roundedScale C H) query j
    let F : MGraph :=
      { V := G.V, E := (restoreTreeNames H T).E ∩ H.E, tail := G.tail, head := G.head }
    let branch := ((fixedPointLastLevelTool oracle C).build G ℓ).2 j
    oracle H (safeLen H ℓ) v = restoreTreeNames H T →
    DynGraphAt mem graph vCap eCap F →
    ZeroFrom mem (graph+dynGraphSize vCap eCap) →
    DynGraphAt mem graph vCap eCap branch.T ∧
    DynGraphAt mem graph vCap eCap branch.F.F ∧ componentRoots G = branch.F.R ∧
    ∀ u < vCap, mem (graph+dynGraphSize vCap eCap+u) = 0 := by
  intro H P query v F branch htree hgraph hz
  obtain ⟨hT,hF,hR⟩ := fixedPointBranch_sharedGraph oracle C G T ℓ j hnl htree
  exact ⟨hT.symm ▸ hgraph,hF.symm ▸ hgraph,hR.symm,
    fun u _ => hz _ (Nat.le_add_right _ _)⟩

end MinCostFlow.LastLevelProgram
