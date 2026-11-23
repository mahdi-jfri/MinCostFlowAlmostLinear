module

public import MinCostFlow.LastLevelProgram.BranchStretch

public import MinCostFlow.LastLevelProgram.BranchRoots
public import MinCostFlow.LastLevelProgram.CollectionHeader
public import MinCostFlow.LastLevelProgram.BranchGraph
public import MinCostFlow.LastLevelProgram.FixedPoint
public import MinCostFlow.LastLevelProgram.Readout
import MinCostFlow.DynSpanner.Program.DynGraphInit
import WordRAM.Tactic
/-!
# Loop-only stretch table

The loop-only rebuild for Definition 5.8 (pages 19–20) exposes one
empty forest and unit stretches. Copy the positive input blocks to
private storage and point both sides of the stretch quotient there.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num MinRatio DynSpanner.Program

/-- Copy the live blocks and publish their shared stretch descriptor. -/
@[expose] def loopOnlyStretchBody (copy : ℕ) : Stmt :=
  .seq (loopOnlyStretchLoop copy) loopOnlyStretchDescriptor

/-- The loop-only stretch table represents unit values on the full live edge set. -/
theorem loopOnlyStretchBody_runs {w copy h L P : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (src desc table names cap : ℕ) (edges : List ℕ) (E : Finset ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (h13 : st.regs 13 = src) (h14 : st.regs 14 = L) (h58 : st.regs 58 = desc)
    (h60 : st.regs 60 = table) (h61 : st.regs 61 = edges.length) (h62 : st.regs 62 = names)
    (hlist : ListAt st.mem names edges) (hnodup : edges.Nodup)
    (hmem : ∀ e, e ∈ edges ↔ e ∈ E) (hcap : ∀ e ∈ E, e < cap)
    (hw : 1 < 2^w) (hdesc : desc+2 < 2^w) (hsep : desc+2 ≤ table)
    (hn : names+edges.length ≤ table) (hs : src+cap*L ≤ table) (hd : table+cap*L < 2^w)
    (hvalues : ∀ e ∈ E, Valid st.mem (src+e*L) h L ∧ 0 < fixVal st.mem (src+e*L) h L P) :
    ∃ out cost, Runs w p ω (loopOnlyStretchBody copy) st .normal out cost ∧
      out.mem desc = table ∧ out.mem (desc+1) = table ∧
      StretchValuesAt out.mem desc h L P E (fun _ => 1) ∧
      (∀ a, (a < desc ∨ desc+2 ≤ a) → (a < table ∨ table+cap*L ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, r ≠ 3 → r ≠ 8 → r ≠ 63 → out.regs r = st.regs r) ∧
      cost ≤ (17*L+37)*edges.length+17 := by
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ := (loopOnlyStretchLoop_triple st src table names cap L edges
    hc h13 h14 h60 h61 h62 hlist hnodup (fun e he => hcap e ((hmem e).mp he)) hw hn hs hd).runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hcopy,hframe,hregs⟩ := hpost
    have hvalues' e (he : e ∈ E) : Valid mid.mem (table+e*L) h L ∧
        0 < fixVal mid.mem (table+e*L) h L P := by
      obtain ⟨hv,hp⟩ := hvalues e he
      have hcell := hcopy e ((hmem e).mpr he)
      refine ⟨fun i hi => (hcell i hi).trans_lt (hv i hi),?_⟩
      simpa only [fixVal,intVal_congr hcell] using hp
    obtain ⟨out,hdescRun,hnum,hden,hlayout,hframe',hregs'⟩ := loopOnlyStretchDescriptor_runs (ω := ω)
      mid desc table E ((hregs 58 (by decide) (by decide) (by decide)).trans h58)
      ((hregs 60 (by decide) (by decide) (by decide)).trans h60) hdesc hsep hvalues'
    exact ⟨out,c+10,runs_seq_iff.mpr (Or.inr ⟨mid,c,9,hr,hdescRun,by omega⟩),
      hnum,hden,hlayout,fun a ha hb => (hframe' a ha).trans (hframe a hb),
      fun r h3 h8 h63 => (congrFun hregs' r).trans (hregs r h3 h8 h63),by omega⟩

/-- The one loop-only readout uses a single empty forest for both graph pointers. -/
def loopOnlyLSF (G : MGraph) : LSF :=
  let F : MGraph := { V := G.V, E := ∅, tail := G.tail, head := G.head }
  { T := F, F := { F := F, R := G.V }, wstr := fun _ => 1 }

/-- Publish the empty forest, its vertex presence bits and the unit stretches. -/
@[expose] def loopOnlyBranchHeader (header : ℕ) : Stmt :=
  .call 7 header [.reg 56,.reg 46,.reg 46,.bin .add (.reg 46) (.const 4),.reg 58]

/-- The loop-only header exposes the shared empty forest and unit stretch table. -/
theorem loopOnlyBranchHeader_runs {w header vCap eCap h L P : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (base graph desc : ℕ)
    (hc : MeetsContract w p header (branchHeaderContract w vCap eCap h L P G.E (loopOnlyLSF G)))
    (h46 : st.regs 46 = graph) (h56 : st.regs 56 = base) (h58 : st.regs 58 = desc)
    (hF : DynGraphAt st.mem graph vCap eCap (loopOnlyLSF G).T)
    (hS : StretchValuesAt st.mem desc h L P G.E (fun _ => 1))
    (hw : 4 < 2^w) (hb : base+4 < 2^w) (hg : graph+4 < 2^w) (hd : desc < 2^w)
    (hbg : base+4 ≤ graph) (hbd : base+4 ≤ desc)
    (hn : base+4 ≤ st.mem desc) (he : base+4 ≤ st.mem (desc+1)) :
    ∃ out cost, Runs w p ω (loopOnlyBranchHeader header) st .normal out cost ∧
      out.mem base = graph ∧ out.mem (base+1) = graph ∧
      out.mem (base+2) = dgVPresBase graph ∧ out.mem (base+3) = desc ∧
      LSFAt out.mem base vCap eCap h L P G.E (loopOnlyLSF G) ∧
      (∀ a, a < base ∨ base+4 ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 7 → out.regs r = st.regs r) ∧ cost ≤ 40 := by
  let roots := dgVPresBase graph
  have ha : evalArgs w st
      [.reg 56,.reg 46,.reg 46,.bin .add (.reg 46) (.const 4),.reg 58] =
      some [base,graph,graph,roots,desc] := by
    simp [evalArgs,Expr.eval,BinOp.eval,h46,h56,h58,hw,hg,roots,dgVPresBase]
  have hwords : ∀ x ∈ [base,graph,graph,roots,desc], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    dsimp [roots,dgVPresBase] at *
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega
  obtain ⟨out,c,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 7) hc ha hwords
      ⟨base,graph,graph,roots,desc,rfl,hb,hF,hF,loopOnlyRoots_at (F := (loopOnlyLSF G).T) hF,hS,
        hbg,hbg,by dsimp [roots,dgVPresBase]; omega,hbd,hn,he⟩ ω
  obtain ⟨b,t,f,r,d,heq,_,hlsf,htree,hforest,hroots,hstretch,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := heq
  change c ≤ 7+32+1 at hcost
  exact ⟨out,c,hr,htree,hforest,hroots,hstretch,hlsf,hframe,hregs,hcost⟩

/-- Publish the single branch in its two-word collection. -/
@[expose] def loopOnlyCollectionHeader : Stmt :=
  .seq (.store (.reg 55) (.const 1))
    (.store (.bin .add (.reg 55) (.const 1)) (.reg 56))

/-- The collection header exposes the one loop-only branch and preserves its payload. -/
theorem loopOnlyCollectionHeader_runs {w vCap eCap h L P : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (collection base limit : ℕ)
    (h55 : st.regs 55 = collection) (h56 : st.regs 56 = base)
    (hw : 1 < 2^w) (hf : collection+1 < 2^w) (hb : collection+2 ≤ base)
    (hlayout : LSFAt st.mem base vCap eCap h L P G.E (loopOnlyLSF G))
    (hspan : BranchWithin st.mem base (collection+2) limit vCap eCap L G.E) :
    ∃ out, Runs w p ω loopOnlyCollectionHeader st .normal out 9 ∧
      CollectionPrefix out.mem collection 1 1 limit vCap eCap h L P G.E (fun _ => loopOnlyLSF G) ∧
      (∀ a, a < collection ∨ collection+2 ≤ a → out.mem a = st.mem a) ∧ out.regs = st.regs := by
  let mid := {st with mem := Function.update st.mem collection 1}
  let out := {mid with mem := Function.update mid.mem (collection+1) base}
  have hfirst : Runs w p ω (.store (.reg 55) (.const 1)) st .normal mid 3 :=
    runs_store_iff.mpr ⟨collection,1,congrArg some h55,by simp [Expr.eval,hw],rfl,rfl,rfl⟩
  have hnext : Runs w p ω (.store (.bin .add (.reg 55) (.const 1)) (.reg 56)) mid .normal out 5 :=
    runs_store_iff.mpr ⟨collection+1,base,by simp [mid,Expr.eval,BinOp.eval,h55,hw,hf],
      congrArg some h56,rfl,rfl,rfl⟩
  have hframe a (ha : a < collection ∨ collection+2 ≤ a) : out.mem a = st.mem a := by
    simp [out,mid,Function.update_of_ne (show a ≠ collection by omega),
      Function.update_of_ne (show a ≠ collection+1 by omega)]
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,3,5,hfirst,hnext,rfl⟩),?_,hframe,rfl⟩
  refine ⟨le_rfl,by simp [out,mid],?_⟩
  intro j hj
  have hj' : j = 0 := by omega
  subst j
  have hptr : out.mem (collection+1+0) = base := by simp [out]
  rw [hptr]
  obtain ⟨_,hB,ht,hT,hf,hF,hr,hR,hs,hS,hn,hd,hN,hD⟩ := hspan
  have hagree a (ha : collection+2 ≤ a) := hframe a (Or.inr ha)
  refine ⟨?_, lsfAt_of_agree_above hlayout hb ht hf hr hs hn hd hagree⟩
  unfold BranchWithin
  rw [hagree base hb, hagree (base+1) (by omega), hagree (base+2) (by omega),
    hagree (base+3) (by omega), hagree _ hs, hagree (st.mem (base+3)+1) (by omega)]
  exact ⟨hb,hB,ht,hT,hf,hF,hr,hR,hs,hS,hn,hd,hN,hD⟩

/-- Publish both the branch header and the collection that points to it. -/
@[expose] def loopOnlyPublish (header : ℕ) : Stmt :=
  .seq (loopOnlyBranchHeader header) loopOnlyCollectionHeader

/-- Publication makes the loop-only forest readable at the collection pointer. -/
theorem loopOnlyPublish_runs {w header vCap eCap h L P : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (collection base graph desc limit : ℕ)
    (hc : MeetsContract w p header (branchHeaderContract w vCap eCap h L P G.E (loopOnlyLSF G)))
    (h46 : st.regs 46 = graph) (h55 : st.regs 55 = collection)
    (h56 : st.regs 56 = base) (h58 : st.regs 58 = desc)
    (hF : DynGraphAt st.mem graph vCap eCap (loopOnlyLSF G).T)
    (hS : StretchValuesAt st.mem desc h L P G.E (fun _ => 1))
    (hb : base+4 < 2^w) (hg : graph+4 < 2^w) (hd : desc < 2^w)
    (hcb : collection+2 ≤ base) (hbg : base+4 ≤ graph) (hbd : base+4 ≤ desc)
    (hn : base+4 ≤ st.mem desc) (he : base+4 ≤ st.mem (desc+1))
    (hgraphEnd : graph+dynGraphSize vCap eCap ≤ limit) (hdescEnd : desc+2 ≤ limit)
    (hN : ∀ e ∈ G.E, st.mem desc+e*L+L ≤ limit)
    (hD : ∀ e ∈ G.E, st.mem (desc+1)+e*L+L ≤ limit) :
    ∃ out cost, Runs w p ω (loopOnlyPublish header) st .normal out cost ∧
      CollectionPrefix out.mem collection 1 1 limit vCap eCap h L P G.E (fun _ => loopOnlyLSF G) ∧
      (∀ a, (a < base ∨ base+4 ≤ a) → (a < collection ∨ collection+2 ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, r ≠ 7 → out.regs r = st.regs r) ∧ cost ≤ 50 := by
  obtain ⟨mid,c,hr,ht,hf,hroots,hstretch,hlayout,hframe,hregs,hcost⟩ :=
    loopOnlyBranchHeader_runs (ω := ω) st G base graph desc hc h46 h56 h58
      hF hS (by omega) hb hg hd hbg hbd hn he
  have hn' := hframe desc (Or.inr hbd)
  have hd' := hframe (desc+1) (Or.inr (by omega))
  have hspan : BranchWithin mid.mem base (collection+2) limit vCap eCap L G.E := by
    unfold BranchWithin
    rw [ht,hf,hroots,hstretch,hn',hd']
    have hrootEnd : dgVPresBase graph+vCap ≤ graph+dynGraphSize vCap eCap := by
      unfold dgVPresBase dynGraphSize
      omega
    exact ⟨hcb,by omega,by omega,hgraphEnd,by omega,hgraphEnd,
      by unfold dgVPresBase; omega,hrootEnd.trans hgraphEnd,by omega,hdescEnd,
      by omega,by omega,hN,hD⟩
  obtain ⟨out,hpub,hread,hout,hkeep⟩ := loopOnlyCollectionHeader_runs (w := w) (ω := ω)
    mid G collection base limit ((hregs 55 (by decide)).trans h55) ((hregs 56 (by decide)).trans h56)
    (by omega) (by omega) hcb hlayout hspan
  exact ⟨out,c+10,runs_seq_iff.mpr (Or.inr ⟨mid,c,9,hr,hpub,by omega⟩),hread,
    fun a ha hb' => (hout a hb').trans (hframe a ha),
    fun r h => (congrFun hkeep r).trans (hregs r h),by omega⟩

/-- Build the empty forest, copy its stretch blocks, and publish one branch. -/
@[expose] def loopOnlyBuild (init copy header : ℕ) : Stmt :=
  .seq (loopOnlyBranchGraph init) (.seq (loopOnlyStretchBody copy) (loopOnlyPublish header))

/-- The loop-only rebuild writes a complete private collection and
preserves memory below the collection and above its allocation. -/
theorem loopOnlyBuild_runs {w init copy header vCap eCap h L P : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (vertices edges : List ℕ)
    (vp ep lengths collection base graph desc table : ℕ)
    (hi : MeetsContract w p init (dgInitFromListsContract w vCap eCap (loopOnlyLSF G).T vertices []))
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hh : MeetsContract w p header (branchHeaderContract w vCap eCap h L P G.E (loopOnlyLSF G)))
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L)
    (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap) (h43 : st.regs 43 = vertices.length)
    (h44 : st.regs 44 = vp) (h45 : st.regs 45 = graph) (h55 : st.regs 55 = collection)
    (h56 : st.regs 56 = base) (h58 : st.regs 58 = desc) (h60 : st.regs 60 = table)
    (h61 : st.regs 61 = edges.length) (h62 : st.regs 62 = ep)
    (hw : 16 ≤ 2^w) (hfit : table+eCap*L < 2^w)
    (hcb : collection+2 ≤ base) (hbg : base+4 ≤ graph)
    (hgd : graph+dynGraphSize vCap eCap ≤ desc) (hdt : desc+2 ≤ table)
    (hvp : vp+vertices.length ≤ collection) (hep : ep+edges.length ≤ collection)
    (hlen : lengths+eCap*L ≤ collection) (hz : ZeroFrom st.mem graph)
    (hv : ∀ v ∈ G.V, v < vCap) (he : ∀ e ∈ G.E, e < eCap)
    (hvs : ListAt st.mem vp vertices) (hes : ListAt st.mem ep edges) (hnd : edges.Nodup)
    (hV : ∀ v, v ∈ vertices ↔ v ∈ G.V) (hE : ∀ e, e ∈ edges ↔ e ∈ G.E)
    (hvalues : ∀ e ∈ G.E, Valid st.mem (lengths+e*L) h L ∧ 0 < fixVal st.mem (lengths+e*L) h L P) :
    ∃ out cost, Runs w p ω (loopOnlyBuild init copy header) st .normal out cost ∧
      CollectionPrefix out.mem collection 1 1 (table+eCap*L) vCap eCap h L P G.E
        (fun _ => loopOnlyLSF G) ∧
      (∀ a < collection, out.mem a = st.mem a) ∧ ZeroFrom out.mem (table+eCap*L) ∧
      out.regs 60 = table ∧ out.regs 42 = eCap ∧ out.regs 14 = L ∧
      cost ≤ 130*vertices.length+(17*L+37)*edges.length+177 := by
  obtain ⟨built,c,hbuild,hF,hzero,hptr,hbelow,hregs,hcost⟩ :=
    loopOnlyBranchGraph_runs (ω := ω) st G vertices graph vp h41 h42 h43 h44 h45 hw
      (by omega) (by omega) hz hv hvs hV hi
  have hvalues' e (he' : e ∈ G.E) :
      Valid built.mem (lengths+e*L) h L ∧ 0 < fixVal built.mem (lengths+e*L) h L P := by
    obtain ⟨hvalid,hpos⟩ := hvalues e he'
    have hbound : e*L+L ≤ eCap*L := by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (he e he'))
    have hcell j (hj : j < L) : built.mem (lengths+e*L+j) = st.mem (lengths+e*L+j) :=
      hbelow _ (by omega)
    exact ⟨fun j hj => (hcell j hj).trans_lt (hvalid j hj),
      by simpa only [fixVal,intVal_congr hcell] using hpos⟩
  obtain ⟨ready,d,hstretch,hnum,hden,hS,hroom,hkeep,hcost'⟩ :=
    loopOnlyStretchBody_runs (ω := ω) built lengths desc table ep eCap edges G.E hc
      ((hregs 13 (by decide)).trans h13) ((hregs 14 (by decide)).trans h14)
      ((hregs 58 (by decide)).trans h58) ((hregs 60 (by decide)).trans h60)
      ((hregs 61 (by decide)).trans h61) ((hregs 62 (by decide)).trans h62)
      (hes.congr fun a ha hb => hbelow a (by omega)) hnd hE he
      (by omega) (by omega) hdt (by omega) (by omega) hfit hvalues'
  have hsize : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
  have hforest : DynGraphAt ready.mem graph vCap eCap (loopOnlyLSF G).T :=
    hF.of_agree (fun a ha hb => hroom a (by omega) (by omega))
  obtain ⟨out,f,hpublish,hLSF,houtside,hpublishRegs,hcost''⟩ :=
    loopOnlyPublish_runs (ω := ω) ready G collection base graph desc (table+eCap*L) hh
      ((hkeep 46 (by decide) (by decide) (by decide)).trans hptr)
      ((hkeep 55 (by decide) (by decide) (by decide)).trans ((hregs 55 (by decide)).trans h55))
      ((hkeep 56 (by decide) (by decide) (by decide)).trans ((hregs 56 (by decide)).trans h56))
      ((hkeep 58 (by decide) (by decide) (by decide)).trans ((hregs 58 (by decide)).trans h58))
      hforest hS (by omega) (by omega) (by omega) hcb hbg (by omega)
      (by rw [hnum]; omega) (by rw [hden]; omega) (by omega) (by omega)
      (fun e he' => by
        rw [hnum]
        have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (he e he'))
        rw [Nat.succ_mul] at hmul
        omega)
      (fun e he' => by
        rw [hden]
        have hmul := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (he e he'))
        rw [Nat.succ_mul] at hmul
        omega)
  have hseq : Runs w p ω (.seq (loopOnlyStretchBody copy) (loopOnlyPublish header))
      built .normal out (d+f+1) :=
    runs_seq_iff.mpr (Or.inr ⟨ready,d,f,hstretch,hpublish,rfl⟩)
  refine ⟨out,c+(d+f+1)+1,runs_seq_iff.mpr (Or.inr ⟨built,c,d+f+1,hbuild,hseq,rfl⟩),
    hLSF,?_,?_,?_,?_,?_,by omega⟩
  · intro a ha
    exact (houtside a (by omega) (by omega)).trans
      ((hroom a (by omega) (by omega)).trans (hbelow a (by omega)))
  · intro a ha
    exact (houtside a (by omega) (by omega)).trans
      ((hroom a (by omega) (by omega)).trans (hzero a (by omega)))
  · exact (hpublishRegs 60 (by decide)).trans
      ((hkeep 60 (by decide) (by decide) (by decide)).trans ((hregs 60 (by decide)).trans h60))
  · exact (hpublishRegs 42 (by decide)).trans
      ((hkeep 42 (by decide) (by decide) (by decide)).trans ((hregs 42 (by decide)).trans h42))
  · exact (hpublishRegs 14 (by decide)).trans
      ((hkeep 14 (by decide) (by decide) (by decide)).trans ((hregs 14 (by decide)).trans h14))

/-- Reserve the collection, branch header, empty forest and stretch descriptor.
Register 4 is the caller heap and registers 41 and 42 are its graph capacities. -/
@[expose] def loopOnlyReserve : Stmt :=
  .seq (.assign 55 (.reg 4))
  (.seq (.assign 56 (.bin .add (.reg 55) (.const 2)))
  (.seq (.assign 45 (.bin .add (.reg 56) (.const 4)))
  (.seq (.assign 58 (.bin .add (.reg 45) (.bin .add (.const 4)
    (.bin .add (.bin .mul (.const 7) (.reg 41)) (.bin .mul (.const 9) (.reg 42))))))
  (.assign 60 (.bin .add (.reg 58) (.const 2))))))

/-- Reservation computes the ordered payload addresses and keeps memory untouched. -/
theorem loopOnlyReserve_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (heap vCap eCap : ℕ)
    (h4 : st.regs 4 = heap) (h41 : st.regs 41 = vCap) (h42 : st.regs 42 = eCap)
    (hw : 16 ≤ 2^w) (hroom : heap+8+dynGraphSize vCap eCap < 2^w) :
    ∃ o out cost, Runs w p ω loopOnlyReserve st o out cost ∧
      (o = .normal ∧ out.mem = st.mem ∧ out.regs 55 = heap ∧ out.regs 56 = heap+2 ∧
        out.regs 45 = heap+6 ∧ out.regs 58 = heap+6+dynGraphSize vCap eCap ∧
        out.regs 60 = heap+8+dynGraphSize vCap eCap ∧
        ∀ r, r ∉ ([45,55,56,58,60] : List ℕ) → out.regs r = st.regs r) ∧ cost ≤ 33 := by
  have hd := hroom
  unfold dynGraphSize at hd
  apply runs_start_le
  unfold loopOnlyReserve
  wram_run
  · simp [dynGraphSize,h41,h42,Nat.add_assoc,Function.update_of_ne]
    constructor
    · omega
    · intro r h45 h55 h56 h58 h60
      simp [Function.update_of_ne,h45,h55,h56,h58,h60]
  · wram_cost

/-- Load the original graph lists and caller length arguments for the empty branch. -/
@[expose] def loopOnlyLoadInput : Stmt :=
  let add := Expr.bin .add
  let loadAt := fun k => Expr.load (add (.reg 0) (.const k))
  let base := add (.reg 0) (.const 4)
  .seq (.assign 13 (.reg 1))
  (.seq (.assign 14 (.reg 2))
  (.seq (.assign 41 (.load (.reg 0)))
  (.seq (.assign 42 (loadAt 1))
  (.seq (.assign 43 (loadAt 2))
  (.seq (.assign 61 (loadAt 3))
  (.seq (.assign 44 (add base (.reg 41)))
    (.assign 62 (add (add base (.bin .mul (.const 7) (.reg 41))) (.reg 42)))))))))

/-- The loader supplies graph capacities, live counts, and the list bases
without modifying caller memory. -/
theorem loopOnlyLoadInput_runs {w g vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (lengths L : ℕ)
    (hG : DynGraphAt st.mem g vCap eCap G)
    (h0 : st.regs 0 = g) (h1 : st.regs 1 = lengths) (h2 : st.regs 2 = L)
    (hw : 16 ≤ 2^w) (hg : g+dynGraphSize vCap eCap < 2^w) :
    ∃ o out cost, Runs w p ω loopOnlyLoadInput st o out cost ∧
      (o = .normal ∧ out.mem = st.mem ∧ out.regs 13 = lengths ∧ out.regs 14 = L ∧
      out.regs 41 = vCap ∧ out.regs 42 = eCap ∧ out.regs 43 = G.n ∧ out.regs 61 = G.m ∧
      out.regs 44 = dgVListBase g vCap ∧ out.regs 62 = dgEListBase g vCap eCap ∧
      out.regs 4 = st.regs 4) ∧ cost ≤ 55 := by
  have hv : st.mem g = vCap := hG.2.2.2.1
  have he : st.mem (g+1) = eCap := hG.2.2.2.2.1
  have hn : st.mem (g+2) = G.n := hG.2.2.2.2.2.1
  have hm : st.mem (g+3) = G.m := hG.2.2.2.2.2.2.1
  unfold dynGraphSize at hg
  apply runs_start_le
  have hvAddr : st.regs 0 + 4 + st.mem (st.regs 0) < 2^w := by rw [h0,hv]; omega
  have hvMul : 7 * st.mem (st.regs 0) < 2^w := by rw [h0,hv]; omega
  have heBase : st.regs 0 + 4 + 7 * st.mem (st.regs 0) < 2^w := by rw [h0,hv]; omega
  have heAddr : st.regs 0 + 4 + 7 * st.mem (st.regs 0) + st.mem (st.regs 0+1) < 2^w := by
    rw [h0,hv,he]
    omega
  unfold loopOnlyLoadInput
  wram_run
  all_goals first | solve | wram_cost | (simp [h0,h2,hv,he,hn,hm,dgVListBase,dgEListBase])

/-- Prepare all runtime registers needed by the loop-only collection builder. -/
@[expose] def loopOnlySetup : Stmt := .seq loopOnlyLoadInput loopOnlyReserve

/-- The setup computes the graph list pointers and private layout without writing memory. -/
theorem loopOnlySetup_runs {w g vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (lengths L heap : ℕ)
    (hG : DynGraphAt st.mem g vCap eCap G)
    (h0 : st.regs 0 = g) (h1 : st.regs 1 = lengths) (h2 : st.regs 2 = L)
    (h4 : st.regs 4 = heap) (hw : 16 ≤ 2^w)
    (hg : g+dynGraphSize vCap eCap < 2^w)
    (hroom : heap+8+dynGraphSize vCap eCap < 2^w) :
    ∃ out cost, Runs w p ω loopOnlySetup st .normal out cost ∧ out.mem = st.mem ∧
      out.regs 13 = lengths ∧ out.regs 14 = L ∧ out.regs 41 = vCap ∧ out.regs 42 = eCap ∧
      out.regs 43 = G.n ∧ out.regs 61 = G.m ∧
      out.regs 44 = dgVListBase g vCap ∧ out.regs 62 = dgEListBase g vCap eCap ∧
      out.regs 55 = heap ∧ out.regs 56 = heap+2 ∧ out.regs 45 = heap+6 ∧
      out.regs 58 = heap+6+dynGraphSize vCap eCap ∧
      out.regs 60 = heap+8+dynGraphSize vCap eCap ∧ cost ≤ 89 := by
  obtain ⟨o,mid,c,hr,⟨rfl,hm,h13,h14,h41,h42,h43,h61,h44,h62,hheap⟩,hc⟩ :=
    loopOnlyLoadInput_runs (ω := ω) st G lengths L hG h0 h1 h2 hw hg
  obtain ⟨o',out,d,hr',⟨rfl,hm',h55,h56,h45,h58,h60,hkeep⟩,hd⟩ :=
    loopOnlyReserve_runs (ω := ω) mid heap vCap eCap (hheap.trans h4) h41 h42 hw hroom
  exact ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hr',rfl⟩),hm'.trans hm,
    (hkeep 13 (by decide)).trans h13,(hkeep 14 (by decide)).trans h14,
    (hkeep 41 (by decide)).trans h41,(hkeep 42 (by decide)).trans h42,
    (hkeep 43 (by decide)).trans h43,(hkeep 61 (by decide)).trans h61,
    (hkeep 44 (by decide)).trans h44,(hkeep 62 (by decide)).trans h62,
    h55,h56,h45,h58,h60,by omega⟩

/-- The exact heap span of the loop-only collection. -/
@[expose] def loopOnlySpace (vCap eCap L : ℕ) : ℕ :=
  8+dynGraphSize vCap eCap+eCap*L

@[expose] def loopOnlyEnd : Expr :=
  .bin .add (.reg 60) (.bin .mul (.reg 42) (.reg 14))

/-- Initialize the collection at the caller heap and return the end of its allocation. -/
@[expose] def loopOnlyInit (init copy header : ℕ) : Stmt :=
  .seq loopOnlySetup (.seq (loopOnlyBuild init copy header) (.ret loopOnlyEnd))

/-- A loop-only initialization from the caller graph produces a private
one-entry collection and returns the next free heap pointer. -/
theorem loopOnlyInit_runs {w bOps bEdge bSplit bBatch copy header vCap eCap L P : ℕ}
    {p : Program} {ω : ℕ → Bool} (G : MGraph) (mem : ℕ → ℕ) (pos g lengths heap : ℕ)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hops : p.HasAt bOps dgOpsProcs)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hh : MeetsContract w p header (branchHeaderContract w vCap eCap 4 L P G.E (loopOnlyLSF G)))
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hg : g+dynGraphSize vCap eCap ≤ heap) (hs : lengths+eCap*L ≤ heap)
    (hfit : heap+loopOnlySpace vCap eCap L < 2^w) (hz : ZeroFrom mem heap)
    (hvalues : ∀ e ∈ G.E, Valid mem (lengths+e*L) 4 L ∧ 0 < fixVal mem (lengths+e*L) 4 L P) :
    ∃ out cost, Runs w p ω (loopOnlyInit (bBatch+dgIdxInitFromLists) copy header)
        (startState [g,lengths,L,P,heap] mem pos) (.returned (heap+loopOnlySpace vCap eCap L)) out cost ∧
      CollectionPrefix out.mem heap 1 1 (heap+loopOnlySpace vCap eCap L) vCap eCap 4 L P G.E
        (fun _ => loopOnlyLSF G) ∧
      (∀ a < heap, out.mem a = mem a) ∧ ZeroFrom out.mem (heap+loopOnlySpace vCap eCap L) ∧
      cost ≤ 130*G.n+(17*L+37)*G.m+274 := by
  let st := startState [g,lengths,L,P,heap] mem pos
  let graph := heap+6
  let desc := graph+dynGraphSize vCap eCap
  let table := heap+8+dynGraphSize vCap eCap
  have hend : table+eCap*L = heap+loopOnlySpace vCap eCap L := by
    simp [table,loopOnlySpace,Nat.add_assoc]
  have htable : table+eCap*L < 2^w := by rwa [hend]
  obtain ⟨ready,c,hr,hm,h13,h14,h41,h42,h43,h61,h44,h62,h55,h56,h45,h58,h60,hcost⟩ :=
    loopOnlySetup_runs (ω := ω) st G lengths L heap hG rfl rfl rfl rfl hw (by omega) (by omega)
  obtain ⟨_,hvc,hec,_,_,_,_,_,⟨vs,hvs,hvnd,hV,hvAt,_⟩,_,_,_,
    ⟨es,hes,hendup,hE,heAt,_⟩,_,_⟩ := hG
  have hvb : vs.length ≤ vCap := by
    simpa using hvnd.length_le_of_subset (l₂ := List.range vCap)
      (fun v hv => List.mem_range.mpr (hvc v ((hV v).mp hv)))
  have heb : es.length ≤ eCap := by
    simpa using hendup.length_le_of_subset (l₂ := List.range eCap)
      (fun e he => List.mem_range.mpr (hec e ((hE e).mp he)))
  have hvp : dgVListBase g vCap+vs.length ≤ heap := by
    simp only [dgVListBase,dynGraphSize] at hg ⊢
    omega
  have hep : dgEListBase g vCap eCap+es.length ≤ heap := by
    simp only [dgEListBase,dynGraphSize] at hg ⊢
    omega
  obtain ⟨out,d,hbuild,hLSF,hframe,hzero,hout60,hout42,hout14,hcost'⟩ :=
    loopOnlyBuild_runs (ω := ω) ready G vs es (dgVListBase g vCap) (dgEListBase g vCap eCap)
      lengths heap (heap+2) graph desc table (dgInitFromLists_meetsContract hbatch hedge hops) hc hh
      h13 h14 h41 h42 (h43.trans hvs.symm) h44 h45 h55 h56 h58 h60
      (h61.trans hes.symm) h62 hw htable (by omega) (by dsimp [graph]; omega) le_rfl
      (by dsimp [desc,graph,table]; omega) hvp hep hs
      (by rw [hm]; exact fun a ha => hz a (by dsimp [graph] at ha; omega))
      hvc hec (by rwa [hm]) (by rwa [hm]) hendup hV hE (by rwa [hm])
  have hproduct : eCap*L < 2^w := by omega
  have hreturn : Runs w p ω (.ret loopOnlyEnd) out
      (.returned (heap+loopOnlySpace vCap eCap L)) out 6 :=
    runs_ret_iff.mpr ⟨_,by simp [loopOnlyEnd,Expr.eval,BinOp.eval,hout60,hout42,
      hout14,hproduct,hend,hfit],rfl,rfl,rfl⟩
  have hseq : Runs w p ω (.seq (loopOnlyBuild (bBatch+dgIdxInitFromLists) copy header) (.ret loopOnlyEnd))
      ready (.returned (heap+loopOnlySpace vCap eCap L)) out (d+7) :=
    runs_seq_iff.mpr (Or.inr ⟨out,d,6,hbuild,hreturn,by omega⟩)
  rw [hvs,hes] at hcost'
  exact ⟨out,c+(d+7)+1,runs_seq_iff.mpr (Or.inr ⟨ready,c,d+7,hr,hseq,rfl⟩),
    hend ▸ hLSF,fun a ha => (hframe a ha).trans (congrFun hm a),by rwa [hend] at hzero,by omega⟩

/-- The loop-only model charges one unit regardless of the number of live
vertices and loops. The multiplier pays for copying both lists' payloads. -/
@[expose] def loopOnlyMultiplier (L n m : ℕ) : ℕ :=
  (130*n+(17*L+37)*m+275)/2

/-- The loop-only initializer meets the cost charged by the runtime contract. -/
theorem loopOnlyInitCost_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (L cost : ℕ) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty)
    (hcost : cost ≤ 130*G.n+(17*L+37)*G.m+274) :
    cost ≤ loopOnlyMultiplier L G.n G.m * ((fixedPointLastLevelTool oracle C).cost G+1) := by
  rw [(fixedPointLastLevelTool_loopOnly oracle C G (fun _ => 1) hloops).2]
  unfold loopOnlyMultiplier
  omega

/-- For loop-only graphs, the runtime initialization precondition supplies
the graph and scalar blocks needed by the one-branch builder. -/
theorem loopOnlyInit_runtime {w bOps bEdge bSplit bBatch copy header vCap eCap L Q : ℕ}
    {p : Program} {ω : ℕ → Bool} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps)) (hops : p.HasAt bOps dgOpsProcs)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hh : MeetsContract w p header
      (branchHeaderContract w vCap eCap 4 L fmt.precision G.E (loopOnlyLSF G)))
    (hw : 16 ≤ 2^w) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty) :
    let D := lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G vCap eCap
      (loopOnlyMultiplier L G.n G.m) Q (fun _ _ => loopOnlySpace vCap eCap L)
    D.initPre args mem → ZeroFrom mem (heapArg args) →
    heapArg args + D.initSpace args mem < 2^w →
    ∃ out cost, Runs w p ω (loopOnlyInit (bBatch+dgIdxInitFromLists) copy header)
        (startState args mem pos) (.returned (heapArg args + D.initSpace args mem)) out cost ∧
      (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).rep
        (heapArg args) (1, fun _ => loopOnlyLSF G) (heapArg args + D.initSpace args mem) out.mem ∧
      D.initPost args mem (1, fun _ => loopOnlyLSF G) out.mem ∧
      (∀ a < heapArg args, out.mem a = mem a) ∧
      ZeroFrom out.mem (heapArg args + D.initSpace args mem) ∧ cost ≤ D.initCost args mem := by
  intro D hpre hz hroom
  obtain ⟨g,lengths,heap,rfl,hbits,_,hinput,_⟩ := hpre
  obtain ⟨g',lengths',heap',heq,hG,hg,hs,hvalid,hpositive⟩ := hinput
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨hg',hl',hh'⟩ := heq
  subst g'
  subst lengths'
  subst heap'
  have hvalues e (he : e ∈ G.E) :
      Valid mem (lengths+e*L) 4 L ∧ 0 < fixVal mem (lengths+e*L) 4 L fmt.precision := by
    refine ⟨hbits ▸ hvalid e he, ?_⟩
    simpa only [readEdgeValues,ite_eq_left he,hbits] using hpositive e he
  obtain ⟨out,cost,hr,hcollection,hframe,hzero,hcost⟩ :=
    loopOnlyInit_runs (ω := ω) G mem pos g lengths heap hbatch hedge hops hc hh hG hw hg hs
      hroom hz hvalues
  refine ⟨out,cost,hr,?_,⟨?_,?_⟩,hframe,hzero,loopOnlyInitCost_le oracle C G L cost hloops hcost⟩
  · change heap+1+1 ≤ heap+loopOnlySpace vCap eCap L ∧
      CollectionPrefix out.mem heap 1 1 (heap+loopOnlySpace vCap eCap L)
        vCap eCap fmt.limbBits L fmt.precision G.E (fun _ => loopOnlyLSF G)
    exact ⟨by unfold loopOnlySpace; omega, hbits.symm ▸ hcollection⟩
  · exact ((fixedPointLastLevelTool_loopOnly oracle C G _ hloops).1).symm
  · simpa only [hbits,show heapArg [g,lengths,L,fmt.precision,heap] = heap by rfl] using hcollection.complete

/-- A linked loop-only initializer and readout implement the runtime contract
on a graph whose edges are all loops. -/
theorem loopOnlyRuntime_implements {w bOps bEdge bSplit bBatch copy header vCap eCap L Q init op : ℕ}
    {p : Program} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (G : MGraph)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps)) (hops : p.HasAt bOps dgOpsProcs)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hh : MeetsContract w p header
      (branchHeaderContract w vCap eCap 4 L fmt.precision G.E (loopOnlyLSF G)))
    (hw : 16 ≤ 2^w) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty)
    (hinit : p.procs[init]? = some (loopOnlyInit (bBatch+dgIdxInitFromLists) copy header))
    (hop : p.procs[op]? = some readoutBody) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G vCap eCap
        (loopOnlyMultiplier L G.n G.m) Q (fun _ _ => loopOnlySpace vCap eCap L)) := by
  apply lastLevelRuntime_implements_of_init _ _ _ _ _ hinit hop
  intro D args mem pos ω _ hpre hz hroom
  obtain ⟨out,c,hr,hrep,hpost,hframe,hzero,hcost⟩ :=
    loopOnlyInit_runtime fmt oracle C G args mem pos
      hbatch hedge hops hc hh hw hloops hpre hz hroom
  exact ⟨_,out,c,_,hr,hrep,hpost,le_rfl,hzero,hframe,hcost⟩

/-- The endpoint slots agree exactly for a self-loop. The inverse
vertex table turns equality of slots into equality of vertex names. -/
theorem edgeSlots_eq_iff_loop {g vCap eCap e : ℕ} {mem : ℕ → ℕ} {G : MGraph}
    (hG : DynGraphAt mem g vCap eCap G) (he : e ∈ G.E) :
    mem (dgETailSlotBase g vCap eCap+e) = mem (dgEHeadSlotBase g vCap eCap+e) ↔
      G.tail e = G.head e := by
  obtain ⟨hvalid,_,_,_,_,_,_,_,_,hslots,_,_,_,hends,_⟩ := hG
  obtain ⟨ht,hh⟩ := hends e he
  rw [ht,hh]
  constructor
  · intro h
    have ht' := (hslots _ (hvalid e he).1).2
    have hh' := (hslots _ (hvalid e he).2).2
    rw [← ht',← hh',h]
  · intro h
    rw [h]

/-- Test the next live edge, retaining a one bit only while all scanned
edges are self-loops. Registers 155–159 leave the caller arguments intact. -/
@[expose] def scanLoopOnlyStep : Stmt :=
  let add := Expr.bin .add
  .assign 159 (.load (add (.reg 62) (.reg 155))) ;;
  .assign 158 (.bin .and (.reg 158)
    (.bin .eq (.load (add (.reg 156) (.reg 159))) (.load (add (.reg 157) (.reg 159)))))

/-- One scan step reads the named edge and compares its stored endpoints. -/
theorem scanLoopOnlyStep_runs {w g vCap eCap i e : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph} (st : State) (hG : DynGraphAt st.mem g vCap eCap G)
    (he : e ∈ G.E) (hi : i < G.m)
    (h155 : st.regs 155 = i) (h156 : st.regs 156 = dgETailSlotBase g vCap eCap)
    (h157 : st.regs 157 = dgEHeadSlotBase g vCap eCap)
    (h62 : st.regs 62 = dgEListBase g vCap eCap)
    (hread : st.mem (dgEListBase g vCap eCap+i) = e)
    (hbit : st.regs 158 ≤ 1) (hw : 1 < 2^w)
    (hfit : g+dynGraphSize vCap eCap < 2^w) :
    ∃ o out cost, Runs w p ω scanLoopOnlyStep st o out cost ∧
      (o = .normal ∧ out.mem = st.mem ∧
        out.regs 158 = (if G.tail e = G.head e then st.regs 158 else 0) ∧
        (∀ r, r ≠ 158 → r ≠ 159 → out.regs r = st.regs r)) ∧ cost ≤ 20 := by
  have heq := edgeSlots_eq_iff_loop hG he
  obtain ⟨_,_,hecap,_,_,_,_,_,_,_,_,_,⟨es,hes,hnd,hE,_,_⟩,_,_⟩ := hG
  have hei : e < eCap := hecap e he
  have hm : G.m ≤ eCap := by
    rw [← hes]
    simpa using hnd.length_le_of_subset (l₂ := List.range eCap)
      (fun f hf => List.mem_range.mpr (hecap f ((hE f).mp hf)))
  have htfit : st.regs 156 + st.mem (dgEListBase g vCap eCap+i) < 2^w := by
    rw [h156,hread]
    unfold dgETailSlotBase dynGraphSize at *
    omega
  have hhfit : st.regs 157 + st.mem (dgEListBase g vCap eCap+i) < 2^w := by
    rw [h157,hread]
    unfold dgEHeadSlotBase dynGraphSize at *
    omega
  have hflag : (st.regs 158 &&& (if
      st.mem (st.regs 156+st.mem (dgEListBase g vCap eCap+i)) =
      st.mem (st.regs 157+st.mem (dgEListBase g vCap eCap+i)) then 1 else 0)) =
      (if G.tail e = G.head e then st.regs 158 else 0) := by
    rw [h156,h157,hread]
    by_cases hloop : G.tail e = G.head e
    · have hb : st.regs 158 = 0 ∨ st.regs 158 = 1 := by omega
      rcases hb with h | h <;> simp [h,hloop,heq.mpr hloop]
    · simp [hloop,mt heq.mp hloop]
  have hflagFit := calc
    _ = (if G.tail e = G.head e then st.regs 158 else 0) := hflag
    _ < 2^w := by split <;> omega
  unfold dynGraphSize at hfit
  apply runs_start_le
  have hlistFit : dgEListBase g vCap eCap+i < 2^w := by
    unfold dgEListBase
    omega
  unfold scanLoopOnlyStep
  wram_run
  · simp only [Function.update_self,true_and]
    exact ⟨hflag,fun r hr hs => by simp [Function.update_of_ne hr,Function.update_of_ne hs]⟩
  · wram_cost

/-- Scan the live-edge list, using an accumulator initialized to one. -/
@[expose] def scanLoopOnly : Stmt :=
  forRange 155 (.const 0) (.reg 61) scanLoopOnlyStep

/-- The scan leaves memory and the caller argument registers untouched.
Its result is one exactly when the graph has no non-loop edge. -/
theorem scanLoopOnly_runs {w g vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph} (st : State) (hG : DynGraphAt st.mem g vCap eCap G)
    (h156 : st.regs 156 = dgETailSlotBase g vCap eCap)
    (h157 : st.regs 157 = dgEHeadSlotBase g vCap eCap)
    (h62 : st.regs 62 = dgEListBase g vCap eCap)
    (h61 : st.regs 61 = G.m) (h158 : st.regs 158 = 1)
    (hw : 1 < 2^w) (hfit : g+dynGraphSize vCap eCap < 2^w) :
    ∃ out cost, Runs w p ω scanLoopOnly st .normal out cost ∧
      out.mem = st.mem ∧ out.regs 158 ≤ 1 ∧
      (out.regs 158 = 1 ↔ ¬ (SparseCore.nonLoopEdges G).Nonempty) ∧
      (∀ r, r ≠ 155 → r ≠ 158 → r ≠ 159 → out.regs r = st.regs r) ∧ cost ≤ 29*G.m+7 := by
  have hGraph := hG
  obtain ⟨_,_,hecap,_,_,_,_,_,_,_,_,_,⟨es,hes,hnd,hE,hAt,_⟩,_,_⟩ := hGraph
  have hm : G.m ≤ eCap := by
    rw [← hes]
    simpa using hnd.length_le_of_subset (l₂ := List.range eCap)
      (fun e he => List.mem_range.mpr (hecap e ((hE e).mp he)))
  have hmFit : G.m < 2^w := by unfold dynGraphSize at hfit; omega
  let Loops (i : ℕ) := ∀ j (hj : j < es.length), j < i →
    G.tail es[j] = G.head es[j]
  let Inv (i : ℕ) (s : State) :=
    s.regs 155 = i ∧ s.mem = st.mem ∧ s.regs 158 ≤ 1 ∧
      (s.regs 158 = 1 ↔ Loops i) ∧
      ∀ r, r ≠ 155 → r ≠ 158 → r ≠ 159 → s.regs r = st.regs r
  have loop := Triple.forRange_const (p := p) (r := 155) (lo := .const 0) (hi := .reg 61)
    (body := scanLoopOnlyStep) (P := fun s => s = st) (Inv := Inv) 20 0 G.m (Nat.zero_le _)
    hw (fun _ => hmFit)
    (fun s (hs : s = st) => by
      subst s
      refine ⟨by simp [Expr.eval,show 0 < 2^w by omega], ?_⟩
      refine ⟨by simp, rfl, ?_, ?_, fun r hr _ _ => Function.update_of_ne hr ..⟩
      · simp [h158]
      · simp [h158,Loops])
    (fun _ _ _ _ h => h.1)
    (fun _ s _ _ h => by simp [Expr.eval,(h.2.2.2.2 61 (by decide) (by decide) (by decide)).trans h61])
    (fun i _ hi s ω hs => by
      obtain ⟨hidx,hmem,hbit,hloops,hregs⟩ := hs
      have hi' : i < es.length := by omega
      have he := (hE es[i]).mp (List.getElem_mem hi')
      obtain ⟨o,out,c,hr,⟨rfl,hm',hb',hk⟩,hc⟩ :=
        scanLoopOnlyStep_runs (ω := ω) s (hmem.symm ▸ hG) he hi hidx
          ((hregs _ (by decide) (by decide) (by decide)).trans h156)
          ((hregs _ (by decide) (by decide) (by decide)).trans h157)
          ((hregs _ (by decide) (by decide) (by decide)).trans h62)
          (hmem.symm ▸ hAt i hi') hbit hw hfit
      refine ⟨.normal,out,c,hr,⟨⟨by simp,hm'.trans hmem,?_,?_,?_⟩,
        (hk 155 (by decide) (by decide)).trans hidx⟩,hc⟩
      · simp only [Function.update_of_ne (show (158 : ℕ) ≠ 155 by decide),hb']
        split <;> omega
      · simp only [Function.update_of_ne (show (158 : ℕ) ≠ 155 by decide),hb']
        by_cases hloop : G.tail es[i] = G.head es[i]
        · rw [ite_eq_left hloop,hloops]
          constructor
          · intro h j hj hj'
            rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hj'' | rfl
            · exact h j hj hj''
            · exact hloop
          · exact fun h j hj hj' => h j hj (by omega)
        · rw [ite_eq_right hloop]
          exact ⟨fun h => by omega,fun h => False.elim (hloop (h i hi' (by omega)))⟩
      · intro r h155 h158 h159
        exact (Function.update_of_ne h155 ..).trans ((hk r h158 h159).trans (hregs r h155 h158 h159)))
  obtain ⟨o,out,c,hr,hpost,hcost⟩ := loop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨_,hmem,hbit,hloops,hregs⟩ := hpost
    refine ⟨out,c,hr,hmem,hbit,hloops.trans ?_,hregs,?_⟩
    · simp only [SparseCore.nonLoopEdges,Finset.Nonempty,Finset.mem_filter,not_exists,not_and,not_not]
      constructor
      · intro hall e he
        obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp ((hE e).mpr he)
        simpa only [hei] using hall i hi (by omega)
      · intro hall i hi _
        exact hall _ ((hE _).mp (List.getElem_mem hi))
    · simpa [Expr.size_reg,Expr.size_const,Nat.mul_comm] using hcost

/-- Load the live-edge count and endpoint table pointers for dispatch. -/
@[expose] def scanLoopOnlySetup : Stmt :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let atOffset := fun i => Expr.load (add (.reg 0) (.const i))
  .assign 41 (.load (.reg 0)) ;;
  .assign 42 (atOffset 1) ;;
  .assign 61 (atOffset 3) ;;
  .assign 62 (add (add (add (.reg 0) (.const 4)) (mul (.const 7) (.reg 41))) (.reg 42)) ;;
  .assign 156 (add (.reg 62) (mul (.const 2) (.reg 42))) ;;
  .assign 157 (add (.reg 156) (.reg 42)) ;;
  .assign 158 (.const 1)

/-- The setup reads graph metadata without changing memory or the five
initializer arguments. -/
theorem scanLoopOnlySetup_runs {w g vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph} (st : State) (hG : DynGraphAt st.mem g vCap eCap G)
    (h0 : st.regs 0 = g) (hw : 16 ≤ 2^w) (hfit : g+dynGraphSize vCap eCap < 2^w) :
    ∃ o out cost, Runs w p ω scanLoopOnlySetup st o out cost ∧
      (o = .normal ∧ out.mem = st.mem ∧
        out.regs 156 = dgETailSlotBase g vCap eCap ∧
        out.regs 157 = dgEHeadSlotBase g vCap eCap ∧
        out.regs 62 = dgEListBase g vCap eCap ∧ out.regs 61 = G.m ∧ out.regs 158 = 1 ∧
        ∀ r < 5, out.regs r = st.regs r) ∧ cost ≤ 60 := by
  have hv : st.mem g = vCap := hG.2.2.2.1
  have he : st.mem (g+1) = eCap := hG.2.2.2.2.1
  have hm : st.mem (g+3) = G.m := hG.2.2.2.2.2.2.1
  unfold dynGraphSize at hfit
  apply runs_start_le
  have htail : st.regs 0+4+7*st.mem g+st.mem (st.regs 0+1)+
      2*st.mem (st.regs 0+1) < 2^w := by rw [h0,hv,he]; omega
  have hhead : st.regs 0+4+7*st.mem g+st.mem (st.regs 0+1)+
      2*st.mem (st.regs 0+1)+st.mem (st.regs 0+1) < 2^w := by rw [h0,hv,he]; omega
  have htwice : 2*st.mem (st.regs 0+1) < 2^w := by omega
  have hbase : st.regs 0+4+7*st.mem g+st.mem (st.regs 0+1) < 2^w := by omega
  unfold scanLoopOnlySetup
  wram_run
  · simp [h0,hv,he,hm,dgETailSlotBase,dgEHeadSlotBase,dgEListBase]
    refine ⟨by omega,by omega,?_⟩
    intro r hr
    simp [Function.update_of_ne (show r ≠ 158 by omega),
      Function.update_of_ne (show r ≠ 157 by omega), Function.update_of_ne (show r ≠ 156 by omega),
      Function.update_of_ne (show r ≠ 62 by omega), Function.update_of_ne (show r ≠ 61 by omega),
      Function.update_of_ne (show r ≠ 42 by omega), Function.update_of_ne (show r ≠ 41 by omega)]
  · wram_cost

/-- Read the graph and decide which initializer to run. -/
@[expose] def scanRuntimeLoops : Stmt :=
  .seq scanLoopOnlySetup scanLoopOnly

/-- The dispatcher reads only the graph and preserves the five input words. -/
theorem scanRuntimeLoops_runs {w g vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph} (mem : ℕ → ℕ) (lengths L P heap pos : ℕ)
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hfit : g+dynGraphSize vCap eCap < 2^w) :
    ∃ out cost, Runs w p ω scanRuntimeLoops (startState [g,lengths,L,P,heap] mem pos)
        .normal out cost ∧ out.mem = mem ∧
      (out.regs 158 = if (SparseCore.nonLoopEdges G).Nonempty then 0 else 1) ∧
      (∀ r < 5, out.regs r = (startState [g,lengths,L,P,heap] mem pos).regs r) ∧
      cost ≤ 29*G.m+68 := by
  classical
  let st := startState [g,lengths,L,P,heap] mem pos
  obtain ⟨o,ready,c,hr,⟨rfl,hmem,h156,h157,h62,h61,h158,hregs⟩,hc⟩ :=
    scanLoopOnlySetup_runs (ω := ω) st hG rfl hw hfit
  obtain ⟨out,d,hr',hmem',hbit,hflag,hkeep,hd⟩ :=
    scanLoopOnly_runs (ω := ω) ready (hmem.symm ▸ hG) h156 h157 h62 h61 h158 (by omega) hfit
  refine ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨ready,c,d,hr,hr',rfl⟩),
    hmem'.trans hmem,?_,fun r h => (hkeep r (by omega) (by omega) (by omega)).trans (hregs r h),
    by omega⟩
  by_cases hnl : (SparseCore.nonLoopEdges G).Nonempty
  · rw [ite_eq_left hnl]
    have hn : out.regs 158 ≠ 1 := fun h => hflag.mp h hnl
    omega
  · rw [ite_eq_right hnl]
    exact hflag.mpr hnl

private def runtimeInitArgs : List Expr :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4]

private def callRuntimeInit (entry : ℕ) : Stmt :=
  .seq (.call 160 entry runtimeInitArgs) (.ret (.reg 160))

/-- Use the live-edge scan to select one of the two initialization routines. -/
def dispatchRuntimeInit (loopOnly general : ℕ) : Stmt :=
  .seq scanRuntimeLoops (.cond (.reg 158) (callRuntimeInit loopOnly) (callRuntimeInit general))

/-- The runtime initializer dispatcher uses no `rand` statement. -/
theorem dispatchRuntimeInit_noRand (loopOnly general : ℕ) :
    (dispatchRuntimeInit loopOnly general).NoRand := by
  simp [dispatchRuntimeInit, callRuntimeInit, scanRuntimeLoops, scanLoopOnlySetup,
    scanLoopOnly, scanLoopOnlyStep, forRange, forUp, Stmt.NoRand]

/-- Dispatch forwards the original arguments and heap result of the
selected initializer, charging only a linear read-only scan. -/
theorem dispatchRuntimeInit_runs {w g vCap eCap loopOnly general : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph}
    (mem : ℕ → ℕ) (lengths L P heap pos budget : ℕ) (Post : ℕ → (ℕ → ℕ) → Prop)
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hfit : g+dynGraphSize vCap eCap < 2^w)
    (hbranch : ∀ pos',
      let entry := if (SparseCore.nonLoopEdges G).Nonempty then general else loopOnly
      ∃ body limit out cost, p.procs[entry]? = some body ∧
        Runs w p ω body (startState [g,lengths,L,P,heap] mem pos') (.returned limit) out cost ∧
        Post limit out.mem ∧ cost ≤ budget) :
    ∃ limit out cost, Runs w p ω (dispatchRuntimeInit loopOnly general)
        (startState [g,lengths,L,P,heap] mem pos) (.returned limit) out cost ∧
      Post limit out.mem ∧ cost ≤ budget+29*G.m+80 := by
  classical
  obtain ⟨ready,cs,hscan,hmem,hflag,hregs,hcs⟩ :=
    scanRuntimeLoops_runs (ω := ω) mem lengths L P heap pos hG hw hfit
  let entry := if (SparseCore.nonLoopEdges G).Nonempty then general else loopOnly
  obtain ⟨body,limit,mid,c,hproc,hr,hpost,hc⟩ := hbranch ready.pos
  have hargs : evalArgs w ready runtimeInitArgs = some [g,lengths,L,P,heap] := by
    simp only [runtimeInitArgs,evalArgs,Expr.eval,hregs 0 (by decide),hregs 1 (by decide),
      hregs 2 (by decide),hregs 3 (by decide),hregs 4 (by decide)]
    rfl
  let out := {mid with regs := Function.update ready.regs 160 limit}
  have hcall : Runs w p ω (.call 160 entry runtimeInitArgs) ready .normal out (c+6) :=
    runs_call_iff.mpr ⟨_,body,.returned limit,mid,c,hargs,hproc,hmem.symm ▸ hr,rfl,rfl,by
      change c+6 = 5+c+1
      omega⟩
  have hret : Runs w p ω (.ret (.reg 160)) out (.returned limit) out 2 :=
    runs_ret_iff.mpr ⟨limit,by simp [Expr.eval,out],rfl,rfl,rfl⟩
  have hfinish : Runs w p ω (callRuntimeInit entry) ready (.returned limit) out (c+9) :=
    runs_seq_iff.mpr (Or.inr ⟨out,c+6,2,hcall,hret,by omega⟩)
  have hcond : Runs w p ω (.cond (.reg 158) (callRuntimeInit loopOnly) (callRuntimeInit general))
      ready (.returned limit) out (c+11) := by
    apply runs_cond_iff.mpr
    refine ⟨ready.regs 158,c+9,rfl,?_,by change c+11 = 1+(c+9)+1; omega⟩
    by_cases hnl : (SparseCore.nonLoopEdges G).Nonempty
    · simpa [entry,hnl,hflag] using hfinish
    · simpa [entry,hnl,hflag] using hfinish
  exact ⟨limit,out,cs+(c+11)+1,runs_seq_iff.mpr (Or.inr ⟨ready,cs,c+11,hscan,hcond,rfl⟩),
    hpost,by omega⟩

/-- On loop-only inputs the model budget is two, so the dispatch scan
contributes half its rounded-up cost to the multiplier. -/
theorem loopOnlyDispatchCost_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (L cost : ℕ) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty)
    (hcost : cost ≤ loopOnlyMultiplier L G.n G.m * ((fixedPointLastLevelTool oracle C).cost G+1)) :
    cost+29*G.m+80 ≤ (loopOnlyMultiplier L G.n G.m+(29*G.m+81)/2) *
      ((fixedPointLastLevelTool oracle C).cost G+1) := by
  rw [(fixedPointLastLevelTool_loopOnly oracle C G (fun _ => 1) hloops).2] at hcost ⊢
  omega

/-- Dispatch and readout meet the runtime contract when the chosen
initializer produces the collection within the branch budget. -/
theorem dispatchRuntime_implements_of_init {w vCap eCap L Q multiplier init op loops general budget : ℕ}
    {p : Program} (fmt : Format w) (tool : Chain.LastLevelTool) (G : MGraph)
    (allocation : ℕ → List ℕ → ℕ) (hw : 16 ≤ 2^w)
    (hinit : p.procs[init]? = some (dispatchRuntimeInit loops general))
    (hop : p.procs[op]? = some readoutBody)
    (hbudget : budget+29*G.m+80 ≤ multiplier*(tool.cost G+1))
    (hbranch :
      let D := lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation
      ∀ args mem pos ω, (∀ a ∈ args, a < 2^w) → D.initPre args mem →
        ZeroFrom mem (heapArg args) → heapArg args+D.initSpace args mem < 2^w →
        let entry := if (SparseCore.nonLoopEdges G).Nonempty then general else loops
        ∃ body limit out cost s, p.procs[entry]? = some body ∧
          Runs w p ω body (startState args mem pos) (.returned limit) out cost ∧
          (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).rep
            (heapArg args) s limit out.mem ∧ D.initPost args mem s out.mem ∧
          limit ≤ heapArg args+D.initSpace args mem ∧ ZeroFrom out.mem limit ∧
          (∀ a < heapArg args, out.mem a = mem a) ∧ cost ≤ budget) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation) := by
  classical
  apply lastLevelRuntime_implements_of_init _ _ _ _ _ hinit hop
  intro D args mem pos ω hwords hpre hz hroom
  have hinput := hpre
  obtain ⟨g,lengths,heap,rfl,_,_,hcaller,_⟩ := hinput
  obtain ⟨g',lengths',heap',heq,hG,hgraph,_⟩ := hcaller
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨hg',hl',hh'⟩ := heq
  subst g'
  subst lengths'
  subst heap'
  have hh : heap < 2^w := hwords heap (by simp)
  let Post := fun (limit : ℕ) out => ∃ s,
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).rep heap s limit out ∧
    D.initPost [g,lengths,L,fmt.precision,heap] mem s out ∧
    limit ≤ heap+D.initSpace [g,lengths,L,fmt.precision,heap] mem ∧ ZeroFrom out limit ∧
    ∀ a < heap, out a = mem a
  obtain ⟨limit,out,cost,hr,⟨s,hrep,hpost,hbound,hzero,hframe⟩,hcost⟩ :=
    dispatchRuntimeInit_runs (ω := ω) mem lengths L fmt.precision heap pos budget Post hG hw
      (hgraph.trans_lt hh) (fun pos' => by
        obtain ⟨body,limit,out,c,s,hproc,hr,hrep,hpost,hend,hzero,hframe,hc⟩ :=
          hbranch _ mem pos' ω hwords hpre hz hroom
        exact ⟨body,limit,out,c,hproc,hr,⟨s,hrep,hpost,hend,hzero,hframe⟩,hc⟩)
  exact ⟨limit,out,cost,s,hr,hrep,hpost,hbound,hzero,hframe,hcost.trans hbudget⟩

/-- The dispatched runtime implementation meets the contract for a
loop-only graph, including the cost of selecting that path. -/
theorem dispatchRuntime_implements_loopOnly
    {w bOps bEdge bSplit bBatch copy header vCap eCap L Q init op loops general : ℕ}
    {p : Program} (fmt : Format w)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (G : MGraph)
    (hbatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hedge : p.HasAt bEdge (dgEdgeProcs bOps)) (hops : p.HasAt bOps dgOpsProcs)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hh : MeetsContract w p header
      (branchHeaderContract w vCap eCap 4 L fmt.precision G.E (loopOnlyLSF G)))
    (hw : 16 ≤ 2^w) (hloops : ¬ (SparseCore.nonLoopEdges G).Nonempty)
    (hinit : p.procs[init]? = some (dispatchRuntimeInit loops general))
    (hproc : p.procs[loops]? = some (loopOnlyInit (bBatch+dgIdxInitFromLists) copy header))
    (hop : p.procs[op]? = some readoutBody) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L (fixedPointLastLevelTool oracle C) G vCap eCap
        (loopOnlyMultiplier L G.n G.m+(29*G.m+81)/2) Q (fun _ _ => loopOnlySpace vCap eCap L)) := by
  let budget := loopOnlyMultiplier L G.n G.m * ((fixedPointLastLevelTool oracle C).cost G+1)
  apply dispatchRuntime_implements_of_init (budget := budget) _ _ _ _ hw hinit hop
    (loopOnlyDispatchCost_le oracle C G L budget hloops le_rfl)
  intro D args mem pos ω _ hpre hz hroom
  dsimp only
  rw [ite_eq_right hloops]
  obtain ⟨out,c,hr,hrep,hpost,hframe,hzero,hcost⟩ :=
    loopOnlyInit_runtime fmt oracle C G args mem pos hbatch hedge hops hc hh hw hloops
      hpre hz hroom
  exact ⟨_,_,out,c,_,hproc,hr,hrep,hpost,le_rfl,hzero,hframe,hcost⟩

/-- For a non-loop input, a complete prefix returned by the representative
initializer supplies the model postcondition for dispatch and readout. -/
theorem dispatchRuntime_implements_of_representativePrefix
    {w vCap eCap L Q multiplier init op loops general budget : ℕ}
    {p : Program} (fmt : Format w) (tool : Chain.LastLevelTool) (G : MGraph)
    (allocation : ℕ → List ℕ → ℕ) (hw : 16 ≤ 2^w)
    (hnl : (SparseCore.nonLoopEdges G).Nonempty)
    (hinit : p.procs[init]? = some (dispatchRuntimeInit loops general))
    (hop : p.procs[op]? = some readoutBody)
    (hbudget : budget+29*G.m+80 ≤ multiplier*(tool.cost G+1))
    (hgeneral :
      let D := lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation
      ∀ g lengths heap mem pos ω,
        let args := [g,lengths,L,fmt.precision,heap]
        let s := tool.build G (MinRatio.readEdgeValues mem lengths 4 L fmt.precision G.E)
        (∀ a ∈ args, a < 2^w) → D.initPre args mem →
        ZeroFrom mem heap → heap+D.initSpace args mem < 2^w →
        ∃ body limit out cost, p.procs[general]? = some body ∧
          Runs w p ω body (startState args mem pos) (.returned limit) out cost ∧
          heap+1+s.1 ≤ limit ∧
          CollectionPrefix out.mem heap s.1 s.1 limit vCap eCap 4 L fmt.precision G.E s.2 ∧
          limit ≤ heap+D.initSpace args mem ∧ ZeroFrom out.mem limit ∧
          (∀ a < heap, out.mem a = mem a) ∧ cost ≤ budget) :
    (lastLevelRepresentation vCap eCap fmt.limbBits L fmt.precision G.E).Implements
      w p init (fun _ => op)
      (lastLevelRuntimeMachineContract fmt L tool G vCap eCap multiplier Q allocation) := by
  classical
  apply dispatchRuntime_implements_of_init fmt tool G allocation hw hinit hop hbudget
  intro D args mem pos ω hwords hpre hz hroom
  have hinput := hpre
  obtain ⟨g,len,heap,rfl,hbits,_,_,_⟩ := hinput
  dsimp only
  rw [ite_eq_left hnl]
  obtain ⟨body,limit,out,cost,hproc,hr,hlo,hprefix,hhi,hzero,hframe,hcost⟩ :=
    hgeneral g len heap mem pos ω hwords hpre hz hroom
  obtain ⟨hrep,hpost⟩ := lastLevelRuntime_initPost_of_prefix (Q := Q) (multiplier := multiplier)
    fmt tool G allocation mem out.mem hbits hlo hprefix
  exact ⟨body,limit,out,cost,_,hproc,hr,hrep,hpost,hhi,hzero,hframe,hcost⟩

end MinCostFlow.LastLevelProgram
