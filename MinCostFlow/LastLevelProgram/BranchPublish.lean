module

public import MinCostFlow.LastLevelProgram.BranchRoots
public import MinCostFlow.LastLevelProgram.CollectionHeader
import WordRAM.Tactic

/-!
# Publishing a connected branch

The last-level branch of Definition 5.8 (pages 19–20) uses the chosen
root and exposes the graph and stretch payloads through a collection slot.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM MinRatio DynSpanner.Program

/-- Write the root bit, then serialize the branch and publish its pointer. -/
def publishRootedBranchBody (root serialize : ℕ) : Stmt :=
  .seq (.call 10 root [.reg 3,.load (.reg 9)])
    (.seq (.call 10 serialize ((List.range 9).map Expr.reg)) (.ret (.const 0)))

/-- The root write and serialization expose the branch while preserving
memory outside the root array, descriptor, header, and collection slot. -/
theorem publishRootedBranch_runs {w root serialize : ℕ} {p : Program} {ω : ℕ → Bool}
    {vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF} {G : MGraph}
    (mem : ℕ → ℕ) (pos base tree forest roots stretch collection j numerator denominator vertices : ℕ)
    (hr : MeetsContract w p root (branchRootsContract w vCap G))
    (hs : MeetsContract w p serialize (serializeBranchContract w vCap eCap h L P E branch)) :
    let ra := [roots,firstVertex G.V]
    let sa := [base,tree,forest,roots,stretch,collection,j,numerator,denominator]
    let args := sa ++ [vertices]
    (∀ a ∈ args, a < 2^w) →
    G.V.Nonempty → mem vertices = vertexName G 0 → firstVertex G.V < 2^w →
    (branchRootsContract w vCap G).pre ra mem →
    (∀ ret mid, (branchRootsContract w vCap G).post ra mem ret mid →
      (serializeBranchContract w vCap eCap h L P E branch).pre sa mid) →
    ∃ o out cost, Runs w p ω (publishRootedBranchBody root serialize)
      (startState args mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem (collection+1+j) = base ∧
        LSFAt out.mem base vCap eCap h L P E branch ∧
        out.mem base = tree ∧ out.mem (base+1) = forest ∧
        out.mem (base+2) = roots ∧ out.mem (base+3) = stretch ∧
        out.mem stretch = numerator ∧ out.mem (stretch+1) = denominator ∧
        ∀ a, a ≠ collection+1+j → (a < base ∨ base+4 ≤ a) →
          (a < stretch ∨ stretch+2 ≤ a) → (a < roots ∨ roots+vCap ≤ a) →
          out.mem a = mem a) ∧ cost ≤ 116 := by
  intro ra sa args hwords hv hname hrootWord hpre hnext
  have hrootName := hname.trans (firstVertex_eq_vertexName_zero hv).symm
  have hvword : vertices < 2^w := hwords _ (by simp [args])
  apply runs_start_le
  unfold publishRootedBranchBody
  refine runs_seq_call_le hr (vs := ra) (by eval_expr) ?_ hpre ?_
  · intro a ha
    rcases (show a = roots ∨ a = firstVertex G.V by simpa [ra] using ha)
      with rfl | rfl
    · exact hwords _ (by simp [args,sa])
    · exact hrootWord
  · intro ret mid pos' hmid
    have hn := hnext ret mid hmid
    obtain ⟨r,he,_,_,hframe⟩ := hmid
    have he' : roots = r := (List.cons.inj he).1
    subst r
    refine runs_seq_call_le hs (vs := sa) rfl
      (fun a ha => hwords a (List.mem_append_left _ ha)) hn ?_
    intro ret' out pos'' hout
    obtain ⟨b,t,f,r,s,c,k,n,d,he,_,hslot,hlayout,hT,hF,hR,hS,hN,hD,houtFrame⟩ := hout
    simp only [sa,List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    have hzero : 0 < 2 ^ w := Nat.two_pow_pos _
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,hslot,hlayout,hT,hF,hR,hS,hN,hD,?_⟩ ?_
    · intro a hne hheader hdescriptor hroot
      exact (houtFrame a hne hheader hdescriptor).trans (hframe a hroot)
    · change 0 + 3 + 10 + 2 + 9 + 88 + 2 + 2 ≤ 116
      decide

/-- With graphs before the roots and tables after the descriptor,
the root and descriptor writes retain all previously built payloads. -/
theorem serializeBranch_pre_of_roots {w vCap eCap h L P : ℕ}
    {E : Finset ℕ} {branch : LSF} {G : MGraph} {mem mid : ℕ → ℕ}
    {ret base tree forest roots stretch collection j numerator denominator : ℕ}
    (hroot : (branchRootsContract w vCap G).post [roots,firstVertex G.V] mem ret mid)
    (hmodel : componentRoots G = branch.F.R)
    (hw : 1 < 2^w) (hslot : collection+1+j < base)
    (hb : base+4 < 2^w) (hs : stretch+2 < 2^w)
    (ht : DynGraphAt mem tree vCap eCap branch.T)
    (hf : DynGraphAt mem forest vCap eCap branch.F.F)
    (hnum : EdgeValuesAt mem numerator h L P E branch.wstr)
    (hden : EdgeValuesAt mem denominator h L P E (fun _ => 1))
    (hT : base+4 ≤ tree) (hF : base+4 ≤ forest) (hR : base+4 ≤ roots)
    (htEnd : tree+dynGraphSize vCap eCap ≤ roots)
    (hfEnd : forest+dynGraphSize vCap eCap ≤ roots)
    (hrEnd : roots+vCap ≤ stretch)
    (hN : stretch+2 ≤ numerator) (hD : stretch+2 ≤ denominator) :
    (serializeBranchContract w vCap eCap h L P E branch).pre
      [base,tree,forest,roots,stretch,collection,j,numerator,denominator] mid := by
  obtain ⟨r,he,_,hr,hframe⟩ := hroot
  have he' : roots = r := (List.cons.inj he).1
  subst r
  have ht' := ht.of_agree (mem' := mid) (fun a _ ha => hframe a (Or.inl (ha.trans_le htEnd)))
  have hf' := hf.of_agree (mem' := mid) (fun a _ ha => hframe a (Or.inl (ha.trans_le hfEnd)))
  have hnum' := hnum.congr (mem' := mid) (fun e _ i _ => hframe _ (Or.inr (by omega)))
  have hden' := hden.congr (mem' := mid) (fun e _ i _ => hframe _ (Or.inr (by omega)))
  refine ⟨base,tree,forest,roots,stretch,collection,j,numerator,denominator,rfl,
    ⟨stretch,numerator,denominator,rfl,hs,hN,hD,hnum',hden'⟩,?_⟩
  intro result out hdesc
  refine ⟨base,tree,forest,roots,stretch,collection,j,rfl,?_,hw,hslot⟩
  exact branchHeader_pre_of_descriptor hdesc hb ht' hf' (hmodel ▸ hr)
    hT hF hR (by omega) (by omega) (by omega) (htEnd.trans (by omega))
    (hfEnd.trans (by omega)) hrEnd

/-- The serialized pointers and the reserved allocation ranges give the
footprint used by the collection append invariant. -/
theorem branchWithin_of_publishedPointers {mem : ℕ → ℕ}
    {base tree forest roots stretch numerator denominator floor limit vCap eCap L : ℕ}
    {E : Finset ℕ}
    (hT : mem base = tree) (hF : mem (base+1) = forest)
    (hR : mem (base+2) = roots) (hS : mem (base+3) = stretch)
    (hN : mem stretch = numerator) (hD : mem (stretch+1) = denominator)
    (hb : floor ≤ base) (hB : base+4 ≤ limit)
    (ht : floor ≤ tree) (htEnd : tree+dynGraphSize vCap eCap ≤ limit)
    (hf : floor ≤ forest) (hfEnd : forest+dynGraphSize vCap eCap ≤ limit)
    (hr : floor ≤ roots) (hrEnd : roots+vCap ≤ limit)
    (hs : floor ≤ stretch) (hsEnd : stretch+2 ≤ limit)
    (hn : floor ≤ numerator) (hd : floor ≤ denominator)
    (hnEnd : ∀ e ∈ E, numerator+e*L+L ≤ limit)
    (hdEnd : ∀ e ∈ E, denominator+e*L+L ≤ limit) :
    BranchWithin mem base floor limit vCap eCap L E := by
  unfold BranchWithin
  rw [hT,hF,hR,hS,hN,hD]
  exact ⟨hb,hB,ht,htEnd,hf,hfEnd,hr,hrEnd,hs,hsEnd,hn,hd,hnEnd,hdEnd⟩

/-- Publishing a branch after the allocated prefix gives the frame and
footprint needed by the Definition 5.8 collection loop. -/
theorem publishRootedBranch_append {w root serialize : ℕ} {p : Program} {ω : ℕ → Bool}
    {vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF} {G : MGraph}
    (mem : ℕ → ℕ)
    (pos base tree forest roots stretch collection j numerator denominator vertices : ℕ)
    (floor oldEnd newEnd : ℕ)
    (hr : MeetsContract w p root (branchRootsContract w vCap G))
    (hs : MeetsContract w p serialize (serializeBranchContract w vCap eCap h L P E branch))
    (hv : G.V.Nonempty) (hname : mem vertices = vertexName G 0)
    (hrootWord : firstVertex G.V < 2^w)
    (hpre : (branchRootsContract w vCap G).pre [roots,firstVertex G.V] mem)
    (hnext : ∀ ret mid,
      (branchRootsContract w vCap G).post [roots,firstVertex G.V] mem ret mid →
      (serializeBranchContract w vCap eCap h L P E branch).pre
        [base,tree,forest,roots,stretch,collection,j,numerator,denominator] mid)
    (hfloor : floor ≤ oldEnd)
    (hb : oldEnd ≤ base) (hB : base+4 ≤ newEnd)
    (ht : base+4 ≤ tree) (htEnd : tree+dynGraphSize vCap eCap ≤ newEnd)
    (hf : base+4 ≤ forest) (hfEnd : forest+dynGraphSize vCap eCap ≤ newEnd)
    (hR : base+4 ≤ roots) (hrEnd : roots+vCap ≤ newEnd)
    (hS : base+4 ≤ stretch) (hsEnd : stretch+2 ≤ newEnd)
    (hn : stretch+2 ≤ numerator) (hd : stretch+2 ≤ denominator)
    (hnEnd : ∀ e ∈ E, numerator+e*L+L ≤ newEnd)
    (hdEnd : ∀ e ∈ E, denominator+e*L+L ≤ newEnd) :
    let args := [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices]
    (∀ a ∈ args, a < 2^w) →
    ∃ o out cost, Runs w p ω (publishRootedBranchBody root serialize)
      (startState args mem pos) o out cost ∧
      o.value = 0 ∧ out.mem (collection+1+j) = base ∧
      (∀ a, a < oldEnd ∨ newEnd ≤ a → a ≠ collection+1+j → out.mem a = mem a) ∧
      BranchWithin out.mem base floor newEnd vCap eCap L E ∧
      LSFAt out.mem base vCap eCap h L P E branch ∧ cost ≤ 116 := by
  intro args hwords
  obtain ⟨o,out,cost,hrun,⟨hret,hslot,hlayout,hT,hF,hroots,hstretch,hN,hD,hframe⟩,hcost⟩ :=
    publishRootedBranch_runs (p := p) (ω := ω) mem pos base tree forest roots stretch
      collection j numerator denominator vertices hr hs hwords hv hname hrootWord hpre hnext
  refine ⟨o,out,cost,hrun,hret,hslot,?_,?_,hlayout,hcost⟩
  · intro a ha hne
    exact hframe a hne (by omega) (by omega) (by omega)
  · exact branchWithin_of_publishedPointers hT hF hroots hstretch hN hD
      (by omega) hB (by omega) htEnd (by omega) hfEnd (by omega) hrEnd
      (by omega) hsEnd (by omega) (by omega) hnEnd hdEnd

/-- Contract for appending a branch after its graph and numeric payloads
are available. The allocation bounds describe the reserved output ranges. -/
def publishRootedBranchContract (w vCap eCap h L P floor oldEnd newEnd : ℕ)
    (E : Finset ℕ) (branch : LSF) (G : MGraph) : Contract where
  pre args mem := ∃ base tree forest roots stretch collection j numerator denominator vertices,
    args = [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices] ∧
    G.V.Nonempty ∧ mem vertices = vertexName G 0 ∧ firstVertex G.V < 2^w ∧
    (branchRootsContract w vCap G).pre [roots,firstVertex G.V] mem ∧
    (∀ ret mid, (branchRootsContract w vCap G).post [roots,firstVertex G.V] mem ret mid →
      (serializeBranchContract w vCap eCap h L P E branch).pre
        [base,tree,forest,roots,stretch,collection,j,numerator,denominator] mid) ∧
    floor ≤ oldEnd ∧ oldEnd ≤ base ∧ base+4 ≤ newEnd ∧
    base+4 ≤ tree ∧ tree+dynGraphSize vCap eCap ≤ newEnd ∧
    base+4 ≤ forest ∧ forest+dynGraphSize vCap eCap ≤ newEnd ∧
    base+4 ≤ roots ∧ roots+vCap ≤ newEnd ∧
    base+4 ≤ stretch ∧ stretch+2 ≤ newEnd ∧
    stretch+2 ≤ numerator ∧ stretch+2 ≤ denominator ∧
    (∀ e ∈ E, numerator+e*L+L ≤ newEnd) ∧
    (∀ e ∈ E, denominator+e*L+L ≤ newEnd)
  post args mem ret out := ∃ base collection j,
    args[0]? = some base ∧ args[5]? = some collection ∧ args[6]? = some j ∧
    ret = 0 ∧ out (collection+1+j) = base ∧
    (∀ a, a < oldEnd ∨ newEnd ≤ a → a ≠ collection+1+j → out a = mem a) ∧
    BranchWithin out base floor newEnd vCap eCap L E ∧
    LSFAt out base vCap eCap h L P E branch
  cost _ _ := 116

/-- A reserved root range and the prepared payloads suffice to call the
rooted publisher with the append allocation bounds. -/
theorem publishRootedBranch_pre_of_payloads {w vCap eCap h L P floor oldEnd newEnd : ℕ}
    {E : Finset ℕ} {branch : LSF} {G : MGraph} {mem : ℕ → ℕ}
    {base tree forest roots stretch collection j numerator denominator vertices : ℕ}
    (hv : G.V.Nonempty) (hname : mem vertices = vertexName G 0)
    (hvertex : firstVertex G.V < vCap) (hcap : roots+vCap < 2^w)
    (hz : ∀ v < vCap, mem (roots+v) = 0)
    (hmodel : componentRoots G = branch.F.R) (hw : 1 < 2^w)
    (hslot : collection+1+j < base) (hfit : newEnd < 2^w)
    (hgraphT : DynGraphAt mem tree vCap eCap branch.T)
    (hgraphF : DynGraphAt mem forest vCap eCap branch.F.F)
    (hnum : EdgeValuesAt mem numerator h L P E branch.wstr)
    (hden : EdgeValuesAt mem denominator h L P E (fun _ => 1))
    (hfloor : floor ≤ oldEnd) (hb : oldEnd ≤ base)
    (ht : base+4 ≤ tree) (htEnd : tree+dynGraphSize vCap eCap ≤ roots)
    (hf : base+4 ≤ forest) (hfEnd : forest+dynGraphSize vCap eCap ≤ roots)
    (hR : base+4 ≤ roots) (hrEnd : roots+vCap ≤ stretch)
    (hsEnd : stretch+2 ≤ newEnd)
    (hn : stretch+2 ≤ numerator) (hd : stretch+2 ≤ denominator)
    (hnEnd : ∀ e ∈ E, numerator+e*L+L ≤ newEnd)
    (hdEnd : ∀ e ∈ E, denominator+e*L+L ≤ newEnd) :
    (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G).pre
      [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices] mem := by
  refine ⟨base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices,rfl,
    hv,hname,by omega,⟨roots,rfl,hw,hvertex,hcap,hz⟩,?_,
    hfloor,hb,by omega,ht,by omega,hf,by omega,hR,by omega,by omega,hsEnd,hn,hd,hnEnd,hdEnd⟩
  intro ret mid hpost
  exact serializeBranch_pre_of_roots hpost hmodel hw hslot (by omega) (by omega)
    hgraphT hgraphF hnum hden ht hf hR htEnd hfEnd hrEnd hn hd

/-- The installed root writer and serializer expose a branch with the
footprint and frame needed by the collection's append invariant. -/
theorem publishRootedBranch_meetsContract {w entry root serialize vCap eCap h L P
    floor oldEnd newEnd : ℕ} {p : Program} {E : Finset ℕ} {branch : LSF} {G : MGraph}
    (hp : p.procs[entry]? = some (publishRootedBranchBody root serialize))
    (hr : MeetsContract w p root (branchRootsContract w vCap G))
    (hs : MeetsContract w p serialize (serializeBranchContract w vCap eCap h L P E branch)) :
    MeetsContract w p entry
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices,rfl,
    hv,hname,hrootWord,hroot,hnext,hfloor,hb,hB,ht,htEnd,hf,hfEnd,hR,hrEnd,hS,hsEnd,
    hn,hd,hnEnd,hdEnd⟩ := hpre
  obtain ⟨o,out,cost,hrun,hret,hslot,hframe,hspan,hlayout,hcost⟩ :=
    publishRootedBranch_append (p := p) (ω := ω)
      mem pos base tree forest roots stretch collection j numerator denominator vertices
      floor oldEnd newEnd hr hs hv hname hrootWord hroot hnext hfloor hb hB ht htEnd hf hfEnd
      hR hrEnd hS hsEnd hn hd hnEnd hdEnd hwords
  exact ⟨o,out,cost,hrun,⟨base,collection,j,rfl,rfl,rfl,hret,hslot,hframe,hspan,hlayout⟩,hcost⟩

/-- Build the branch payloads, publish the branch, and return the allocation end.
The first ten registers are the publisher's arguments. -/
def appendBranchBody (prepare publish : ℕ) (payloadArgs : List Expr) : Stmt :=
  .seq (.call 11 prepare payloadArgs)
    (.seq (.call 12 publish ((List.range 10).map Expr.reg)) (.ret (.reg 11)))

/-- The append call combines the payload builder's prefix frame with the
publisher's single-slot exception and returns the allocation end. -/
theorem appendBranch_runs {w prepare publish : ℕ} {p : Program} {ω : ℕ → Bool}
    {vCap eCap h L P floor oldEnd newEnd : ℕ} {E : Finset ℕ}
    {branch : LSF} {G : MGraph} {C : Contract} {payloadArgs : List Expr}
    (st : State) (base tree forest roots stretch collection j numerator denominator vertices : ℕ)
    (vs : List ℕ)
    (hp : MeetsContract w p prepare C)
    (hb : MeetsContract w p publish
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G))
    (ha : evalArgs w st payloadArgs = some vs)
    (hw : ∀ a ∈ vs, a < 2^w) (hc : C.pre vs st.mem) :
    let args := [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices]
    (∀ i < 10, st.regs i = args[i]!) →
    (∀ a ∈ args, a < 2^w) → newEnd < 2^w →
    (∀ ret mid, C.post vs st.mem ret mid →
      ret = newEnd ∧ (∀ a < oldEnd, mid a = st.mem a) ∧
        (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G).pre args mid) →
    ∃ o out cost, Runs w p ω (appendBranchBody prepare publish payloadArgs) st o out cost ∧
      (o.value = newEnd ∧ (∀ a < oldEnd, a ≠ collection+1+j → out.mem a = st.mem a) ∧
        (let ptr := out.mem (collection+1+j)
         BranchWithin out.mem ptr floor newEnd vCap eCap L E ∧
           LSFAt out.mem ptr vCap eCap h L P E branch)) ∧
      cost ≤ argsSize payloadArgs + C.cost vs st.mem + 132 := by
  intro args hregs hwords hend hnext
  apply runs_start_le
  unfold appendBranchBody
  refine runs_seq_call_le hp ha hw hc ?_
  intro ret mid pos hpost
  obtain ⟨rfl,hframe,hpre⟩ := hnext ret mid hpost
  have hEval : evalArgs w ⟨mid,Function.update st.regs 11 ret,pos⟩
      ((List.range 10).map Expr.reg) = some args := by
    have h0 := hregs 0 (by decide)
    have h1 := hregs 1 (by decide)
    have h2 := hregs 2 (by decide)
    have h3 := hregs 3 (by decide)
    have h4 := hregs 4 (by decide)
    have h5 := hregs 5 (by decide)
    have h6 := hregs 6 (by decide)
    have h7 := hregs 7 (by decide)
    have h8 := hregs 8 (by decide)
    have h9 := hregs 9 (by decide)
    dsimp [args] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp [args, List.range_succ, evalArgs, Expr.eval, Function.update_of_ne,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  refine runs_seq_call_le hb hEval hwords hpre ?_
  intro result out pos' ho
  obtain ⟨b,c,k,hb',hc',hk,_,hslot,hout,hspan,hlayout⟩ := ho
  simp only [args,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.some.injEq] at hb' hc' hk
  simp only [← hb', ← hc', ← hk] at hslot hout hspan hlayout
  refine runs_ret_le (v := ret) (by eval_expr) ⟨rfl,?_,?_⟩ ?_
  · intro a hlt hne
    exact (hout a (Or.inl hlt) hne).trans (hframe a hlt)
  · change BranchWithin out (out (collection+1+j)) floor ret vCap eCap L E ∧
      LSFAt out (out (collection+1+j)) vCap eCap h L P E branch
    rw [hslot]
    exact ⟨hspan,hlayout⟩
  · change 0 + argsSize payloadArgs + C.cost vs st.mem + 2 + 10 + 116 + 2 + 2 ≤ _
    omega

/-- The append procedure takes ten publication words followed by the
payload builder inputs, and returns the new allocation end. -/
def appendBranchContract (w vCap eCap h L P floor oldEnd newEnd collection j : ℕ)
    (E : Finset ℕ) (branch : LSF) (G : MGraph) (C : Contract)
    (payloadArgs : List Expr) (payload : List ℕ) : Contract where
  pre args mem := ∃ base tree forest roots stretch numerator denominator vertices rest,
    let publish := [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices]
    args = publish ++ rest ∧
    (∀ pos, evalArgs w (startState args mem pos) payloadArgs = some payload) ∧
    (∀ a ∈ payload, a < 2^w) ∧ C.pre payload mem ∧ newEnd < 2^w ∧
    ∀ ret mid, C.post payload mem ret mid →
      ret = newEnd ∧ (∀ a < oldEnd, mid a = mem a) ∧
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G).pre publish mid
  post _ mem ret out :=
    ret = newEnd ∧ (∀ a < oldEnd, a ≠ collection+1+j → out a = mem a) ∧
    (let ptr := out (collection+1+j)
     BranchWithin out ptr floor newEnd vCap eCap L E ∧
       LSFAt out ptr vCap eCap h L P E branch)
  cost _ mem := argsSize payloadArgs + C.cost payload mem + 132

/-- The installed append body implements the round loop's branch frame
and readout conditions. -/
theorem appendBranch_meetsContract {w entry prepare publish vCap eCap h L P floor oldEnd newEnd
    collection j : ℕ} {p : Program} {E : Finset ℕ} {branch : LSF} {G : MGraph}
    {C : Contract} {payloadArgs : List Expr} {payload : List ℕ}
    (he : p.procs[entry]? = some (appendBranchBody prepare publish payloadArgs))
    (hp : MeetsContract w p prepare C)
    (hb : MeetsContract w p publish
      (publishRootedBranchContract w vCap eCap h L P floor oldEnd newEnd E branch G)) :
    MeetsContract w p entry
      (appendBranchContract w vCap eCap h L P floor oldEnd newEnd collection j E branch G C
        payloadArgs payload) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,tree,forest,roots,stretch,numerator,denominator,vertices,rest,rfl,
    ha,hw,hc,hend,hnext⟩ := hpre
  refine appendBranch_runs (p := p) (ω := ω) _ base tree forest roots stretch collection j
    numerator denominator vertices payload hp hb (ha pos) hw hc ?_
    (fun a hs => hwords a (List.mem_append_left _ hs)) hend hnext
  intro i hi
  simp only [startState]
  have hleft : i < [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices].length := hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hleft,
    List.getElem?_eq_getElem hleft]
  simpa only [Option.getD_some] using (getElem!_pos (c := [base,tree,forest,roots,stretch,collection,j,numerator,denominator,vertices]) (i := i) hleft).symm

end MinCostFlow.LastLevelProgram
