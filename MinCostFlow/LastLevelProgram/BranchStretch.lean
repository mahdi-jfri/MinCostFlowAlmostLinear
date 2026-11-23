module

public import MinCostFlow.LastLevelProgram.BranchStretchSources
import WordRAM.Tactic

/-!
# Writing stretches by original edge name

The Definition 5.8 rebuild (pages 19–20) translates compact sources into addresses and scatters the stretch blocks by original edge name.
-/

public section

namespace MinCostFlow.LastLevelProgram

open SparseCore Num MinRatio WordRAM

/-- The address scan writes the source pointers for the scatter and
preserves the earlier names and source blocks. -/
theorem scatterBranchStretch_pre_of_sourceTable {w h L m cap names addr dst : ℕ}
    {mem mid : ℕ → ℕ} (name index : ℕ → ℕ) (sentinel src stride unit : ℕ)
    (hframe : ∀ a < addr, mid a = mem a)
    (htable : ∀ i < m, mid (addr+i) = if index i = sentinel then unit else src+index i*stride)
    (hnames : names + m ≤ addr) (haddr : addr + m ≤ dst) (hcap : cap ≤ 2^w)
    (hn : ∀ i < m, mem (names+i) = name i ∧ name i < cap)
    (hblocks : ∀ i < m,
      let a := if index i = sentinel then unit else src+index i*stride
      a + L ≤ addr ∧ Valid mem a h L) :
    ∀ i < m,
      let a := if index i = sentinel then unit else src+index i*stride
      mid (names+i) = name i ∧ mid (addr+i) = a ∧
        name i < cap ∧ name i < 2^w ∧ a + L ≤ dst ∧ Valid mid a h L := by
  intro i hi a
  obtain ⟨hnamed, hfit⟩ := hn i hi
  obtain ⟨hb, hv⟩ := hblocks i hi
  refine ⟨(hframe _ (by omega)).trans hnamed, htable i hi, hfit, hfit.trans_le hcap,
    hb.trans (by omega), ?_⟩
  intro k hk
  rw [hframe _ (by omega)]
  exact hv k hk

/-- Callable form of the stretch source address loop. -/
@[expose] def stretchSourceBody (entry : ℕ) : Stmt :=
  .seq (stretchSourceLoop entry) (.ret (.const 0))

/-- Contract of the installed source-address table pass. -/
@[expose] def stretchSourceContract (w : ℕ) (index : ℕ → ℕ) : Contract where
  pre args mem := ∃ indices sentinel src stride unit dst m,
    args = [indices,sentinel,src,stride,unit,dst,m] ∧
    1 < 2^w ∧ indices+m ≤ dst ∧ dst+m < 2^w ∧
    ∀ i < m, mem (indices+i) = index i ∧ index i < 2^w ∧
      (src+index i*stride < 2^w ∨ index i = sentinel)
  post args mem ret out := ∃ indices sentinel src stride unit dst m,
    args = [indices,sentinel,src,stride,unit,dst,m] ∧ ret = 0 ∧
    (∀ i < m, out (dst+i) = if index i = sentinel then unit else src+index i*stride) ∧
    ∀ a, a < dst ∨ dst+m ≤ a → out a = mem a
  cost args _ := 45 * args.getD 6 0 + 10

/-- The installed address pass builds the table and frames other cells. -/
theorem stretchSource_meetsContract {w entry write : ℕ} {p : Program} (index : ℕ → ℕ)
    (hp : p.procs[entry]? = some (stretchSourceBody write))
    (hw : MeetsContract w p write (writeStretchSourceContract w)) :
    MeetsContract w p entry (stretchSourceContract w index) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨indices,sentinel,src,stride,unit,dst,m,rfl,hw',hs,hr,hi⟩ := hpre
  have ht := stretchSourceLoop_triple hw mem pos indices sentinel src stride unit dst m
    index hw' hwords hs hr hi
  apply runs_start_le
  unfold stretchSourceBody
  refine runs_seq_triple_le ht rfl ?_
  intro st hs
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨indices,sentinel,src,stride,unit,dst,m,rfl,rfl,hs⟩ ?_
  simp [stretchSourceContract, Expr.size]

/-- Callable scatter from a table of absolute source addresses. -/
@[expose] def scatterBranchStretchBody (entry : ℕ) : Stmt :=
  .seq (scatterBranchStretchLoop entry) (.ret (.const 0))

/-- The scatter writes the named stretch table without scanning gaps. -/
@[expose] def scatterBranchStretchContract (w h P cap : ℕ) (name source : ℕ → ℕ) : Contract where
  pre args mem := ∃ names addresses dst L m,
    args = [0,1,names,addresses,dst,L,m] ∧
    1 < 2^w ∧ names+m ≤ dst ∧ addresses+m ≤ dst ∧ dst+cap*L < 2^w ∧
    (∀ i < m, mem (names+i) = name i ∧ mem (addresses+i) = source i ∧
      name i < cap ∧ name i < 2^w ∧ source i+L ≤ dst ∧ Valid mem (source i) h L) ∧
    ∀ i < m, ∀ j < m, name i = name j → i = j
  post args mem ret out := ∃ names addresses dst L m,
    args = [0,1,names,addresses,dst,L,m] ∧ ret = 0 ∧
    (∀ i < m, Valid out (dst+name i*L) h L ∧
      fixVal out (dst+name i*L) h L P = fixVal mem (source i) h L P) ∧
    ∀ a, a < dst ∨ dst+cap*L ≤ a → out a = mem a
  cost args _ := (17 * args.getD 5 0 + 47) * args.getD 6 0 + 10

/-- The named scatter meets its ordinary procedure contract. -/
theorem scatterBranchStretch_meetsContract {w h P cap entry copy : ℕ} {p : Program}
    (name source : ℕ → ℕ) (hp : p.procs[entry]? = some (scatterBranchStretchBody copy))
    (hc : MeetsContract w p copy (copyBranchStretchContract w h P)) :
    MeetsContract w p entry (scatterBranchStretchContract w h P cap name source) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨names,addresses,dst,L,m,rfl,hw,hn,ha,hd,he,hdistinct⟩ := hpre
  have ht := scatterBranchStretch_addresses hc mem pos names addresses dst L m cap name source
    hw (hwords L (by simp)) (hwords m (by simp)) hn ha hd he hdistinct
  apply runs_start_le
  unfold scatterBranchStretchBody
  refine runs_seq_triple_le ht rfl ?_
  intro st hs
  refine runs_ret_le (v := 0) (by eval_expr) ⟨names,addresses,dst,L,m,rfl,rfl,hs⟩ ?_
  simp [scatterBranchStretchContract, Expr.size]

/-- Translate the source indices and scatter the named stretch blocks. -/
@[expose] def namedStretchBody (translate scatter : ℕ) : Stmt :=
  .seq (.call 10 translate [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6])
    (.seq (.call 11 scatter [.const 0,.const 1,.reg 7,.reg 5,.reg 8,.reg 9,.reg 6])
      (.ret (.const 0)))

/-- The two scans compute the named values from the unchanged compact
source blocks, framing memory before and after their allocations. -/
theorem namedStretch_runs {w h P translate scatter : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos indices sentinel src stride unit addresses m names dst L cap : ℕ)
    (index name : ℕ → ℕ) :
    let source := fun i => if index i = sentinel then unit else src+index i*stride
    let input := [indices,sentinel,src,stride,unit,addresses,m,names,dst,L]
    MeetsContract w p translate (stretchSourceContract w index) →
    MeetsContract w p scatter (scatterBranchStretchContract w h P cap name source) →
    (∀ a ∈ input, a < 2^w) → 1 < 2^w →
    indices+m ≤ addresses → names+m ≤ addresses → addresses+m ≤ dst →
    dst+cap*L < 2^w → cap ≤ 2^w →
    (∀ i < m, mem (indices+i) = index i ∧ index i < 2^w ∧
      (src+index i*stride < 2^w ∨ index i = sentinel)) →
    (∀ i < m, mem (names+i) = name i ∧ name i < cap) →
    (∀ i < m, source i + L ≤ addresses ∧ Valid mem (source i) h L) →
    (∀ i < m, ∀ j < m, name i = name j → i = j) →
    ∃ o out cost, Runs w p ω (namedStretchBody translate scatter)
        (startState input mem pos) o out cost ∧
      (o.value = 0 ∧
        (∀ i < m, Valid out.mem (dst+name i*L) h L ∧
          fixVal out.mem (dst+name i*L) h L P = fixVal mem (source i) h L P) ∧
        ∀ a, a < addresses ∨ (addresses+m ≤ a ∧ a < dst) ∨ dst+cap*L ≤ a → out.mem a = mem a) ∧
      cost ≤ (17*L+92)*m+40 := by
  intro source input ht hs hwords hw hidx hnames haddr hroom hcap hin hnamesAt hblocks hdistinct
  apply runs_start_le
  unfold namedStretchBody
  refine runs_seq_call_le ht (vs := [indices,sentinel,src,stride,unit,addresses,m])
    (by rfl) ?_ ⟨indices,sentinel,src,stride,unit,addresses,m,rfl,hw,hidx,by omega,hin⟩ ?_
  · intro a ha
    exact hwords a (List.mem_append_left [names,dst,L] ha)
  · intro ret mid pos' hp
    obtain ⟨ix,sen,sr,str,un,ad,sz,he,_,htable,hframe⟩ := hp
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
    have he' := scatterBranchStretch_pre_of_sourceTable (w := w) name index sentinel src stride unit
      (fun a ha => hframe a (Or.inl ha)) htable hnames haddr hcap hnamesAt hblocks
    refine runs_seq_call_le hs (vs := [0,1,names,addresses,dst,L,m]) (by eval_expr) ?_
      ⟨names,addresses,dst,L,m,rfl,hw,by omega,haddr,hroom,he',hdistinct⟩ ?_
    · intro a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | omega | exact hwords _ (by simp [input])
    · intro ret' out _ hout
      obtain ⟨na,ad,ds,l,sz,he,_,hvals,houtFrame⟩ := hout
      simp only [List.cons.injEq,and_true,true_and] at he
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
      refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,?_,?_⟩ ?_
      · intro i hi
        obtain ⟨hv,hval⟩ := hvals i hi
        have hsrc : intVal mid (source i) h L = intVal mem (source i) h L :=
          intVal_congr fun k hk => hframe _ (Or.inl (by have := (hblocks i hi).1; omega))
        exact ⟨hv,hval.trans (by simp only [fixVal,hsrc])⟩
      · intro a ha
        exact (houtFrame a (by omega)).trans (hframe a (by omega))
      · simp [stretchSourceContract,scatterBranchStretchContract,Expr.size,argsSize]
        ring_nf
        exact le_rfl

/-- Linked interface for the two scans that produce the named stretch blocks. -/
@[expose] def namedStretchContract (w h L P cap : ℕ) (index name : ℕ → ℕ) : Contract where
  pre args mem := ∃ indices sentinel src stride unit addresses m names dst,
    let source := fun i => if index i = sentinel then unit else src+index i*stride
    args = [indices,sentinel,src,stride,unit,addresses,m,names,dst,L] ∧
    1 < 2^w ∧ indices+m ≤ addresses ∧ names+m ≤ addresses ∧ addresses+m ≤ dst ∧
    dst+cap*L < 2^w ∧ cap ≤ 2^w ∧
    (∀ i < m, mem (indices+i) = index i ∧ index i < 2^w ∧
      (src+index i*stride < 2^w ∨ index i = sentinel)) ∧
    (∀ i < m, mem (names+i) = name i ∧ name i < cap) ∧
    (∀ i < m, source i + L ≤ addresses ∧ Valid mem (source i) h L) ∧
    (∀ i < m, ∀ j < m, name i = name j → i = j)
  post args mem ret out := ∃ indices sentinel src stride unit addresses m names dst,
    let source := fun i => if index i = sentinel then unit else src+index i*stride
    args = [indices,sentinel,src,stride,unit,addresses,m,names,dst,L] ∧ ret = 0 ∧
    (∀ i < m, Valid out (dst+name i*L) h L ∧
      fixVal out (dst+name i*L) h L P = fixVal mem (source i) h L P) ∧
    ∀ a, a < addresses ∨ (addresses+m ≤ a ∧ a < dst) ∨ dst+cap*L ≤ a → out a = mem a
  cost args _ := (17*L+92)*args[6]!+40

/-- The compact representative array and the original edge tables
suffice for a named scatter. The sentinel reads the unit block. -/
theorem namedStretch_pre_of_compact {w h L P cap : ℕ}
    (G : MGraph) (ℓ : ℕ → ℝ) (mem : ℕ → ℕ)
    (indices src stride unit addresses names dst : ℕ)
    (hw : 1 < 2^w) (hi : indices+G.m ≤ addresses)
    (hn : names+G.m ≤ addresses) (ha : addresses+G.m ≤ dst)
    (hfit : dst+cap*L < 2^w) (hcap : cap ≤ 2^w)
    (hNames : ∀ i < G.m, mem (names+i) = edgeName G i)
    (hBound : ∀ e ∈ G.E, e < cap)
    (hu : unit+L ≤ addresses) (huValid : Valid mem unit h L) :
    let H := representativeGraph G ℓ
    let index := branchStretchIndex G ℓ ∘ edgeName G
    H.m < 2^w →
    (∀ i < G.m, mem (indices+i) = index i) →
    (∀ i < H.m, src+i*stride+L ≤ addresses ∧ Valid mem (src+i*stride) h L) →
    (namedStretchContract w h L P cap index (edgeName G)).pre
      [indices,H.m,src,stride,unit,addresses,G.m,names,dst,L] mem := by
  intro H index hm hIndex hRep
  have hIndexLe (i : ℕ) : index i ≤ H.m := branchStretchIndex_le G ℓ (edgeName G i)
  refine ⟨indices,H.m,src,stride,unit,addresses,G.m,names,dst,rfl,hw,hi,hn,ha,hfit,hcap,
    ?_,?_,?_,?_⟩
  · intro i hi'
    refine ⟨hIndex i hi', (hIndexLe i).trans_lt hm, ?_⟩
    rcases (hIndexLe i).lt_or_eq with hlt | heq
    · have := (hRep _ hlt).1
      exact Or.inl (by omega)
    · exact Or.inr heq
  · intro i hi'
    exact ⟨hNames i hi', hBound _ (edgeName_mem hi')⟩
  · intro i _
    rcases (hIndexLe i).lt_or_eq with hlt | heq
    · simpa only [ite_eq_right hlt.ne] using hRep _ hlt
    · simpa only [ite_eq_left heq] using And.intro hu huValid
  · intro i hi' j hj' hEq
    simpa only [edgeIndex_name hi',edgeIndex_name hj'] using congrArg (edgeIndex G) hEq

/-- A numerator scatter leaves both original index tables and the unit
block available for a denominator scatter with zero source stride. -/
theorem namedStretch_denominator_pre {w h L P cap : ℕ}
    {index name mem mid : ℕ → ℕ}
    {indices sentinel src stride unit addresses m names numerator denominator : ℕ}
    (hnum : (namedStretchContract w h L P cap index name).pre
      [indices,sentinel,src,stride,unit,addresses,m,names,numerator,L] mem)
    (hframe : ∀ a < addresses, mid a = mem a)
    (hunit : Valid mem unit h L) (hunitEnd : unit+L ≤ addresses)
    (horder : numerator ≤ denominator) (hfit : denominator+cap*L < 2^w) :
    (namedStretchContract w h L P cap index name).pre
      [indices,sentinel,unit,0,unit,addresses,m,names,denominator,L] mid := by
  obtain ⟨ix,se,sr,str,un,ad,sz,na,dst,heq,hw,hi,hn,ha,_,hcap,hidx,hname,_,hdistinct⟩ := hnum
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have huword : unit < 2^w := by omega
  refine ⟨indices,sentinel,unit,0,unit,addresses,m,names,denominator,rfl,
    hw,hi,hn,ha.trans horder,hfit,hcap,?_,?_,?_,hdistinct⟩
  · intro i h
    obtain ⟨hread,hword,_⟩ := hidx i h
    exact ⟨(hframe _ (by omega)).trans hread,hword,Or.inl (by simpa using huword)⟩
  · intro i h
    obtain ⟨hread,hbound⟩ := hname i h
    exact ⟨(hframe _ (by omega)).trans hread,hbound⟩
  · intro i _
    have hv : Valid mid unit h L := fun k hk =>
      (hframe (unit+k) (by omega)) ▸ hunit k hk
    simpa using And.intro hunitEnd hv

/-- The installed named stretch procedure implements the two scans and
preserves the compact stretch values used as their source. -/
theorem namedStretch_meetsContract {w h L P cap entry translate scatter : ℕ}
    {p : Program} (index name : ℕ → ℕ)
    (hp : p.procs[entry]? = some (namedStretchBody translate scatter))
    (ht : MeetsContract w p translate (stretchSourceContract w index))
    (hs : ∀ sentinel src stride unit, MeetsContract w p scatter
      (scatterBranchStretchContract w h P cap name
        (fun i => if index i = sentinel then unit else src+index i*stride))) :
    MeetsContract w p entry (namedStretchContract w h L P cap index name) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨indices,sentinel,src,stride,unit,addresses,m,names,dst,rfl,
    hw,hi,hn,ha,hr,hcap,hidx,hname,hblocks,hdistinct⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ := namedStretch_runs (p := p) (ω := ω)
    mem pos indices sentinel src stride unit addresses m names dst L cap index name
    ht (hs sentinel src stride unit) hwords hw hi hn ha hr hcap hidx hname hblocks hdistinct
  exact ⟨o,out,cost,hrun,⟨indices,sentinel,src,stride,unit,addresses,m,names,dst,rfl,hpost⟩,hcost⟩

/-- Identify the output of the address translation and scatter with
the exact fixed-point model branch. The unit block may be separate
from the strided representative blocks. -/
theorem branchStretch_of_namedOutput
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (j h L P src stride unit dst : ℕ) (mem out : ℕ → ℕ)
    (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let prec := weightPrecision C H
    let query := stretchQuery oracle H ℓ prec
    let v := weights prec (roundedScale C H) query j
    let index := branchStretchIndex G ℓ ∘ edgeName G
    (∀ i < H.m, fixVal mem (src+i*stride) h L P = query v (edgeName H i)) →
    fixVal mem unit h L P = 1 →
    (∀ i < G.m, Valid out (dst+edgeName G i*L) h L ∧
      fixVal out (dst+edgeName G i*L) h L P =
        fixVal mem (if index i = H.m then unit else src+index i*stride) h L P) →
    EdgeValuesAt out dst h L P G.E ((fixedPointLastLevelTool oracle C).build G ℓ |>.2 j).wstr := by
  intro H prec query v index hrep hunit hout
  let source := fun i => if i = H.m then unit else src+i*stride
  refine branchStretch_edgeValuesAt_of_scatter oracle C G ℓ j h L P dst source mem out hnl
    (fun i hi => ?_) ?_ hout
  · change fixVal mem (source i) h L P = query v (edgeName H i)
    have hne : i ≠ H.m := Nat.ne_of_lt hi
    rw [show source i = src+i*stride from ite_eq_right hne]
    exact hrep i hi
  · change fixVal mem (source H.m) h L P = 1
    simpa only [source, ite_eq_left rfl] using hunit

/-- A single positive table can serve as both numerator and denominator
for unit stretches. The loop-only branch can keep one private table. -/
theorem loopOnlyStretch_at {mem : ℕ → ℕ} {desc table h L P : ℕ} {E : Finset ℕ}
    (hnum : mem desc = table) (hden : mem (desc+1) = table)
    (hvalues : ∀ e ∈ E, Valid mem (table+e*L) h L ∧ 0 < fixVal mem (table+e*L) h L P) :
    StretchValuesAt mem desc h L P E (fun _ => 1) := by
  intro e he
  rw [hnum,hden]
  obtain ⟨hvalid,hpos⟩ := hvalues e he
  exact ⟨hvalid,hvalid,hpos,div_self hpos.ne'⟩

/-- Copy one live edge's positive length to the loop-only stretch table. -/
@[expose] def loopOnlyCopyStretch (entry : ℕ) : Stmt :=
  let offset : Expr := .bin .mul (.reg 3) (.reg 14)
  .call 63 entry [.bin .add (.reg 13) offset,.bin .add (.reg 60) offset,.reg 14]

/-- A stretch block copy leaves other addresses and scan registers intact. -/
theorem loopOnlyCopyStretch_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (src dst e L : ℕ)
    (hc : MeetsContract w p entry (copyWordsContract w))
    (h3 : st.regs 3 = e) (h13 : st.regs 13 = src) (h14 : st.regs 14 = L)
    (h60 : st.regs 60 = dst)
    (hw : 1 < 2^w) (hs : src+e*L+L < 2^w) (hd : dst+e*L+L < 2^w)
    (hsep : src+e*L+L ≤ dst+e*L ∨ dst+e*L+L ≤ src+e*L) :
    ∃ out cost, Runs w p ω (loopOnlyCopyStretch entry) st .normal out cost ∧
      (∀ i < L, out.mem (dst+e*L+i) = st.mem (src+e*L+i)) ∧
      (∀ a, a < dst+e*L ∨ dst+e*L+L ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 63 → out.regs r = st.regs r) ∧ cost ≤ 17*L+22 := by
  let a := src+e*L
  let b := dst+e*L
  have hoff : e*L < 2^w := by omega
  have ha : a < 2^w := by dsimp [a]; omega
  have hb : b < 2^w := by dsimp [b]; omega
  have hargs : evalArgs w st [.bin .add (.reg 13) (.bin .mul (.reg 3) (.reg 14)),
      .bin .add (.reg 60) (.bin .mul (.reg 3) (.reg 14)),.reg 14] = some [a,b,L] := by
    simp [evalArgs,Expr.eval,BinOp.eval,h3,h13,h14,h60,hoff,ha,hb,a,b]
  have hwords : ∀ x ∈ [a,b,L], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact ha
    · exact hb
    · omega
  obtain ⟨out,c,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 63) hc hargs hwords
      ⟨a,b,L,rfl,hw,hs.le,hd.le,hsep.symm⟩ ω
  obtain ⟨a',b',len,heq,_,hcopy,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  change c ≤ 11+(17*L+10)+1 at hcost
  exact ⟨out,c,hr,hcopy,hframe,hregs,by omega⟩

/-- Load the next live edge name and copy only its block. -/
@[expose] def loopOnlyStretchStep (entry : ℕ) : Stmt :=
  .seq (.assign 3 (.load (.bin .add (.reg 62) (.reg 8)))) (loopOnlyCopyStretch entry)

/-- One iteration copies the live block named by the edge list. -/
theorem loopOnlyStretchStep_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (src dst names i e L : ℕ)
    (hc : MeetsContract w p entry (copyWordsContract w))
    (h8 : st.regs 8 = i) (h13 : st.regs 13 = src) (h14 : st.regs 14 = L)
    (h60 : st.regs 60 = dst) (h62 : st.regs 62 = names)
    (hname : st.mem (names+i) = e) (hn : names+i < 2^w)
    (hw : 1 < 2^w) (hs : src+e*L+L < 2^w) (hd : dst+e*L+L < 2^w)
    (hsep : src+e*L+L ≤ dst+e*L ∨ dst+e*L+L ≤ src+e*L) :
    ∃ out cost, Runs w p ω (loopOnlyStretchStep entry) st .normal out cost ∧
      (∀ j < L, out.mem (dst+e*L+j) = st.mem (src+e*L+j)) ∧
      (∀ a, a < dst+e*L ∨ dst+e*L+L ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 3 → r ≠ 63 → out.regs r = st.regs r) ∧ cost ≤ 17*L+28 := by
  let mid := {st with regs := Function.update st.regs 3 e}
  have hload : Runs w p ω (.assign 3 (.load (.bin .add (.reg 62) (.reg 8))))
      st .normal mid 5 :=
    runs_assign_iff.mpr ⟨e,by simp [Expr.eval,BinOp.eval,h62,h8,hn,hname],rfl,rfl,rfl⟩
  obtain ⟨out,c,hr,hcopy,hframe,hkeep,hcost⟩ :=
    loopOnlyCopyStretch_runs (ω := ω) mid src dst e L hc (by simp [mid])
      (by simpa [mid] using h13) (by simpa [mid] using h14) (by simpa [mid] using h60)
      hw hs hd hsep
  refine ⟨out,5+c+1,runs_seq_iff.mpr (Or.inr ⟨mid,5,c,hload,hr,rfl⟩),
    hcopy,hframe,?_,by omega⟩
  exact fun r h3 h63 => (hkeep r h63).trans (Function.update_of_ne h3 ..)

/-- Copy the stretches for live edges only, even with gaps in the edge names. -/
@[expose] def loopOnlyStretchLoop (entry : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 61) (loopOnlyStretchStep entry)

/-- The private table receives all live blocks in time linear in their total width. -/
theorem loopOnlyStretchLoop_triple {w entry : ℕ} {p : Program}
    (initial : State) (src dst names cap L : ℕ) (edges : List ℕ)
    (hc : MeetsContract w p entry (copyWordsContract w))
    (h13 : initial.regs 13 = src) (h14 : initial.regs 14 = L) (h60 : initial.regs 60 = dst)
    (h61 : initial.regs 61 = edges.length) (h62 : initial.regs 62 = names)
    (hlist : ListAt initial.mem names edges) (hnodup : edges.Nodup)
    (hcap : ∀ e ∈ edges, e < cap) (hw : 1 < 2^w)
    (hn : names+edges.length ≤ dst) (hs : src+cap*L ≤ dst) (hd : dst+cap*L < 2^w) :
    Triple w p (fun st => st = initial) (loopOnlyStretchLoop entry)
      (normalPost fun st =>
        (∀ e ∈ edges, ∀ j < L, st.mem (dst+e*L+j) = initial.mem (src+e*L+j)) ∧
        (∀ a, a < dst ∨ dst+cap*L ≤ a → st.mem a = initial.mem a) ∧
        ∀ r, r ≠ 3 → r ≠ 8 → r ≠ 63 → st.regs r = initial.regs r)
      (fun _ => (17*L+37)*edges.length+7) := by
  let frame (st : State) := ∀ a, a < dst ∨ dst+cap*L ≤ a → st.mem a = initial.mem a
  let keep (st : State) := ∀ r, r ≠ 3 → r ≠ 8 → r ≠ 63 → st.regs r = initial.regs r
  let Inv i (st : State) := st.regs 8 = i ∧ keep st ∧ frame st ∧
    ∀ k (hk : k < min i edges.length), ∀ j < L,
      st.mem (dst+edges[k]*L+j) = initial.mem (src+edges[k]*L+j)
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 61)
    (body := loopOnlyStretchStep entry) (P := fun st => st = initial) (Inv := Inv)
    (17*L+28) 0 edges.length (Nat.zero_le _) hw (fun _ => by omega)
    (fun st h => by
      subst st
      exact ⟨by simp [Expr.eval,show 0 < 2^w by omega],by simp,
        fun _ _ hr _ => Function.update_of_ne hr ..,fun _ _ => rfl,
        fun _ hk => False.elim (by simp at hk)⟩)
    (fun _ _ _ _ h => h.1)
    (fun _ st _ _ h => by simp [Expr.eval,(h.2.1 61 (by decide) (by decide) (by decide)).trans h61])
    (fun i _ hi => by
      intro st ω ⟨hindex,hkeep,hframe,hdone⟩
      let e := edges[i]
      have he := hcap e (List.getElem_mem hi)
      have hblock : e*L+L ≤ cap*L := by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
      obtain ⟨out,c,hr,hcopy,hout,hkeep',hcost⟩ :=
        loopOnlyStretchStep_runs (ω := ω) st src dst names i e L hc hindex
          ((hkeep 13 (by decide) (by decide) (by decide)).trans h13)
          ((hkeep 14 (by decide) (by decide) (by decide)).trans h14)
          ((hkeep 60 (by decide) (by decide) (by decide)).trans h60)
          ((hkeep 62 (by decide) (by decide) (by decide)).trans h62)
          ((hframe _ (by omega)).trans (hlist i hi)) (by omega)
          hw (by omega) (by omega) (Or.inl (by omega))
      refine ⟨.normal,out,c,hr,⟨⟨by simp,?_,?_,?_⟩,
        (hkeep' 8 (by decide) (by decide)).trans hindex⟩,hcost⟩
      · intro r hr3 hr8 hr63
        exact (Function.update_of_ne hr8 ..).trans ((hkeep' r hr3 hr63).trans (hkeep r hr3 hr8 hr63))
      · intro a ha
        exact (hout a (by omega)).trans (hframe a ha)
      · intro k hk j hj
        change out.mem (dst+edges[k]*L+j) = _
        by_cases h : k = i
        · subst k
          exact (hcopy j hj).trans (hframe _ (by omega))
        · have hne : edges[k] ≠ e := fun hh => h (hnodup.getElem_inj_iff.mp hh)
          have hsep : dst+edges[k]*L+j < dst+e*L ∨ dst+e*L+L ≤ dst+edges[k]*L+j := by
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hle := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
              rw [Nat.succ_mul] at hle
              omega
            · have hle := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hgt)
              rw [Nat.succ_mul] at hle
              omega
          exact (hout _ hsep).trans (hdone k (by omega) j hj))
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal =>
      refine ⟨?_,h.2.2.1,h.2.1⟩
      intro e he j hj
      obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
      exact h.2.2.2 i (by simpa using hi) j hj
  · intro _ _
    simp [Expr.size_reg,Expr.size_const,Nat.mul_comm,Nat.add_assoc]

/-- Point both stretch descriptor entries to the private positive table. -/
@[expose] def loopOnlyStretchDescriptor : Stmt :=
  .seq (.store (.reg 58) (.reg 60))
    (.store (.bin .add (.reg 58) (.const 1)) (.reg 60))

/-- Publishing the private table exposes unit stretch and only modifies
the two descriptor words. -/
theorem loopOnlyStretchDescriptor_runs {w h L P : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (desc table : ℕ) (E : Finset ℕ)
    (h58 : st.regs 58 = desc) (h60 : st.regs 60 = table)
    (hfit : desc+2 < 2^w) (hsep : desc+2 ≤ table)
    (hvalues : ∀ e ∈ E, Valid st.mem (table+e*L) h L ∧ 0 < fixVal st.mem (table+e*L) h L P) :
    ∃ out, Runs w p ω loopOnlyStretchDescriptor st .normal out 9 ∧
      out.mem desc = table ∧ out.mem (desc+1) = table ∧
      StretchValuesAt out.mem desc h L P E (fun _ => 1) ∧
      (∀ a, a < desc ∨ desc+2 ≤ a → out.mem a = st.mem a) ∧ out.regs = st.regs := by
  let mid := {st with mem := Function.update st.mem desc table}
  let out := {mid with mem := Function.update mid.mem (desc+1) table}
  have hfirst : Runs w p ω (.store (.reg 58) (.reg 60)) st .normal mid 3 :=
    runs_store_iff.mpr ⟨desc,table,congrArg some h58,congrArg some h60,rfl,rfl,rfl⟩
  have hsecond : Runs w p ω (.store (.bin .add (.reg 58) (.const 1)) (.reg 60))
      mid .normal out 5 :=
    runs_store_iff.mpr ⟨desc+1,table,by
      simp [Expr.eval,BinOp.eval,mid,h58,show desc+1 < 2^w by omega,show 1 < 2^w by omega],
      congrArg some h60,rfl,rfl,rfl⟩
  have hframe a (ha : a < desc ∨ desc+2 ≤ a) : out.mem a = st.mem a := by
    simp [out,mid,Function.update_of_ne (show a ≠ desc by omega),
      Function.update_of_ne (show a ≠ desc+1 by omega)]
  have hnum : out.mem desc = table := by simp [out,mid]
  have hden : out.mem (desc+1) = table := by simp [out]
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,3,5,hfirst,hsecond,rfl⟩),hnum,hden,?_,hframe,rfl⟩
  apply loopOnlyStretch_at hnum hden
  · intro e he
    obtain ⟨hv,hp⟩ := hvalues e he
    have hcell (i : ℕ) (_ : i < L) : out.mem (table+e*L+i) = st.mem (table+e*L+i) :=
      hframe _ (Or.inr (by omega))
    refine ⟨fun i hi => (hcell i hi).trans_lt (hv i hi),?_⟩
    simpa only [fixVal,intVal_congr hcell] using hp

end MinCostFlow.LastLevelProgram
