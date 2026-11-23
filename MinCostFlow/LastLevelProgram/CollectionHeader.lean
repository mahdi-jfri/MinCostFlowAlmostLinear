module

public import MinCostFlow.MinRatio.Layouts
public import WordRAM.Logic
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Publishing last-level branch pointers

The collection for Definition 5.8 (pages 19–20) stores a count followed
by branch pointers. Each completed branch adds one pointer to the table.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM MinRatio DynSpanner.Program

/-- Write the collection count and reserve one consecutive cell per branch. -/
def initCollectionBody : Stmt :=
  .seq (.store (.reg 0) (.reg 1))
    (.ret (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 1)))

/-- The collection header write reserves the pointer table and leaves
the suffix beyond the reservation fresh. -/
theorem initCollection_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos base count : ℕ)
    (_hroom : base + 1 + count < 2^w) (hz : ZeroFrom mem base) :
    ∃ o out cost, Runs w p ω initCollectionBody (startState [base,count] mem pos)
      o out cost ∧ (o.value = base + 1 + count ∧ out.mem base = count ∧
        (∀ a < base, out.mem a = mem a) ∧ ZeroFrom out.mem (base + 1)) ∧ cost ≤ 10 := by
  apply runs_start_le
  unfold initCollectionBody
  wram_run
  · refine ⟨rfl, Function.update_self .., ?_, ?_⟩
    · intro a ha
      exact Function.update_of_ne (Nat.ne_of_lt ha) ..
    · intro a ha
      change Function.update mem base count a = 0
      rw [Function.update_of_ne (by omega)]
      exact hz a (by omega)
  · wram_cost

/-- Collection initialization is deterministic. -/
theorem initCollectionBody_noRand : initCollectionBody.NoRand := by
  simp [initCollectionBody, Stmt.NoRand]

/-- Publish the branch at index `j`. Arguments are the collection
base, branch index, and branch header pointer. -/
def publishBranchBody : Stmt :=
  .seq (.store (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 1)) (.reg 2))
    (.ret (.const 0))

/-- Publishing a branch is a deterministic constant-time store. -/
theorem publishBranch_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos collection j branch : ℕ)
    (_hw : 1 < 2^w) (_haddr : collection + 1 + j < 2^w) (_hptr : branch < 2^w) :
    ∃ o out cost, Runs w p ω publishBranchBody (startState [collection,j,branch] mem pos)
      o out cost ∧ (o.value = 0 ∧ out.mem = Function.update mem (collection + 1 + j) branch) ∧
      cost ≤ 10 := by
  apply runs_start_le
  unfold publishBranchBody
  wram_run
  · exact ⟨rfl,rfl⟩
  · wram_cost

/-- Publishing a branch adds no random instruction. -/
theorem publishBranchBody_noRand : publishBranchBody.NoRand := by
  simp [publishBranchBody, Stmt.NoRand]

/-- Contract for reserving the count and branch pointer table in fresh memory. -/
def initCollectionContract (w : ℕ) : Contract where
  pre args mem := ∃ base count, args = [base,count] ∧
    base+1+count < 2^w ∧ ZeroFrom mem base
  post args mem ret out := ∃ base count, args = [base,count] ∧
    ret = base+1+count ∧ out base = count ∧
    (∀ a < base, out a = mem a) ∧ ZeroFrom out (base+1)
  cost _ _ := 10

/-- The installed initializer reserves the complete pointer table. -/
theorem initCollection_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some initCollectionBody) :
    MeetsContract w p entry (initCollectionContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨base,count,rfl,hroom,hzero⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    initCollection_runs (p := p) (ω := ω) mem pos base count hroom hzero
  exact ⟨o,out,cost,hrun,⟨base,count,rfl,hpost⟩,hcost⟩

/-- Contract for writing a branch pointer into its collection slot. -/
def publishBranchContract (w : ℕ) : Contract where
  pre args _ := ∃ collection j branch, args = [collection,j,branch] ∧
    1 < 2^w ∧ collection+1+j < 2^w
  post args mem ret out := ∃ collection j branch, args = [collection,j,branch] ∧
    ret = 0 ∧ out = Function.update mem (collection+1+j) branch
  cost _ _ := 10

/-- The installed publisher updates exactly the chosen pointer cell. -/
theorem publishBranch_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some publishBranchBody) :
    MeetsContract w p entry (publishBranchContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨collection,j,branch,rfl,hw,haddr⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    publishBranch_runs (p := p) (ω := ω) mem pos collection j branch
      hw haddr (hwords _ (by simp))
  exact ⟨o,out,cost,hrun,⟨collection,j,branch,rfl,hpost⟩,hcost⟩

/-- Write the four pointers read by `LSFAt` in their layout order. -/
def writeBranchHeaderBody : Stmt :=
  .seq (.store (.reg 0) (.reg 1))
  (.seq (.store (.bin .add (.reg 0) (.const 1)) (.reg 2))
  (.seq (.store (.bin .add (.reg 0) (.const 2)) (.reg 3))
  (.seq (.store (.bin .add (.reg 0) (.const 3)) (.reg 4))
    (.ret (.const 0)))))

/-- The branch header stores its pointers and frames every other cell. -/
theorem writeBranchHeader_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos base tree forest roots stretch : ℕ)
    (_hroom : base + 4 < 2^w)
    (_ht : tree < 2^w) (_hf : forest < 2^w) (_hr : roots < 2^w) (_hs : stretch < 2^w) :
    ∃ o out cost, Runs w p ω writeBranchHeaderBody
      (startState [base,tree,forest,roots,stretch] mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem base = tree ∧ out.mem (base+1) = forest ∧
        out.mem (base+2) = roots ∧ out.mem (base+3) = stretch ∧
        ∀ a, a < base ∨ base + 4 ≤ a → out.mem a = mem a) ∧ cost ≤ 32 := by
  apply runs_start_le
  unfold writeBranchHeaderBody
  wram_run
  · dsimp only [startState]
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_self]
    · exact Function.update_self ..
    · intro a ha
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · wram_cost

/-- Header serialization is deterministic. -/
theorem writeBranchHeaderBody_noRand : writeBranchHeaderBody.NoRand := by
  simp [writeBranchHeaderBody, Stmt.NoRand]

/-- Write the shared stretch descriptor's numerator and denominator pointers. -/
def writeStretchDescriptorBody : Stmt :=
  .seq (.store (.reg 0) (.reg 1))
  (.seq (.store (.bin .add (.reg 0) (.const 1)) (.reg 2)) (.ret (.const 0)))

/-- The two descriptor words feed the exact quotient used by `LSFAt`.
The numerator and unit denominator tables lie beyond the descriptor. -/
theorem writeStretchDescriptor_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos base numerator denominator h L P : ℕ)
    (E : Finset ℕ) (values : ℕ → ℝ)
    (_hroom : base + 2 < 2^w) (_hn : numerator < 2^w) (_hd : denominator < 2^w)
    (hnum : base + 2 ≤ numerator) (hden : base + 2 ≤ denominator)
    (hN : EdgeValuesAt mem numerator h L P E values)
    (hD : EdgeValuesAt mem denominator h L P E (fun _ => 1)) :
    ∃ o out cost, Runs w p ω writeStretchDescriptorBody
      (startState [base,numerator,denominator] mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem base = numerator ∧ out.mem (base+1) = denominator ∧
        StretchValuesAt out.mem base h L P E values ∧
        ∀ a, a < base ∨ base + 2 ≤ a → out.mem a = mem a) ∧ cost ≤ 16 := by
  apply runs_start_le
  unfold writeStretchDescriptorBody
  wram_run
  · dsimp only [startState]
    let store := Function.update (Function.update mem base numerator) (base+1) denominator
    have hf (a : ℕ) (ha : a < base ∨ base+2 ≤ a) : store a = mem a := by
      unfold store
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hn : store base = numerator := by
      unfold store
      rw [Function.update_of_ne (by omega), Function.update_self]
    have hd : store (base+1) = denominator := Function.update_self ..
    refine ⟨rfl, hn, hd, ?_, hf⟩
    have hn' : EdgeValuesAt store numerator h L P E values :=
      hN.congr (fun e _ i _ => hf _ (Or.inr (by omega)))
    have hd' : EdgeValuesAt store denominator h L P E (fun _ => 1) :=
      hD.congr (fun e _ i _ => hf _ (Or.inr (by omega)))
    change StretchValuesAt store base h L P E values
    intro e he
    rw [hn, hd]
    obtain ⟨hNV, hNv⟩ := hn' e he
    obtain ⟨hDV, hDv⟩ := hd' e he
    refine ⟨hNV, hDV, ?_, ?_⟩
    · rw [hDv]
      exact zero_lt_one
    · rw [hNv, hDv, div_one]
  · wram_cost

/-- Contract for publishing the two tables as a stretch descriptor. -/
def stretchDescriptorContract (w h L P : ℕ) (E : Finset ℕ) (values : ℕ → ℝ) : Contract where
  pre args mem := ∃ base numerator denominator, args = [base,numerator,denominator] ∧
    base+2 < 2^w ∧ base+2 ≤ numerator ∧ base+2 ≤ denominator ∧
    EdgeValuesAt mem numerator h L P E values ∧
    EdgeValuesAt mem denominator h L P E (fun _ => 1)
  post args mem ret out := ∃ base numerator denominator, args = [base,numerator,denominator] ∧
    ret = 0 ∧ out base = numerator ∧ out (base+1) = denominator ∧
    StretchValuesAt out base h L P E values ∧
    ∀ a, a < base ∨ base+2 ≤ a → out a = mem a
  cost _ _ := 16

/-- The installed descriptor writer exposes the fixed-point tables
through the shared quotient layout. -/
theorem stretchDescriptor_meetsContract {w h L P entry : ℕ} {p : Program}
    {E : Finset ℕ} {values : ℕ → ℝ}
    (hp : p.procs[entry]? = some writeStretchDescriptorBody) :
    MeetsContract w p entry (stretchDescriptorContract w h L P E values) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨base,numerator,denominator,rfl,hr,hn,hd,hN,hD⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    writeStretchDescriptor_runs (p := p) (ω := ω) mem pos base numerator denominator
      h L P E values hr (hwords _ (by simp)) (hwords _ (by simp)) hn hd hN hD
  exact ⟨o,out,cost,hrun,⟨base,numerator,denominator,rfl,hpost⟩,hcost⟩

/-- A fresh header exposes the two graph payloads, root bits, and
stretch descriptor. All payload cells lie after the four header words. -/
theorem lsfAt_of_branchHeader {mem out : ℕ → ℕ}
    {base tree forest roots stretch vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF}
    (ht : DynGraphAt mem tree vCap eCap branch.T)
    (hf : DynGraphAt mem forest vCap eCap branch.F.F)
    (hr : RootsAt mem roots vCap branch.F.R)
    (hs : StretchValuesAt mem stretch h L P E branch.wstr)
    (hTree : base+4 ≤ tree) (hForest : base+4 ≤ forest)
    (hRoots : base+4 ≤ roots) (hStretch : base+4 ≤ stretch)
    (hNum : base+4 ≤ mem stretch) (hDen : base+4 ≤ mem (stretch+1))
    (hheader : out base = tree ∧ out (base+1) = forest ∧
      out (base+2) = roots ∧ out (base+3) = stretch)
    (hframe : ∀ a ≥ base+4, out a = mem a) :
    LSFAt out base vCap eCap h L P E branch := by
  obtain ⟨ht',hf',hr',hs'⟩ := hheader
  unfold LSFAt
  rw [ht',hf',hr',hs']
  refine ⟨ht.of_agree (fun a ha _ => hframe a (hTree.trans ha)),
    hf.of_agree (fun a ha _ => hframe a (hForest.trans ha)), ?_, ?_⟩
  · refine ⟨hr.1, fun v hv => ?_⟩
    have he := hframe (roots+v) (by omega)
    simpa only [he] using hr.2 v hv
  · intro e he
    have hn' := hframe stretch hStretch
    have hd' := hframe (stretch+1) (by omega)
    rw [hn',hd']
    have hnum (i : ℕ) (_ : i < L) : out (mem stretch+e*L+i) = mem (mem stretch+e*L+i) :=
      hframe _ (by omega)
    have hden (i : ℕ) (_ : i < L) :
        out (mem (stretch+1)+e*L+i) = mem (mem (stretch+1)+e*L+i) :=
      hframe _ (by omega)
    obtain ⟨hvN,hvD,hpos,hvalue⟩ := hs e he
    refine ⟨fun i hi => (hnum i hi).trans_lt (hvN i hi),
      fun i hi => (hden i hi).trans_lt (hvD i hi), ?_, ?_⟩
    · simpa only [Num.fixVal, Num.intVal_congr hden] using hpos
    · simpa only [Num.fixVal, Num.intVal_congr hnum, Num.intVal_congr hden] using hvalue

/-- Writing a header over reserved cells returns the shared branch
layout and frames all cells outside the header. -/
theorem writeBranchHeader_lsfAt {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {E : Finset ℕ} {branch : LSF}
    (mem : ℕ → ℕ) (pos base tree forest roots stretch vCap eCap h L P : ℕ)
    (hroom : base+4 < 2^w)
    (htw : tree < 2^w) (hfw : forest < 2^w) (hrw : roots < 2^w) (hsw : stretch < 2^w)
    (ht : DynGraphAt mem tree vCap eCap branch.T)
    (hf : DynGraphAt mem forest vCap eCap branch.F.F)
    (hr : RootsAt mem roots vCap branch.F.R)
    (hs : StretchValuesAt mem stretch h L P E branch.wstr)
    (hTree : base+4 ≤ tree) (hForest : base+4 ≤ forest)
    (hRoots : base+4 ≤ roots) (hStretch : base+4 ≤ stretch)
    (hNum : base+4 ≤ mem stretch) (hDen : base+4 ≤ mem (stretch+1)) :
    ∃ o out cost, Runs w p ω writeBranchHeaderBody
      (startState [base,tree,forest,roots,stretch] mem pos) o out cost ∧
      o.value = 0 ∧ LSFAt out.mem base vCap eCap h L P E branch ∧
      (∀ a, a < base ∨ base+4 ≤ a → out.mem a = mem a) ∧ cost ≤ 32 := by
  obtain ⟨o,out,cost,hrun,⟨hret,ht',hf',hr',hs',hframe⟩,hcost⟩ :=
    writeBranchHeader_runs (p := p) (ω := ω) mem pos base tree forest roots stretch
      hroom htw hfw hrw hsw
  exact ⟨o,out,cost,hrun,hret,lsfAt_of_branchHeader ht hf hr hs
    hTree hForest hRoots hStretch hNum hDen ⟨ht',hf',hr',hs'⟩
    (fun a ha => hframe a (Or.inr ha)),hframe,hcost⟩

/-- Contract for exposing a branch's payloads through its reserved header. -/
def branchHeaderContract (w vCap eCap h L P : ℕ) (E : Finset ℕ) (branch : LSF) :
    Contract where
  pre args mem := ∃ base tree forest roots stretch,
    args = [base,tree,forest,roots,stretch] ∧ base+4 < 2^w ∧
      DynGraphAt mem tree vCap eCap branch.T ∧
      DynGraphAt mem forest vCap eCap branch.F.F ∧
      RootsAt mem roots vCap branch.F.R ∧ StretchValuesAt mem stretch h L P E branch.wstr ∧
      base+4 ≤ tree ∧ base+4 ≤ forest ∧ base+4 ≤ roots ∧ base+4 ≤ stretch ∧
      base+4 ≤ mem stretch ∧ base+4 ≤ mem (stretch+1)
  post args mem ret out := ∃ base tree forest roots stretch,
    args = [base,tree,forest,roots,stretch] ∧ ret = 0 ∧
      LSFAt out base vCap eCap h L P E branch ∧
      out base = tree ∧ out (base+1) = forest ∧ out (base+2) = roots ∧
      out (base+3) = stretch ∧
      ∀ a, a < base ∨ base+4 ≤ a → out a = mem a
  cost _ _ := 32

/-- The installed header writer exposes the payloads of Definition 5.8
(pages 19–20) and preserves all other memory. -/
theorem branchHeader_meetsContract {w entry vCap eCap h L P : ℕ} {p : Program}
    {E : Finset ℕ} {branch : LSF}
    (hp : p.procs[entry]? = some writeBranchHeaderBody) :
    MeetsContract w p entry (branchHeaderContract w vCap eCap h L P E branch) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨base,tree,forest,roots,stretch,rfl,hroom,ht,hf,hr,hs,hT,hF,hR,hS,hN,hD⟩ := hpre
  obtain ⟨o,out,cost,hrun,⟨hret,hTree,hForest,hRoots,hStretch,hframe⟩,hcost⟩ :=
    writeBranchHeader_runs (p := p) (ω := ω) mem pos base tree forest roots stretch
      hroom (hwords _ (by simp)) (hwords _ (by simp))
      (hwords _ (by simp)) (hwords _ (by simp))
  have hlayout := lsfAt_of_branchHeader ht hf hr hs hT hF hR hS hN hD
    ⟨hTree,hForest,hRoots,hStretch⟩ (fun a ha => hframe a (Or.inr ha))
  exact ⟨o,out,cost,hrun,⟨base,tree,forest,roots,stretch,rfl,hret,hlayout,
    hTree,hForest,hRoots,hStretch,hframe⟩,hcost⟩

/-- A descriptor written after the graph and root payloads supplies the
stretch layout for header publication and preserves the other payloads. -/
theorem branchHeader_pre_of_descriptor {w vCap eCap h L P : ℕ}
    {E : Finset ℕ} {branch : LSF} {mem out : ℕ → ℕ}
    {ret base tree forest roots stretch numerator denominator : ℕ}
    (hdesc : (stretchDescriptorContract w h L P E branch.wstr).post
      [stretch,numerator,denominator] mem ret out)
    (hroom : base+4 < 2^w)
    (ht : DynGraphAt mem tree vCap eCap branch.T)
    (hf : DynGraphAt mem forest vCap eCap branch.F.F)
    (hr : RootsAt mem roots vCap branch.F.R)
    (hT : base+4 ≤ tree) (hF : base+4 ≤ forest) (hR : base+4 ≤ roots)
    (hS : base+4 ≤ stretch) (hN : base+4 ≤ numerator) (hD : base+4 ≤ denominator)
    (htEnd : tree+dynGraphSize vCap eCap ≤ stretch)
    (hfEnd : forest+dynGraphSize vCap eCap ≤ stretch)
    (hrEnd : roots+vCap ≤ stretch) :
    (branchHeaderContract w vCap eCap h L P E branch).pre
      [base,tree,forest,roots,stretch] out := by
  obtain ⟨s,n,d,he,_,hn,hd,hStretch,hframe⟩ := hdesc
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  refine ⟨base,tree,forest,roots,stretch,rfl,hroom,
    ht.of_agree (fun a _ ha => hframe a (Or.inl (ha.trans_le htEnd))),
    hf.of_agree (fun a _ ha => hframe a (Or.inl (ha.trans_le hfEnd))),
    ⟨hr.1,?_⟩,hStretch,hT,hF,hR,hS,hn.symm ▸ hN,hd.symm ▸ hD⟩
  intro v hv
  rw [hframe _ (Or.inl (by omega))]
  exact hr.2 v hv

/-- A branch whose header and payloads are above a memory boundary is
preserved by writes below that boundary. -/
theorem lsfAt_of_agree_above {mem out : ℕ → ℕ}
    {base floor vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF}
    (hlayout : LSFAt mem base vCap eCap h L P E branch)
    (hb : floor ≤ base)
    (ht : floor ≤ mem base) (hf : floor ≤ mem (base+1))
    (hr : floor ≤ mem (base+2)) (hs : floor ≤ mem (base+3))
    (hn : floor ≤ mem (mem (base+3))) (hd : floor ≤ mem (mem (base+3)+1))
    (hagree : ∀ a ≥ floor, out a = mem a) :
    LSFAt out base vCap eCap h L P E branch := by
  obtain ⟨hT,hF,hR,hS⟩ := hlayout
  unfold LSFAt
  rw [hagree base hb, hagree (base+1) (by omega), hagree (base+2) (by omega),
    hagree (base+3) (by omega)]
  refine ⟨hT.of_agree (fun a ha _ => hagree a (ht.trans ha)),
    hF.of_agree (fun a ha _ => hagree a (hf.trans ha)), ⟨hR.1, ?_⟩, ?_⟩
  · intro v hv
    rw [hagree _ (by omega)]
    exact hR.2 v hv
  · intro e he
    rw [hagree _ hs, hagree _ (by omega)]
    have hnum (i : ℕ) (_ : i < L) :
        out (mem (mem (base+3))+e*L+i) = mem (mem (mem (base+3))+e*L+i) :=
      hagree _ (by omega)
    have hden (i : ℕ) (_ : i < L) :
        out (mem (mem (base+3)+1)+e*L+i) = mem (mem (mem (base+3)+1)+e*L+i) :=
      hagree _ (by omega)
    obtain ⟨hvN,hvD,hpos,hvalue⟩ := hS e he
    refine ⟨fun i hi => (hnum i hi).trans_lt (hvN i hi),
      fun i hi => (hden i hi).trans_lt (hvD i hi), ?_, ?_⟩
    · simpa only [Num.fixVal, Num.intVal_congr hden] using hpos
    · simpa only [Num.fixVal, Num.intVal_congr hnum, Num.intVal_congr hden] using hvalue

/-- Agreement below the allocation end preserves an earlier branch.
Each payload range must end within the allocated prefix. -/
theorem lsfAt_of_agree_below {mem out : ℕ → ℕ}
    {base limit vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF}
    (hlayout : LSFAt mem base vCap eCap h L P E branch)
    (hb : base+4 ≤ limit)
    (ht : mem base + dynGraphSize vCap eCap ≤ limit)
    (hf : mem (base+1) + dynGraphSize vCap eCap ≤ limit)
    (hr : mem (base+2) + vCap ≤ limit)
    (hs : mem (base+3)+2 ≤ limit)
    (hn : ∀ e ∈ E, mem (mem (base+3))+e*L+L ≤ limit)
    (hd : ∀ e ∈ E, mem (mem (base+3)+1)+e*L+L ≤ limit)
    (hagree : ∀ a < limit, out a = mem a) :
    LSFAt out base vCap eCap h L P E branch := by
  obtain ⟨hT,hF,hR,hS⟩ := hlayout
  unfold LSFAt
  rw [hagree base (by omega), hagree (base+1) (by omega), hagree (base+2) (by omega),
    hagree (base+3) (by omega)]
  refine ⟨hT.of_agree (fun a _ ha => hagree a (ha.trans_le ht)),
    hF.of_agree (fun a _ ha => hagree a (ha.trans_le hf)), ⟨hR.1, ?_⟩, ?_⟩
  · intro v hv
    rw [hagree _ (by omega)]
    exact hR.2 v hv
  · intro e he
    rw [hagree (mem (base+3)) (by omega), hagree (mem (base+3)+1) (by omega)]
    have hun := hn e he
    have hud := hd e he
    have hnum (i : ℕ) (hi : i < L) :
        out (mem (mem (base+3))+e*L+i) = mem (mem (mem (base+3))+e*L+i) :=
      hagree _ (by omega)
    have hden (i : ℕ) (hi : i < L) :
        out (mem (mem (base+3)+1)+e*L+i) = mem (mem (mem (base+3)+1)+e*L+i) :=
      hagree _ (by omega)
    obtain ⟨hvN,hvD,hpos,hvalue⟩ := hS e he
    refine ⟨fun i hi => (hnum i hi).trans_lt (hvN i hi),
      fun i hi => (hden i hi).trans_lt (hvD i hi), ?_, ?_⟩
    · simpa only [Num.fixVal, Num.intVal_congr hden] using hpos
    · simpa only [Num.fixVal, Num.intVal_congr hnum, Num.intVal_congr hden] using hvalue

/-- A pointer write below a branch preserves its layout and makes the
branch readable through the collection slot. -/
theorem lsfAt_of_publishBranch {mem : ℕ → ℕ}
    {slot base vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF}
    (hlayout : LSFAt mem base vCap eCap h L P E branch)
    (hb : slot < base)
    (ht : base ≤ mem base) (hf : base ≤ mem (base+1))
    (hr : base ≤ mem (base+2)) (hs : base ≤ mem (base+3))
    (hn : base ≤ mem (mem (base+3))) (hd : base ≤ mem (mem (base+3)+1)) :
    let out := Function.update mem slot base
    LSFAt out (out slot) vCap eCap h L P E branch := by
  dsimp only
  rw [Function.update_self]
  exact lsfAt_of_agree_above hlayout le_rfl ht hf hr hs hn hd
    (fun a ha => Function.update_of_ne (by omega) ..)

/-- Write a branch header and install its pointer in the collection. -/
def finishBranchBody (header publish : ℕ) : Stmt :=
  .seq (.call 7 header [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4])
    (.seq (.call 7 publish [.reg 5,.reg 6,.reg 0]) (.ret (.const 0)))

/-- The final two calls expose a completed branch through its reserved slot. -/
theorem finishBranch_runs {w header publish : ℕ} {p : Program} {ω : ℕ → Bool}
    {vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF}
    (mem : ℕ → ℕ) (pos base tree forest roots stretch collection j : ℕ)
    (hh : MeetsContract w p header (branchHeaderContract w vCap eCap h L P E branch))
    (hp : MeetsContract w p publish (publishBranchContract w)) :
    let ha := [base,tree,forest,roots,stretch]
    let args := ha ++ [collection,j]
    let slot := collection+1+j
    (∀ a ∈ args, a < 2^w) →
    (branchHeaderContract w vCap eCap h L P E branch).pre ha mem →
    1 < 2^w → slot < base →
    ∃ o out cost, Runs w p ω (finishBranchBody header publish)
      (startState args mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem slot = base ∧ LSFAt out.mem base vCap eCap h L P E branch ∧
        out.mem base = tree ∧ out.mem (base+1) = forest ∧
        out.mem (base+2) = roots ∧ out.mem (base+3) = stretch ∧
        (∀ a, a ≠ slot → (a < base ∨ base+4 ≤ a) → out.mem a = mem a)) ∧ cost ≤ 56 := by
  intro ha args slot hwords hpre hw hslot
  have hb : base < 2^w := hwords _ (by simp [args,ha])
  have hpre' := hpre
  obtain ⟨b,t,f,r,s,he,_,_,_,_,_,ht,hf,hr,hs,hn,hd⟩ := hpre'
  simp only [ha,List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  apply runs_start_le
  unfold finishBranchBody
  refine runs_seq_call_le hh (vs := ha) rfl
    (fun a hmem => hwords a (List.mem_append_left _ hmem)) hpre ?_
  intro ret mid pos' hmid
  obtain ⟨b,t,f,r,s,he,_,hlsf,hT,hF,hR,hS,hframe⟩ := hmid
  simp only [ha,List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  refine runs_seq_call_le hp (vs := [collection,j,base]) rfl ?_
    ⟨collection,j,base,rfl,hw,hslot.trans hb⟩ ?_
  · intro a ha'
    apply hwords
    rcases (show a = collection ∨ a = j ∨ a = base by simpa using ha') with rfl | rfl | rfl <;> simp [args,ha]
  · intro ret' out pos'' hout
    obtain ⟨c,k,b,he,_,rfl⟩ := hout
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl⟩ := he
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,Function.update_self ..,?_,?_,?_,?_,?_,?_⟩ ?_
    · apply lsfAt_of_agree_above hlsf (floor := base) le_rfl
      · rw [hT]; omega
      · rw [hF]; omega
      · rw [hR]; omega
      · rw [hS]; omega
      · rw [hS,hframe stretch (Or.inr hs)]; exact (Nat.le_add_right base 4).trans hn
      · rw [hS,hframe (stretch+1) (Or.inr (by omega))]; exact (Nat.le_add_right base 4).trans hd
      · intro a ha'
        exact Function.update_of_ne (by omega) ..
    · exact (Function.update_of_ne (by omega) ..).trans hT
    · exact (Function.update_of_ne (by omega) ..).trans hF
    · exact (Function.update_of_ne (by omega) ..).trans hR
    · exact (Function.update_of_ne (by omega) ..).trans hS
    · intro a ha' ha''
      exact (Function.update_of_ne ha' ..).trans (hframe a ha'')
    · change 0 + 5 + 32 + 2 + 3 + 10 + 2 + 2 ≤ 56
      decide

/-- Contract for writing a completed branch header and publishing its pointer. -/
def finishBranchContract (w vCap eCap h L P : ℕ) (E : Finset ℕ) (branch : LSF) :
    Contract where
  pre args mem := ∃ base tree forest roots stretch collection j,
    args = [base,tree,forest,roots,stretch,collection,j] ∧
    (branchHeaderContract w vCap eCap h L P E branch).pre
      [base,tree,forest,roots,stretch] mem ∧
    1 < 2^w ∧ collection+1+j < base
  post args mem ret out := ∃ base tree forest roots stretch collection j,
    args[0]? = some base ∧ args[1]? = some tree ∧ args[2]? = some forest ∧
    args[3]? = some roots ∧ args[4]? = some stretch ∧ args[5]? = some collection ∧ args[6]? = some j ∧
    ret = 0 ∧ out (collection+1+j) = base ∧ LSFAt out base vCap eCap h L P E branch ∧
    out base = tree ∧ out (base+1) = forest ∧ out (base+2) = roots ∧
    out (base+3) = stretch ∧
    ∀ a, a ≠ collection+1+j → (a < base ∨ base+4 ≤ a) → out a = mem a
  cost _ _ := 56

/-- The two linked publication calls expose a branch through its reserved slot. -/
theorem finishBranch_meetsContract {w entry header publish vCap eCap h L P : ℕ}
    {p : Program} {E : Finset ℕ} {branch : LSF}
    (he : p.procs[entry]? = some (finishBranchBody header publish))
    (hh : MeetsContract w p header (branchHeaderContract w vCap eCap h L P E branch))
    (hp : MeetsContract w p publish (publishBranchContract w)) :
    MeetsContract w p entry (finishBranchContract w vCap eCap h L P E branch) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,tree,forest,roots,stretch,collection,j,rfl,hheader,hw,hslot⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ := finishBranch_runs (p := p) (ω := ω)
    mem pos base tree forest roots stretch collection j hh hp hwords hheader hw hslot
  exact ⟨o,out,cost,hrun,⟨base,tree,forest,roots,stretch,collection,j,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hpost⟩,hcost⟩

/-- Serialize the descriptor and publish the branch with its collection pointer. -/
def serializeBranchBody (descriptor finish : ℕ) : Stmt :=
  .seq (.call 9 descriptor [.reg 4,.reg 7,.reg 8])
    (.seq (.call 9 finish ((List.range 7).map Expr.reg)) (.ret (.const 0)))

/-- The linked serializer leaves memory outside the header, descriptor,
and collection slot unchanged. -/
theorem serializeBranch_runs {w descriptor finish : ℕ} {p : Program} {ω : ℕ → Bool}
    {vCap eCap h L P : ℕ} {E : Finset ℕ} {branch : LSF}
    (mem : ℕ → ℕ) (pos base tree forest roots stretch collection j numerator denominator : ℕ)
    (hd : MeetsContract w p descriptor (stretchDescriptorContract w h L P E branch.wstr))
    (hf : MeetsContract w p finish (finishBranchContract w vCap eCap h L P E branch)) :
    let da := [stretch,numerator,denominator]
    let fa := [base,tree,forest,roots,stretch,collection,j]
    let args := fa ++ [numerator,denominator]
    (∀ a ∈ args, a < 2^w) →
    (stretchDescriptorContract w h L P E branch.wstr).pre da mem →
    (∀ ret mid, (stretchDescriptorContract w h L P E branch.wstr).post da mem ret mid →
      (finishBranchContract w vCap eCap h L P E branch).pre fa mid) →
    ∃ o out cost, Runs w p ω (serializeBranchBody descriptor finish)
      (startState args mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem (collection+1+j) = base ∧
        LSFAt out.mem base vCap eCap h L P E branch ∧
        out.mem base = tree ∧ out.mem (base+1) = forest ∧
        out.mem (base+2) = roots ∧ out.mem (base+3) = stretch ∧
        out.mem stretch = numerator ∧ out.mem (stretch+1) = denominator ∧
        ∀ a, a ≠ collection+1+j → (a < base ∨ base+4 ≤ a) →
          (a < stretch ∨ stretch+2 ≤ a) → out.mem a = mem a) ∧ cost ≤ 88 := by
  intro da fa args hwords hpre hnext
  apply runs_start_le
  unfold serializeBranchBody
  refine runs_seq_call_le hd (vs := da) rfl ?_ hpre ?_
  · intro a ha
    rcases (show a = stretch ∨ a = numerator ∨ a = denominator by simpa [da] using ha)
      with rfl | rfl | rfl <;> exact hwords _ (by simp [args,fa])
  · intro ret mid pos' hmid
    have hn := hnext ret mid hmid
    obtain ⟨s,n,d,he,_,hNum,hDen,_,hframe⟩ := hmid
    simp only [da,List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl⟩ := he
    have hbounds : collection+1+j < base ∧ base+4 ≤ stretch := by
      obtain ⟨b,t,f,r,s,c,k,he',hheader,_,hslot⟩ := hn
      simp only [fa,List.cons.injEq,and_true] at he'
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := he'
      obtain ⟨b,t,f,r,s,he',_,_,_,_,_,_,_,_,hStretch,_,_⟩ := hheader
      simp only [List.cons.injEq,and_true] at he'
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he'
      exact ⟨hslot,hStretch⟩
    refine runs_seq_call_le hf (vs := fa) rfl
      (fun a ha => hwords a (List.mem_append_left _ ha)) hn ?_
    intro ret' out pos'' hout
    obtain ⟨b,t,f,r,s,c,k,hb,ht,hf',hr,hs,hc,hk,_,hslot,hlayout,hT,hF,hR,hS,houtFrame⟩ := hout
    simp only [fa,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.some.injEq] at hb ht hf' hr hs hc hk
    simp only [← hb, ← ht, ← hf', ← hr, ← hs, ← hc, ← hk] at hslot hlayout hT hF hR hS houtFrame
    have hzero : 0 < 2 ^ w := Nat.two_pow_pos _
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,hslot,hlayout,hT,hF,hR,hS,?_,?_,?_⟩ ?_
    · exact (houtFrame stretch (by have := hbounds.1; have := hbounds.2; omega)
        (Or.inr hbounds.2)).trans hNum
    · exact (houtFrame (stretch+1) (by have := hbounds.1; have := hbounds.2; omega)
        (Or.inr (by have := hbounds.2; omega))).trans hDen
    · intro a hne hh hs
      exact (houtFrame a hne hh).trans (hframe a hs)
    · change 0 + 3 + 16 + 2 + 7 + 56 + 2 + 2 ≤ 88
      decide

/-- Contract for publishing the stretch descriptor, branch header and
collection pointer after the payloads have been built. -/
def serializeBranchContract (w vCap eCap h L P : ℕ) (E : Finset ℕ) (branch : LSF) :
    Contract where
  pre args mem := ∃ base tree forest roots stretch collection j numerator denominator,
    let da := [stretch,numerator,denominator]
    let fa := [base,tree,forest,roots,stretch,collection,j]
    args = fa ++ [numerator,denominator] ∧
      (stretchDescriptorContract w h L P E branch.wstr).pre da mem ∧
      ∀ ret mid, (stretchDescriptorContract w h L P E branch.wstr).post da mem ret mid →
        (finishBranchContract w vCap eCap h L P E branch).pre fa mid
  post args mem ret out := ∃ base tree forest roots stretch collection j numerator denominator,
    args = [base,tree,forest,roots,stretch,collection,j,numerator,denominator] ∧
      ret = 0 ∧ out (collection+1+j) = base ∧ LSFAt out base vCap eCap h L P E branch ∧
      out base = tree ∧ out (base+1) = forest ∧
      out (base+2) = roots ∧ out (base+3) = stretch ∧
      out stretch = numerator ∧ out (stretch+1) = denominator ∧
      ∀ a, a ≠ collection+1+j → (a < base ∨ base+4 ≤ a) →
        (a < stretch ∨ stretch+2 ≤ a) → out a = mem a
  cost _ _ := 88

/-- The installed serializer exposes the completed branch at its collection slot. -/
theorem serializeBranch_meetsContract {w entry descriptor finish vCap eCap h L P : ℕ}
    {p : Program} {E : Finset ℕ} {branch : LSF}
    (he : p.procs[entry]? = some (serializeBranchBody descriptor finish))
    (hd : MeetsContract w p descriptor (stretchDescriptorContract w h L P E branch.wstr))
    (hf : MeetsContract w p finish (finishBranchContract w vCap eCap h L P E branch)) :
    MeetsContract w p entry (serializeBranchContract w vCap eCap h L P E branch) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,tree,forest,roots,stretch,collection,j,numerator,denominator,rfl,hstart,hnext⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ := serializeBranch_runs (p := p) (ω := ω)
    mem pos base tree forest roots stretch collection j numerator denominator
    hd hf hwords hstart hnext
  exact ⟨o,out,cost,hrun,⟨base,tree,forest,roots,stretch,collection,j,numerator,denominator,rfl,hpost⟩,hcost⟩

/-- Once the table contains the published pointers, its count and the
branch layouts give the shared collection layout. -/
theorem lsfCollectionAt_of_headers {mem : ℕ → ℕ} {a vCap eCap h L P : ℕ}
    {E : Finset ℕ} {count : ℕ} {forests : ℕ → LSF} (ptr : ℕ → ℕ)
    (hcount : mem a = count)
    (hptr : ∀ j < count, mem (a + 1 + j) = ptr j)
    (hforest : ∀ j < count, LSFAt mem (ptr j) vCap eCap h L P E (forests j)) :
    LSFCollectionAt mem a vCap eCap h L P E (count, forests) := by
  refine ⟨hcount, fun j hj => ?_⟩
  rw [hptr j hj]
  exact hforest j hj

/-- The parts of a serialized branch lie above the collection table and
below the current allocation end. -/
def BranchWithin (mem : ℕ → ℕ) (base floor limit vCap eCap L : ℕ)
    (E : Finset ℕ) : Prop :=
  floor ≤ base ∧ base+4 ≤ limit ∧
  floor ≤ mem base ∧ mem base + dynGraphSize vCap eCap ≤ limit ∧
  floor ≤ mem (base+1) ∧ mem (base+1) + dynGraphSize vCap eCap ≤ limit ∧
  floor ≤ mem (base+2) ∧ mem (base+2) + vCap ≤ limit ∧
  floor ≤ mem (base+3) ∧ mem (base+3)+2 ≤ limit ∧
  floor ≤ mem (mem (base+3)) ∧ floor ≤ mem (mem (base+3)+1) ∧
  (∀ e ∈ E, mem (mem (base+3))+e*L+L ≤ limit) ∧
  (∀ e ∈ E, mem (mem (base+3)+1)+e*L+L ≤ limit)

/-- A published prefix records the count and the layout and extent of each
branch inserted so far. -/
def CollectionPrefix (mem : ℕ → ℕ) (collection count filled limit vCap eCap h L P : ℕ)
    (E : Finset ℕ) (branches : ℕ → LSF) : Prop :=
  filled ≤ count ∧ mem collection = count ∧
  ∀ j < filled, let base := mem (collection+1+j)
    BranchWithin mem base (collection+1+count) limit vCap eCap L E ∧
      LSFAt mem base vCap eCap h L P E (branches j)

/-- Appending a fresh branch may update its pointer slot and new memory.
Earlier branches and the original count survive these writes. -/
theorem collectionPrefix_succ {mem out : ℕ → ℕ}
    {collection count filled limit limit' vCap eCap h L P : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (hp : CollectionPrefix mem collection count filled limit vCap eCap h L P E branches)
    (hf : filled < count) (hle : limit ≤ limit') (hroom : collection+1+count ≤ limit)
    (hframe : ∀ a < limit, a ≠ collection+1+filled → out a = mem a)
    (hnew : let base := out (collection+1+filled)
      BranchWithin out base (collection+1+count) limit' vCap eCap L E ∧
        LSFAt out base vCap eCap h L P E (branches filled)) :
    CollectionPrefix out collection count (filled+1) limit' vCap eCap h L P E branches := by
  refine ⟨hf,hp.2.1 ▸ hframe collection (by omega) (by omega),?_⟩
  intro j hj
  by_cases he : j = filled
  · subst j
    exact hnew
  have hj' : j < filled := by omega
  dsimp only
  rw [hframe (collection+1+j) (by omega) (by omega)]
  obtain ⟨hspan,hbranch⟩ := hp.2.2 j hj'
  generalize hbase : mem (collection+1+j) = base at hspan hbranch ⊢
  obtain ⟨hb,hB,ht,hT,hf',hF,hr,hR,hs,hS,hn,hd,hN,hD⟩ := hspan
  have hagree (a : ℕ) (ha : collection+1+count ≤ a) (ha' : a < limit) :
      out a = mem a := hframe a ha' (by omega)
  have hst := hagree (base+3) (by omega) (by omega)
  refine ⟨?_,?_⟩
  · unfold BranchWithin
    rw [hagree base hb (by omega), hagree (base+1) (by omega) (by omega),
      hagree (base+2) (by omega) (by omega), hst,
      hagree (mem (base+3)) hs (by omega),
      hagree (mem (base+3)+1) (by omega) (by omega)]
    exact ⟨hb,hB.trans hle,ht,hT.trans hle,hf',hF.trans hle,hr,hR.trans hle,
      hs,hS.trans hle,hn,hd,fun e he => (hN e he).trans hle,fun e he => (hD e he).trans hle⟩
  · let mid := Function.update out (collection+1+filled) (mem (collection+1+filled))
    have hmid (a : ℕ) (ha : a < limit) : mid a = mem a := by
      by_cases he' : a = collection+1+filled
      · subst a
        exact Function.update_self ..
      · exact (Function.update_of_ne he' ..).trans (hframe a ha he')
    have hm := lsfAt_of_agree_below hbranch hB hT hF hR hS hN hD hmid
    have hbnd (a : ℕ) (ha : collection+1+count ≤ a) : out a = mid a :=
      (Function.update_of_ne (by omega) ..).symm
    have hPtr := hmid (base+3) (by omega)
    apply lsfAt_of_agree_above hm hb
    · rw [hmid base (by omega)]; exact ht
    · rw [hmid (base+1) (by omega)]; exact hf'
    · rw [hmid (base+2) (by omega)]; exact hr
    · rwa [hPtr]
    · rw [hPtr,hmid (mem (base+3)) (by omega)]; exact hn
    · rw [hPtr,hmid (mem (base+3)+1) (by omega)]; exact hd
    · exact hbnd

/-- A full published prefix is the shared collection readout. -/
theorem CollectionPrefix.complete {mem : ℕ → ℕ}
    {collection count limit vCap eCap h L P : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (hp : CollectionPrefix mem collection count count limit vCap eCap h L P E branches) :
    LSFCollectionAt mem collection vCap eCap h L P E (count,branches) :=
  ⟨hp.2.1, fun j hj => (hp.2.2 j hj).2⟩

/-- The collection and each branch depend only on the allocated interval. -/
theorem CollectionPrefix.of_agree {mem out : ℕ → ℕ}
    {base count filled limit vCap eCap h L P : ℕ} {E : Finset ℕ}
    {branches : ℕ → LSF}
    (hp : CollectionPrefix mem base count filled limit vCap eCap h L P E branches)
    (htable : base+1+count ≤ limit)
    (hmem : ∀ a, base ≤ a → a < limit → out a = mem a) :
    CollectionPrefix out base count filled limit vCap eCap h L P E branches := by
  refine ⟨hp.1, (hmem base le_rfl (by omega)).trans hp.2.1, ?_⟩
  intro j hj
  have hj' := hp.1
  dsimp only
  rw [hmem (base+1+j) (by omega) (by omega)]
  obtain ⟨hspan,hbranch⟩ := hp.2.2 j hj
  generalize mem (base+1+j) = b at hspan hbranch ⊢
  obtain ⟨hb,hB,ht,hT,hf,hF,hr,hR,hs,hS,hn,hd,hN,hD⟩ := hspan
  let mid a := if a < limit then mem a else out a
  have hbelow a (ha : a < limit) : mid a = mem a := ite_eq_left ha
  have hagree a (ha : base+1+count ≤ a) : out a = mid a := by
    by_cases hlt : a < limit
    · exact (hmem a (by omega) hlt).trans (hbelow a hlt).symm
    · exact (ite_eq_right hlt).symm
  have htree := hmem b (by omega) (by omega)
  have hforest := hmem (b+1) (by omega) (by omega)
  have hroot := hmem (b+2) (by omega) (by omega)
  have hdesc := hmem (b+3) (by omega) (by omega)
  have hnum := hmem (mem (b+3)) (by omega) (by omega)
  have hden := hmem (mem (b+3)+1) (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · unfold BranchWithin
    rw [htree,hforest,hroot,hdesc,hnum,hden]
    exact ⟨hb,hB,ht,hT,hf,hF,hr,hR,hs,hS,hn,hd,hN,hD⟩
  · apply lsfAt_of_agree_above (lsfAt_of_agree_below hbranch hB hT hF hR hS hN hD hbelow) hb
    · rwa [hbelow b (by omega)]
    · rwa [hbelow (b+1) (by omega)]
    · rwa [hbelow (b+2) (by omega)]
    · rwa [hbelow (b+3) (by omega)]
    · rwa [hbelow (b+3) (by omega),hbelow (mem (b+3)) (by omega)]
    · rwa [hbelow (b+3) (by omega),hbelow (mem (b+3)+1) (by omega)]
    · exact hagree

/-- A branch stays readable after writing the next-round descriptor just
beyond its allocation. The same payloads lie within the enlarged allocation. -/
theorem branchWithin_cursorWrite {mem : ℕ → ℕ} {base floor stop vCap eCap h L P value : ℕ}
    {E : Finset ℕ} {branch : LSF}
    (hspan : BranchWithin mem base floor stop vCap eCap L E)
    (hbranch : LSFAt mem base vCap eCap h L P E branch) :
    let out := Function.update mem stop value
    BranchWithin out base floor (stop+1) vCap eCap L E ∧
      LSFAt out base vCap eCap h L P E branch := by
  intro out
  obtain ⟨hb,hB,ht,hT,hf,hF,hr,hR,hs,hS,hn,hd,hN,hD⟩ := hspan
  have hagree a (ha : a < stop) : out a = mem a := Function.update_of_ne (ne_of_lt ha) ..
  refine ⟨?_,lsfAt_of_agree_below hbranch hB hT hF hR hS hN hD hagree⟩
  unfold BranchWithin
  rw [hagree base (by omega),hagree (base+1) (by omega),hagree (base+2) (by omega),
    hagree (base+3) (by omega),hagree (mem (base+3)) (by omega),
    hagree (mem (base+3)+1) (by omega)]
  exact ⟨hb,by omega,ht,by omega,hf,by omega,hr,by omega,hs,by omega,hn,hd,
    fun e he => (hN e he).trans (Nat.le_succ _),fun e he => (hD e he).trans (Nat.le_succ _)⟩

/-- The row that points to the new branch stays readable after cursor
publication, including all payloads needed by the collection loop. -/
theorem publishedBranch_cursorWrite {mem : ℕ → ℕ} {slot floor stop vCap eCap h L P value : ℕ}
    {E : Finset ℕ} {branch : LSF}
    (hslot : slot < stop)
    (hspan : BranchWithin mem (mem slot) floor stop vCap eCap L E)
    (hbranch : LSFAt mem (mem slot) vCap eCap h L P E branch) :
    let out := Function.update mem stop value
    let base := out slot
    BranchWithin out base floor (stop+1) vCap eCap L E ∧
      LSFAt out base vCap eCap h L P E branch := by
  dsimp only
  rw [Function.update_of_ne (ne_of_lt hslot)]
  exact branchWithin_cursorWrite hspan hbranch

/-- Copying the count and branch pointers to an earlier table publishes
the same collection at the caller's handle. The branch payloads stay put. -/
theorem CollectionPrefix.publishEarlier {mem out : ℕ → ℕ}
    {src dst count limit vCap eCap h L P : ℕ} {E : Finset ℕ} {branches : ℕ → LSF}
    (hp : CollectionPrefix mem src count count limit vCap eCap h L P E branches)
    (hsep : dst+1+count ≤ src)
    (htable : ∀ i < count+1, out (dst+i) = mem (src+i))
    (hframe : ∀ a ≥ src, out a = mem a) :
    CollectionPrefix out dst count count limit vCap eCap h L P E branches := by
  refine ⟨le_rfl, ?_, ?_⟩
  · simpa only [Nat.add_zero,hp.2.1] using htable 0 (by omega)
  · intro j hj
    dsimp only
    rw [show out (dst+1+j) = mem (src+1+j) by
      simpa only [Nat.add_assoc] using htable (1+j) (by omega)]
    obtain ⟨hspan,hbranch⟩ := hp.2.2 j hj
    generalize mem (src+1+j) = b at hspan hbranch ⊢
    obtain ⟨hb,hB,ht,hT,hf,hF,hr,hR,hs,hS,hn,hd,hN,hD⟩ := hspan
    have hlow : dst+1+count ≤ src+1+count := by omega
    refine ⟨?_,lsfAt_of_agree_above hbranch hb ht hf hr hs hn hd
      (fun a ha => hframe a (by omega))⟩
    unfold BranchWithin
    rw [hframe b (by omega), hframe (b+1) (by omega), hframe (b+2) (by omega),
      hframe (b+3) (by omega), hframe (mem (b+3)) (by omega),
      hframe (mem (b+3)+1) (by omega)]
    exact ⟨hlow.trans hb,hB,hlow.trans ht,hT,hlow.trans hf,hF,hlow.trans hr,hR,
      hlow.trans hs,hS,hlow.trans hn,hlow.trans hd,hN,hD⟩

/-- Copy the staged header to the handle and return the next free address. -/
def publishRuntimeCollection (copy : ℕ) : Stmt :=
  .seq (.call 154 copy [.reg 3,.reg 151,.bin .add (.reg 1) (.const 1)])
    (.ret (.reg 0))

/-- Copying a completed header preserves caller memory and zero memory above
the returned allocation end. -/
theorem publishRuntimeCollection_runs {w copy src dst count limit vCap eCap h L P : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ} {branches : ℕ → LSF}
    (st : State) (hc : MeetsContract w p copy (copyWordsContract w))
    (hp : CollectionPrefix st.mem src count count limit vCap eCap h L P E branches)
    (hsrc : st.regs 3 = src) (hdst : st.regs 151 = dst)
    (hcount : st.regs 1 = count) (hlimit : st.regs 0 = limit)
    (hw : 1 < 2^w) (hsep : dst+1+count ≤ src) (hspan : src+1+count ≤ limit)
    (hfit : limit < 2^w) (hz : ZeroFrom st.mem limit) :
    ∃ out cost, Runs w p ω (publishRuntimeCollection copy) st (.returned limit) out cost ∧
      CollectionPrefix out.mem dst count count limit vCap eCap h L P E branches ∧
      (∀ a < dst, out.mem a = st.mem a) ∧ ZeroFrom out.mem limit ∧
      cost ≤ 17*(count+1)+19 := by
  let es : List Expr := [.reg 3,.reg 151,.bin .add (.reg 1) (.const 1)]
  have hcountFit : count+1 < 2^w := by omega
  have he : evalArgs w st es = some [src,dst,count+1] := by
    simp [es,evalArgs,Expr.eval,BinOp.eval,hsrc,hdst,hcount,hw,hcountFit]
  have hwords : ∀ a ∈ [src,dst,count+1], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  obtain ⟨out,c,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 154) hc he hwords
      ⟨src,dst,count+1,rfl,hw,by omega,by omega,Or.inl (by omega)⟩ ω
  obtain ⟨s,d,n,heq,_,hcopy,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hr' : Runs w p ω (.ret (.reg 0)) out (.returned limit) out 2 :=
    runs_ret_iff.mpr ⟨limit,congrArg some ((hregs 0 (by decide)).trans hlimit),rfl,rfl,rfl⟩
  refine ⟨out,c+3,runs_seq_iff.mpr (Or.inr ⟨out,c,2,hr,hr',by omega⟩),
    hp.publishEarlier hsep hcopy (fun a ha => hframe a (Or.inr (by omega))),
    fun a ha => hframe a (Or.inl ha),fun a ha => (hframe a (Or.inr (by omega))).trans (hz a ha),?_⟩
  change c ≤ 5+(17*(count+1)+10)+1 at hcost
  omega

/-- The final loop state supplies the header, the allocation end, and
the frame needed by runtime publication. -/
theorem publishRuntimeCollection_triple {w copy src dst count vCap eCap h L P bound : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF} (mem : ℕ → ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hw : 1 < 2^w) (hsep : dst+1+count ≤ src) :
    Triple w p
      (fun st =>
        st.regs 3 = src ∧ st.regs 151 = dst ∧ st.regs 1 = count ∧
        src+1+count ≤ st.regs 0 ∧ st.regs 0 ≤ bound ∧ st.regs 0 < 2^w ∧
        CollectionPrefix st.mem src count count (st.regs 0) vCap eCap h L P E branches ∧
        ZeroFrom st.mem (st.regs 0) ∧ (∀ a < dst, st.mem a = mem a))
      (publishRuntimeCollection copy)
      (fun o out => ∃ limit, o = .returned limit ∧ dst+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem dst count count limit vCap eCap h L P E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < dst, out.mem a = mem a))
      (fun _ => 17*(count+1)+19) := by
  intro st ω ⟨hs,hd,hn,hspan,hbound,hfit,hprefix,hzero,hframe⟩
  obtain ⟨out,cost,hr,hpublish,hkeep,hfresh,hcost⟩ :=
    publishRuntimeCollection_runs (ω := ω) st hc hprefix hs hd hn rfl hw hsep hspan hfit hzero
  exact ⟨_,out,cost,hr,⟨_,rfl,by omega,
    hbound,hpublish,hfresh,fun a ha => (hkeep a ha).trans (hframe a ha)⟩,hcost⟩

end MinCostFlow.LastLevelProgram
