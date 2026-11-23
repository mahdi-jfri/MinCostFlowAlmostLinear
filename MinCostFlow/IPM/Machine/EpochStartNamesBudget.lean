module

public import MinCostFlow.IPM.Machine.EpochStartProgram
public import MinCostFlow.IPM.Machine.EpochStartOutput
public import MinCostFlow.IPM.Machine.EpochBudgetInit
public import MinCostFlow.IPM.Machine.VertexNames
import MinCostFlow.IPM.Machine.VectorFrame
import WordRAM.Tactic

/-!
# Starting an epoch with names and its guarded report budget

Compute the numerical coefficient arrays, initialize the min-ratio
structure, write the full edge-name list and append its initial
five-edge report budget. The fresh
metadata preserves the actual initialized state and credit. The caller
uses the same fifteen-word numerical packet as epoch initialization.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The coefficient/Init packet is forwarded unchanged, then the actual
initialized endpoint receives the full name list before fresh budget metadata. -/
def epochStartNamesBudgetBody (start names budget : ℕ) : Stmt :=
  .call 15 start [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13,.reg 14] ;;
  .call 16 names [.reg 0,.reg 15] ;;
  .call 17 budget [.reg 0,.reg 16] ;;
  .ret (.reg 17)

/-- The caller's instructions are deterministic. -/
theorem epochStartNamesBudget_noRand (start names budget : ℕ) : (epochStartNamesBudgetBody start names budget).NoRand := by
  simp [epochStartNamesBudgetBody,Stmt.NoRand]

/-- Actual coefficient initialization and the fresh budget writer retain
the same concrete initialized state and credit, with all operation costs. -/
theorem epochStartNamesBudget_runs_with_potential {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry start names budget : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hstart : p.procs[start]?=some (epochStartBody refresh initEntry))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (cp rp lo fp up ap one E graph heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
      Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph],z<2^w)
    (hpre : (epochStartContract F A I κ α rate allocation R q K).pre
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : heap+epochStartSpace F I E graph heap allocation+I.m+3<2^w) :
    ∃ o st cost s x initEnd initMem namesMem,
      Runs w p ω (epochStartNamesBudgetBody start names budget)
        (startState [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
          Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
          Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem pos) o st cost ∧
      (epochStartContract F A I κ α rate allocation R q K).post
        [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
          Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
          Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem initEnd initMem ∧
      (vertexNamesContract w).post [I.m,initEnd] initMem (initEnd+I.m) namesMem ∧
      (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] namesMem o.value st.mem ∧
      ListAt st.mem initEnd (List.range I.m) ∧
      let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
      let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
      let handle := heap+(la+ga)
      (∀ z<heap,st.mem z=mem z) ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
      R.rep handle s x st.mem ∧
      s=A.init (namedInstance I)
        (readVector st.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector st.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∃ coefficients,
        (coefficientRefreshContract w F.fmt.limbBits q K).post
          [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap] mem handle coefficients ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).initPost
          [graph,heap+la,heap,F.limbs,F.fmt.precision,handle] coefficients s st.mem) ∧
      (∀ z,R.foot handle x z → handle≤z ∧ z < initEnd) ∧
      cost+R.phi handle x st.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision E+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision E+rate I.m*(I.m+1)+30*I.m+700 := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  let handle := heap+(la+ga)
  let args := [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap,graph]
  obtain ⟨oC,stC,cC,s,x,hrC,hCpost,hrep,hstateC,hmodel,hfoot,hCcost⟩ :=
    epochStart_runs_with_potential F A I κ α rate allocation R himpl hrefresh hinit
      cp rp lo fp up ap one E graph heap mem pos ω hwords hpre
  obtain ⟨_,_,_,_,hlower,hupper,hzero⟩ := (epochStart_output F A I κ α rate allocation R hCpost).2.2
  have hend : oC.value≤heap+epochStartSpace F I E graph heap allocation := by
    simpa only [epochStartSpace,Nat.add_assoc] using hupper
  have hrecordSpace : oC.value+I.m+3<2^w := by omega
  have hvC : oC.value<2^w := by omega
  have hm : I.m<2^w := hwords _ (by simp)
  have hNpre : (vertexNamesContract w).pre [I.m,oC.value] stC.mem :=
    ⟨⟨I.m,oC.value,rfl⟩,hzero,by change oC.value+I.m<2^w; omega⟩
  obtain ⟨namesBody,hNamesBody,oN,stN,cN,hrN,hNpost,hNcost⟩ := hnames [I.m,oC.value] stC.mem stC.pos ω
    (by wram_words) hNpre
  have hvN : oN.value=oC.value+I.m := hNpost.2
  have hvNword : oN.value<2^w := by omega
  have hNframe := hNpost.1.2.2.1
  change ∀ z<oC.value,stN.mem z=stC.mem z at hNframe
  have hNpres := himpl.1 handle s x stC.mem stN.mem (fun z hz => (hNframe z (hfoot z hz).2).symm)
  have hNrep := hNpres.1 hrep
  have hBpre : (epochBudgetInitContract w).pre [I.m,oN.value] stN.mem :=
    ⟨I.m,oN.value,rfl,hfive,hcount,⟨⟨5*I.m,0,1,oN.value,rfl,by omega⟩,hNpost.1.2.2.2.1,by change oN.value+3<2^w; omega⟩⟩
  obtain ⟨body,hbody,oB,stB,cB,hrB,hBpost,hBcost⟩ := hbudget [I.m,oN.value] stN.mem stN.pos ω
    (by wram_words) hBpre
  change (epochBudgetRecordContract w).post [5*I.m,0,1,oN.value] stN.mem oB.value stB.mem at hBpost
  have hpres := epochBudgetRecord_preserves_state R himpl.1 hBpost hNrep
    (fun z hz => by have hh := (hfoot z hz).2; omega)
  have hbudgetEnd : oB.value=oN.value+3 := hBpost.2
  have hvB : oB.value<2^w := by omega
  have hBframe := hBpost.1.2.2.1
  change ∀ z<oN.value,stB.mem z=stN.mem z at hBframe
  have hframe : ∀ z<oC.value,stB.mem z=stC.mem z := by
    intro z hz
    exact (hBframe z (by omega)).trans (hNframe z hz)
  have hnamesFinal : ListAt stB.mem oC.value (List.range I.m) := by
    have htable := hNpost.1.2.2.2.2
    change ListAt stN.mem oC.value (List.range I.m) at htable
    intro i hi
    have hi' : i<I.m := by simpa only [List.length_range] using hi
    exact (hBframe (oC.value+i) (by omega)).trans (htable i hi)
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  change heap+(la+ga)≤oC.value at hlower
  have hlEnd : heap+I.m*F.limbs≤oC.value := by omega
  have hgEnd : heap+la+I.m*F.limbs≤oC.value := by omega
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
  have hstate : s=A.init (namedInstance I)
      (readVector stB.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector stB.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
    rw [hgSame,hlSame]
    exact hstateC
  have hOldFrame := epochStart_frame F A I κ α rate allocation R hCpost
  have hsourceFrame : ∀ z<heap,stB.mem z=mem z := by
    intro z hz
    exact (hframe z (by omega)).trans (hOldFrame z hz)
  have hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s := by
    obtain ⟨coefficients,_,hInitModel⟩ := hmodel
    exact hInitModel.2
  let original := startState args mem pos
  let afterC : State := ⟨stC.mem,Function.update original.regs 15 oC.value,stC.pos⟩
  let afterN : State := ⟨stN.mem,Function.update afterC.regs 16 oN.value,stN.pos⟩
  let afterB : State := ⟨stB.mem,Function.update afterN.regs 17 oB.value,stB.pos⟩
  have hcallC : Runs w p ω (.call 15 start [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
      .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13,.reg 14]) original .normal afterC (cC+16) := by
    apply runs_call_iff.mpr
    refine ⟨args,epochStartBody refresh initEntry,oC,stC,cC,?_,hstart,hrC,rfl,?_,?_⟩
    · dsimp only [original,args]
      eval_expr
    · cases stC
      rfl
    · simp [argsSize]
      omega
  have hcallN : Runs w p ω (.call 16 names [.reg 0,.reg 15]) afterC .normal afterN (cN+3) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,oC.value],namesBody,oN,stN,cN,?_,hNamesBody,hrN,rfl,?_,by simp [argsSize]; omega⟩
    · dsimp only [afterC,original,args]
      eval_expr
    · cases stN
      rfl
  have hcallB : Runs w p ω (.call 17 budget [.reg 0,.reg 16]) afterN .normal afterB (cB+3) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,oN.value],body,oB,stB,cB,?_,hbody,hrB,rfl,?_,by simp [argsSize]; omega⟩
    · dsimp only [afterN,afterC,original,args]
      eval_expr
    · cases stB
      rfl
  have hret : Runs w p ω (.ret (.reg 17)) afterB (.returned oB.value) afterB 2 := by
    apply runs_ret_iff.mpr
    exact ⟨oB.value,by dsimp only [afterB]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned oB.value,afterB,cC+cN+cB+27,s,x,oC.value,stC.mem,stN.mem,?_,hCpost,?_,?_,hnamesFinal,hsourceFrame,hfit,hpres.1,hstate,?_,?_,?_⟩
  · unfold epochStartNamesBudgetBody
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterC,cC+16,cN+cB+10,hcallC,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterN,cN+3,cB+6,hcallN,?_,by omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨afterB,cB+3,2,hcallB,hret,rfl⟩)
  · simpa only [hvN] using hNpost
  · change (epochBudgetRecordContract w).post [5*I.m,0,1,oC.value+I.m] stN.mem oB.value stB.mem
    simpa only [hvN] using hBpost
  · exact hmodel
  · exact hfoot
  · change cC+cN+cB+27+R.phi handle x stB.mem≤_
    rw [← hpres.2,← hNpres.2]
    change cB≤80 at hBcost
    change cN≤30*I.m+40 at hNcost
    dsimp only [handle,la,ga]
    omega

/-- `V`-passing variant of `epochStartNamesBudgetBody`: forwards `[0..14, V]` (`V` at `.reg 15`)
to `start`, then appends names and fresh budget metadata using registers 16..18. -/
def epochStartNamesBudgetBodyWithV (start names budget : ℕ) : Stmt :=
  .call 16 start [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15] ;;
  .call 17 names [.reg 0,.reg 16] ;;
  .call 18 budget [.reg 0,.reg 17] ;;
  .ret (.reg 18)

/-- The `V`-passing caller's instructions are deterministic. -/
theorem epochStartNamesBudgetBodyWithV_noRand (start names budget : ℕ) :
    (epochStartNamesBudgetBodyWithV start names budget).NoRand := by
  simp [epochStartNamesBudgetBodyWithV,Stmt.NoRand]

/-- `V`-passing variant of `epochStartNamesBudget_runs_with_potential` for
`minRatioMachineContractWithV`. -/
theorem epochStartNamesBudget_runs_with_potential_withV {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry start names budget : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hstart : p.procs[start]?=some (epochStartBodyWithV refresh initEntry))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (cp rp lo fp up ap one E graph heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
      Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph,V],z<2^w)
    (hpre : (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).pre
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem)
    (hgradRange : ∀ i < I.m,
      |Num.IPM.arrayGradient mem I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i| +
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i ≤
        (2:ℝ)^F.rangeExponent)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : heap+epochStartSpace F I E graph heap (allocationWithV V allocation)+I.m+3<2^w) :
    ∃ o st cost s x initEnd initMem namesMem,
      Runs w p ω (epochStartNamesBudgetBodyWithV start names budget)
        (startState [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
          Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
          Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph,V] mem pos) o st cost ∧
      (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).post
        [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
          Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
          Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem initEnd initMem ∧
      (vertexNamesContract w).post [I.m,initEnd] initMem (initEnd+I.m) namesMem ∧
      (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] namesMem o.value st.mem ∧
      ListAt st.mem initEnd (List.range I.m) ∧
      let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
      let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
      let handle := heap+(la+ga)
      (∀ z<heap,st.mem z=mem z) ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
      R.rep handle s x st.mem ∧
      s=A.init (namedInstance I)
        (readVector st.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector st.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∃ coefficients,
        (coefficientRefreshContract w F.fmt.limbBits q K).post
          [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap] mem handle coefficients ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate (allocationWithV V allocation)).initPost
          [graph,heap+la,heap,F.limbs,F.fmt.precision,handle] coefficients s st.mem) ∧
      (∀ z,R.foot handle x z → handle≤z ∧ z < initEnd) ∧
      cost+R.phi handle x st.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision E+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision E+rate I.m*(I.m+1)+30*I.m+700 := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  let handle := heap+(la+ga)
  let argsV := [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap,graph,V]
  obtain ⟨oC,stC,cC,s,x,hrC,hCpost,hrep,hstateC,hmodel,hfoot,hCcost⟩ :=
    epochStart_runs_with_potential_withV F A I V κ α rate allocation R himpl hrefresh hinit
      cp rp lo fp up ap one E graph heap mem pos ω hwords hpre hgradRange
  obtain ⟨_,_,_,_,hlower,hupper,hzero⟩ :=
    (epochStart_output F A I κ α rate (allocationWithV V allocation) R hCpost).2.2
  have hend : oC.value≤heap+epochStartSpace F I E graph heap (allocationWithV V allocation) := by
    simpa only [epochStartSpace,Nat.add_assoc] using hupper
  have hrecordSpace : oC.value+I.m+3<2^w := by omega
  have hvC : oC.value<2^w := by omega
  have hm : I.m<2^w := hwords _ (by simp)
  have hNpre : (vertexNamesContract w).pre [I.m,oC.value] stC.mem :=
    ⟨⟨I.m,oC.value,rfl⟩,hzero,by change oC.value+I.m<2^w; omega⟩
  obtain ⟨namesBody,hNamesBody,oN,stN,cN,hrN,hNpost,hNcost⟩ := hnames [I.m,oC.value] stC.mem stC.pos ω
    (by wram_words) hNpre
  have hvN : oN.value=oC.value+I.m := hNpost.2
  have hvNword : oN.value<2^w := by omega
  have hNframe := hNpost.1.2.2.1
  change ∀ z<oC.value,stN.mem z=stC.mem z at hNframe
  have hNpres := himpl.1 handle s x stC.mem stN.mem (fun z hz => (hNframe z (hfoot z hz).2).symm)
  have hNrep := hNpres.1 hrep
  have hBpre : (epochBudgetInitContract w).pre [I.m,oN.value] stN.mem :=
    ⟨I.m,oN.value,rfl,hfive,hcount,⟨⟨5*I.m,0,1,oN.value,rfl,by omega⟩,hNpost.1.2.2.2.1,by change oN.value+3<2^w; omega⟩⟩
  obtain ⟨body,hbody,oB,stB,cB,hrB,hBpost,hBcost⟩ := hbudget [I.m,oN.value] stN.mem stN.pos ω
    (by wram_words) hBpre
  change (epochBudgetRecordContract w).post [5*I.m,0,1,oN.value] stN.mem oB.value stB.mem at hBpost
  have hpres := epochBudgetRecord_preserves_state R himpl.1 hBpost hNrep
    (fun z hz => by have hh := (hfoot z hz).2; omega)
  have hbudgetEnd : oB.value=oN.value+3 := hBpost.2
  have hvB : oB.value<2^w := by omega
  have hBframe := hBpost.1.2.2.1
  change ∀ z<oN.value,stB.mem z=stN.mem z at hBframe
  have hframe : ∀ z<oC.value,stB.mem z=stC.mem z := by
    intro z hz
    exact (hBframe z (by omega)).trans (hNframe z hz)
  have hnamesFinal : ListAt stB.mem oC.value (List.range I.m) := by
    have htable := hNpost.1.2.2.2.2
    change ListAt stN.mem oC.value (List.range I.m) at htable
    intro i hi
    have hi' : i<I.m := by simpa only [List.length_range] using hi
    exact (hBframe (oC.value+i) (by omega)).trans (htable i hi)
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  change heap+(la+ga)≤oC.value at hlower
  have hlEnd : heap+I.m*F.limbs≤oC.value := by omega
  have hgEnd : heap+la+I.m*F.limbs≤oC.value := by omega
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
  have hstate : s=A.init (namedInstance I)
      (readVector stB.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector stB.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
    rw [hgSame,hlSame]
    exact hstateC
  have hOldFrame := epochStart_frame F A I κ α rate (allocationWithV V allocation) R hCpost
  have hsourceFrame : ∀ z<heap,stB.mem z=mem z := by
    intro z hz
    exact (hframe z (by omega)).trans (hOldFrame z hz)
  have hfit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s := by
    obtain ⟨coefficients,_,hInitModel⟩ := hmodel
    exact hInitModel.2
  let original := startState argsV mem pos
  let afterC : State := ⟨stC.mem,Function.update original.regs 16 oC.value,stC.pos⟩
  let afterN : State := ⟨stN.mem,Function.update afterC.regs 17 oN.value,stN.pos⟩
  let afterB : State := ⟨stB.mem,Function.update afterN.regs 18 oB.value,stB.pos⟩
  have hcallC : Runs w p ω (.call 16 start [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
      .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15])
      original .normal afterC (cC+17) := by
    apply runs_call_iff.mpr
    refine ⟨argsV,epochStartBodyWithV refresh initEntry,oC,stC,cC,?_,hstart,hrC,rfl,?_,?_⟩
    · dsimp only [original,argsV]
      eval_expr
    · cases stC
      rfl
    · change cC+17=16+cC+1
      omega
  have hcallN : Runs w p ω (.call 17 names [.reg 0,.reg 16]) afterC .normal afterN (cN+3) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,oC.value],namesBody,oN,stN,cN,?_,hNamesBody,hrN,rfl,?_,by simp [argsSize]; omega⟩
    · dsimp only [afterC,original,argsV]
      eval_expr
    · cases stN
      rfl
  have hcallB : Runs w p ω (.call 18 budget [.reg 0,.reg 17]) afterN .normal afterB (cB+3) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,oN.value],body,oB,stB,cB,?_,hbody,hrB,rfl,?_,by simp [argsSize]; omega⟩
    · dsimp only [afterN,afterC,original,argsV]
      eval_expr
    · cases stB
      rfl
  have hret : Runs w p ω (.ret (.reg 18)) afterB (.returned oB.value) afterB 2 := by
    apply runs_ret_iff.mpr
    exact ⟨oB.value,by dsimp only [afterB]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned oB.value,afterB,cC+cN+cB+28,s,x,oC.value,stC.mem,stN.mem,?_,hCpost,?_,?_,hnamesFinal,hsourceFrame,hfit,hpres.1,hstate,?_,?_,?_⟩
  · unfold epochStartNamesBudgetBodyWithV
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterC,cC+17,cN+cB+10,hcallC,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterN,cN+3,cB+6,hcallN,?_,by omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨afterB,cB+3,2,hcallB,hret,rfl⟩)
  · simpa only [hvN] using hNpost
  · change (epochBudgetRecordContract w).post [5*I.m,0,1,oC.value+I.m] stN.mem oB.value stB.mem
    simpa only [hvN] using hBpost
  · exact hmodel
  · exact hfoot
  · change cC+cN+cB+28+R.phi handle x stB.mem≤_
    rw [← hpres.2,← hNpres.2]
    change cB≤80 at hBcost
    change cN≤30*I.m+40 at hNcost
    dsimp only [handle,la,ga]
    omega

end MinCostFlow.IPM.Machine
