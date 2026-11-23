module

public import MinCostFlow.IPM.Machine.EpochCheckedStartup
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.IPM.Machine.VectorFrame
import WordRAM.Tactic

/-!
# `V`-passing range-checked epoch startup before min-ratio Init

Mirrors `EpochCheckedStartup.lean` for `minRatioMachineContractWithV`,
scanning all `m` refreshed entries before calling Init and calling Init
only when every entry is strictly in range.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- `V`-passing variant of `epochInitNamesBudget_runs_with_potential`. -/
theorem epochInitNamesBudgetWithV_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init initEntry names budget : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (graph grad len handle : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[I.m,graph,grad,len,F.limbs,F.fmt.precision,V,handle],z<2^w)
    (hInitPre : (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation).initPre
      [graph,grad,len,F.limbs,F.fmt.precision,V,handle] mem)
    (hz : ZeroFrom mem handle)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : handle+allocation 3 [graph,grad,len,F.limbs,F.fmt.precision,V,handle]+I.m+3<2^w) :
    ∃ initEnd final cost s x initialized named,
      let end_ := initEnd+I.m+3
      Runs w p ω (epochInitNamesBudgetBodyWithV initEntry names budget)
        (startState [I.m,graph,grad,len,F.limbs,F.fmt.precision,V,handle] mem pos)
        (.returned end_) final cost ∧
      (minRatioInitContract w R
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate (allocationWithV V allocation))).post
        [graph,grad,len,F.limbs,F.fmt.precision,handle] mem initEnd initialized ∧
      (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
      (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ final.mem ∧
      ListAt final.mem initEnd (List.range I.m) ∧
      (∀ z<handle,final.mem z=mem z) ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
      R.rep handle s x final.mem ∧
      s=A.init (namedInstance I)
        (readVector final.mem grad F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector final.mem len F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∀ z,R.foot handle x z → handle≤z ∧ z < initEnd) ∧
      handle ≤ initEnd ∧ initEnd ≤ handle+allocation 3 [graph,grad,len,F.limbs,F.fmt.precision,V,handle] ∧
      cost+R.phi handle x final.mem≤rate I.m*(I.m+1)+30*I.m+200 := by
  have hmW : I.m<2^w := hwords _ (by simp)
  have hEntryPre : (minRatioInitContractWithV w R
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation)).pre
      [graph,grad,len,F.limbs,F.fmt.precision,V,handle] mem :=
    ⟨⟨graph,grad,len,F.limbs,F.fmt.precision,V,handle,rfl,hInitPre⟩,hz,by
      change handle+allocation 3 [graph,grad,len,F.limbs,F.fmt.precision,V,handle]<2^w; omega⟩
  have hInitWords : ∀ z∈[graph,grad,len,F.limbs,F.fmt.precision,V,handle],z<2^w :=
    fun z hz' => hwords z (List.mem_cons_of_mem _ hz')
  obtain ⟨oI,stI,cI,s,x,hrI,hIpost,hrep,hmodel,hfoot,hIcost⟩ :=
    minRatioInit_runs_with_potential_withV R
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation)
      himpl graph grad len F.limbs F.fmt.precision V handle mem pos ω hInitWords hEntryPre
  have hIlo : handle≤oI.value := hIpost.1
  have hIhi : oI.value≤handle+allocation 3 [graph,grad,len,F.limbs,F.fmt.precision,V,handle] := hIpost.2.1
  have hIframe : ∀ z<handle,stI.mem z=mem z := hIpost.2.2.1
  have hIzero : ZeroFrom stI.mem oI.value := hIpost.2.2.2.1
  have hoIW : oI.value<2^w := by omega
  have hNpre : (vertexNamesContract w).pre [I.m,oI.value] stI.mem :=
    ⟨⟨I.m,oI.value,rfl⟩,hIzero,by change oI.value+I.m<2^w; omega⟩
  obtain ⟨nBody,hnBody,oN,stN,cN,hrN,hNpost,hNcost⟩ :=
    hnames [I.m,oI.value] stI.mem stI.pos ω (by wram_words) hNpre
  have hvN : oN.value=oI.value+I.m := hNpost.2
  have hvNW : oN.value<2^w := by omega
  have hNframe : ∀ z<oI.value,stN.mem z=stI.mem z := hNpost.1.2.2.1
  have hNpres := himpl.1 handle s x stI.mem stN.mem (fun z hz' => (hNframe z (hfoot z hz').2).symm)
  have hNrep := hNpres.1 hrep
  have hBpre : (epochBudgetInitContract w).pre [I.m,oN.value] stN.mem :=
    ⟨I.m,oN.value,rfl,hfive,hcount,
      ⟨⟨5*I.m,0,1,oN.value,rfl,by omega⟩,hNpost.1.2.2.2.1,by change oN.value+3<2^w; omega⟩⟩
  obtain ⟨bBody,hbBody,oB,stB,cB,hrB,hBpost,hBcost⟩ :=
    hbudget [I.m,oN.value] stN.mem stN.pos ω (by wram_words) hBpre
  change (epochBudgetRecordContract w).post [5*I.m,0,1,oN.value] stN.mem oB.value stB.mem at hBpost
  have hvB : oB.value=oN.value+3 := hBpost.2
  have hvBW : oB.value<2^w := by omega
  have hBframe : ∀ z<oN.value,stB.mem z=stN.mem z := hBpost.1.2.2.1
  have hBpres := epochBudgetRecord_preserves_state R himpl.1 hBpost hNrep
    (fun z hz' => by have hh := (hfoot z hz').2; omega)
  have hFrameAll : ∀ z<handle,stB.mem z=mem z := fun z hz' =>
    (hBframe z (by omega)).trans ((hNframe z (by omega)).trans (hIframe z hz'))
  obtain ⟨_,_,_,_,heqPre,_,_,_,_,_,_,_,_,hgEnd,hlEnd,_,_⟩ := hInitPre
  simp only [List.cons.injEq,and_true] at heqPre
  obtain ⟨rfl,rfl,rfl,_,_,_,rfl⟩ := heqPre
  have hgradSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hFrameAll hgEnd
  have hlenSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hFrameAll hlEnd
  have hstate : s=A.init (namedInstance I)
      (readVector stB.mem grad F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector stB.mem len F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
    rw [hgradSame,hlenSame]; exact hmodel.1
  have hlist : ListAt stB.mem oI.value (List.range I.m) :=
    hNpost.1.2.2.2.2.congr (fun z _ hz' =>
      hBframe z (by rw [hvN]; rw [List.length_range] at hz'; exact hz'))
  have hIpostCompat : (minRatioInitContract w R
      (minRatioMachineContract F A (namedInstance I) I.m κ α rate (allocationWithV V allocation))).post
      [graph,grad,len,F.limbs,F.fmt.precision,handle] mem oI.value stI.mem := by
    obtain ⟨hlo,hhi,hfr,hz',s',x',hrep',hmod',hft'⟩ := hIpost
    change oI.value≤handle+allocation 3 [graph,grad,len,F.limbs,F.fmt.precision,V,handle] at hhi
    exact ⟨hlo,by
      change oI.value≤handle+allocationWithV V allocation 3 [graph,grad,len,F.limbs,F.fmt.precision,handle]
      rw [allocationWithV_init]; exact hhi,hfr,hz',s',x',hrep',hmod',hft'⟩
  let start := startState [I.m,graph,grad,len,F.limbs,F.fmt.precision,V,handle] mem pos
  let afterI : State := ⟨stI.mem,Function.update start.regs 8 oI.value,stI.pos⟩
  let afterN : State := ⟨stN.mem,Function.update afterI.regs 9 oN.value,stN.pos⟩
  let afterB : State := ⟨stB.mem,Function.update afterN.regs 10 oB.value,stB.pos⟩
  have hcallI : Runs w p ω (.call 8 initEntry [.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7])
      start .normal afterI (7+cI+1) := by
    apply runs_call_iff.mpr
    refine ⟨[graph,grad,len,F.limbs,F.fmt.precision,V,handle],minRatioInitBodyWithV init,oI,stI,cI,
      by dsimp only [start]; eval_expr,hinit,hrI,rfl,?_,rfl⟩
    cases stI; rfl
  have hcallN : Runs w p ω (.call 9 names [.reg 0,.reg 8])
      afterI .normal afterN (2+cN+1) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,oI.value],nBody,oN,stN,cN,
      by dsimp only [afterI,start]; eval_expr,hnBody,hrN,rfl,?_,rfl⟩
    cases stN; rfl
  have hcallB : Runs w p ω (.call 10 budget [.reg 0,.reg 9])
      afterN .normal afterB (2+cB+1) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,oN.value],bBody,oB,stB,cB,
      by dsimp only [afterN,afterI,start]; eval_expr,hbBody,hrB,rfl,?_,rfl⟩
    cases stB; rfl
  have hret : Runs w p ω (.ret (.reg 10)) afterB (.returned (oI.value+I.m+3)) afterB 2 :=
    runs_ret_iff.mpr ⟨oB.value,by dsimp only [afterB]; eval_expr,by rw [hvB,hvN],rfl,rfl⟩
  refine ⟨oI.value,afterB,cI+cN+cB+19,s,x,stI.mem,stN.mem,?_,hIpostCompat,hvN ▸ hNpost,
    by rw [← hvN,← hvB]; exact hBpost,hlist,hFrameAll,hmodel.2,hBpres.1,hstate,hfoot,hIlo,hIhi,?_⟩
  · unfold epochInitNamesBudgetBodyWithV
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterI,7+cI+1,(2+cN+1)+((2+cB+1)+2+1)+1,hcallI,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterN,2+cN+1,(2+cB+1)+2+1,hcallN,?_,rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨afterB,2+cB+1,2,hcallB,hret,rfl⟩)
  · change cI+cN+cB+19+R.phi handle x stB.mem≤_
    rw [← hBpres.2,← hNpres.2]
    change cI+R.phi handle x stI.mem≤rate I.m*(I.m+1)+30 at hIcost
    change cN≤30*I.m+40 at hNcost
    change cB≤80 at hBcost
    omega

set_option maxHeartbeats 500000 in
/-- `V`-passing variant of `epochCheckedStartup_runs_with_potential` for
`minRatioMachineContractWithV`. -/
theorem epochCheckedStartupWithV_runs_with_potential {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh fullScan initEntry initNames names budget flag : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBodyWithV initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (old : EpochLayout) (base rp fp heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈(old.next F I base rp fp heap 0).startupPacket F I++[V],z<2^w)
    (hI : I.IsValid) (hgraph : GraphAt mem old.initGraph (namedInstance I))
    (hgraphWords : ∀ z∈graphWords (namedInstance I),z<2^w)
    (hgraphEnd : old.initGraph+(graphWords (namedInstance I)).length≤heap)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprecision : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hRpre : (coefficientRefreshContract w F.fmt.limbBits q K).pre
      (((old.next F I base rp fp heap 0).startPacket F I).take 14) mem)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4<2^w)
    (hnegEnd : old.gradientMin+F.limbs≤heap) (hmaxEnd : old.gradientMax+F.limbs≤heap)
    (hminEnd : old.lengthMin+F.limbs≤heap)
    (hneg : ScalarAt mem old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hmin : ScalarAt mem old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ)))) :
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
    let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
    let handle := heap+(la+ga)
    ∃ v final cost bit coeffMem,
      Runs w p ω (epochCheckedStartupBodyWithV refresh fullScan initNames flag)
        (startState ((old.next F I base rp fp heap 0).startupPacket F I++[V]) mem pos)
        (.returned v) final cost ∧
      (coefficientRefreshContract w F.fmt.limbBits q K).post
        (((old.next F I base rp fp heap 0).startPacket F I).take 14) mem handle coeffMem ∧
      (coefficientRangeFullContract w F.fmt.limbBits).post
        [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
        coeffMem bit coeffMem ∧
      bit≤1 ∧ final.mem (v-1)=bit ∧ v<2^w ∧ ZeroFrom final.mem v ∧
      heap≤v ∧ v≤heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4 ∧
      (∀ z<heap,final.mem z=mem z) ∧
      (bit=0 → cost≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+900) ∧
      (bit=1 →
        ∃ s x initEnd initialized named,
          let L := old.next F I base rp fp heap initEnd
          let end_ := initEnd+I.m+3
          v=end_ ∧
          (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).post
            (L.startPacket F I) mem initEnd initialized ∧
          (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
          (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ final.mem ∧
          ListAt final.mem initEnd (List.range I.m) ∧
          MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
          R.rep L.handle s x final.mem ∧
          s=A.init (namedInstance I)
            (readVector final.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
            (readVector final.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
          (∀ z,R.foot L.handle x z → L.handle≤z ∧ z < initEnd) ∧
          (coefficientRangeListContract w F.fmt.limbBits).post
            [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs]
            final.mem 1 final.mem ∧
          cost+R.phi L.handle x final.mem≤
            Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
            Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+
            rate I.m*(I.m+1)+I.m*(164*F.limbs+530)+900) := by
  dsimp only
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
  let handle := heap+(la+ga)
  let input := (old.next F I base rp fp heap 0).startupPacket F I++[V]
  have hRwords : ∀ z∈[I.m,old.cost,rp,old.lower,fp,old.upper,old.alpha,old.one,
      F.limbs,F.fmt.precision,old.exponent,la,ga,heap],z<2^w := by
    intro z hz'
    exact hwords z (by
      simp only [EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left [old.initGraph] hz')))
  obtain ⟨rBody,hrBody,oR,stR,cR,hrR,hRpost,hRcost⟩ := hrefresh _ _ pos ω hRwords hRpre
  have hvR : oR.value=handle := hRpost.2
  have hRpostH : (coefficientRefreshContract w F.fmt.limbBits q K).post
      (((old.next F I base rp fp heap 0).startPacket F I).take 14) mem handle stR.mem := by
    rw [← hvR]; exact hRpost
  have hRframe : ∀ z<heap,stR.mem z=mem z := hRpost.1.2.2.1
  have hRzero : ZeroFrom stR.mem handle := hvR ▸ hRpost.1.2.2.2.1
  have hml : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hmg : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hSpaceExpand : handle+allocation 3 [old.initGraph,heap+la,heap,F.limbs,F.fmt.precision,V,handle]+I.m+4<2^w := by
    simpa only [epochStartSpace,allocationWithV_init,la,ga,handle,Nat.add_assoc] using hspace
  have hOne : 1<2^w := by omega
  have hmW : I.m<2^w := hwords _ (by simp [EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next])
  have hgW : heap+la<2^w := by omega
  have hhW : heap<2^w := by omega
  have hhandleW : handle<2^w := by omega
  have hgraphW : old.initGraph<2^w := hwords _ (by simp [EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next])
  have hVW : V<2^w := hwords _ (by simp)
  have hnegW : old.gradientMin<2^w := by omega
  have hmaxW : old.gradientMax<2^w := by omega
  have hminW : old.lengthMin<2^w := by omega
  have hLW : F.limbs<2^w := F.parameters_fit.1
  have hPW : F.fmt.precision<2^w := F.parameters_fit.2.1
  have hnegR : ScalarAt stR.mem old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent) :=
    ⟨Num.IPM.valid_frozen hRframe hnegEnd hneg.1,(Num.IPM.fixVal_frozen hRframe hnegEnd).trans hneg.2⟩
  have hmaxR : ScalarAt stR.mem old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent) :=
    ⟨Num.IPM.valid_frozen hRframe hmaxEnd hmax.1,(Num.IPM.fixVal_frozen hRframe hmaxEnd).trans hmax.2⟩
  have hminR : ScalarAt stR.mem old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))) :=
    ⟨Num.IPM.valid_frozen hRframe hminEnd hmin.1,(Num.IPM.fixVal_frozen hRframe hminEnd).trans hmin.2⟩
  have hvalidR : ∀ e<I.m,Num.Valid stR.mem (heap+la+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid stR.mem (heap+e*F.limbs) F.fmt.limbBits F.limbs :=
    fun e he => ⟨(hRpost.1.2.2.2.2.2 e he).1,(hRpost.1.2.2.2.2.1 e he).1⟩
  have hScanPre := coefficientRangeFull_pre (w:=w) (h:=F.fmt.limbBits) (m:=I.m) (g:=heap+la) (l:=heap)
    hOne (by omega) (by omega) (by omega) (by omega) (by omega) hnegR.1 hmaxR.1 hminR.1 hvalidR
  obtain ⟨sBody,hsBody,oS,stS,cS,hrS,hSpost,hScost⟩ :=
    hfullScan [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
      stR.mem stR.pos ω (by wram_words) hScanPre
  have hSmem : stS.mem=stR.mem := hSpost.1
  have hSpost' : (coefficientRangeFullContract w F.fmt.limbBits).post
      [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
      stR.mem oS.value stR.mem := hSmem ▸ hSpost
  have hbitLe : oS.value≤1 := hSpost.2.1
  let start := startState input mem pos
  let afterR : State := ⟨stR.mem,Function.update start.regs 19 handle,stR.pos⟩
  let afterS : State := ⟨stR.mem,Function.update afterR.regs 20 oS.value,stS.pos⟩
  have hcallR : Runs w p ω (.call 19 refresh ((List.range 14).map Expr.reg))
      start .normal afterR (cR+15) := by
    apply runs_call_iff.mpr
    refine ⟨_,rBody,oR,stR,cR,rfl,hrBody,hrR,rfl,?_,by change cR+15=14+cR+1; omega⟩
    cases stR; simp [afterR,hvR]
  have hcallS : Runs w p ω (.call 20 fullScan [.reg 0,.bin .add (.reg 13) (.reg 11),.reg 13,
      .reg 15,.reg 16,.reg 17,.reg 8]) afterR .normal afterS (cS+10) := by
    apply runs_call_iff.mpr
    refine ⟨[I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs],
      sBody,oS,stS,cS,?_,hsBody,hrS,rfl,?_,by change cS+10=9+cS+1; omega⟩
    · dsimp only [afterR,start,input,EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next]
      eval_expr
    · cases stS; dsimp only at hSmem ⊢; rw [hSmem]
  have hreg20 : Expr.eval w afterS (.reg 20)=some oS.value := by simp [afterS,Expr.eval]
  by_cases hb : oS.value=1
  · have hlenWithin : LengthsWithin (namedInstance I) F.rangeExponent
        (readVector stR.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) :=
      coefficientRangeFull_lengthsWithin F I hminR hnegR hmaxR (hb ▸ hSpost')
    have hgradWithin : ∀ e ∈ (namedInstance I).E,
        |readVector stR.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m e| ≤
          (2:ℝ)^F.rangeExponent :=
      coefficientRangeFull_gradientsWithin F I hminR hnegR hmaxR (hb ▸ hSpost')
    have hInitPre := minRatio_initPreWithV_after_refresh F A I V κ α rate allocation
      hI hgraph hgraphWords hgraphEnd hquality hprecision hRpostH hlenWithin hgradWithin
    obtain ⟨initEnd,stINB,cINB,s,x,initialized,named,hrINB,hIpost,hNpost,hBpost,hList,
      hINBframe,hFit,hRep,hState,hFoot,hIlo,hIhi,hINBcost⟩ :=
      epochInitNamesBudgetWithV_runs_with_potential F A I V κ α rate allocation R himpl hinit hnames hbudget
        old.initGraph (heap+la) heap handle stR.mem afterS.pos ω (by wram_words) hInitPre hRzero
        hfive hcount (by omega)
    let end_ := initEnd+I.m+3
    let afterINB : State := ⟨stINB.mem,Function.update afterS.regs 21 end_,stINB.pos⟩
    have hcallINB : Runs w p ω (.call 21 initNames [.reg 0,.reg 14,.bin .add (.reg 13) (.reg 11),
        .reg 13,.reg 8,.reg 9,.reg 18,.reg 19]) afterS .normal afterINB (cINB+11) := by
      apply runs_call_iff.mpr
      refine ⟨[I.m,old.initGraph,heap+la,heap,F.limbs,F.fmt.precision,V,handle],
        epochInitNamesBudgetBodyWithV initEntry names budget,.returned end_,stINB,cINB,?_,
        hinitNames,hrINB,rfl,?_,by change cINB+11=10+cINB+1; omega⟩
      · dsimp only [afterS,afterR,start,input,EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next]
        eval_expr
      · cases stINB; rfl
    have hret : Runs w p ω (.ret (.reg 21)) afterINB (.returned end_) afterINB 2 :=
      runs_ret_iff.mpr ⟨end_,by simp [afterINB,Expr.eval],rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.reg 20)
        (.call 21 initNames [.reg 0,.reg 14,.bin .add (.reg 13) (.reg 11),
          .reg 13,.reg 8,.reg 9,.reg 18,.reg 19] ;; .ret (.reg 21))
        (.call 21 flag [.const 0,.reg 19] ;; .ret (.reg 21)))
        afterS (.returned end_) afterINB (cINB+16) :=
      runs_cond_iff.mpr ⟨1,cINB+14,hb ▸ hreg20,by
        simpa using runs_seq_iff.mpr (Or.inr ⟨afterINB,cINB+11,2,hcallINB,hret,by omega⟩),
        by change cINB+16=1+(cINB+14)+1; omega⟩
    have hFullRun : Runs w p ω (epochCheckedStartupBodyWithV refresh fullScan initNames flag)
        start (.returned end_) afterINB (cR+cS+cINB+43) := by
      unfold epochCheckedStartupBodyWithV
      apply runs_seq_iff.mpr
      refine Or.inr ⟨afterR,cR+15,(cS+10)+(cINB+16)+1,hcallR,?_,by omega⟩
      exact runs_seq_iff.mpr (Or.inr ⟨afterS,cS+10,cINB+16,hcallS,hcond,rfl⟩)
    have hListScan : (coefficientRangeListContract w F.fmt.limbBits).post
        [initEnd,I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
        stINB.mem 1 stINB.mem :=
      coefficientRangeFull_to_listPost hList hINBframe (by omega) (by omega)
        (by omega) (by omega) (by omega) (hb ▸ hSpost')
    have hbitEnd : stINB.mem (end_-1)=1 := (epochBudgetRecord_output hBpost).2.2
    have hEndLe : end_≤heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4 := by
      simp only [epochStartSpace,allocationWithV_init,la,ga,handle,end_] at hIhi ⊢; omega
    refine ⟨end_,afterINB,cR+cS+cINB+43,oS.value,stR.mem,hFullRun,hRpostH,hSpost',
      hbitLe,by simpa [afterINB,hb] using hbitEnd,by omega,hBpost.1.2.2.2.1,by omega,hEndLe,
      fun z hz' => (hINBframe z (by omega)).trans (hRframe z hz'),fun h0 => by omega,?_⟩
    intro _
    refine ⟨s,x,initEnd,initialized,named,rfl,⟨stR.mem,hRpostH,hIpost⟩,hNpost,hBpost,hList,
      hFit,hRep,hState,hFoot,hListScan,?_⟩
    change cR+cS+cINB+43+R.phi handle x stINB.mem≤_
    change cR≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+400 at hRcost
    change cS≤I.m*(164*F.limbs+500)+100 at hScost
    have hmul : I.m*(164*F.limbs+530)=I.m*(164*F.limbs+500)+30*I.m := by
      rw [show 164*F.limbs+530=164*F.limbs+500+30 by omega,Nat.mul_add,Nat.mul_comm I.m 30]
    rw [hmul]
    omega
  · have hb0 : oS.value=0 := by omega
    obtain ⟨fBody,hfBody,oF,stF,cF,hrF,hFpost,hFcost⟩ :=
      hflag [0,handle] stR.mem afterS.pos ω (by wram_words)
        ⟨⟨0,handle,rfl,by decide⟩,hRzero,by change handle+1<2^w; omega⟩
    have hvF : oF.value=handle+1 := hFpost.2
    let afterF : State := ⟨stF.mem,Function.update afterS.regs 21 oF.value,stF.pos⟩
    have hcallF : Runs w p ω (.call 21 flag [.const 0,.reg 19]) afterS .normal afterF (cF+3) := by
      apply runs_call_iff.mpr
      refine ⟨[0,handle],fBody,oF,stF,cF,by dsimp only [afterS,afterR]; eval_expr,
        hfBody,hrF,rfl,?_,by change cF+3=2+cF+1; omega⟩
      cases stF; rfl
    have hret : Runs w p ω (.ret (.reg 21)) afterF (.returned oF.value) afterF 2 :=
      runs_ret_iff.mpr ⟨oF.value,by simp [afterF,Expr.eval],rfl,rfl,rfl⟩
    have hcond : Runs w p ω (.cond (.reg 20)
        (.call 21 initNames [.reg 0,.reg 14,.bin .add (.reg 13) (.reg 11),
          .reg 13,.reg 8,.reg 9,.reg 18,.reg 19] ;; .ret (.reg 21))
        (.call 21 flag [.const 0,.reg 19] ;; .ret (.reg 21)))
        afterS (.returned oF.value) afterF (cF+8) :=
      runs_cond_iff.mpr ⟨0,cF+6,hb0 ▸ hreg20,by
        simpa using runs_seq_iff.mpr (Or.inr ⟨afterF,cF+3,2,hcallF,hret,by omega⟩),
        by change cF+8=1+(cF+6)+1; omega⟩
    have hFullRun : Runs w p ω (epochCheckedStartupBodyWithV refresh fullScan initNames flag)
        start (.returned oF.value) afterF (cR+cS+cF+35) := by
      unfold epochCheckedStartupBodyWithV
      apply runs_seq_iff.mpr
      refine Or.inr ⟨afterR,cR+15,(cS+10)+(cF+8)+1,hcallR,?_,by omega⟩
      exact runs_seq_iff.mpr (Or.inr ⟨afterS,cS+10,cF+8,hcallS,hcond,rfl⟩)
    have hEndLe : oF.value≤heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4 := by
      simp only [epochStartSpace,allocationWithV_init,la,ga,handle] at hvF ⊢; omega
    have hFframe : ∀ z<handle,stF.mem z=stR.mem z := hFpost.1.2.2.1
    refine ⟨oF.value,afterF,cR+cS+cF+35,oS.value,stR.mem,hFullRun,hRpostH,hSpost',
      hbitLe,(flagRecord_output hFpost).trans hb0.symm,by omega,hFpost.1.2.2.2.1,by omega,hEndLe,
      fun z hz' => (hFframe z (by omega)).trans (hRframe z hz'),?_,fun h1 => by omega⟩
    intro _
    change cR≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+400 at hRcost
    change cS≤I.m*(164*F.limbs+500)+100 at hScost
    change cF≤20 at hFcost
    have hmul : I.m*(164*F.limbs+530)=I.m*(164*F.limbs+500)+30*I.m := by
      rw [show 164*F.limbs+530=164*F.limbs+500+30 by omega,Nat.mul_add,Nat.mul_comm I.m 30]
    rw [hmul]
    omega

end MinCostFlow.IPM.Machine
