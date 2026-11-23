module

public import MinCostFlow.IPM.Machine.EpochStart
import MinCostFlow.IPM.Machine.VectorFrame
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Executing coefficient refresh followed by initialization

The numerical call fixes the exact coefficient endpoint. Its frame
preserves the serialized graph, so the derived Init input applies to
the actual output memory. The initialization call retains its concrete
credit and both footprint bounds for the subsequent epoch iterations.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem lengthsWithin_of_refresh {w q K : ℕ} (F : MinRatioFormat w) (I : Instance)
    {cp rp lo fp up ap one E heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (coefficientRefreshContract w F.fmt.limbBits q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap] mem v mem')
    (hlenRange : ∀ i<I.m,(2:ℝ)^(-(F.rangeExponent:ℤ))*2≤
      Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i ∧
      2*Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i≤
        (2:ℝ)^F.rangeExponent) :
    LengthsWithin (namedInstance I) F.rangeExponent
      (readVector mem' heap F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
  have hlength := hout.1.2.2.2.2.1
  change ∀ i < I.m, Num.Valid mem' (heap+i*F.limbs) F.fmt.limbBits F.limbs ∧
    ScalarApprox (1+1/(2:ℝ)^q)
      (Num.fixVal mem' (heap+i*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
      (Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i) at hlength
  intro e he
  have hem : e < I.m := Finset.mem_range.mp he
  simp only [readVector, hem, ↓reduceIte]
  have ha := (hlength e hem).2
  have hr := hlenRange e hem
  have hpow : (1:ℝ) ≤ (2:ℝ)^q := one_le_pow₀ (by norm_num)
  have hδ : 1/(2:ℝ)^q ≤ 1 := (div_le_iff₀ (by positivity)).2 (by simpa only [one_mul] using hpow)
  have hb : 1+1/(2:ℝ)^q ≤ 2 := by linarith only [hδ]
  have hbpos : 0 < 1+1/(2:ℝ)^q := by positivity
  have hinv : (2:ℝ)⁻¹ ≤ (1+1/(2:ℝ)^q)⁻¹ := inv_anti₀ hbpos hb
  constructor
  · have h1 : (2:ℝ)^(-(F.rangeExponent:ℤ)) ≤ (2:ℝ)⁻¹ * Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision e := by
      linarith only [hr.1]
    exact h1.trans ((mul_le_mul_of_nonneg_right hinv ha.2.1.le).trans ha.2.2.1)
  · exact (ha.2.2.2.trans (mul_le_mul_of_nonneg_right hb ha.2.1.le)).trans hr.2

/-- The epoch-start program computes its arrays before calling Init.
The returned state, exact Init transition and retained credit all refer
to the same concrete run, for every tape. -/
theorem epochStart_runs_with_potential {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (cp rp lo fp up ap one E graph heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
      Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph],z<2^w)
    (hpre : (epochStartContract F A I κ α rate allocation R q K).pre
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem) :
    ∃ o st cost s x,Runs w p ω (epochStartBody refresh initEntry)
      (startState [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem pos) o st cost ∧
      (epochStartContract F A I κ α rate allocation R q K).post
        [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
          Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
          Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem o.value st.mem ∧
      let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
      let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
      let handle := heap+(la+ga)
      R.rep handle s x st.mem ∧
      s=A.init (namedInstance I)
        (readVector st.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector st.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∃ coefficients,
        (coefficientRefreshContract w F.fmt.limbBits q K).post
          [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap] mem handle coefficients ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).initPost
          [graph,heap+la,heap,F.limbs,F.fmt.precision,handle] coefficients s st.mem) ∧
      (∀ z,R.foot handle x z → handle≤z ∧ z<o.value) ∧
      cost+R.phi handle x st.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision E+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision E+rate I.m*(I.m+1)+500 := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  obtain ⟨cp',rp',lo',fp',up',ap',one',E',graph',heap',heq,hI,hgraph,hgraphWords,hgraphEnd,
    hk,hprec,hRpre,hspace,hlenRange⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_,_,rfl,rfl⟩ := heq
  have hRwords : ∀ z∈[I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap],z<2^w := by
    intro z hz
    exact hwords z (List.mem_append_left [graph] hz)
  obtain ⟨body,hbody,oR,stR,cR,hrR,hRpost,hRcost⟩ := hrefresh _ _ pos ω hRwords hRpre
  have hvR : oR.value=heap+(la+ga) := hRpost.2
  have hspace' : heap+(la+ga)+allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,heap+(la+ga)]<2^w := by
    simpa only [epochStartSpace,la,ga,Nat.add_assoc] using hspace
  have hvWord : oR.value<2^w := by omega
  have hgWord : heap+la<2^w := by omega
  have hhWord : heap<2^w := hwords _ (by simp)
  have hgraphWord : graph<2^w := hwords _ (by simp)
  have hLWord : F.limbs<2^w := F.parameters_fit.1
  have hPWord : F.fmt.precision<2^w := F.parameters_fit.2.1
  have hInitPre := minRatio_initPre_after_refresh F A I κ α rate allocation
    hI hgraph hgraphWords hgraphEnd hk hprec hRpost (lengthsWithin_of_refresh F I hRpost hlenRange)
  have hEntryPre : (minRatioInitContract w R
      (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation)).pre
      [graph,heap+la,heap,F.limbs,F.fmt.precision,oR.value] stR.mem :=
    ⟨⟨graph,heap+la,heap,F.limbs,F.fmt.precision,oR.value,rfl,hInitPre⟩,hRpost.1.2.2.2.1,by
      change oR.value+allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,oR.value]<2^w
      simpa only [hvR] using hspace'⟩
  obtain ⟨oI,stI,cI,s,x,hrI,hIpost,hrep,hmodel,hfoot,hIcost⟩ :=
    minRatioInit_runs_with_potential R (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation)
      himpl graph (heap+la) heap F.limbs F.fmt.precision oR.value stR.mem stR.pos ω (by wram_words) hEntryPre
  have hInitFrame := hIpost.2.2.1
  change ∀ z<oR.value,stI.mem z=stR.mem z at hInitFrame
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hlEnd : heap+I.m*F.limbs≤oR.value := by omega
  have hgEnd : heap+la+I.m*F.limbs≤oR.value := by omega
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hInitFrame hlEnd
  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hInitFrame hgEnd
  have hstate : s=A.init (namedInstance I)
      (readVector stI.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector stI.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
    rw [hgSame,hlSame]
    exact hmodel.1
  let start := startState [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap,graph] mem pos
  let saved : State := {start with regs:=Function.update start.regs 15 graph}
  let afterR : State := ⟨stR.mem,Function.update saved.regs 14 oR.value,stR.pos⟩
  let afterI : State := ⟨stI.mem,Function.update afterR.regs 16 oI.value,stI.pos⟩
  have hsave : Runs w p ω (.assign 15 (.reg 14)) start .normal saved 2 :=
    runs_assign_iff.mpr ⟨graph,by dsimp only [start]; eval_expr,rfl,rfl,rfl⟩
  have hcallR : Runs w p ω (.call 14 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
      .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13]) saved .normal afterR (14+cR+1) := by
    apply runs_call_iff.mpr
    refine ⟨_,body,oR,stR,cR,by dsimp only [saved,start]; eval_expr,hbody,hrR,rfl,?_,rfl⟩
    cases stR
    rfl
  have hcallI : Runs w p ω (.call 16 initEntry [.reg 15,.bin .add (.reg 13) (.reg 11),.reg 13,.reg 8,.reg 9,.reg 14])
      afterR .normal afterI (8+cI+1) := by
    apply runs_call_iff.mpr
    refine ⟨[graph,heap+la,heap,F.limbs,F.fmt.precision,oR.value],minRatioInitBody init,oI,stI,cI,
      by dsimp only [afterR,saved,start]; eval_expr,hinit,hrI,rfl,?_,rfl⟩
    cases stI
    rfl
  have hret : Runs w p ω (.ret (.reg 16)) afterI (.returned oI.value) afterI 2 :=
    runs_ret_iff.mpr ⟨oI.value,by dsimp only [afterI]; eval_expr,rfl,rfl,rfl⟩
  refine ⟨.returned oI.value,afterI,cR+cI+31,s,x,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold epochStartBody
    apply runs_seq_iff.mpr
    refine Or.inr ⟨saved,2,(14+cR+1)+((8+cI+1)+2+1)+1,hsave,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterR,14+cR+1,(8+cI+1)+2+1,hcallR,?_,rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨afterI,8+cI+1,2,hcallI,hret,rfl⟩)
  · exact ⟨stR.mem,hvR ▸ hRpost,hvR ▸ hIpost⟩
  · exact hvR ▸ hrep
  · exact hstate
  · exact ⟨stR.mem,hvR ▸ hRpost,hvR ▸ hmodel⟩
  · exact hvR ▸ hfoot
  · change cR+cI+31+R.phi (heap+(la+ga)) x stI.mem≤_
    rw [hvR] at hIcost
    change cI+R.phi (heap+(la+ga)) x stI.mem≤rate I.m*(I.m+1)+30 at hIcost
    change cR≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision E+
      Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision E+400 at hRcost
    omega

/-- The linked epoch-start entry meets its exact numerical/Init contract,
with every instruction counted and no extra graph-size factor. -/
theorem epochStart_meetsContract {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry entry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hp : p.procs[entry]?=some (epochStartBody refresh initEntry)) :
    MeetsContract w p entry (epochStartContract F A I κ α rate allocation R q K) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hcopy := hpre
  obtain ⟨cp,rp,lo,fp,up,ap,one,E,graph,heap,rfl,_⟩ := hpre
  obtain ⟨o,st,cost,_,_,hr,hpost,_,_,_,_,hc⟩ := epochStart_runs_with_potential F A I κ α rate allocation R
    himpl hrefresh hinit cp rp lo fp up ap one E graph heap mem pos ω hwords hcopy
  exact ⟨o,st,cost,hr,hpost,(Nat.le_add_right cost _).trans hc⟩

private theorem gradientsWithin_of_refresh {w q K : ℕ} (F : MinRatioFormat w) (I : Instance)
    {cp rp lo fp up ap one E heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (coefficientRefreshContract w F.fmt.limbBits q K).post
      [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap] mem v mem')
    (hgradRange : ∀ i < I.m,
      |Num.IPM.arrayGradient mem I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i| +
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i ≤
        (2:ℝ)^F.rangeExponent) :
    ∀ e ∈ (namedInstance I).E,
      |readVector mem' (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E)
        F.fmt.limbBits F.limbs F.fmt.precision I.m e| ≤ (2:ℝ)^F.rangeExponent := by
  have hgrad := hout.1.2.2.2.2.2
  change ∀ i < I.m, Num.Valid mem'
      (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+i*F.limbs)
      F.fmt.limbBits F.limbs ∧
    |Num.fixVal mem' (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E+i*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision -
      Num.IPM.arrayGradient mem I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i| ≤
      (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision i at hgrad
  intro e he
  have hem : e < I.m := Finset.mem_range.mp he
  simp only [readVector, hem, ↓reduceIte]
  have h1 := (hgrad e hem).2
  have h2 := hgradRange e hem
  rw [abs_le] at h1 ⊢
  have h3 := abs_le.mp (le_refl |Num.IPM.arrayGradient mem I.m cp rp lo fp up ap F.fmt.limbBits F.limbs F.fmt.precision e|)
  constructor <;> linarith

/-- `V`-passing variant of `epochStart_runs_with_potential` for `minRatioMachineContractWithV`.
Produces the exact `epochStartContract` postcondition at `allocationWithV V allocation`. -/
theorem epochStart_runs_with_potential_withV {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
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
        (2:ℝ)^F.rangeExponent) :
    ∃ o st cost s x,Runs w p ω (epochStartBodyWithV refresh initEntry)
      (startState [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
        Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
        Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph,V] mem pos) o st cost ∧
      (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).post
        [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,
          Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E,
          Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E,heap,graph] mem o.value st.mem ∧
      let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
      let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
      let handle := heap+(la+ga)
      R.rep handle s x st.mem ∧
      s=A.init (namedInstance I)
        (readVector st.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector st.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∃ coefficients,
        (coefficientRefreshContract w F.fmt.limbBits q K).post
          [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap] mem handle coefficients ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate (allocationWithV V allocation)).initPost
          [graph,heap+la,heap,F.limbs,F.fmt.precision,handle] coefficients s st.mem) ∧
      (∀ z,R.foot handle x z → handle≤z ∧ z<o.value) ∧
      cost+R.phi handle x st.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision E+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision E+rate I.m*(I.m+1)+500 := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision E
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision E
  obtain ⟨cp',rp',lo',fp',up',ap',one',E',graph',heap',heq,hI,hgraph,hgraphWords,hgraphEnd,
    hk,hprec,hRpre,hspace,hlenRange⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,_,_,rfl,rfl⟩ := heq
  have hRwords : ∀ z∈[I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap],z<2^w := by
    intro z hz
    exact hwords z (List.mem_append_left [graph,V] hz)
  obtain ⟨body,hbody,oR,stR,cR,hrR,hRpost,hRcost⟩ := hrefresh _ _ pos ω hRwords hRpre
  have hvR : oR.value=heap+(la+ga) := hRpost.2
  have hspace' : heap+(la+ga)+
      allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,V,heap+(la+ga)]<2^w := by
    simpa only [epochStartSpace,allocationWithV_init,la,ga,Nat.add_assoc] using hspace
  have hvWord : oR.value<2^w := by omega
  have hgWord : heap+la<2^w := by omega
  have hhWord : heap<2^w := hwords _ (by simp)
  have hgraphWord : graph<2^w := hwords _ (by simp)
  have hVWord : V<2^w := hwords _ (by simp)
  have hLWord : F.limbs<2^w := F.parameters_fit.1
  have hPWord : F.fmt.precision<2^w := F.parameters_fit.2.1
  have hInitPre := minRatio_initPreWithV_after_refresh F A I V κ α rate allocation
    hI hgraph hgraphWords hgraphEnd hk hprec hRpost
    (lengthsWithin_of_refresh F I hRpost hlenRange)
    (gradientsWithin_of_refresh F I hRpost hgradRange)
  have hEntryPre : (minRatioInitContractWithV w R
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation)).pre
      [graph,heap+la,heap,F.limbs,F.fmt.precision,V,oR.value] stR.mem :=
    ⟨⟨graph,heap+la,heap,F.limbs,F.fmt.precision,V,oR.value,rfl,hInitPre⟩,hRpost.1.2.2.2.1,by
      change oR.value+allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,V,oR.value]<2^w
      simpa only [hvR] using hspace'⟩
  obtain ⟨oI,stI,cI,s,x,hrI,hIpost,hrep,hmodel,hfoot,hIcost⟩ :=
    minRatioInit_runs_with_potential_withV R
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation)
      himpl graph (heap+la) heap F.limbs F.fmt.precision V oR.value stR.mem stR.pos ω
      (by wram_words) hEntryPre
  have hInitFrame := hIpost.2.2.1
  change ∀ z<oR.value,stI.mem z=stR.mem z at hInitFrame
  have hls : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hgs : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
  have hlEnd : heap+I.m*F.limbs≤oR.value := by omega
  have hgEnd : heap+la+I.m*F.limbs≤oR.value := by omega
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hInitFrame hlEnd
  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hInitFrame hgEnd
  have hstate : s=A.init (namedInstance I)
      (readVector stI.mem (heap+la) F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector stI.mem heap F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
    rw [hgSame,hlSame]
    exact hmodel.1
  let start := startState [I.m,cp,rp,lo,fp,up,ap,one,F.limbs,F.fmt.precision,E,la,ga,heap,graph,V] mem pos
  let saved : State := {start with regs:=Function.update start.regs 16 graph}
  let afterR : State := ⟨stR.mem,Function.update saved.regs 14 oR.value,stR.pos⟩
  let afterI : State := ⟨stI.mem,Function.update afterR.regs 17 oI.value,stI.pos⟩
  have hsave : Runs w p ω (.assign 16 (.reg 14)) start .normal saved 2 :=
    runs_assign_iff.mpr ⟨graph,by dsimp only [start]; eval_expr,rfl,rfl,rfl⟩
  have hcallR : Runs w p ω (.call 14 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
      .reg 8,.reg 9,.reg 10,.reg 11,.reg 12,.reg 13]) saved .normal afterR (14+cR+1) := by
    apply runs_call_iff.mpr
    refine ⟨_,body,oR,stR,cR,by dsimp only [saved,start]; eval_expr,hbody,hrR,rfl,?_,rfl⟩
    cases stR
    rfl
  have hcallI : Runs w p ω (.call 17 initEntry [.reg 16,.bin .add (.reg 13) (.reg 11),.reg 13,.reg 8,.reg 9,.reg 15,.reg 14])
      afterR .normal afterI (9+cI+1) := by
    apply runs_call_iff.mpr
    refine ⟨[graph,heap+la,heap,F.limbs,F.fmt.precision,V,oR.value],minRatioInitBodyWithV init,oI,stI,cI,
      by dsimp only [afterR,saved,start]; eval_expr,hinit,hrI,rfl,?_,rfl⟩
    cases stI
    rfl
  have hret : Runs w p ω (.ret (.reg 17)) afterI (.returned oI.value) afterI 2 :=
    runs_ret_iff.mpr ⟨oI.value,by dsimp only [afterI]; eval_expr,rfl,rfl,rfl⟩
  have hIpostCompat : (minRatioInitContract w R
      (minRatioMachineContract F A (namedInstance I) I.m κ α rate (allocationWithV V allocation))).post
      [graph,heap+la,heap,F.limbs,F.fmt.precision,oR.value] stR.mem oI.value stI.mem := by
    obtain ⟨hlo,hhi,hfr,hz,s',x',hrep',hmod',hft'⟩ := hIpost
    change oI.value ≤ oR.value + allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,V,oR.value] at hhi
    exact ⟨hlo,by
      change oI.value ≤ oR.value + allocationWithV V allocation 3 [graph,heap+la,heap,F.limbs,F.fmt.precision,oR.value]
      rw [allocationWithV_init]
      exact hhi,hfr,hz,s',x',hrep',hmod',hft'⟩
  have hModelCompat : (minRatioMachineContract F A (namedInstance I) I.m κ α rate
      (allocationWithV V allocation)).initPost
      [graph,heap+la,heap,F.limbs,F.fmt.precision,heap+(la+ga)] stR.mem s stI.mem := by
    simpa only [minRatioMachineContract] using (hvR ▸ hmodel)
  refine ⟨.returned oI.value,afterI,cR+cI+32,s,x,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold epochStartBodyWithV
    apply runs_seq_iff.mpr
    refine Or.inr ⟨saved,2,(14+cR+1)+((9+cI+1)+2+1)+1,hsave,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterR,14+cR+1,(9+cI+1)+2+1,hcallR,?_,rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨afterI,9+cI+1,2,hcallI,hret,rfl⟩)
  · exact ⟨stR.mem,hvR ▸ hRpost,hvR ▸ hIpostCompat⟩
  · exact hvR ▸ hrep
  · exact hstate
  · exact ⟨stR.mem,hvR ▸ hRpost,hModelCompat⟩
  · exact hvR ▸ hfoot
  · change cR+cI+32+R.phi (heap+(la+ga)) x stI.mem≤_
    rw [hvR] at hIcost
    change cI+R.phi (heap+(la+ga)) x stI.mem≤rate I.m*(I.m+1)+30 at hIcost
    change cR≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision E+
      Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision E+400 at hRcost
    omega

end MinCostFlow.IPM.Machine
