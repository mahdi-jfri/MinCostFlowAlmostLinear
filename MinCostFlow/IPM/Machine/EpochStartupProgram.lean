module

public import MinCostFlow.IPM.Machine.EpochStartupRun
public import MinCostFlow.IPM.Machine.EpochNextLayout
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Run guarded startup with one initialization and the full coefficient scan

The initial model state is the state constructed by the actual Init.
The name and budget writers preserve its footprint. The range scan
reads those same arrays and can return a fresh failure flag before
any calls of the finite epoch loop.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

private theorem epochStartNamesBudget_not_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {start names budget cost : ℕ} {initial final : State}
    (h : Runs w p ω (epochStartNamesBudgetBody start names budget) initial .normal final cost) :
    False := by
  unfold epochStartNamesBudgetBody at h
  rcases runs_seq_iff.mp h with ⟨_,_,_,hh,_⟩ | ⟨_,_,_,_,h₁,_⟩
  · cases hh
  rcases runs_seq_iff.mp h₁ with ⟨_,_,_,hh,_⟩ | ⟨_,_,_,_,h₂,_⟩
  · cases hh
  rcases runs_seq_iff.mp h₂ with ⟨_,_,_,hh,_⟩ | ⟨_,_,_,_,h₃,_⟩
  · cases hh
  obtain ⟨_,_,hh,_,_⟩ := runs_ret_iff.mp h₃
  cases hh

set_option maxHeartbeats 400000 in
/-- Execute the full checked startup. The successful output is the
original initialized state, while the scan postcondition is retained
even on failure. The same initial credit is charged at most once. -/
theorem epochStartup_runs_with_potential {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry start startNames names budget scan flag : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hstart : p.procs[start]?=some (epochStartBody refresh initEntry))
    (hstartNames : p.procs[startNames]?=some (epochStartNamesBudgetBody start names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hscan : MeetsContract w p scan (coefficientRangeListContract w F.fmt.limbBits))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (old : EpochLayout) (base rp fp heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈(old.next F I base rp fp heap 0).startupPacket F I,z<2^w)
    (hpre : (epochStartContract F A I κ α rate allocation R q K).pre
      ((old.next F I base rp fp heap 0).startPacket F I) mem)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : heap+epochStartSpace F I old.exponent old.initGraph heap allocation+I.m+4<2^w)
    (hneg : old.gradientMin+F.limbs≤heap) (hmax : old.gradientMax+F.limbs≤heap) (hmin : old.lengthMin+F.limbs≤heap)
    (hvneg : Num.Valid mem old.gradientMin F.fmt.limbBits F.limbs)
    (hvmax : Num.Valid mem old.gradientMax F.fmt.limbBits F.limbs)
    (hvmin : Num.Valid mem old.lengthMin F.fmt.limbBits F.limbs) :
    ∃ v final cost bit s x initEnd initialized named started,
      let L := old.next F I base rp fp heap initEnd
      let end_ := initEnd+I.m+3
      Runs w p ω (epochStartupBody startNames scan flag)
        (startState (L.startupPacket F I) mem pos) (.returned v) final cost ∧
      (epochStartContract F A I κ α rate allocation R q K).post (L.startPacket F I) mem initEnd initialized ∧
      (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
      (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ started ∧
      ListAt started initEnd (List.range I.m) ∧ (∀ z<heap,started z=mem z) ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
      R.rep L.handle s x started ∧
      s=A.init (namedInstance I)
        (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∀ z,R.foot L.handle x z → L.handle≤z ∧ z< initEnd) ∧
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started ∧
      (if bit=1 then v=end_ ∧ final.mem=started else
        (flagRecordContract w).post [0,end_] started v final.mem) ∧
      final.mem (v-1)=bit ∧ v<2^w ∧
      cost+R.phi L.handle x started≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision L.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision L.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+900 := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
  let startArgs := (old.next F I base rp fp heap 0).startPacket F I
  have hwordsStart : ∀ z∈startArgs,z<2^w :=
    fun z hz => hwords z (List.mem_append_left _ hz)
  obtain ⟨o,st,cost,s,x,initEnd,initMem,named,hRun,hOut,hN,hB,hList,hFrame,hFit,hRep,hState,_,hFoot,hCost⟩ :=
    epochStartNamesBudget_runs_with_potential F A I κ α rate allocation R himpl hrefresh hinit hstart hnames hbudget
      old.cost rp old.lower fp old.upper old.alpha old.one old.exponent old.initGraph heap mem pos ω hwordsStart
      hpre hfive hcount (by omega)
  cases o with
  | normal => exact False.elim (epochStartNamesBudget_not_normal hRun)
  | returned end_ =>
    have hv : end_=initEnd+I.m+3 := hB.2
    have hbit := (epochBudgetRecord_output hB).2.2
    have hz : ZeroFrom st.mem end_ := hB.1.2.2.2.1
    obtain ⟨hLength,hGradient,_,_,_,_,hLower,hUpper,_⟩ := epochStart_output F A I κ α rate allocation R hOut
    change heap+(la+ga)≤ initEnd at hLower
    have hUpper' : initEnd≤heap+epochStartSpace F I old.exponent old.initGraph heap allocation := by
      simpa only [epochStartSpace,Nat.add_assoc] using hUpper
    have hs : end_+1<2^w := by omega
    have hml : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
    have hmg : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
    have hOld : ∀ z< initEnd,st.mem z=initMem z := by
      intro z hz'
      exact (hB.1.2.2.1 z (by change z< initEnd+I.m; omega)).trans (hN.1.2.2.1 z hz')
    have hvalid (e : ℕ) (he : e<I.m) : Num.Valid st.mem (heap+la+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid st.mem (heap+e*F.limbs) F.fmt.limbBits F.limbs := by
      have hge := reported_entry_end (heap+la) F.limbs e I.m he
      have hle := reported_entry_end heap F.limbs e I.m he
      exact ⟨Num.IPM.valid_frozen hOld (hge.trans (by omega)) (hGradient e he).1,
        Num.IPM.valid_frozen hOld (hle.trans (by omega)) (hLength e he).1⟩
    have hscanPre := coefficientRangeList_full_pre (w:=w) (L:=F.limbs) (g:=heap+la) (l:=heap)
      hList (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (Num.IPM.valid_frozen hFrame hneg hvneg) (Num.IPM.valid_frozen hFrame hmax hvmax)
      (Num.IPM.valid_frozen hFrame hmin hvmin) hvalid
    have hscanWords : ∀ z∈[initEnd,I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs],
        z<2^w := by
      intro z hz'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
      rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega
    obtain ⟨v,final,c,bit,hActual,hScan,hStatus,hFinalBit,hW,hTotal⟩ :=
      epochStartup_runs_of_start hstartNames hRun hscan hflag hs (by omega) hv (by omega)
        hscanWords hscanPre hbit hz
    refine ⟨v,final,c,bit,s,x,initEnd,initMem,named,st.mem,hActual,hOut,hN,?_,hList,hFrame,
      hFit,hRep,hState,hFoot,hScan,?_,hFinalBit,hW,?_⟩
    · exact hv ▸ hB
    · simpa only [hv] using hStatus
    · change cost+R.phi (heap+(la+ga)) x st.mem≤_ at hCost
      change c+R.phi (heap+(la+ga)) x st.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+900
      have hmul : I.m*(164*F.limbs+530)=I.m*(164*F.limbs+500)+30*I.m := by
        rw [show 164*F.limbs+530=164*F.limbs+500+30 by omega,Nat.mul_add,Nat.mul_comm I.m 30]
      rw [hmul]
      omega

private theorem epochStartNamesBudgetWithV_not_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {start names budget cost : ℕ} {initial final : State}
    (h : Runs w p ω (epochStartNamesBudgetBodyWithV start names budget) initial .normal final cost) :
    False := by
  unfold epochStartNamesBudgetBodyWithV at h
  rcases runs_seq_iff.mp h with ⟨_,_,_,hh,_⟩ | ⟨_,_,_,_,h₁,_⟩
  · cases hh
  rcases runs_seq_iff.mp h₁ with ⟨_,_,_,hh,_⟩ | ⟨_,_,_,_,h₂,_⟩
  · cases hh
  rcases runs_seq_iff.mp h₂ with ⟨_,_,_,hh,_⟩ | ⟨_,_,_,_,h₃,_⟩
  · cases hh
  obtain ⟨_,_,hh,_,_⟩ := runs_ret_iff.mp h₃
  cases hh

set_option maxHeartbeats 400000 in
/-- `V`-passing variant of `epochStartup_runs_with_potential` for `minRatioMachineContractWithV`. -/
theorem epochStartup_runs_with_potential_withV {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh initEntry start startNames names budget scan flag : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hstart : p.procs[start]?=some (epochStartBodyWithV refresh initEntry))
    (hstartNames : p.procs[startNames]?=some (epochStartNamesBudgetBodyWithV start names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hscan : MeetsContract w p scan (coefficientRangeListContract w F.fmt.limbBits))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (old : EpochLayout) (base rp fp heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈(old.next F I base rp fp heap 0).startupPacket F I ++ [V],z<2^w)
    (hpre : (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).pre
      ((old.next F I base rp fp heap 0).startPacket F I) mem)
    (hgradRange : ∀ i < I.m,
      |Num.IPM.arrayGradient mem I.m old.cost rp old.lower fp old.upper old.alpha
        F.fmt.limbBits F.limbs F.fmt.precision i| +
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem old.lower fp old.upper old.alpha
          F.fmt.limbBits F.limbs F.fmt.precision i ≤
        (2:ℝ)^F.rangeExponent)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4<2^w)
    (hneg : old.gradientMin+F.limbs≤heap) (hmax : old.gradientMax+F.limbs≤heap) (hmin : old.lengthMin+F.limbs≤heap)
    (hvneg : Num.Valid mem old.gradientMin F.fmt.limbBits F.limbs)
    (hvmax : Num.Valid mem old.gradientMax F.fmt.limbBits F.limbs)
    (hvmin : Num.Valid mem old.lengthMin F.fmt.limbBits F.limbs) :
    ∃ v final cost bit s x initEnd initialized named started,
      let L := old.next F I base rp fp heap initEnd
      let end_ := initEnd+I.m+3
      Runs w p ω (epochStartupBodyWithV startNames scan flag)
        (startState (L.startupPacket F I ++ [V]) mem pos) (.returned v) final cost ∧
      (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).post
        (L.startPacket F I) mem initEnd initialized ∧
      (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
      (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ started ∧
      ListAt started initEnd (List.range I.m) ∧ (∀ z<heap,started z=mem z) ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
      R.rep L.handle s x started ∧
      s=A.init (namedInstance I)
        (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
      (∀ z,R.foot L.handle x z → L.handle≤z ∧ z< initEnd) ∧
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started ∧
      (if bit=1 then v=end_ ∧ final.mem=started else
        (flagRecordContract w).post [0,end_] started v final.mem) ∧
      final.mem (v-1)=bit ∧ v<2^w ∧
      cost+R.phi L.handle x started≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision L.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision L.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+900 := by
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
  let startArgs := (old.next F I base rp fp heap 0).startPacket F I
  have hwordsStart : ∀ z∈startArgs ++ [V],z<2^w := by
    intro z hz
    simp only [List.mem_append] at hz
    rcases hz with hz | hz
    · exact hwords z (List.mem_append_left _ (List.mem_append_left _ hz))
    · exact hwords z (List.mem_append_right _ hz)
  obtain ⟨o,st,cost,s,x,initEnd,initMem,named,hRun,hOut,hN,hB,hList,hFrame,hFit,hRep,hState,_,hFoot,hCost⟩ :=
    epochStartNamesBudget_runs_with_potential_withV F A I V κ α rate allocation R himpl hrefresh hinit hstart hnames hbudget
      old.cost rp old.lower fp old.upper old.alpha old.one old.exponent old.initGraph heap mem pos ω hwordsStart
      hpre hgradRange hfive hcount (by omega)
  cases o with
  | normal => exact False.elim (epochStartNamesBudgetWithV_not_normal hRun)
  | returned end_ =>
    have hv : end_=initEnd+I.m+3 := hB.2
    have hbit := (epochBudgetRecord_output hB).2.2
    have hz : ZeroFrom st.mem end_ := hB.1.2.2.2.1
    obtain ⟨hLength,hGradient,_,_,_,_,hLower,hUpper,_⟩ :=
      epochStart_output F A I κ α rate (allocationWithV V allocation) R hOut
    change heap+(la+ga)≤ initEnd at hLower
    have hUpper' : initEnd≤heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation) := by
      simpa only [epochStartSpace,Nat.add_assoc] using hUpper
    have hs : end_+1<2^w := by omega
    have hml : I.m*F.limbs≤la := by simp only [la,Num.IPM.lengthArraySpace,Nat.add_mul,Nat.one_mul]; omega
    have hmg : I.m*F.limbs≤ga := by simp only [ga,Num.IPM.gradientArraySpace,Nat.add_mul,Nat.one_mul]; omega
    have hOld : ∀ z< initEnd,st.mem z=initMem z := by
      intro z hz'
      exact (hB.1.2.2.1 z (by change z< initEnd+I.m; omega)).trans (hN.1.2.2.1 z hz')
    have hvalid (e : ℕ) (he : e<I.m) : Num.Valid st.mem (heap+la+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid st.mem (heap+e*F.limbs) F.fmt.limbBits F.limbs := by
      have hge := reported_entry_end (heap+la) F.limbs e I.m he
      have hle := reported_entry_end heap F.limbs e I.m he
      exact ⟨Num.IPM.valid_frozen hOld (hge.trans (by omega)) (hGradient e he).1,
        Num.IPM.valid_frozen hOld (hle.trans (by omega)) (hLength e he).1⟩
    have hscanPre := coefficientRangeList_full_pre (w:=w) (L:=F.limbs) (g:=heap+la) (l:=heap)
      hList (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (Num.IPM.valid_frozen hFrame hneg hvneg) (Num.IPM.valid_frozen hFrame hmax hvmax)
      (Num.IPM.valid_frozen hFrame hmin hvmin) hvalid
    have hscanWords : ∀ z∈[initEnd,I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs],
        z<2^w := by
      intro z hz'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
      rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega
    obtain ⟨v,final,c,bit,hActual,hScan,hStatus,hFinalBit,hW,hTotal⟩ :=
      epochStartupWithV_runs_of_start hstartNames hRun hscan hflag hs (by omega) hv (by omega)
        hscanWords hscanPre hbit hz
    refine ⟨v,final,c,bit,s,x,initEnd,initMem,named,st.mem,?_,hOut,hN,?_,hList,hFrame,
      hFit,hRep,hState,hFoot,hScan,?_,hFinalBit,hW,?_⟩
    · exact hActual
    · exact hv ▸ hB
    · simpa only [hv] using hStatus
    · change cost+R.phi (heap+(la+ga)) x st.mem≤_ at hCost
      change c+R.phi (heap+(la+ga)) x st.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+900
      have hmul : I.m*(164*F.limbs+530)=I.m*(164*F.limbs+500)+30*I.m := by
        rw [show 164*F.limbs+530=164*F.limbs+500+30 by omega,Nat.mul_add,Nat.mul_comm I.m 30]
      rw [hmul]
      omega

end MinCostFlow.IPM.Machine
