module

public import MinCostFlow.IPM.Machine.EpochIterationsProgram
public import MinCostFlow.IPM.Machine.EpochCompleteTrace
public import MinCostFlow.IPM.Machine.EpochCompleteAcceptance
public import MinCostFlow.IPM.Machine.EpochCompleteFlow
public import MinCostFlow.IPM.Machine.EpochCompleteSpace

/-!
# Running one complete epoch

Execute the finite iteration loop and then its actual full read if
the loop succeeds. Pass the decoded history to the analytic proof
on upper targets and account for the shared data structure credit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 500000 in
/-- The complete call runs from the initialized numerical input. Its
result contains the exact history and retains the analytic prefix
certificate when the target and initial potential satisfy the promise. -/
theorem epochComplete_runs_with_potential_upTo_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K : ℕ)
    (q : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation initPre))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity : ℝ)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024) L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hqbits : q=ipmErrorBits I.m U)
    (hwords : ∀ z∈L.packet F I 0,z<2^w)
    (hi : finish≤I.m)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hE : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base)) :
    let a := Num.IPM.alphaPrime I.m U
    let base := epochVector F I mem L.base
    let space := budgetedIterationSpace F I.m L.exponent B
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let certified := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefix I U target κ r A base finish Q
    ∃ v final cost credit loopEnd st loopCredit,
      Runs w p ω (epochCompleteBody iterations refresh) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost ∧ v<2^w ∧ v≤heap+(finish+1)*space ∧
      EpochCompletePost F A I κ (a/8) rate allocation R L q K heap space finish mem loopEnd st loopCredit
        certified v final credit ∧ (promised → st.mem (loopEnd-1)=1) ∧
      L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) ∧
      cost+R.phi L.handle credit final.mem≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate+
        46*finish+I.m*reportedEdgesCharge F I.m L.exponent rate+200+R.phi L.handle x mem := by
  dsimp only
  subst q
  let a := Num.IPM.alphaPrime I.m U
  let q := ipmErrorBits I.m U
  let space := budgetedIterationSpace F I.m L.exponent B
  let base := epochVector F I mem L.base
  let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
    potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
  let cert := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefix I U target κ r A base finish Q
  obtain ⟨P,loopEnd,st,c,loopCredit,hloop,hmem,hheap,_,htrace,hword,hcost⟩ :=
    epochIterations_runs_with_potential_upTo_at F A I U κ (a/8) _ _ rate allocation R hA L q K
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
      hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
      heap finish B x mem pos ω capacity _ hstatic halloc hspace hbudgetFit hOne hfinish hi hpre hbudget hcache hranges
  obtain ⟨hpromise,hcert⟩ := epoch_complete_trace_upTo F A I U κ target r rate allocation R hA L K heap space
    finish loopEnd P st loopCredit capacity mem hi hstatic hsource hE hm hU hsize hnums hFlo hκ hκ' hxlo
    hres hr hf hroute hmem hheap hbudget htrace
  have hcallTrace : if st.mem (loopEnd-1)=1 then
      ∃ Q : EpochPoint R.τ,EpochConditions F A I κ (a/8) rate allocation R L q K mem heap space finish finish Q ∧
        loopCredit=Q.credit ∧ cert Q ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem loopEnd st.mem ∧
        R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) loopCredit st.mem
      else st.mem (loopEnd-1)=0 := by
    by_cases hb : st.mem (loopEnd-1)=1
    · simpa only [ite_eq_left hb] using hcert
    · exact ite_eq_right hb ▸ (ite_eq_right hb ▸ hcert).1
  obtain ⟨v,final,cost,credit,hrun,hv,hpost,hcreditCost⟩ := epochComplete_runs_of_loop_at F A I κ (a/8)
    rate allocation R L q K heap space finish loopEnd c mem pos ω st loopCredit cert himpl hstore hquery
    hcoefficient hflag hedge hrefresh hiterations hloop hwords hOne hword hcallTrace
  have hstopped := fun hb => (ite_eq_right hb ▸ hcert).2
  obtain ⟨hLo,hbit,hz,hframe⟩ := epochComplete_output_frame F A I κ (a/8) rate allocation R L q K heap space
    finish loopEnd mem st loopCredit cert hpost hstopped
  have hEnd := epochComplete_end_le F A I κ (a/8) rate allocation R L q K heap B finish loopEnd mem
    st loopCredit cert halloc hpost hstopped
  refine ⟨v,final,cost,credit,loopEnd,st,loopCredit,hrun,hv,hEnd,hpost,hpromise,hLo,hbit,hz,hframe,?_⟩
  have hmul : (5*I.m+finish+(if st.mem (loopEnd-1)=1 then 0 else I.m))*
      budgetedIterationCharge F I.m L.exponent rate≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate := by
    apply Nat.mul_le_mul_right
    split <;> omega
  omega

theorem epochComplete_runs_with_potential_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K : ℕ)
    (q : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity : ℝ)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024) L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hqbits : q=ipmErrorBits I.m U)
    (hwords : ∀ z∈L.packet F I 0,z<2^w)
    (hi : finish≤I.m)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hE : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base)) :
    let a := Num.IPM.alphaPrime I.m U
    let base := epochVector F I mem L.base
    let space := budgetedIterationSpace F I.m L.exponent B
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let certified := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefix I U target κ r A base finish Q
    ∃ v final cost credit loopEnd st loopCredit,
      Runs w p ω (epochCompleteBody iterations refresh) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost ∧ v<2^w ∧ v≤heap+(finish+1)*space ∧
      EpochCompletePost F A I κ (a/8) rate allocation R L q K heap space finish mem loopEnd st loopCredit
        certified v final credit ∧ (promised → st.mem (loopEnd-1)=1) ∧
      L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) ∧
      cost+R.phi L.handle credit final.mem≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate+
        46*finish+I.m*reportedEdgesCharge F I.m L.exponent rate+200+R.phi L.handle x mem :=
  epochComplete_runs_with_potential_upTo_at F A I U κ target r rate allocation R hA L K q himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    hiterations heap finish B x mem pos ω capacity hstatic halloc hspace hbudgetFit hOne hfinish hpre
    hbudget hcache hranges hqbits hwords hi hsource hE hm hU hsize hnums hFlo hκ hκ' hxlo hres hr hf
    hroute

/-- The complete call runs from the initialized numerical input. Its
result contains the exact history and retains the analytic prefix
certificate when the target and initial potential satisfy the promise. -/
theorem epochComplete_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (L : EpochLayout) (K : ℕ)
    (q : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity : ℝ)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024) L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hqbits : q=ipmErrorBits I.m U)
    (hwords : ∀ z∈L.packet F I 0,z<2^w)
    (hi : finish≤I.m)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hE : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base)) :
    let a := Num.IPM.alphaPrime I.m U
    let base := epochVector F I mem L.base
    let space := budgetedIterationSpace F I.m L.exponent B
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let certified := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefix I U target κ r A base finish Q
    ∃ v final cost credit loopEnd st loopCredit,
      Runs w p ω (epochCompleteBody iterations refresh) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost ∧ v<2^w ∧ v≤heap+(finish+1)*space ∧
      EpochCompletePost F A I κ (a/8) rate allocation R L q K heap space finish mem loopEnd st loopCredit
        certified v final credit ∧ (promised → st.mem (loopEnd-1)=1) ∧
      L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) ∧
      cost+R.phi L.handle credit final.mem≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate+
        46*finish+I.m*reportedEdgesCharge F I.m L.exponent rate+200+R.phi L.handle x mem :=
  epochComplete_runs_with_potential_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n)
    L K q himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord
    hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked
    hbudgetRecord hbody hiterations heap finish B x mem pos ω capacity hstatic halloc hspace
    hbudgetFit hOne hfinish hpre hbudget hcache hranges hqbits hwords hi hsource hE hm hU hsize
    hnums hFlo hκ hκ' hxlo hres hr hf hroute

/-- The complete call runs from the initialized numerical input. Its
result contains the exact history and retains the analytic prefix
certificate when the target and initial potential satisfy the promise. -/
theorem epochComplete_runs_with_potential_widened_upTo_on_at {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K : ℕ)
    (q : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation initPre))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity : ℝ)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024) L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (hwords : ∀ z∈L.packet F I 0,z<2^w)
    (hi : finish≤I.m)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hE : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base)) :
    let a := Num.IPM.alphaPrime I.m U
    let base := epochVector F I mem L.base
    let space := budgetedIterationSpace F I.m L.exponent B
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let certified := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base finish Q
    ∃ v final cost credit loopEnd st loopCredit,
      Runs w p ω (epochCompleteBody iterations refresh) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost ∧ v<2^w ∧ v≤heap+(finish+1)*space ∧
      EpochCompletePost F A I κ (a/8) rate allocation R L q K heap space finish mem loopEnd st loopCredit
        certified v final credit ∧ (promised → st.mem (loopEnd-1)=1) ∧
      L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) ∧
      cost+R.phi L.handle credit final.mem≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate+
        46*finish+I.m*reportedEdgesCharge F I.m L.exponent rate+200+R.phi L.handle x mem := by
  dsimp only
  subst q
  let a := Num.IPM.alphaPrime I.m U
  let q := ipmQualityErrorBits I.m U k
  let space := budgetedIterationSpace F I.m L.exponent B
  let base := epochVector F I mem L.base
  let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
    potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
  let cert := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base finish Q
  have hWide : ipmRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  obtain ⟨P,loopEnd,st,c,loopCredit,hloop,hmem,hheap,_,htrace,hword,hcost⟩ :=
    epochIterations_runs_at_range_upTo_on_at F A I U (ipmQualityRangeExponent I.m U k) κ (a/8) _ _ rate allocation R hA hPG L q K
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
      hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
      heap finish B x mem pos ω capacity _ hWide hstatic halloc hspace hbudgetFit hOne hfinish hi hpre hbudget hcache hranges
  obtain ⟨hpromise,hcert⟩ := epoch_complete_trace_widened_upTo_on F A I U k κ target r rate allocation R hA hPG L K heap space
    finish loopEnd P st loopCredit capacity mem hi hstatic hsource hE hm hU hsize hnums hFlo hκ hκ' hxlo
    hres hr hf hroute hmem hheap hbudget htrace
  have hcallTrace : if st.mem (loopEnd-1)=1 then
      ∃ Q : EpochPoint R.τ,EpochConditions F A I κ (a/8) rate allocation R L q K mem heap space finish finish Q ∧
        loopCredit=Q.credit ∧ cert Q ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem loopEnd st.mem ∧
        R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) loopCredit st.mem
      else st.mem (loopEnd-1)=0 := by
    by_cases hb : st.mem (loopEnd-1)=1
    · simpa only [ite_eq_left hb] using hcert
    · exact ite_eq_right hb ▸ (ite_eq_right hb ▸ hcert).1
  obtain ⟨v,final,cost,credit,hrun,hv,hpost,hcreditCost⟩ := epochComplete_runs_of_loop_at F A I κ (a/8)
    rate allocation R L q K heap space finish loopEnd c mem pos ω st loopCredit cert himpl hstore hquery
    hcoefficient hflag hedge hrefresh hiterations hloop hwords hOne hword hcallTrace
  have hstopped := fun hb => (ite_eq_right hb ▸ hcert).2
  obtain ⟨hLo,hbit,hz,hframe⟩ := epochComplete_output_frame F A I κ (a/8) rate allocation R L q K heap space
    finish loopEnd mem st loopCredit cert hpost hstopped
  have hEnd := epochComplete_end_le F A I κ (a/8) rate allocation R L q K heap B finish loopEnd mem
    st loopCredit cert halloc hpost hstopped
  refine ⟨v,final,cost,credit,loopEnd,st,loopCredit,hrun,hv,hEnd,hpost,hpromise,hLo,hbit,hz,hframe,?_⟩
  have hmul : (5*I.m+finish+(if st.mem (loopEnd-1)=1 then 0 else I.m))*
      budgetedIterationCharge F I.m L.exponent rate≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate := by
    apply Nat.mul_le_mul_right
    split <;> omega
  omega

theorem epochComplete_runs_with_potential_widened_upTo_on {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K : ℕ)
    (q : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity : ℝ)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024) L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (hwords : ∀ z∈L.packet F I 0,z<2^w)
    (hi : finish≤I.m)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hE : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base)) :
    let a := Num.IPM.alphaPrime I.m U
    let base := epochVector F I mem L.base
    let space := budgetedIterationSpace F I.m L.exponent B
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let certified := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base finish Q
    ∃ v final cost credit loopEnd st loopCredit,
      Runs w p ω (epochCompleteBody iterations refresh) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost ∧ v<2^w ∧ v≤heap+(finish+1)*space ∧
      EpochCompletePost F A I κ (a/8) rate allocation R L q K heap space finish mem loopEnd st loopCredit
        certified v final credit ∧ (promised → st.mem (loopEnd-1)=1) ∧
      L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) ∧
      cost+R.phi L.handle credit final.mem≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate+
        46*finish+I.m*reportedEdgesCharge F I.m L.exponent rate+200+R.phi L.handle x mem :=
  epochComplete_runs_with_potential_widened_upTo_on_at F A I U k κ target r rate allocation R hA hPG
    L K q himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    hiterations heap finish B x mem pos ω capacity hstatic halloc hspace hbudgetFit hOne hfinish hpre
    hbudget hcache hranges hqbits hwords hi hsource hE hm hU hsize hnums hFlo hκ hκ' hxlo hres hr hf
    hroute

/-- The complete call runs from the initialized numerical input. Its
result contains the exact history and retains the analytic prefix
certificate when the target and initial potential satisfy the promise. -/
theorem epochComplete_runs_with_potential_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K : ℕ)
    (q : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity : ℝ)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024) L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (hwords : ∀ z∈L.packet F I 0,z<2^w)
    (hi : finish≤I.m)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hE : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base)) :
    let a := Num.IPM.alphaPrime I.m U
    let base := epochVector F I mem L.base
    let space := budgetedIterationSpace F I.m L.exponent B
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I a target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let certified := fun Q : EpochPoint R.τ => promised → EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base finish Q
    ∃ v final cost credit loopEnd st loopCredit,
      Runs w p ω (epochCompleteBody iterations refresh) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) final cost ∧ v<2^w ∧ v≤heap+(finish+1)*space ∧
      EpochCompletePost F A I κ (a/8) rate allocation R L q K heap space finish mem loopEnd st loopCredit
        certified v final credit ∧ (promised → st.mem (loopEnd-1)=1) ∧
      L.flow≤v ∧ final.mem (v-1)≤1 ∧ ZeroFrom final.mem v ∧ (∀ z<L.flow,final.mem z=mem z) ∧
      cost+R.phi L.handle credit final.mem≤(6*I.m+finish)*budgetedIterationCharge F I.m L.exponent rate+
        46*finish+I.m*reportedEdgesCharge F I.m L.exponent rate+200+R.phi L.handle x mem :=
  epochComplete_runs_with_potential_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L K q himpl hrawDetect hdetect hstore hquery hcoefficient
    hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
    hreportBody hreport hchecked hbudgetRecord hbody hiterations heap finish B x mem pos ω capacity
    hstatic halloc hspace hbudgetFit hOne hfinish hpre hbudget hcache hranges hqbits hwords hi
    hsource hE hm hU hsize hnums hFlo hκ hκ' hxlo hres hr hf hroute

end MinCostFlow.IPM.Machine
