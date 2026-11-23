module

public import MinCostFlow.IPM.Machine.TargetEpochContinuation

/-!
# V-passing target-epoch continuations

Wrappers around `TargetEpochContinuation` for the `V`-passing
`minRatioMachineContractWithV` startup interface.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 800000 in
/-- `V`-passing variant of `targetEpoch_continuation_runs_upTo`. -/
theorem targetEpoch_continuation_runs_withV_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U V : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBodyWithV initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBodyWithV refreshArrays fullScan initNames flag))
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hVreg : checked.regs 29=V) (hVword : V<2^w)
    (hH : checked.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hLarge : 2<epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source oldHeap,z<2^w)
    (hframe : ∀ z<oldHeap,checked.mem z=mem z)
    (hqbits : q=ipmErrorBits I.m U)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : oldHeap+targetStageSpace F I.m old.exponent B<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U) (hI : I.IsValid)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hfixed : TargetFixedInputs F I old tp qp oldHeap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hfmt : F.rangeExponent=ipmRangeExponent I.m U)
    (hprecision : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(Num.IPM.alphaPrime I.m U/8))
    (hNormLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤(25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50)
    (hNormHi : (25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50≤(2:ℝ)^F.rangeExponent)
    (hR : ScalarAt checked.mem (oldHeap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r)
    (hcopy : ∀ e : Fin I.m,ScalarAt checked.mem (epochResidualEnd I.m F.limbs oldHeap+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e))
    (hcoefficientPre : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) 0
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) checked.mem) :
    ∃ out final cost,
      Runs w p ω (targetEpochBranchWithV startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate := by
  refine targetEpoch_continuation_of_startup_upTo F A I U κ target r rate (allocationWithV V allocation) R hA
    (minRatioImplements_allocationWithV R V himpl)
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord
    hbody hiterations hcomplete hstatusRecord old tp qp source oldHeap B checked mem ω hregs hF hH
    hLarge hwords hframe hqbits (allocationWithV_le V halloc) hspace hFiveM hEight hE hm hU hsize
    hnums hI hLower hFlo hκ hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision hquality hNormLo
    hNormHi hR hcopy hcoefficientPre (targetEpochInitWithV startup)
    (targetEpochBranchWithV startup complete statusRecord)
    (fun after out final c₁ c₂ hInit hTail =>
      targetEpochBranchWithV_continue_runs hH (by omega) (by omega) hInit hTail) ?_
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := fp+I.m*F.limbs
  let space := budgetedIterationSpace F I.m old.exponent B
  let startSpace := epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)
  have hsplit : heap+startSpace+I.m+4+(I.m+1)*space+2≤oldHeap+targetStageSpace F I.m old.exponent B :=
    targetStage_space_split F I old oldHeap B (allocationWithV V allocation) (allocationWithV_le V halloc)
  have hbound : heap+startSpace+I.m+4+(I.m+1)*space+2<2^w := hsplit.trans_lt hspace
  have hfp : oldHeap≤fp := Nat.le_add_right _ _
  have hfpHeap : fp≤heap := Nat.le_add_right _ _
  have hRend : rp+F.limbs=fp := by
    simp [rp,fp,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hfpWord : fp<2^w := by omega
  have hrpWord : rp<2^w := by omega
  have hHeapWord : heap<2^w := by omega
  have hchecked := hfixed.frozen hframe hfp
  exact targetEpoch_startup_call_withV F A I V κ (Num.IPM.alphaPrime I.m U/8) rate allocation R himpl hrefreshArrays
    hfullScan hinit hinitNames hnames hinitBudget hflag hstartup old tp qp source oldHeap checked ω
    hregs hF hVreg hVword hH
    (targetEpoch_startup_words F I old tp qp source oldHeap rp fp heap 0 hwords hrpWord hfpWord hHeapWord)
    hI hchecked.graph hchecked.graphWordsFit (hchecked.graphEnd.trans hfpHeap)
    hquality hprecision hcoefficientPre (by omega) hFiveM (show heap+startSpace+I.m+4<2^w by omega)
    ((hchecked.scalars old.gradientMin (by simp)).trans hfpHeap)
    ((hchecked.scalars old.gradientMax (by simp)).trans hfpHeap)
    ((hchecked.scalars old.lengthMin (by simp)).trans hfpHeap)
    hchecked.gradientMin hchecked.gradientMax hchecked.lengthMin

/-- `V`-passing variant of `targetEpoch_continuation_runs`. -/
theorem targetEpoch_continuation_runs_withV {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U V : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBodyWithV initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBodyWithV refreshArrays fullScan initNames flag))
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hVreg : checked.regs 29=V) (hVword : V<2^w)
    (hH : checked.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hLarge : 2<epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source oldHeap,z<2^w)
    (hframe : ∀ z<oldHeap,checked.mem z=mem z)
    (hqbits : q=ipmErrorBits I.m U)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : oldHeap+targetStageSpace F I.m old.exponent B<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U) (hI : I.IsValid)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hfixed : TargetFixedInputs F I old tp qp oldHeap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hfmt : F.rangeExponent=ipmRangeExponent I.m U)
    (hprecision : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(Num.IPM.alphaPrime I.m U/8))
    (hNormLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤(25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50)
    (hNormHi : (25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50≤(2:ℝ)^F.rangeExponent)
    (hR : ScalarAt checked.mem (oldHeap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r)
    (hcopy : ∀ e : Fin I.m,ScalarAt checked.mem (epochResidualEnd I.m F.limbs oldHeap+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e))
    (hcoefficientPre : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) 0
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) checked.mem) :
    ∃ out final cost,
      Runs w p ω (targetEpochBranchWithV startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate :=
  targetEpoch_continuation_runs_withV_upTo F A I U V κ target r rate allocation R (hA.upTo I.m I.n)
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord
    hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames
    hinitBudget hstartup old tp qp source oldHeap B checked mem ω hregs hF hVreg hVword hH
    hLarge hwords hframe hqbits halloc hspace hFiveM hEight hE hm hU hsize hnums hI hLower hFlo hκ
    hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision hquality hNormLo hNormHi hR hcopy
    hcoefficientPre

set_option maxHeartbeats 800000 in
/-- `V`-passing variant of `targetEpoch_continuation_runs_widened_upTo_on`. -/
theorem targetEpoch_continuation_runs_withV_widened_upTo_on {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k V : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBodyWithV initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBodyWithV refreshArrays fullScan initNames flag))
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hVreg : checked.regs 29=V) (hVword : V<2^w)
    (hH : checked.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hLarge : 2<epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source oldHeap,z<2^w)
    (hframe : ∀ z<oldHeap,checked.mem z=mem z)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : oldHeap+targetStageSpace F I.m old.exponent B<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U) (hI : I.IsValid)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hfixed : TargetFixedInputs F I old tp qp oldHeap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hfmt : F.rangeExponent=ipmQualityRangeExponent I.m U k)
    (hprecision : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(Num.IPM.alphaPrime I.m U/8))
    (hNormLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤(25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50)
    (hNormHi : (25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50≤(2:ℝ)^F.rangeExponent)
    (hR : ScalarAt checked.mem (oldHeap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r)
    (hcopy : ∀ e : Fin I.m,ScalarAt checked.mem (epochResidualEnd I.m F.limbs oldHeap+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e))
    (hcoefficientPre : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) 0
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) checked.mem) :
    ∃ out final cost,
      Runs w p ω (targetEpochBranchWithV startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate := by
  refine targetEpoch_continuation_of_startup_widened_upTo_on F A I U k κ target r rate
    (allocationWithV V allocation) R hA hP (minRatioImplements_allocationWithV R V himpl)
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord
    hbody hiterations hcomplete hstatusRecord old tp qp source oldHeap B checked mem ω hregs hF hH
    hLarge hwords hframe hqbits (allocationWithV_le V halloc) hspace hFiveM hEight hE hm hU hsize
    hnums hI hLower hFlo hκ hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision hquality hNormLo
    hNormHi hR hcopy hcoefficientPre (targetEpochInitWithV startup)
    (targetEpochBranchWithV startup complete statusRecord)
    (fun after out final c₁ c₂ hInit hTail =>
      targetEpochBranchWithV_continue_runs hH (by omega) (by omega) hInit hTail) ?_
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := fp+I.m*F.limbs
  let space := budgetedIterationSpace F I.m old.exponent B
  let startSpace := epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)
  have hsplit : heap+startSpace+I.m+4+(I.m+1)*space+2≤oldHeap+targetStageSpace F I.m old.exponent B :=
    targetStage_space_split F I old oldHeap B (allocationWithV V allocation) (allocationWithV_le V halloc)
  have hbound : heap+startSpace+I.m+4+(I.m+1)*space+2<2^w := hsplit.trans_lt hspace
  have hfp : oldHeap≤fp := Nat.le_add_right _ _
  have hfpHeap : fp≤heap := Nat.le_add_right _ _
  have hRend : rp+F.limbs=fp := by
    simp [rp,fp,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hfpWord : fp<2^w := by omega
  have hrpWord : rp<2^w := by omega
  have hHeapWord : heap<2^w := by omega
  have hchecked := hfixed.frozen hframe hfp
  exact targetEpoch_startup_call_withV F A I V κ (Num.IPM.alphaPrime I.m U/8) rate allocation R himpl hrefreshArrays
    hfullScan hinit hinitNames hnames hinitBudget hflag hstartup old tp qp source oldHeap checked ω
    hregs hF hVreg hVword hH
    (targetEpoch_startup_words F I old tp qp source oldHeap rp fp heap 0 hwords hrpWord hfpWord hHeapWord)
    hI hchecked.graph hchecked.graphWordsFit (hchecked.graphEnd.trans hfpHeap)
    hquality hprecision hcoefficientPre (by omega) hFiveM (show heap+startSpace+I.m+4<2^w by omega)
    ((hchecked.scalars old.gradientMin (by simp)).trans hfpHeap)
    ((hchecked.scalars old.gradientMax (by simp)).trans hfpHeap)
    ((hchecked.scalars old.lengthMin (by simp)).trans hfpHeap)
    hchecked.gradientMin hchecked.gradientMax hchecked.lengthMin

/-- `V`-passing variant of `targetEpoch_continuation_runs_widened_upTo`. -/
theorem targetEpoch_continuation_runs_withV_widened_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k V : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ (Num.IPM.alphaPrime I.m U/8) rate allocation))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBodyWithV initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBodyWithV refreshArrays fullScan initNames flag))
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hVreg : checked.regs 29=V) (hVword : V<2^w)
    (hH : checked.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hLarge : 2<epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source oldHeap,z<2^w)
    (hframe : ∀ z<oldHeap,checked.mem z=mem z)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : oldHeap+targetStageSpace F I.m old.exponent B<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U) (hI : I.IsValid)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hfixed : TargetFixedInputs F I old tp qp oldHeap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hfmt : F.rangeExponent=ipmQualityRangeExponent I.m U k)
    (hprecision : 5*F.rangeExponent+I.m.size+30≤F.fmt.precision)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(Num.IPM.alphaPrime I.m U/8))
    (hNormLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤(25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50)
    (hNormHi : (25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50≤(2:ℝ)^F.rangeExponent)
    (hR : ScalarAt checked.mem (oldHeap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r)
    (hcopy : ∀ e : Fin I.m,ScalarAt checked.mem (epochResidualEnd I.m F.limbs oldHeap+e.val*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e))
    (hcoefficientPre : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) 0
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) checked.mem) :
    ∃ out final cost,
      Runs w p ω (targetEpochBranchWithV startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate :=
  targetEpoch_continuation_runs_withV_widened_upTo_on F A I U k V κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) himpl hrawDetect hdetect hstore hquery hcoefficient
    hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
    hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup old tp qp source
    oldHeap B checked mem ω hregs hF hVreg hVword hH hLarge hwords hframe hqbits halloc hspace
    hFiveM hEight hE hm hU hsize hnums hI hLower hFlo hκ hκ' hxlo ha ha' hres hr hflow hfixed
    hfmt hprecision hquality hNormLo hNormHi hR hcopy hcoefficientPre

end MinCostFlow.IPM.Machine
