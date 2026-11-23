module

public import MinCostFlow.IPM.Machine.TargetTestRun
public import MinCostFlow.IPM.Machine.TargetEpochProgram

/-!
# The target test at the selected fixed-point precision

The counted loop uses the verified stage program on its actual
registers, keeping the immutable graph and scalar blocks through
any number of restarts. The terminal result is in the same
fixed-point format as the input.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 500000 in
/-- The actual machine target test for Algorithm 7 (Chen et al.,
arXiv:2203.00671v2, page 69). It returns the first terminal record,
or rejects at exhaustion, within the stated complete stage budget. -/
theorem targetTest_runs_upTo {w : ℕ} (I : Instance) (U k : ℕ)
    (hw : ipmParameterWordBits I.m U≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBody initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBody refreshArrays fullScan initNames flag))
    (hEpoch : p.procs[epoch]?=some (targetEpochBody base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBody epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 := by
  subst κ
  let κ := (1:ℝ)/(2:ℝ)^k
  let space := targetStageSpace F I.m old.exponent B
  let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
  have hTwo : 2<2^w := by
    have hWord := (ipm_parameter_words_fit I.m U hw).1
    exact (by decide : 2<2^14).trans_le (Nat.pow_le_pow_right (by decide) hWord)
  apply targetTest_runs_of_stage F I U k old tp qp source heap space price target mem pos ω
    hEpoch hstatusRecord hTwo hm hsize hwords hLimit hspace hflow hz
  intro st i stream hInv hFit
  obtain ⟨_,_,_,hWords,hheap,_,hFrame,hZero,hFlow,_⟩ := hInv
  have hFixed := hfixed.frozen hFrame hheap
  exact targetEpoch_runs_upTo I U k hw A rate allocation R F q K κ hA
    hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
    hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
    old tp qp (st.regs 20) (st.regs 21) B st.mem st.pos stream target
    hF hq hK rfl hE hFixed hFlow hWords halloc hFit hZero hm hU hsize hk hI hnums hLower hTarget

/-- The actual machine target test for Algorithm 7 (Chen et al.,
arXiv:2203.00671v2, page 69). It returns the first terminal record,
or rejects at exhaustion, within the stated complete stage budget. -/
theorem targetTest_runs {w : ℕ} (I : Instance) (U k : ℕ)
    (hw : ipmParameterWordBits I.m U≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBody initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBody refreshArrays fullScan initNames flag))
    (hEpoch : p.procs[epoch]?=some (targetEpochBody base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBody epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 :=
  targetTest_runs_upTo I U k hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup hEpoch old tp qp source heap B mem pos ω
    target hF hq hK hκ hE hfixed hflow hwords halloc hLimit hspace hz hm hU hsize hk hI hnums
    hLower hTarget

/-- The actual machine target test for Algorithm 7 (Chen et al.,
arXiv:2203.00671v2, page 69). It returns the first terminal record,
or rejects at exhaustion, within the stated complete stage budget. -/
theorem targetTest_runs_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k : ℕ)
    (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBody initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBody refreshArrays fullScan initNames flag))
    (hEpoch : p.procs[epoch]?=some (targetEpochBody base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBody epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 := by
  subst κ
  let κ := (1:ℝ)/(2:ℝ)^k
  let space := targetStageSpace F I.m old.exponent B
  let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
  have hTwo : 2<2^w := by
    have hWord := (ipm_quality_parameter_words_fit I.m U k hw).1
    exact (by decide : 2<2^14).trans_le (Nat.pow_le_pow_right (by decide) hWord)
  apply targetTest_runs_of_stage F I U k old tp qp source heap space price target mem pos ω
    hEpoch hstatusRecord hTwo hm hsize hwords hLimit hspace hflow hz
  intro st i stream hInv hFit
  obtain ⟨_,_,_,hWords,hheap,_,hFrame,hZero,hFlow,_⟩ := hInv
  have hFixed := hfixed.frozen hFrame hheap
  exact targetEpoch_runs_widened_upTo_on I U k hw A rate allocation R F q K κ hA hP
    hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
    hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
    old tp qp (st.regs 20) (st.regs 21) B st.mem st.pos stream target
    hF hq hK rfl hE hFixed hFlow hWords halloc hFit hZero hm hU hsize hI hnums hLower hTarget

/-- The actual machine target test for Algorithm 7 (Chen et al.,
arXiv:2203.00671v2, page 69). It returns the first terminal record,
or rejects at exhaustion, within the stated complete stage budget. -/
theorem targetTest_runs_widened_upTo {w : ℕ} (I : Instance) (U k : ℕ)
    (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hcheckedProc : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (hiterations : p.procs[iterations]?=some (epochIterationsBody iteration flag))
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (hrefreshArrays : MeetsContract w p refreshArrays (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBody initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hinitBudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBody refreshArrays fullScan initNames flag))
    (hEpoch : p.procs[epoch]?=some (targetEpochBody base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBody epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 :=
  targetTest_runs_widened_upTo_on I U k hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch old tp qp source
    heap B mem pos ω target hF hq hK hκ hE hfixed hflow hwords halloc hLimit hspace hz hm hU hsize
    hI hnums hLower hTarget

/-- `V`-passing variant of `targetTest_runs_upTo`. -/
theorem targetTest_runs_withV_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
    (hw : ipmParameterWordBits I.m U≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hEpoch : p.procs[epoch]?=some (targetEpochBodyWithV base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (hV : V<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBodyWithV epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit,V]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 := by
  subst κ
  let κ := (1:ℝ)/(2:ℝ)^k
  let space := targetStageSpace F I.m old.exponent B
  let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
  have hTwo : 2<2^w := by
    have hWord := (ipm_parameter_words_fit I.m U hw).1
    exact (by decide : 2<2^14).trans_le (Nat.pow_le_pow_right (by decide) hWord)
  apply targetTestWithV_runs_of_stage F I U k V old tp qp source heap space price target mem pos ω
    hEpoch hstatusRecord hTwo hm hsize hwords hV hLimit hspace hflow hz
  intro st i stream hInv _ hFit
  obtain ⟨_,_,_,hWords,hheap,_,hFrame,hZero,hFlow,_⟩ := hInv
  have hFixed := hfixed.frozen hFrame hheap
  have hWordsV : ∀ z ∈ targetEpochPacketWithV old F I tp qp (st.regs 20) (st.regs 21) V, z < 2^w := by
    intro z hz
    simp only [targetEpochPacketWithV,List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hWords z hz
    · exact hV
  exact targetEpoch_runs_withV_upTo I U k V hw A rate allocation R F q K κ hA
    hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
    hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
    old tp qp (st.regs 20) (st.regs 21) B st.mem st.pos stream target
    hF hq hK rfl hE hFixed hFlow hWordsV halloc hFit hZero hm hU hsize hk hI hnums hLower hTarget

/-- `V`-passing variant of `targetTest_runs`. -/
theorem targetTest_runs_withV {w : ℕ} (I : Instance) (U k V : ℕ)
    (hw : ipmParameterWordBits I.m U≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hEpoch : p.procs[epoch]?=some (targetEpochBodyWithV base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (hV : V<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBodyWithV epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit,V]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 :=
  targetTest_runs_withV_upTo I U k V hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup hEpoch old tp qp source heap B mem pos ω
    target hF hq hK hκ hE hfixed hflow hwords hV halloc hLimit hspace hz hm hU hsize hk hI hnums
    hLower hTarget

/-- `V`-passing variant of `targetTest_runs_widened_upTo_on`. -/
theorem targetTest_runs_withV_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k V : ℕ)
    (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hEpoch : p.procs[epoch]?=some (targetEpochBodyWithV base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (hV : V<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBodyWithV epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit,V]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 := by
  subst κ
  let κ := (1:ℝ)/(2:ℝ)^k
  let space := targetStageSpace F I.m old.exponent B
  let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
  have hTwo : 2<2^w := by
    have hWord := (ipm_quality_parameter_words_fit I.m U k hw).1
    exact (by decide : 2<2^14).trans_le (Nat.pow_le_pow_right (by decide) hWord)
  apply targetTestWithV_runs_of_stage F I U k V old tp qp source heap space price target mem pos ω
    hEpoch hstatusRecord hTwo hm hsize hwords hV hLimit hspace hflow hz
  intro st i stream hInv _ hFit
  obtain ⟨_,_,_,hWords,hheap,_,hFrame,hZero,hFlow,_⟩ := hInv
  have hFixed := hfixed.frozen hFrame hheap
  have hWordsV : ∀ z ∈ targetEpochPacketWithV old F I tp qp (st.regs 20) (st.regs 21) V, z < 2^w := by
    intro z hz
    simp only [targetEpochPacketWithV,List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hWords z hz
    · exact hV
  exact targetEpoch_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ hA hP
    hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
    hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
    old tp qp (st.regs 20) (st.regs 21) B st.mem st.pos stream target
    hF hq hK rfl hE hFixed hFlow hWordsV halloc hFit hZero hm hU hsize hI hnums hLower hTarget

/-- `V`-passing variant of `targetTest_runs_widened_upTo`. -/
theorem targetTest_runs_withV_widened_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
    (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch startup fullScan initEntry initNames names budget refreshArrays : ℕ}
    {dsop : ℕ → ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
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
    (hEpoch : p.procs[epoch]?=some (targetEpochBodyWithV base startup complete statusRecord))
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (hV : V<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetTestLimit I.m U k*targetStageSpace F I.m old.exponent B+2<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    let limit := targetTestLimit I.m U k
    let space := targetStageSpace F I.m old.exponent B
    let price := epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81
    ∃ v final cost,
      Runs w p ω (targetTestBodyWithV epoch statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap++[limit,V]) mem pos) (.returned v) final cost ∧
      TargetTestResult F I U old.exponent source heap v (target:ℝ) mem final.mem ∧
      v≤heap+limit*space+2 ∧ cost≤limit*(price+59)+50 :=
  targetTest_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch old tp qp source
    heap B mem pos ω target hF hq hK hκ hE hfixed hflow hwords hV halloc hLimit hspace hz hm hU hsize
    hI hnums hLower hTarget

end MinCostFlow.IPM.Machine
