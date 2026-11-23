module

public import MinCostFlow.IPM.Machine.TargetTestProgram
public import MinCostFlow.IPM.Machine.TargetOffsetTestRun

/-!
# The complete target comparison used by bisection

A freshly written target block fits at the chosen precision. The
same initialized half-slack flow is used for every comparison,
and the bounded IPM test uses its verified stage procedure.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Workspace added by one encoded target test. -/
def targetOffsetSpace {w : ℕ} (F : MinRatioFormat w) (m U k E B : ℕ) : ℕ :=
  3*F.limbs+targetTestLimit m U k*targetStageSpace F m E B+2

/-- Cost of an encoded target test including its exact integer load. -/
def targetOffsetCost {w : ℕ} (F : MinRatioFormat w) (m U k E : ℕ) (rate : ℕ → ℕ) : ℕ :=
  targetTestLimit m U k*(epochBaseCost m F.limbs+targetStageContinuationCost F m E rate+140)+
    100*F.limbs+350

private theorem targetOffset_forward_words {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (offset qp source heap limit radius tp next : ℕ)
    (hWords : ∀ z∈targetOffsetPacket L F I offset qp source heap limit radius,z<2^w)
    (ht : tp<2^w) (hh : next<2^w) :
    ∀ z∈targetEpochPacket L F I tp qp source next,z<2^w := by
  intro z hz
  simp only [targetEpochPacket,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ht | exact hh | exact hWords _ (by simp [targetOffsetPacket,targetEpochPacket])

set_option maxHeartbeats 600000 in
/-- Verify one machine comparison at a numerically bounded unsigned
offset. Its exact test decision and returned flow follow from all
executed stages at the chosen precision. -/
theorem targetOffsetTest_runs_upTo {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBody epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBody guess test)
        (startState (targetOffsetPacket old F I offset qp source heap limit radius) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate := by
  let radius := I.m*U^2
  let value := offsetTarget radius offset
  let limit := targetTestLimit I.m U k
  let space := limit*targetStageSpace F I.m old.exponent B+2
  let price := limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50
  obtain ⟨hbounded,hfits,hscaled⟩ := offsetTarget_precision I.m U offset hm hU hOffset
  have hspace' : heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)<2^w := hspace
  have hEncodeSpace : heap+3*F.limbs<2^w := by omega
  have hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem :=
    by
      rw [hF]
      exact targetGuess_pre_of_fits hfits hscaled hz (hF ▸ hEncodeSpace)
  obtain ⟨v,final,c,hRun,hresult,hend,hcost⟩ := targetOffsetTest_runs_of_test F I U old offset qp source heap
    limit radius space price mem pos ω hGuess hTest hwords hpre hEncodeSpace hflow hhalf hm hU hsize hnums
    (abs_le.mp hbounded).1 fstar z hstar hzOpt (by
      intro st tp next htp hnext hframe hzero htarget
      have hle : heap≤next := by omega
      have hFit : next+space<2^w := by change next+(limit*targetStageSpace F I.m old.exponent B+2)<2^w; omega
      have htpFit : tp<2^w := by omega
      have hnextFit : next<2^w := by omega
      have hFixed := (hfixed.frozen hframe hle).retarget (show tp+F.limbs≤next by omega) htarget
      have hFlow := hflow.frozen hframe hle
      have hWords := targetOffset_forward_words F I old offset qp source heap limit radius tp next hwords htpFit hnextFit
      exact targetTest_runs_upTo I U k hw A rate allocation R F q K κ hA hbase himpl hrawDetect hdetect hstore hquery
        hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
        hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
        hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch
        old tp qp source next B st.mem st.pos ω value hF hq hK hκ hE hFixed hFlow hWords halloc
        hLimit hFit hzero hm hU hsize hk hI hnums hLower hbounded)
  refine ⟨v,final,c,hRun,hresult,?_,?_⟩
  · change v≤heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)
    change v≤heap+3*F.limbs+(limit*targetStageSpace F I.m old.exponent B+2) at hend
    omega
  · change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140)+
      100*F.limbs+350
    change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50+
      100*F.limbs+300 at hcost
    have heq : epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59=
        epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140 := by
      omega
    rw [heq] at hcost
    omega

/-- Verify one machine comparison at a numerically bounded unsigned
offset. Its exact test decision and returned flow follow from all
executed stages at the chosen precision. -/
theorem targetOffsetTest_runs {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBody epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBody guess test)
        (startState (targetOffsetPacket old F I offset qp source heap limit radius) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate :=
  targetOffsetTest_runs_upTo I U k hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess old qp source heap B
    offset mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hOffset halloc hLimit hspace hz hm
    hU hsize hk hI hnums hLower fstar z hstar hzOpt

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- Verify one machine comparison at a numerically bounded unsigned
offset. Its exact test decision and returned flow follow from all
executed stages at the chosen precision. -/
theorem targetOffsetTest_runs_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBody epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBody guess test)
        (startState (targetOffsetPacket old F I offset qp source heap limit radius) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate := by
  let radius := I.m*U^2
  let value := offsetTarget radius offset
  let limit := targetTestLimit I.m U k
  let space := limit*targetStageSpace F I.m old.exponent B+2
  let price := limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50
  have hbounded := (offsetTarget_precision I.m U offset hm hU hOffset).1
  have hExp : slackRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmQualityRangeExponent
    omega
  have hRad : (I.m:ℝ)*(U:ℝ)^2 ≤ (2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
    have hDouble := twice_search_radius_le_dyadic I.m U hm hU
    have hPow : (2:ℝ)^(slackRangeExponent I.m U)≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) :=
      pow_le_pow_right₀ (by norm_num) hExp
    have hPos : (0:ℝ)≤(I.m:ℝ)*(U:ℝ)^2 := by positivity
    linarith only [hDouble,hPow,hPos]
  obtain ⟨hfits,hscaled⟩ := fits_integer_at_quality_precision I.m U k (offsetTarget radius offset)
    (hbounded.trans hRad)
  have hspace' : heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)<2^w := hspace
  have hEncodeSpace : heap+3*F.limbs<2^w := by omega
  have hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem :=
    by
      rw [hF]
      exact targetGuess_pre_of_fits hfits hscaled hz (hF ▸ hEncodeSpace)
  obtain ⟨v,final,c,hRun,hresult,hend,hcost⟩ := targetOffsetTest_runs_of_test F I U old offset qp source heap
    limit radius space price mem pos ω hGuess hTest hwords hpre hEncodeSpace hflow hhalf hm hU hsize hnums
    (abs_le.mp hbounded).1 fstar z hstar hzOpt (by
      intro st tp next htp hnext hframe hzero htarget
      have hle : heap≤next := by omega
      have hFit : next+space<2^w := by change next+(limit*targetStageSpace F I.m old.exponent B+2)<2^w; omega
      have htpFit : tp<2^w := by omega
      have hnextFit : next<2^w := by omega
      have hFixed := (hfixed.frozen hframe hle).retarget (show tp+F.limbs≤next by omega) htarget
      have hFlow := hflow.frozen hframe hle
      have hWords := targetOffset_forward_words F I old offset qp source heap limit radius tp next hwords htpFit hnextFit
      exact targetTest_runs_widened_upTo_on I U k hw A rate allocation R F q K κ hA hP hbase himpl hrawDetect hdetect hstore hquery
        hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
        hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
        hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch
        old tp qp source next B st.mem st.pos ω value hF hq hK hκ hE hFixed hFlow hWords halloc
        hLimit hFit hzero hm hU hsize hI hnums hLower hbounded)
  refine ⟨v,final,c,hRun,hresult,?_,?_⟩
  · change v≤heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)
    change v≤heap+3*F.limbs+(limit*targetStageSpace F I.m old.exponent B+2) at hend
    omega
  · change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140)+
      100*F.limbs+350
    change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50+
      100*F.limbs+300 at hcost
    have heq : epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59=
        epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140 := by
      omega
    rw [heq] at hcost
    omega

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- Verify one machine comparison at a numerically bounded unsigned
offset. Its exact test decision and returned flow follow from all
executed stages at the chosen precision. -/
theorem targetOffsetTest_runs_widened_upTo {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBody epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBody guess test)
        (startState (targetOffsetPacket old F I offset qp source heap limit radius) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate :=
  targetOffsetTest_runs_widened_upTo_on I U k hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess
    old qp source heap B offset mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hOffset halloc
    hLimit hspace hz hm hU hsize hI hnums hLower fstar z hstar hzOpt

/-- `V`-passing variant of `targetOffsetTest_runs_upTo`. -/
theorem targetOffsetTest_runs_withV_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBodyWithV epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBodyWithV guess test)
        (startState (targetOffsetPacketWithV old F I offset qp source heap limit radius V) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate := by
  let radius := I.m*U^2
  let value := offsetTarget radius offset
  let limit := targetTestLimit I.m U k
  let space := limit*targetStageSpace F I.m old.exponent B+2
  let price := limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50
  obtain ⟨hbounded,hfits,hscaled⟩ := offsetTarget_precision I.m U offset hm hU hOffset
  have hspace' : heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)<2^w := hspace
  have hEncodeSpace : heap+3*F.limbs<2^w := by omega
  have hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem :=
    by
      rw [hF]
      exact targetGuess_pre_of_fits hfits hscaled hz (hF ▸ hEncodeSpace)
  obtain ⟨v,final,c,hRun,hresult,hend,hcost⟩ := targetOffsetTestWithV_runs_of_test F I U V old offset qp source heap
    limit radius space price mem pos ω hGuess hTest hwords hV hpre hEncodeSpace hflow hhalf hm hU hsize hnums
    (abs_le.mp hbounded).1 fstar z hstar hzOpt (by
      intro st tp next htp hnext hframe hzero htarget
      have hle : heap≤next := by omega
      have hFit : next+space<2^w := by change next+(limit*targetStageSpace F I.m old.exponent B+2)<2^w; omega
      have htpFit : tp<2^w := by omega
      have hnextFit : next<2^w := by omega
      have hFixed := (hfixed.frozen hframe hle).retarget (show tp+F.limbs≤next by omega) htarget
      have hFlow := hflow.frozen hframe hle
      have hWords := targetOffset_forward_words F I old offset qp source heap limit radius tp next hwords htpFit hnextFit
      exact targetTest_runs_withV_upTo I U k V hw A rate allocation R F q K κ hA hbase himpl hrawDetect hdetect hstore hquery
        hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
        hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
        hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch
        old tp qp source next B st.mem st.pos ω value hF hq hK hκ hE hFixed hFlow hWords hV halloc
        hLimit hFit hzero hm hU hsize hk hI hnums hLower hbounded)
  refine ⟨v,final,c,hRun,hresult,?_,?_⟩
  · change v≤heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)
    change v≤heap+3*F.limbs+(limit*targetStageSpace F I.m old.exponent B+2) at hend
    omega
  · change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140)+
      100*F.limbs+350
    change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50+
      100*F.limbs+300 at hcost
    have heq : epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59=
        epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140 := by
      omega
    rw [heq] at hcost
    omega

/-- `V`-passing variant of `targetOffsetTest_runs`. -/
theorem targetOffsetTest_runs_withV {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBodyWithV epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBodyWithV guess test)
        (startState (targetOffsetPacketWithV old F I offset qp source heap limit radius V) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate :=
  targetOffsetTest_runs_withV_upTo I U k V hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess old qp source heap B
    offset mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hV hOffset halloc hLimit hspace hz hm
    hU hsize hk hI hnums hLower fstar z hstar hzOpt

/-- `V`-passing variant of `targetOffsetTest_runs_widened_upTo_on`. -/
theorem targetOffsetTest_runs_withV_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBodyWithV epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBodyWithV guess test)
        (startState (targetOffsetPacketWithV old F I offset qp source heap limit radius V) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate := by
  let radius := I.m*U^2
  let value := offsetTarget radius offset
  let limit := targetTestLimit I.m U k
  let space := limit*targetStageSpace F I.m old.exponent B+2
  let price := limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50
  have hbounded := (offsetTarget_precision I.m U offset hm hU hOffset).1
  have hExp : slackRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmQualityRangeExponent
    omega
  have hRad : (I.m:ℝ)*(U:ℝ)^2 ≤ (2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
    have hDouble := twice_search_radius_le_dyadic I.m U hm hU
    have hPow : (2:ℝ)^(slackRangeExponent I.m U)≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) :=
      pow_le_pow_right₀ (by norm_num) hExp
    have hPos : (0:ℝ)≤(I.m:ℝ)*(U:ℝ)^2 := by positivity
    linarith only [hDouble,hPow,hPos]
  obtain ⟨hfits,hscaled⟩ := fits_integer_at_quality_precision I.m U k (offsetTarget radius offset)
    (hbounded.trans hRad)
  have hspace' : heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)<2^w := hspace
  have hEncodeSpace : heap+3*F.limbs<2^w := by omega
  have hpre : (targetGuessContract w F.fmt.limbBits).pre [offset,radius,F.limbs,F.fmt.precision,heap] mem :=
    by
      rw [hF]
      exact targetGuess_pre_of_fits hfits hscaled hz (hF ▸ hEncodeSpace)
  obtain ⟨v,final,c,hRun,hresult,hend,hcost⟩ := targetOffsetTestWithV_runs_of_test F I U V old offset qp source heap
    limit radius space price mem pos ω hGuess hTest hwords hV hpre hEncodeSpace hflow hhalf hm hU hsize hnums
    (abs_le.mp hbounded).1 fstar z hstar hzOpt (by
      intro st tp next htp hnext hframe hzero htarget
      have hle : heap≤next := by omega
      have hFit : next+space<2^w := by change next+(limit*targetStageSpace F I.m old.exponent B+2)<2^w; omega
      have htpFit : tp<2^w := by omega
      have hnextFit : next<2^w := by omega
      have hFixed := (hfixed.frozen hframe hle).retarget (show tp+F.limbs≤next by omega) htarget
      have hFlow := hflow.frozen hframe hle
      have hWords := targetOffset_forward_words F I old offset qp source heap limit radius tp next hwords htpFit hnextFit
      exact targetTest_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ hA hP hbase himpl
        hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
        hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
        hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget
        hstartup hEpoch old tp qp source next B st.mem st.pos ω value hF hq hK hκ hE hFixed hFlow
        hWords hV halloc hLimit hFit hzero hm hU hsize hI hnums hLower hbounded)
  refine ⟨v,final,c,hRun,hresult,?_,?_⟩
  · change v≤heap+(3*F.limbs+limit*targetStageSpace F I.m old.exponent B+2)
    change v≤heap+3*F.limbs+(limit*targetStageSpace F I.m old.exponent B+2) at hend
    omega
  · change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140)+
      100*F.limbs+350
    change c≤limit*(epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59)+50+
      100*F.limbs+300 at hcost
    have heq : epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81+59=
        epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+140 := by
      omega
    rw [heq] at hcost
    omega

/-- `V`-passing variant of `targetOffsetTest_runs_widened_upTo`. -/
theorem targetOffsetTest_runs_withV_widened_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hTest : p.procs[test]?=some (targetTestBodyWithV epoch statusRecord))
    (hGuess : MeetsContract w p guess (targetGuessContract w F.fmt.limbBits))
    (old : EpochLayout) (qp source heap B offset : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I offset qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hOffset : offset≤2*(I.m*U^2))
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetOffsetSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (fstar : Fin I.m → ℝ) (z : ℤ) (hstar : I.IsMinCostFlow fstar) (hzOpt : I.cost fstar=(z:ℝ)) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost,
      Runs w p ω (targetOffsetTestBodyWithV guess test)
        (startState (targetOffsetPacketWithV old F I offset qp source heap limit radius V) mem pos)
        (.returned v) final cost ∧
      TargetOffsetResult F I old.exponent heap v (offsetTarget radius offset) z mem final.mem ∧
      v≤heap+targetOffsetSpace F I.m U k old.exponent B ∧
      cost≤targetOffsetCost F I.m U k old.exponent rate :=
  targetOffsetTest_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess
    old qp source heap B offset mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hV hOffset halloc
    hLimit hspace hz hm hU hsize hI hnums hLower fstar z hstar hzOpt

end MinCostFlow.IPM.Machine
