module

public import MinCostFlow.IPM.Machine.TargetSearchRun
public import MinCostFlow.IPM.Machine.TargetOffsetTestProgram
public import MinCostFlow.IPM.IntegralOptimum
import Mathlib.Tactic.Linarith
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Machine binary search at the selected IPM precision

The original feasible half-slack flow and all immutable tables
remain available for each new signed target. The integer optimum
bounds the bracket. The final test produces a fixed-point flow
within a quarter of that optimum.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Full bisection space, including the final fresh target test. -/
def targetSearchSpace {w : ℕ} (F : MinRatioFormat w) (m U k E B : ℕ) : ℕ :=
  (targetSearchRounds (m*U^2)+1)*targetOffsetSpace F m U k E B

/-- All bisection work, including every restarted test. -/
def targetSearchCost {w : ℕ} (F : MinRatioFormat w) (m U k E : ℕ) (rate : ℕ → ℕ) : ℕ :=
  (targetSearchRounds (m*U^2)+1)*(targetOffsetCost F m U k E rate+69)

set_option maxHeartbeats 550000 in
/-- The integer-cost search runs over the full inclusive cost interval.
Its output points at an exact fixed-point flow within a quarter of the
integer optimum. The time and space include all independent target runs. -/
theorem targetSearch_runs_upTo {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBody guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBody offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate := by
  dsimp only
  let limit := targetTestLimit I.m U k
  let radius := I.m*U^2
  let space := targetOffsetSpace F I.m U k old.exponent B
  let price := targetOffsetCost F I.m U k old.exponent rate
  obtain ⟨fstar,hstar,hint⟩ := exists_integral_minCostFlow I hI ⟨_,hflow.2.1⟩
  obtain ⟨z,hCostOpt⟩ := integral_cost I fstar hint
  have hopt := feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums fstar hstar.1
  rw [hCostOpt] at hopt
  have hRadiusReal : |(z:ℝ)|≤(radius:ℝ) := by
    simpa only [radius,Nat.cast_mul,Nat.cast_pow] using hopt
  have hlo : -(radius:ℤ)≤z := by exact_mod_cast (abs_le.mp hRadiusReal).1
  have hhi : z≤(radius:ℤ) := by exact_mod_cast (abs_le.mp hRadiusReal).2
  have hTwo : 2<2^w := (by decide : 2<2^14).trans_le
    (Nat.pow_le_pow_right (by decide) (ipm_parameter_words_fit I.m U hw).1)
  obtain ⟨v,final,c,hRun,hResult,hB,hEnd,hCost⟩ :=
    targetSearch_runs_of_offset F I old qp source heap limit radius space price z mem pos ω hOffsetTest
      hTwo hRadius hRound hspace hlo hhi hz (by
        intro st offset stream hOff hHeap hFrame hZero hFit
        have hWord : offset<2^w := hOff.trans_lt hRadius
        have hHeapWord : st.regs 21<2^w := (Nat.le_add_right _ _).trans_lt hFit
        have hNewWords := targetOffsetPacket_words F I old 0 offset qp source heap (st.regs 21) limit radius hwords hWord hHeapWord
        have hFixed := hfixed.frozen hFrame hHeap
        have hFlow := hflow.frozen hFrame hHeap
        have hSame : epochVector F I st.mem source=epochVector F I mem source := by
          funext e
          exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
        exact targetOffsetTest_runs_upTo I U k hw A rate allocation R F q K κ hA
          hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
          hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
          hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
          hEpoch hTest hGuess old qp source (st.regs 21) B offset st.mem st.pos stream hF hq hK hκ hE
          hFixed hFlow (hSame.symm ▸ hhalf) hNewWords hOff halloc hLimit hFit hZero hm hU hsize hk hI hnums
          hLower fstar z hstar hCostOpt)
  exact ⟨v,final,c,z,fstar,hRun,hstar,hCostOpt,hResult,hB,hEnd,hCost⟩

/-- The integer-cost search runs over the full inclusive cost interval.
Its output points at an exact fixed-point flow within a quarter of the
integer optimum. The time and space include all independent target runs. -/
theorem targetSearch_runs {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBody guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBody offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate :=
  targetSearch_runs_upTo I U k hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess hOffsetTest old qp source
    heap B mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hRadius hRound halloc hLimit
    hspace hz hm hU hsize hk hI hnums hLower

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- The integer-cost search runs over the full inclusive cost interval.
Its output points at an exact fixed-point flow within a quarter of the
integer optimum. The time and space include all independent target runs. -/
theorem targetSearch_runs_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBody guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBody offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate := by
  dsimp only
  let limit := targetTestLimit I.m U k
  let radius := I.m*U^2
  let space := targetOffsetSpace F I.m U k old.exponent B
  let price := targetOffsetCost F I.m U k old.exponent rate
  obtain ⟨fstar,hstar,hint⟩ := exists_integral_minCostFlow I hI ⟨_,hflow.2.1⟩
  obtain ⟨z,hCostOpt⟩ := integral_cost I fstar hint
  have hopt := feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums fstar hstar.1
  rw [hCostOpt] at hopt
  have hRadiusReal : |(z:ℝ)|≤(radius:ℝ) := by
    simpa only [radius,Nat.cast_mul,Nat.cast_pow] using hopt
  have hlo : -(radius:ℤ)≤z := by exact_mod_cast (abs_le.mp hRadiusReal).1
  have hhi : z≤(radius:ℤ) := by exact_mod_cast (abs_le.mp hRadiusReal).2
  have hTwo : 2<2^w := (by decide : 2<2^14).trans_le
    (Nat.pow_le_pow_right (by decide) (ipm_quality_parameter_words_fit I.m U k hw).1)
  obtain ⟨v,final,c,hRun,hResult,hB,hEnd,hCost⟩ :=
    targetSearch_runs_of_offset F I old qp source heap limit radius space price z mem pos ω hOffsetTest
      hTwo hRadius hRound hspace hlo hhi hz (by
        intro st offset stream hOff hHeap hFrame hZero hFit
        have hWord : offset<2^w := hOff.trans_lt hRadius
        have hHeapWord : st.regs 21<2^w := (Nat.le_add_right _ _).trans_lt hFit
        have hNewWords := targetOffsetPacket_words F I old 0 offset qp source heap (st.regs 21) limit radius hwords hWord hHeapWord
        have hFixed := hfixed.frozen hFrame hHeap
        have hFlow := hflow.frozen hFrame hHeap
        have hSame : epochVector F I st.mem source=epochVector F I mem source := by
          funext e
          exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
        exact targetOffsetTest_runs_widened_upTo_on I U k hw A rate allocation R F q K κ hA hP
          hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
          hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
          hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
          hEpoch hTest hGuess old qp source (st.regs 21) B offset st.mem st.pos stream hF hq hK hκ hE
          hFixed hFlow (hSame.symm ▸ hhalf) hNewWords hOff halloc hLimit hFit hZero hm hU hsize hI hnums
          hLower fstar z hstar hCostOpt)
  exact ⟨v,final,c,z,fstar,hRun,hstar,hCostOpt,hResult,hB,hEnd,hCost⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- The integer-cost search runs over the full inclusive cost interval.
Its output points at an exact fixed-point flow within a quarter of the
integer optimum. The time and space include all independent target runs. -/
theorem targetSearch_runs_widened_upTo {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBody guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBody offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate :=
  targetSearch_runs_widened_upTo_on I U k hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess
    hOffsetTest old qp source heap B mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hRadius
    hRound halloc hLimit hspace hz hm hU hsize hI hnums hLower

/-- `V`-passing variant of `targetSearch_runs_upTo`. -/
theorem targetSearch_runs_withV_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBodyWithV guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate := by
  dsimp only
  let limit := targetTestLimit I.m U k
  let radius := I.m*U^2
  let space := targetOffsetSpace F I.m U k old.exponent B
  let price := targetOffsetCost F I.m U k old.exponent rate
  obtain ⟨fstar,hstar,hint⟩ := exists_integral_minCostFlow I hI ⟨_,hflow.2.1⟩
  obtain ⟨z,hCostOpt⟩ := integral_cost I fstar hint
  have hopt := feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums fstar hstar.1
  rw [hCostOpt] at hopt
  have hRadiusReal : |(z:ℝ)|≤(radius:ℝ) := by
    simpa only [radius,Nat.cast_mul,Nat.cast_pow] using hopt
  have hlo : -(radius:ℤ)≤z := by exact_mod_cast (abs_le.mp hRadiusReal).1
  have hhi : z≤(radius:ℤ) := by exact_mod_cast (abs_le.mp hRadiusReal).2
  have hTwo : 2<2^w := (by decide : 2<2^14).trans_le
    (Nat.pow_le_pow_right (by decide) (ipm_parameter_words_fit I.m U hw).1)
  obtain ⟨v,final,c,hRun,hResult,hB,hEnd,hCost⟩ :=
    targetSearchWithV_runs_of_offset F I old qp source heap limit radius space price V z mem pos ω hOffsetTest
      hTwo hRadius hV hRound hspace hlo hhi hz (by
        intro st offset stream hOff hHeap hFrame hZero hFit
        have hWord : offset<2^w := hOff.trans_lt hRadius
        have hHeapWord : st.regs 21<2^w := (Nat.le_add_right _ _).trans_lt hFit
        have hNewWords := targetOffsetPacket_words F I old 0 offset qp source heap (st.regs 21) limit radius hwords hWord hHeapWord
        have hFixed := hfixed.frozen hFrame hHeap
        have hFlow := hflow.frozen hFrame hHeap
        have hSame : epochVector F I st.mem source=epochVector F I mem source := by
          funext e
          exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
        exact targetOffsetTest_runs_withV_upTo I U k V hw A rate allocation R F q K κ hA
          hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
          hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
          hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
          hEpoch hTest hGuess old qp source (st.regs 21) B offset st.mem st.pos stream hF hq hK hκ hE
          hFixed hFlow (hSame.symm ▸ hhalf) hNewWords hV hOff halloc hLimit hFit hZero hm hU hsize hk hI hnums
          hLower fstar z hstar hCostOpt)
  exact ⟨v,final,c,z,fstar,hRun,hstar,hCostOpt,hResult,hB,hEnd,hCost⟩

/-- `V`-passing variant of `targetSearch_runs`. -/
theorem targetSearch_runs_withV {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBodyWithV guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate :=
  targetSearch_runs_withV_upTo I U k V hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess hOffsetTest old qp source
    heap B mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hV hRadius hRound halloc hLimit hspace
    hz hm hU hsize hk hI hnums hLower

/-- `V`-passing variant of `targetSearch_runs_widened_upTo_on`. -/
theorem targetSearch_runs_withV_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k V : ℕ)
    (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (F : MinRatioFormat w)
    (q K : ℕ)
    (κ : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBodyWithV guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate := by
  dsimp only
  let limit := targetTestLimit I.m U k
  let radius := I.m*U^2
  let space := targetOffsetSpace F I.m U k old.exponent B
  let price := targetOffsetCost F I.m U k old.exponent rate
  obtain ⟨fstar,hstar,hint⟩ := exists_integral_minCostFlow I hI ⟨_,hflow.2.1⟩
  obtain ⟨z,hCostOpt⟩ := integral_cost I fstar hint
  have hopt := feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums fstar hstar.1
  rw [hCostOpt] at hopt
  have hRadiusReal : |(z:ℝ)|≤(radius:ℝ) := by
    simpa only [radius,Nat.cast_mul,Nat.cast_pow] using hopt
  have hlo : -(radius:ℤ)≤z := by exact_mod_cast (abs_le.mp hRadiusReal).1
  have hhi : z≤(radius:ℤ) := by exact_mod_cast (abs_le.mp hRadiusReal).2
  have hTwo : 2<2^w := (by decide : 2<2^14).trans_le
    (Nat.pow_le_pow_right (by decide) (ipm_quality_parameter_words_fit I.m U k hw).1)
  obtain ⟨v,final,c,hRun,hResult,hB,hEnd,hCost⟩ :=
    targetSearchWithV_runs_of_offset F I old qp source heap limit radius space price V z mem pos ω hOffsetTest
      hTwo hRadius hV hRound hspace hlo hhi hz (by
        intro st offset stream hOff hHeap hFrame hZero hFit
        have hWord : offset<2^w := hOff.trans_lt hRadius
        have hHeapWord : st.regs 21<2^w := (Nat.le_add_right _ _).trans_lt hFit
        have hNewWords := targetOffsetPacket_words F I old 0 offset qp source heap (st.regs 21) limit radius hwords hWord hHeapWord
        have hFixed := hfixed.frozen hFrame hHeap
        have hFlow := hflow.frozen hFrame hHeap
        have hSame : epochVector F I st.mem source=epochVector F I mem source := by
          funext e
          exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
        exact targetOffsetTest_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ hA hP
          hbase himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
          hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody
          hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
          hEpoch hTest hGuess old qp source (st.regs 21) B offset st.mem st.pos stream hF hq hK hκ hE
          hFixed hFlow (hSame.symm ▸ hhalf) hNewWords hV hOff halloc hLimit hFit hZero hm hU hsize hI hnums
          hLower fstar z hstar hCostOpt)
  exact ⟨v,final,c,z,fstar,hRun,hstar,hCostOpt,hResult,hB,hEnd,hCost⟩

/-- `V`-passing variant of `targetSearch_runs_widened_upTo`. -/
theorem targetSearch_runs_withV_widened_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base epoch guess test offsetTest startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hOffsetTest : p.procs[offsetTest]?=some (targetOffsetTestBodyWithV guess test))
    (old : EpochLayout) (qp source heap B : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old qp qp heap (1/4)
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old F I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace F I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV offsetTest)
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate :=
  targetSearch_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup hEpoch hTest hGuess
    hOffsetTest old qp source heap B mem pos ω hF hq hK hκ hE hfixed hflow hhalf hwords hV hRadius
    hRound halloc hLimit hspace hz hm hU hsize hI hnums hLower

end MinCostFlow.IPM.Machine
