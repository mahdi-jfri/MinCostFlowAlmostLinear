module

public import MinCostFlow.IPM.Machine.TargetEpochContinuation
public import MinCostFlow.IPM.Machine.TargetEpochContinuationWithV
public import MinCostFlow.IPM.Machine.TargetEpochDriver
public import MinCostFlow.IPM.Machine.TargetEpochResidualInput
import MinCostFlow.IPM.Machine.PrecisionCallRanges
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Word RAM verification of a target stage

A stage first guards the exact residual. Convergence or a failed
range check returns at once. A continuing residual starts a fresh
epoch and then follows the actual startup and complete-epoch flags.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 600000 in
/-- Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69) at the
selected fixed precision. One actual stage either returns a terminal
record or a materialized feasible iterate with its conditional
potential decrease and explicit cost and workspace bounds. -/
theorem targetEpoch_runs_upTo {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBody base startup complete statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 := by
  subst F q K κ
  let F := ipmMinRatioFormat I.m U hw
  let κ := (1:ℝ)/(2:ℝ)^k
  let a := Num.IPM.alphaPrime I.m U
  let normalization := (25/32:ℝ)*(κ*a/32)^2/50
  let stageSpace := targetStageSpace F I.m old.exponent B
  let price := targetStageContinuationCost F I.m old.exponent rate
  let flow := epochVector F I mem source
  have hparams := ipm_parameter_words_fit I.m U hw
  have hEight : 8<2^w := (by decide : 8<2^14).trans_le (Nat.pow_le_pow_right (by decide) hparams.1)
  have hL : 0<F.limbs := by change 0 < ipmLimbs I.m U; unfold ipmLimbs; omega
  have hFiveM : 5*I.m<2^w := by have hh := hparams.2.2.2.2.2.1; omega
  have hS := targetStage_residual_space F I.m old.exponent B heap
  have hsplit := targetStage_space_split F I old heap B allocation halloc
  let fp := epochResidualEnd I.m F.limbs heap
  let rHeap := fp+I.m*F.limbs
  let res := residual I target flow
  have hsplit' : rHeap+epochStartSpace F I old.exponent old.initGraph rHeap allocation+I.m+4+
      (I.m+1)*budgetedIterationSpace F I.m old.exponent B+2≤heap+stageSpace := hsplit
  have hfit : rHeap<2^w := by
    have hspace' : heap+stageSpace<2^w := hspace
    omega
  have hpre := epochBase_pre_of_chosen_precision I U flow target (w:=w) hm hU hnums hflow.2.1
    hfixed.cost (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hfixed.targetValue hTarget
    (hfixed.arrays old.cost (by simp)) hflow.1 (hfixed.scalars tp (by simp))
    (hfixed.scalars old.slackMin (by simp)) (hfixed.scalars old.slackMax (by simp))
    (hfixed.scalars qp (by simp)) hfixed.slackMin.1 hfixed.slackMax.1 hfixed.quarter.1 hz hEight hfit
  have hFlo := (abs_le.mp hTarget).1
  have hκpos : 0<κ := by unfold κ; positivity
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have hκle : κ≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hale : a≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hx := dyadic_quality_product_lower I.m U k hsize hk
  have hprecision := (ipm_precision_margins I.m U).2.2.1
  have hqual : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(a/8) := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact chosen_minRatio_quality_range I.m U k hsize hk
  have hNorm : 1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent I.m U))=normalization := by
    rw [dyadicNormalization_eq]
    dsimp only [normalization,κ,a,Num.IPM.alphaPrime]
    ring
  obtain ⟨hNormLo,hNormHi⟩ := chosen_normalization_range I.m U k hsize hk
  rw [hNorm] at hNormLo hNormHi
  have hNormLo' : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact hNormLo
  have hCostVal (e : Fin I.m) :
      Num.intVal mem (old.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost := by
    simpa [Num.fixVal] using (hfixed.cost e).2
  apply targetEpoch_runs_of_continue F I U κ (target:ℝ) old tp qp source heap stageSpace price mem pos ω
    hbase hstatusRecord hwords hpre hL hEight (hS.trans_lt hspace) hS hflow hCostVal hfixed.targetValue.2
    (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp))
    hfixed.slackMin hfixed.slackMax hfixed.quarter hE hm hU hsize hnums hFlo
  intro checked
  dsimp only
  intro hregs hfr hhr hlarge hframe hzero hres hlo hhi hrcopy hcopy
  have hspaceArrays : rHeap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent)<2^w := by
    have hh := hsplit'.trans_lt hspace
    dsimp only [epochStartSpace] at hh
    omega
  have hCoeffPre := targetEpoch_coefficient_pre I U hw old tp qp source heap target normalization a res
    mem checked.mem hfixed hflow hE hU hnums ha.le hale hframe hlo hhi hrcopy hcopy hzero hspaceArrays
  obtain ⟨out,final,c,hrun,hResult,hEnd,hCost⟩ :=
    targetEpoch_continuation_runs_upTo F A I U κ target res rate allocation R hA himpl hrawDetect hdetect hstore
      hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate
      hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
      hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
      old tp qp source heap B checked mem ω hregs hhr hfr hlarge hwords hframe rfl halloc hspace hFiveM hEight
      hE hm hU hsize hnums hI hLower hFlo hκpos hκle hx ha hale rfl hres hflow hfixed
      rfl hprecision hqual hNormLo' hNormHi hrcopy hcopy hCoeffPre
  exact ⟨out,final,c,hrun,hResult,hEnd,hCost.trans (Nat.le_add_right _ _)⟩

/-- Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69) at the
selected fixed precision. One actual stage either returns a terminal
record or a materialized feasible iterate with its conditional
potential decrease and explicit cost and workspace bounds. -/
theorem targetEpoch_runs {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBody base startup complete statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 :=
  targetEpoch_runs_upTo I U k hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup old tp qp source heap B mem pos ω target hF hq
    hK hκ hE hfixed hflow hwords halloc hspace hz hm hU hsize hk hI hnums hLower hTarget

/-- Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69) at the
selected fixed precision. One actual stage either returns a terminal
record or a materialized feasible iterate with its conditional
potential decrease and explicit cost and workspace bounds. -/
theorem targetEpoch_runs_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBody base startup complete statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 := by
  subst F q K κ
  let F := ipmQualityMinRatioFormat I.m U k hw
  let κ := (1:ℝ)/(2:ℝ)^k
  let a := Num.IPM.alphaPrime I.m U
  let normalization := (25/32:ℝ)*(κ*a/32)^2/50
  let stageSpace := targetStageSpace F I.m old.exponent B
  let price := targetStageContinuationCost F I.m old.exponent rate
  let flow := epochVector F I mem source
  have hparams := ipm_quality_parameter_words_fit I.m U k hw
  have hEight : 8<2^w := (by decide : 8<2^14).trans_le (Nat.pow_le_pow_right (by decide) hparams.1)
  have hL : 0<F.limbs := by change 0 < ipmQualityLimbs I.m U k; unfold ipmQualityLimbs; omega
  have hFiveM : 5*I.m<2^w := by have hh := hparams.2.2.2.2.2.1; omega
  have hS := targetStage_residual_space F I.m old.exponent B heap
  have hsplit := targetStage_space_split F I old heap B allocation halloc
  let fp := epochResidualEnd I.m F.limbs heap
  let rHeap := fp+I.m*F.limbs
  let res := residual I target flow
  have hsplit' : rHeap+epochStartSpace F I old.exponent old.initGraph rHeap allocation+I.m+4+
      (I.m+1)*budgetedIterationSpace F I.m old.exponent B+2≤heap+stageSpace := hsplit
  have hfit : rHeap<2^w := by
    have hspace' : heap+stageSpace<2^w := hspace
    omega
  have hpre := epochBase_pre_of_widened_precision I U k flow target (w:=w) hm hU hnums hflow.2.1
    hfixed.cost (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hfixed.targetValue hTarget
    (hfixed.arrays old.cost (by simp)) hflow.1 (hfixed.scalars tp (by simp))
    (hfixed.scalars old.slackMin (by simp)) (hfixed.scalars old.slackMax (by simp))
    (hfixed.scalars qp (by simp)) hfixed.slackMin.1 hfixed.slackMax.1 hfixed.quarter.1 hz hEight hfit
  have hFlo := (abs_le.mp hTarget).1
  have hκpos : 0<κ := by unfold κ; positivity
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have hκle : κ≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hale : a≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hx := widened_dyadic_quality_product_lower I.m U k hsize
  have hprecision := (ipm_quality_precision_margins I.m U k).2.2.1
  have hqual : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(a/8) := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact widened_minRatio_quality_range I.m U k hsize
  have hNorm : 1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent I.m U))=normalization := by
    rw [dyadicNormalization_eq]
    dsimp only [normalization,κ,a,Num.IPM.alphaPrime]
    ring
  obtain ⟨hNormLo,hNormHi⟩ := widened_normalization_range I.m U k hsize
  rw [hNorm] at hNormLo hNormHi
  have hNormLo' : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact hNormLo
  have hCostVal (e : Fin I.m) :
      Num.intVal mem (old.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost := by
    simpa [Num.fixVal] using (hfixed.cost e).2
  have hWide : ipmRangeExponent I.m U ≤ old.exponent := by
    rw [hE]
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  apply targetEpoch_runs_of_continue_at_range F I U κ (target:ℝ) old tp qp source heap stageSpace price mem pos ω
    hbase hstatusRecord hwords hpre hL hEight (hS.trans_lt hspace) hS hflow hCostVal hfixed.targetValue.2
    (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp))
    hfixed.slackMin hfixed.slackMax hfixed.quarter hWide hm hU hsize hnums hFlo
  intro checked
  dsimp only
  intro hregs hfr hhr hlarge hframe hzero hres hlo hhi hrcopy hcopy
  have hspaceArrays : rHeap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent)<2^w := by
    have hh := hsplit'.trans_lt hspace
    dsimp only [epochStartSpace] at hh
    omega
  have hCoeffPre := targetEpoch_coefficient_pre_widened I U k hw old tp qp source heap target normalization a res
    mem checked.mem hfixed hflow hE hU hnums ha.le hale hframe hlo hhi hrcopy hcopy hzero hspaceArrays
  obtain ⟨out,final,c,hrun,hResult,hEnd,hCost⟩ :=
    targetEpoch_continuation_runs_widened_upTo_on F A I U k κ target res rate allocation R hA hP himpl hrawDetect hdetect hstore
      hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate
      hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
      hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
      old tp qp source heap B checked mem ω hregs hhr hfr hlarge hwords hframe rfl halloc hspace hFiveM hEight
      hE hm hU hsize hnums hI hLower hFlo hκpos hκle hx ha hale rfl hres hflow hfixed
      rfl hprecision hqual hNormLo' hNormHi hrcopy hcopy hCoeffPre
  exact ⟨out,final,c,hrun,hResult,hEnd,hCost.trans (Nat.le_add_right _ _)⟩

/-- Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69) at the
selected fixed precision. One actual stage either returns a terminal
record or a materialized feasible iterate with its conditional
potential decrease and explicit cost and workspace bounds. -/
theorem targetEpoch_runs_widened_upTo {w : ℕ} (I : Instance) (U k : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBody base startup complete statusRecord)
        (startState (targetEpochPacket old F I tp qp source heap) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 :=
  targetEpoch_runs_widened_upTo_on I U k hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup old tp qp source
    heap B mem pos ω target hF hq hK hκ hE hfixed hflow hwords halloc hspace hz hm hU hsize hI
    hnums hLower hTarget

set_option maxHeartbeats 600000 in
/-- `V`-passing variant of `targetEpoch_runs_upTo` for `minRatioMachineContractWithV`. -/
theorem targetEpoch_runs_withV_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacketWithV old F I tp qp source heap V,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete statusRecord)
        (startState (targetEpochPacketWithV old F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 := by
  subst F q K κ
  let F := ipmMinRatioFormat I.m U hw
  let κ := (1:ℝ)/(2:ℝ)^k
  let a := Num.IPM.alphaPrime I.m U
  let normalization := (25/32:ℝ)*(κ*a/32)^2/50
  let stageSpace := targetStageSpace F I.m old.exponent B
  let price := targetStageContinuationCost F I.m old.exponent rate
  let flow := epochVector F I mem source
  have hparams := ipm_parameter_words_fit I.m U hw
  have hEight : 8<2^w := (by decide : 8<2^14).trans_le (Nat.pow_le_pow_right (by decide) hparams.1)
  have hL : 0<F.limbs := by change 0 < ipmLimbs I.m U; unfold ipmLimbs; omega
  have hFiveM : 5*I.m<2^w := by have hh := hparams.2.2.2.2.2.1; omega
  have hS := targetStage_residual_space F I.m old.exponent B heap
  have hsplit := targetStage_space_split F I old heap B (allocationWithV V allocation)
    (allocationWithV_le V halloc)
  let fp := epochResidualEnd I.m F.limbs heap
  let rHeap := fp+I.m*F.limbs
  let res := residual I target flow
  have hsplit' : rHeap+epochStartSpace F I old.exponent old.initGraph rHeap (allocationWithV V allocation)+
      I.m+4+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2≤heap+stageSpace := hsplit
  have hfit : rHeap<2^w := by
    have hspace' : heap+stageSpace<2^w := hspace
    omega
  have hpre := epochBase_pre_of_chosen_precision I U flow target (w:=w) hm hU hnums hflow.2.1
    hfixed.cost (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hfixed.targetValue hTarget
    (hfixed.arrays old.cost (by simp)) hflow.1 (hfixed.scalars tp (by simp))
    (hfixed.scalars old.slackMin (by simp)) (hfixed.scalars old.slackMax (by simp))
    (hfixed.scalars qp (by simp)) hfixed.slackMin.1 hfixed.slackMax.1 hfixed.quarter.1 hz hEight hfit
  have hFlo := (abs_le.mp hTarget).1
  have hκpos : 0<κ := by unfold κ; positivity
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have hκle : κ≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hale : a≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hx := dyadic_quality_product_lower I.m U k hsize hk
  have hprecision := (ipm_precision_margins I.m U).2.2.1
  have hqual : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(a/8) := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact chosen_minRatio_quality_range I.m U k hsize hk
  have hNorm : 1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent I.m U))=normalization := by
    rw [dyadicNormalization_eq]
    dsimp only [normalization,κ,a,Num.IPM.alphaPrime]
    ring
  obtain ⟨hNormLo,hNormHi⟩ := chosen_normalization_range I.m U k hsize hk
  rw [hNorm] at hNormLo hNormHi
  have hNormLo' : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact hNormLo
  have hCostVal (e : Fin I.m) :
      Num.intVal mem (old.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost := by
    simpa [Num.fixVal] using (hfixed.cost e).2
  have hwordsBase : ∀ z ∈ targetEpochPacket old F I tp qp source heap, z < 2^w :=
    fun z hz => hwords z (List.mem_append_left [V] hz)
  have hVword : V < 2^w := hwords V (by simp [targetEpochPacketWithV])
  apply targetEpochWithV_runs_of_continue F I U κ (target:ℝ) old tp qp source heap stageSpace price V mem pos ω
    hbase hstatusRecord hwordsBase hpre hL hEight (hS.trans_lt hspace) hS hflow hCostVal hfixed.targetValue.2
    (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp))
    hfixed.slackMin hfixed.slackMax hfixed.quarter hE hm hU hsize hnums hFlo
  intro checked
  dsimp only
  intro hregs hfr hhr hVreg hlarge hframe hzero hres hlo hhi hrcopy hcopy
  have hspaceArrays : rHeap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent)<2^w := by
    have hh := hsplit'.trans_lt hspace
    dsimp only [epochStartSpace] at hh
    omega
  have hCoeffPre := targetEpoch_coefficient_pre I U hw old tp qp source heap target normalization a res
    mem checked.mem hfixed hflow hE hU hnums ha.le hale hframe hlo hhi hrcopy hcopy hzero hspaceArrays
  obtain ⟨out,final,c,hrun,hResult,hEnd,hCost⟩ :=
    targetEpoch_continuation_runs_withV_upTo F A I U V κ target res rate allocation R hA himpl hrawDetect hdetect hstore
      hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate
      hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
      hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
      old tp qp source heap B checked mem ω hregs hhr hVreg hVword hfr hlarge hwordsBase hframe rfl halloc hspace hFiveM hEight
      hE hm hU hsize hnums hI hLower hFlo hκpos hκle hx ha hale rfl hres hflow hfixed
      rfl hprecision hqual hNormLo' hNormHi hrcopy hcopy hCoeffPre
  exact ⟨out,final,c,hrun,hResult,hEnd,hCost.trans (Nat.le_add_right _ _)⟩

/-- `V`-passing variant of `targetEpoch_runs` for `minRatioMachineContractWithV`. -/
theorem targetEpoch_runs_withV {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmMinRatioFormat I.m U hw) (hq : q=ipmErrorBits I.m U)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacketWithV old F I tp qp source heap V,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete statusRecord)
        (startState (targetEpochPacketWithV old F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 :=
  targetEpoch_runs_withV_upTo I U k V hw A rate allocation R F q K κ (hA.upTo I.m I.n) hbase himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup old tp qp source heap B mem pos ω target hF hq
    hK hκ hE hfixed hflow hwords halloc hspace hz hm hU hsize hk hI hnums hLower hTarget

set_option maxHeartbeats 600000 in
/-- `V`-passing variant of `targetEpoch_runs_widened_upTo_on` for `minRatioMachineContractWithV`. -/
theorem targetEpoch_runs_withV_widened_upTo_on {w : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacketWithV old F I tp qp source heap V,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete statusRecord)
        (startState (targetEpochPacketWithV old F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 := by
  subst F q K κ
  let F := ipmQualityMinRatioFormat I.m U k hw
  let κ := (1:ℝ)/(2:ℝ)^k
  let a := Num.IPM.alphaPrime I.m U
  let normalization := (25/32:ℝ)*(κ*a/32)^2/50
  let stageSpace := targetStageSpace F I.m old.exponent B
  let price := targetStageContinuationCost F I.m old.exponent rate
  let flow := epochVector F I mem source
  have hparams := ipm_quality_parameter_words_fit I.m U k hw
  have hEight : 8<2^w := (by decide : 8<2^14).trans_le (Nat.pow_le_pow_right (by decide) hparams.1)
  have hL : 0<F.limbs := by change 0 < ipmQualityLimbs I.m U k; unfold ipmQualityLimbs; omega
  have hFiveM : 5*I.m<2^w := by have hh := hparams.2.2.2.2.2.1; omega
  have hS := targetStage_residual_space F I.m old.exponent B heap
  have hsplit := targetStage_space_split F I old heap B (allocationWithV V allocation)
    (allocationWithV_le V halloc)
  let fp := epochResidualEnd I.m F.limbs heap
  let rHeap := fp+I.m*F.limbs
  let res := residual I target flow
  have hsplit' : rHeap+epochStartSpace F I old.exponent old.initGraph rHeap (allocationWithV V allocation)+
      I.m+4+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2≤heap+stageSpace := hsplit
  have hfit : rHeap<2^w := by
    have hspace' : heap+stageSpace<2^w := hspace
    omega
  have hpre := epochBase_pre_of_widened_precision I U k flow target (w:=w) hm hU hnums hflow.2.1
    hfixed.cost (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hfixed.targetValue hTarget
    (hfixed.arrays old.cost (by simp)) hflow.1 (hfixed.scalars tp (by simp))
    (hfixed.scalars old.slackMin (by simp)) (hfixed.scalars old.slackMax (by simp))
    (hfixed.scalars qp (by simp)) hfixed.slackMin.1 hfixed.slackMax.1 hfixed.quarter.1 hz hEight hfit
  have hFlo := (abs_le.mp hTarget).1
  have hκpos : 0<κ := by unfold κ; positivity
  have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
  have hκle : κ≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hale : a≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hx := widened_dyadic_quality_product_lower I.m U k hsize
  have hprecision := (ipm_quality_precision_margins I.m U k).2.2.1
  have hqual : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*(a/8) := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact widened_minRatio_quality_range I.m U k hsize
  have hNorm : 1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent I.m U))=normalization := by
    rw [dyadicNormalization_eq]
    dsimp only [normalization,κ,a,Num.IPM.alphaPrime]
    ring
  obtain ⟨hNormLo,hNormHi⟩ := widened_normalization_range I.m U k hsize
  rw [hNorm] at hNormLo hNormHi
  have hNormLo' : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization := by
    rw [zpow_neg,zpow_natCast,← one_div]
    exact hNormLo
  have hCostVal (e : Fin I.m) :
      Num.intVal mem (old.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost := by
    simpa [Num.fixVal] using (hfixed.cost e).2
  have hWide : ipmRangeExponent I.m U ≤ old.exponent := by
    rw [hE]
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  have hwordsBase : ∀ z ∈ targetEpochPacket old F I tp qp source heap, z < 2^w :=
    fun z hz => hwords z (List.mem_append_left [V] hz)
  have hVword : V < 2^w := hwords V (by simp [targetEpochPacketWithV])
  apply targetEpochWithV_runs_of_continue_at_range F I U κ (target:ℝ) old tp qp source heap stageSpace price V mem pos ω
    hbase hstatusRecord hwordsBase hpre hL hEight (hS.trans_lt hspace) hS hflow hCostVal hfixed.targetValue.2
    (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp)) (hfixed.scalars _ (by simp))
    hfixed.slackMin hfixed.slackMax hfixed.quarter hWide hm hU hsize hnums hFlo
  intro checked
  dsimp only
  intro hregs hfr hhr hVreg hlarge hframe hzero hres hlo hhi hrcopy hcopy
  have hspaceArrays : rHeap+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent)<2^w := by
    have hh := hsplit'.trans_lt hspace
    dsimp only [epochStartSpace] at hh
    omega
  have hCoeffPre := targetEpoch_coefficient_pre_widened I U k hw old tp qp source heap target normalization a res
    mem checked.mem hfixed hflow hE hU hnums ha.le hale hframe hlo hhi hrcopy hcopy hzero hspaceArrays
  obtain ⟨out,final,c,hrun,hResult,hEnd,hCost⟩ :=
    targetEpoch_continuation_runs_withV_widened_upTo_on F A I U k V κ target res rate allocation R hA hP himpl hrawDetect hdetect hstore
      hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate
      hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
      hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup
      old tp qp source heap B checked mem ω hregs hhr hVreg hVword hfr hlarge hwordsBase hframe rfl halloc hspace hFiveM hEight
      hE hm hU hsize hnums hI hLower hFlo hκpos hκle hx ha hale rfl hres hflow hfixed
      rfl hprecision hqual hNormLo' hNormHi hrcopy hcopy hCoeffPre
  exact ⟨out,final,c,hrun,hResult,hEnd,hCost.trans (Nat.le_add_right _ _)⟩

/-- `V`-passing variant of `targetEpoch_runs_widened_upTo` for `minRatioMachineContractWithV`. -/
theorem targetEpoch_runs_withV_widened_upTo {w : ℕ} (I : Instance) (U k V : ℕ)
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
    {iteration iterations complete statusRecord base startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source heap B : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (target : ℤ)
    (hF : F=ipmQualityMinRatioFormat I.m U k hw) (hq : q=ipmQualityErrorBits I.m U k)
    (hK : K=gradientCoefficientExponent I.m U) (hκ : κ=1/(2:ℝ)^k)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs F I old tp qp heap target
      ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow F I old.exponent source heap mem)
    (hwords : ∀ z∈targetEpochPacketWithV old F I tp qp source heap V,z<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+targetStageSpace F I.m old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower)
    (hTarget : |(target:ℝ)|≤I.m*(U:ℝ)^2) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete statusRecord)
        (startState (targetEpochPacketWithV old F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source heap out mem final.mem ∧
      out≤heap+targetStageSpace F I.m old.exponent B ∧
      cost≤epochBaseCost I.m F.limbs+targetStageContinuationCost F I.m old.exponent rate+81 :=
  targetEpoch_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) hbase himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup old tp qp source
    heap B mem pos ω target hF hq hK hκ hE hfixed hflow hwords halloc hspace hz hm hU hsize hI
    hnums hLower hTarget

end MinCostFlow.IPM.Machine
