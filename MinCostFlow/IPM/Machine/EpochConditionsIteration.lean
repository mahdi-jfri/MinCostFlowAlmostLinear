module

public import MinCostFlow.IPM.Machine.EpochConditionsDetectInput
public import MinCostFlow.IPM.Machine.EpochLayoutArgs
public import MinCostFlow.IPM.Machine.EpochStaticInputs
public import MinCostFlow.IPM.Machine.BudgetedIterationFromCache
public import MinCostFlow.IPM.Machine.BudgetedIterationLoopStep
public import MinCostFlow.IPM.Machine.BudgetedIterationSpace
import MinCostFlow.IPM.Machine.DetectRefreshDetectInput

/-!
# Running one finite epoch call from its current conditions

The current valid history and held cache supply all numeric inputs.
The actual Detect input extends that history with unchanged arrays.
The reserved address block supplies word fit. The caller reads the
actual output status and keeps its trace and concrete credit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Execute the actual epoch call from its current loop conditions,
retaining the returned state, report count, frames and amortized charge. -/
theorem epochConditions_iteration_runs_upTo_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
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
    (initialMem : ℕ → ℕ) (initialHeap finish i B : ℕ) (P : EpochPoint R.τ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i P)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinishLe : finish ≤ I.m) :
    let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
    ∃ o st cost v s' y,
      Runs w p ω (epochIterationsStep iteration) P.machine o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R L.handle s s' P.credit q K L.sourceEnd L.tableEnd
        (L.packet F I (P.machine.regs 8)) P.machine.mem v st.mem ∧
      R.rep L.handle s' y st.mem ∧
      (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ P.machine.regs 8≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 8=v else o=.returned v) ∧
      (∀ j,j≠8 → j≠27 → j≠28 → st.regs j=P.machine.regs j) ∧
      (A.detect s).1.card≤I.m ∧ v<2^w ∧
      cost+R.phi L.handle y st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m L.exponent rate+
        37+R.phi L.handle P.credit P.machine.mem := by
  let heap := P.machine.regs 8
  let Q := P.detectInput i
  let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)
  obtain ⟨hQ,hValid,hG,hOp,hLength,hState⟩ := hcond.detect_input
  change minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)=_ at hState
  have hBudgetWord := hcond.budget_word hbudgetFit
  obtain ⟨hi,_,_,hRegs,hHeap,_,hPrefix,_,_,hPre,hGOld,hLOld,hCache,hRanges,_⟩ := hQ
  have hstaticCurrent := hstatic.frozen hPrefix
  obtain ⟨hWords,hI,hGraph,hGraphEnd,hGraphWords,hArrays,_,hGuard,hRequest,hNormLo,hNormHi,
    hNeg,hMax,hMin,hQuality,hPrecision,hCapacity,hSources,hLower,hAlpha,hFormat,_,hEps⟩ := hstaticCurrent
  have hBlock := epoch_iteration_space_of_initial_bound w initialHeap heap
    (budgetedIterationSpace F I.m L.exponent B) finish i hi hHeap hspace
  have hHeapWord : heap<2^w := (Nat.le_add_right heap _).trans_lt hBlock
  have hPacket := L.packet_words F I heap hWords hHeapWord
  have hCard := (detectRefresh_detect_pre F A (namedInstance I) I.m κ α rate allocation R hPre).2
  have hCallSpace := budgetedIteration_space_input F I.m L.exponent B L.handle heap L.gradient L.lengths
    L.request (A.detect s).1.card allocation halloc hCard hBlock
  obtain ⟨oI,stI,cI,s',y,hRun,hOut,hRep,hFoot,hCost⟩ :=
    budgetedIteration_runs_from_cache_upTo_at F A I U κ α Ψ eps rate allocation R s P.credit hA
      Q.history Q.eta Q.op (2*i+1) (2*i) rfl hValid le_rfl hOp hG (by omega) hEps hFormat
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
      (hsnapshot s) hbatchBody (hbatch s) hupdate hcore hstatus hreportBody (hreport s) hchecked hbudgetRecord
      L.names L.base L.lower L.upper L.flow heap L.cost L.residual L.alpha L.one L.slackMin L.slackMax
      L.exponent L.lengths L.gradient L.graph L.request L.gradientMin L.gradientMax L.lengthMin
      P.machine.mem P.machine.pos ω capacity normalization hPacket hBudgetWord hPre hI hGraph hGraphEnd hGraphWords
      (hGuard _ (by simp)) (hGuard _ (by simp)) (hGuard _ (by simp)) (hGuard _ (by simp))
      hRequest hNormLo hNormHi hNeg hMax hMin hQuality hPrecision
      (fun e he => ⟨(hRanges e he).1,(hRanges e he).2.1⟩)
      (fun e he => (hRanges e (Finset.mem_range.mp he)).2.2)
      hCapacity (fun ptr hp => hArrays ptr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto)) hSources hLength hAlpha hLower
      (fun e he => hCache e (Finset.mem_range.mp he))
      (fun e _ => ⟨congrFun hGOld e,congrFun hLOld e⟩) hCallSpace
  have hOutSpace := budgetedIteration_space_output F A I κ α rate allocation R B halloc hPre hOut
  have hResultWord : oI.value<2^w := hOutSpace.trans_lt hBlock
  obtain ⟨o,st,cost,hRunStep,hTrace,hRep',hCost',hStatus,hFixed⟩ :=
    budgetedIteration_loop_step_runs (E:=L.exponent) P.machine ω hbody
      (L.packet_args F I heap P.machine hRegs) hRun hOut hRep hCost hResultWord hOne
  dsimp only
  rw [← hState]
  exact ⟨o,st,cost,oI.value,s',y,hRunStep,hTrace,hRep',hFoot,hStatus,hFixed,hCard,hResultWord,hCost'⟩

theorem epochConditions_iteration_runs_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
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
    (initialMem : ℕ → ℕ) (initialHeap finish i B : ℕ) (P : EpochPoint R.τ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i P)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinishLe : finish ≤ I.m) :
    let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
    ∃ o st cost v s' y,
      Runs w p ω (epochIterationsStep iteration) P.machine o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R L.handle s s' P.credit q K L.sourceEnd L.tableEnd
        (L.packet F I (P.machine.regs 8)) P.machine.mem v st.mem ∧
      R.rep L.handle s' y st.mem ∧
      (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ P.machine.regs 8≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 8=v else o=.returned v) ∧
      (∀ j,j≠8 → j≠27 → j≠28 → st.regs j=P.machine.regs j) ∧
      (A.detect s).1.card≤I.m ∧ v<2^w ∧
      cost+R.phi L.handle y st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m L.exponent rate+
        37+R.phi L.handle P.credit P.machine.mem :=
  epochConditions_iteration_runs_upTo_at F A I U κ α Ψ eps rate allocation R hA L q K himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    initialMem initialHeap finish i B P ω capacity normalization hstatic hcond halloc hspace
    hbudgetFit hOne hfinishLe

/-- Execute the actual epoch call from its current loop conditions,
retaining the returned state, report count, frames and amortized charge. -/
theorem epochConditions_iteration_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
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
    (initialMem : ℕ → ℕ) (initialHeap finish i B : ℕ) (P : EpochPoint R.τ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i P)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinishLe : finish ≤ I.m) :
    let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
    ∃ o st cost v s' y,
      Runs w p ω (epochIterationsStep iteration) P.machine o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R L.handle s s' P.credit q K L.sourceEnd L.tableEnd
        (L.packet F I (P.machine.regs 8)) P.machine.mem v st.mem ∧
      R.rep L.handle s' y st.mem ∧
      (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ P.machine.regs 8≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 8=v else o=.returned v) ∧
      (∀ j,j≠8 → j≠27 → j≠28 → st.regs j=P.machine.regs j) ∧
      (A.detect s).1.card≤I.m ∧ v<2^w ∧
      cost+R.phi L.handle y st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m L.exponent rate+
        37+R.phi L.handle P.credit P.machine.mem :=
  epochConditions_iteration_runs_upTo F A I U κ α Ψ eps rate allocation R (hA.upTo I.m I.n) L q
    K himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord
    hbody initialMem initialHeap finish i B P ω capacity normalization hstatic hcond halloc
    hspace hbudgetFit hOne hfinishLe

/-- Execute the actual epoch call from its current loop conditions under `P`,
retaining the returned state, report count, frames and amortized charge. -/
theorem epochConditions_iteration_runs_at_range_upTo_on_at {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (q K : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
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
    (initialMem : ℕ → ℕ) (initialHeap finish i B : ℕ) (Pt : EpochPoint R.τ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i Pt)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinishLe : finish ≤ I.m) :
    let s := minRatioState A.eraseFailure Pt.history Pt.eta Pt.op (2*i)
    ∃ o st cost v s' y,
      Runs w p ω (epochIterationsStep iteration) Pt.machine o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R L.handle s s' Pt.credit q K L.sourceEnd L.tableEnd
        (L.packet F I (Pt.machine.regs 8)) Pt.machine.mem v st.mem ∧
      R.rep L.handle s' y st.mem ∧
      (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle Pt.credit z ∨ Pt.machine.regs 8≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 8=v else o=.returned v) ∧
      (∀ j,j≠8 → j≠27 → j≠28 → st.regs j=Pt.machine.regs j) ∧
      (A.detect s).1.card≤I.m ∧ v<2^w ∧
      cost+R.phi L.handle y st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m L.exponent rate+
        37+R.phi L.handle Pt.credit Pt.machine.mem := by
  let heap := Pt.machine.regs 8
  let Q := Pt.detectInput i
  let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)
  obtain ⟨hQ,hValid,hG,hOp,hLength,hState⟩ := hcond.detect_input
  change minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)=_ at hState
  have hBudgetWord := hcond.budget_word hbudgetFit
  obtain ⟨hi,_,_,hRegs,hHeap,_,hPrefix,_,_,hPre,hGOld,hLOld,hCache,hRanges,_⟩ := hQ
  have hPD : ∀ j≤2*i+1,P (Q.history.G j) (Q.history.ℓ j) :=
    hP.history hG (appendHistoryStage_lengthsWithin [] _ _ hcond.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (hcond.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (2*i) le_rfl))
  have hstaticCurrent := hstatic.frozen hPrefix
  obtain ⟨hWords,hI,hGraph,hGraphEnd,hGraphWords,hArrays,_,hGuard,hRequest,hNormLo,hNormHi,
    hNeg,hMax,hMin,hQuality,hPrecision,hCapacity,hSources,hLower,hAlpha,hFormat,_,hEps⟩ := hstaticCurrent
  have hBlock := epoch_iteration_space_of_initial_bound w initialHeap heap
    (budgetedIterationSpace F I.m L.exponent B) finish i hi hHeap hspace
  have hHeapWord : heap<2^w := (Nat.le_add_right heap _).trans_lt hBlock
  have hPacket := L.packet_words F I heap hWords hHeapWord
  have hCard := (detectRefresh_detect_pre F A (namedInstance I) I.m κ α rate allocation R hPre).2
  have hCallSpace := budgetedIteration_space_input F I.m L.exponent B L.handle heap L.gradient L.lengths
    L.request (A.detect s).1.card allocation halloc hCard hBlock
  obtain ⟨oI,stI,cI,s',y,hRun,hOut,hRep,hFoot,hCost⟩ :=
    budgetedIteration_runs_from_cache_at_range_upTo_on_at F A I U κ α Ψ eps rate allocation R s Pt.credit hA
      Q.history Q.eta Q.op (2*i+1) (2*i) rfl hValid le_rfl hOp hG (by omega) hPD hEps (hWide.trans_eq hFormat.symm)
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
      (hsnapshot s) hbatchBody (hbatch s) hupdate hcore hstatus hreportBody (hreport s) hchecked hbudgetRecord
      L.names L.base L.lower L.upper L.flow heap L.cost L.residual L.alpha L.one L.slackMin L.slackMax
      L.exponent L.lengths L.gradient L.graph L.request L.gradientMin L.gradientMax L.lengthMin
      Pt.machine.mem Pt.machine.pos ω capacity normalization hPacket hBudgetWord hPre hI hGraph hGraphEnd hGraphWords
      (hGuard _ (by simp)) (hGuard _ (by simp)) (hGuard _ (by simp)) (hGuard _ (by simp))
      hRequest hNormLo hNormHi hNeg hMax hMin hQuality hPrecision
      (fun e he => ⟨(hRanges e he).1,(hRanges e he).2.1⟩)
      (fun e he => (hRanges e (Finset.mem_range.mp he)).2.2)
      hCapacity (fun ptr hp => hArrays ptr (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hp ⊢; tauto)) hSources hLength hAlpha hLower
      (fun e he => hCache e (Finset.mem_range.mp he))
      (fun e _ => ⟨congrFun hGOld e,congrFun hLOld e⟩) hCallSpace
  have hOutSpace := budgetedIteration_space_output F A I κ α rate allocation R B halloc hPre hOut
  have hResultWord : oI.value<2^w := hOutSpace.trans_lt hBlock
  obtain ⟨o,st,cost,hRunStep,hTrace,hRep',hCost',hStatus,hFixed⟩ :=
    budgetedIteration_loop_step_runs (E:=L.exponent) Pt.machine ω hbody
      (L.packet_args F I heap Pt.machine hRegs) hRun hOut hRep hCost hResultWord hOne
  dsimp only
  rw [← hState]
  exact ⟨o,st,cost,oI.value,s',y,hRunStep,hTrace,hRep',hFoot,hStatus,hFixed,hCard,hResultWord,hCost'⟩

theorem epochConditions_iteration_runs_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
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
    (initialMem : ℕ → ℕ) (initialHeap finish i B : ℕ) (Pt : EpochPoint R.τ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i Pt)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinishLe : finish ≤ I.m) :
    let s := minRatioState A.eraseFailure Pt.history Pt.eta Pt.op (2*i)
    ∃ o st cost v s' y,
      Runs w p ω (epochIterationsStep iteration) Pt.machine o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R L.handle s s' Pt.credit q K L.sourceEnd L.tableEnd
        (L.packet F I (Pt.machine.regs 8)) Pt.machine.mem v st.mem ∧
      R.rep L.handle s' y st.mem ∧
      (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle Pt.credit z ∨ Pt.machine.regs 8≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 8=v else o=.returned v) ∧
      (∀ j,j≠8 → j≠27 → j≠28 → st.regs j=Pt.machine.regs j) ∧
      (A.detect s).1.card≤I.m ∧ v<2^w ∧
      cost+R.phi L.handle y st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m L.exponent rate+
        37+R.phi L.handle Pt.credit Pt.machine.mem :=
  epochConditions_iteration_runs_at_range_upTo_on_at F A I U E κ α Ψ eps rate allocation R hA hP
    L q K himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    initialMem initialHeap finish i B Pt ω capacity normalization hWide hstatic hcond halloc hspace
    hbudgetFit hOne hfinishLe

/-- Execute the actual epoch call from its current loop conditions,
retaining the returned state, report count, frames and amortized charge. -/
theorem epochConditions_iteration_runs_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
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
    (initialMem : ℕ → ℕ) (initialHeap finish i B : ℕ) (P : EpochPoint R.τ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i P)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinishLe : finish ≤ I.m) :
    let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
    ∃ o st cost v s' y,
      Runs w p ω (epochIterationsStep iteration) P.machine o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R L.handle s s' P.credit q K L.sourceEnd L.tableEnd
        (L.packet F I (P.machine.regs 8)) P.machine.mem v st.mem ∧
      R.rep L.handle s' y st.mem ∧
      (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ P.machine.regs 8≤z)) ∧
      (if st.mem (v-1)=1 then o=.normal ∧ st.regs 8=v else o=.returned v) ∧
      (∀ j,j≠8 → j≠27 → j≠28 → st.regs j=P.machine.regs j) ∧
      (A.detect s).1.card≤I.m ∧ v<2^w ∧
      cost+R.phi L.handle y st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m L.exponent rate+
        37+R.phi L.handle P.credit P.machine.mem :=
  epochConditions_iteration_runs_at_range_upTo_on F A I U E κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L q K himpl hrawDetect hdetect hstore hquery hcoefficient
    hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody
    hreport hchecked hbudgetRecord hbody initialMem initialHeap finish i B P ω capacity normalization
    hWide hstatic hcond halloc hspace hbudgetFit hOne hfinishLe

end MinCostFlow.IPM.Machine
