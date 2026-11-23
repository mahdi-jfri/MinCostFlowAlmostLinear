module

public import MinCostFlow.IPM.Machine.EpochCompleteProgram
public import MinCostFlow.IPM.Machine.TargetEpochCompleteTail
public import MinCostFlow.IPM.Machine.TargetEpochArguments
public import MinCostFlow.IPM.Machine.TargetEpochStatic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Running the finite epoch after startup accepts

The caller keeps the startup credit, runs the complete epoch with the
fresh initialized packet, and writes the exact status record. The
proof uses the actual fixed-point flow returned by the full read.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 500000 in
/-- Execute the complete epoch through the real target-stage caller,
starting from the initialized cache and actual register values. -/
theorem targetEpoch_accepted_runs_upTo_at {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
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
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (old : EpochLayout) (tp qp source oldHeap B initEnd : ℕ) (before : State) (x : R.τ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,before.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hR : before.regs 24=oldHeap+(8*I.m+3)*F.limbs)
    (hF : before.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : before.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hInit : before.regs 25=initEnd+I.m+3) (hInitBit : before.regs 26=1)
    (hPrefix : ∀ z<oldHeap,before.mem z=mem z)
    (hqbits : q=ipmErrorBits I.m U)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hdata : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
      let s := A.init (namedInstance I)
        (readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let heap := initEnd+I.m+3
      EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
        L (U:ℝ) ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) before.mem ∧
      L.handle≤ initEnd ∧ epochVector F I before.mem L.base=epochVector F I mem source ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r before.mem ∧
      (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
        s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) before.mem ∧
      before.mem (heap-3)=5*I.m ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e before.mem) ∧
      (∀ e<I.m,Num.Valid before.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid before.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
        (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
        readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)) :
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
    ∃ out final cost,
      Runs w p ω (targetEpochAfterInit complete statusRecord) before (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤ initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2 ∧
      cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem := by
  dsimp only
  let a := Num.IPM.alphaPrime I.m U
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let L := old.next F I source rp fp (fp+I.m*F.limbs) initEnd
  let heap := initEnd+I.m+3
  obtain ⟨hstatic,hhandle,hbase,hsource,hpre,hbudget,hcache,hranges⟩ := hdata
  have hHandle : L.handle ≤ initEnd := hhandle
  have hhandleWord : L.handle<2^w := by omega
  have hHeapWord : heap<2^w := by change heap+_+2<2^w at hspace; omega
  have hM : I.m<2^w := by omega
  have hFP : fp<2^w := hstatic.1 fp (by simp [EpochLayout.packet,fp,EpochLayout.next])
  have hargs := targetEpoch_complete_args F I old tp qp source oldHeap rp fp (fp+I.m*F.limbs)
    initEnd heap before hregs hR hF hH hInit rfl hHeapWord (by omega) hhandleWord
  have hres' : r=residual I target (epochVector F I before.mem L.base) := by rw [hbase]; exact hres
  have hin := hbase.symm ▸ hflow.inside
  have hroute := hbase.symm ▸ hflow.2.1.1
  obtain ⟨v,st,c,y,loopEnd,loopState,loopCredit,hRun,hWord,hHi,hPost,hPromise,hLo,hBit,hZero,hFrame,hCost⟩ :=
    epochComplete_runs_with_potential_upTo_at F A I U κ target r rate allocation R hA L K q
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
      hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody hiterations
      heap I.m B x before.mem before.pos ω U hstatic halloc (by exact lt_of_le_of_lt (Nat.le_add_right _ 2) hspace)
      hFiveM (by omega) hM hpre hbudget hcache hranges hqbits hstatic.1 le_rfl hsource hE hm hU hsize
      hnums hFlo hκ hκ' hxlo hres' hr hin hroute
  have hmul := mul_pos hκ ha
  have hmul' : κ*a≤1 := (mul_le_mul_of_nonneg_left ha' hκ.le).trans (by simpa using hκ')
  have hq : 0<κ*a/32 := div_pos hmul (by norm_num)
  have hq' : κ*a/32≤1/2 := by linarith only [hmul']
  obtain ⟨hNo,hYes⟩ := targetEpoch_complete_result_upTo F A I U κ target r hA rate allocation R L q K
    heap (budgetedIterationSpace F I.m old.exponent B) loopEnd before.mem loopState loopCredit
    hPost hPromise hFrame hsource hstatic.2.2.2.2.2.1
    ⟨hstatic.2.2.2.2.2.2.1 rp (by simp [EpochLayout.next,rp]),
      hstatic.2.2.2.2.2.2.1 old.alpha (by simp [EpochLayout.next])⟩
    hm hU hsize hnums hFlo hq hq' hres'.symm hr hin hroute hE
  rw [hbase] at hNo hYes
  have hOld : oldHeap≤fp := Nat.le_add_right _ _
  have hNon : 1/4<residual I target (epochVector F I mem source) := hres ▸ hr
  have hFrame' : ∀ z<oldHeap,st.mem z=mem z :=
    fun z hz => (hFrame z (hz.trans_le hOld)).trans (hPrefix z hz)
  have hFit : v+2<2^w := by
    change v≤heap+(I.m+1)*budgetedIterationSpace F I.m old.exponent B at hHi
    exact lt_of_le_of_lt (Nat.add_le_add_right hHi 2) hspace
  obtain ⟨out,final,cost,hActual,hResult,hEnd,hC⟩ :=
    targetEpoch_complete_tail before st hcomplete hargs hRun hstatusRecord F I U old.exponent fp κ target mem
      hF hInitBit (hOld.trans hLo) hFP hFit hZero hBit hFrame' hNon hNo hYes
  refine ⟨out,final,cost,hActual,hResult,?_,?_⟩
  · rw [hEnd]
    exact Nat.add_le_add_right hHi 2
  · change cost≤c+36+60 at hC
    change c+R.phi L.handle y st.mem≤(6*I.m+I.m)*budgetedIterationCharge F I.m old.exponent rate+
      46*I.m+I.m*reportedEdgesCharge F I.m old.exponent rate+200+R.phi L.handle x before.mem at hCost
    rw [show 6*I.m+I.m=7*I.m by omega] at hCost
    change cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
      I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem
    omega

theorem targetEpoch_accepted_runs_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
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
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (old : EpochLayout) (tp qp source oldHeap B initEnd : ℕ) (before : State) (x : R.τ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,before.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hR : before.regs 24=oldHeap+(8*I.m+3)*F.limbs)
    (hF : before.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : before.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hInit : before.regs 25=initEnd+I.m+3) (hInitBit : before.regs 26=1)
    (hPrefix : ∀ z<oldHeap,before.mem z=mem z)
    (hqbits : q=ipmErrorBits I.m U)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hdata : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
      let s := A.init (namedInstance I)
        (readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let heap := initEnd+I.m+3
      EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
        L (U:ℝ) ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) before.mem ∧
      L.handle≤ initEnd ∧ epochVector F I before.mem L.base=epochVector F I mem source ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r before.mem ∧
      (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
        s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) before.mem ∧
      before.mem (heap-3)=5*I.m ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e before.mem) ∧
      (∀ e<I.m,Num.Valid before.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid before.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
        (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
        readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)) :
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
    ∃ out final cost,
      Runs w p ω (targetEpochAfterInit complete statusRecord) before (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤ initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2 ∧
      cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem :=
  targetEpoch_accepted_runs_upTo_at F A I U κ target r rate allocation R hA himpl hrawDetect hdetect
    hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch
    hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody hiterations hcomplete
    hstatusRecord old tp qp source oldHeap B initEnd before x mem ω hregs hR hF hH hInit hInitBit
    hPrefix hqbits halloc hspace hFiveM hEight hE hm hU hsize hnums hFlo hκ hκ' hxlo ha ha' hres
    hr hflow hdata

/-- Execute the complete epoch through the real target-stage caller,
starting from the initialized cache and actual register values. -/
theorem targetEpoch_accepted_runs {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
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
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (old : EpochLayout) (tp qp source oldHeap B initEnd : ℕ) (before : State) (x : R.τ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,before.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hR : before.regs 24=oldHeap+(8*I.m+3)*F.limbs)
    (hF : before.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : before.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hInit : before.regs 25=initEnd+I.m+3) (hInitBit : before.regs 26=1)
    (hPrefix : ∀ z<oldHeap,before.mem z=mem z)
    (hqbits : q=ipmErrorBits I.m U)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hdata : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
      let s := A.init (namedInstance I)
        (readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let heap := initEnd+I.m+3
      EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
        L (U:ℝ) ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) before.mem ∧
      L.handle≤ initEnd ∧ epochVector F I before.mem L.base=epochVector F I mem source ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r before.mem ∧
      (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
        s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) before.mem ∧
      before.mem (heap-3)=5*I.m ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e before.mem) ∧
      (∀ e<I.m,Num.Valid before.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid before.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
        (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
        readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)) :
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
    ∃ out final cost,
      Runs w p ω (targetEpochAfterInit complete statusRecord) before (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤ initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2 ∧
      cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem :=
  targetEpoch_accepted_runs_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n) himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord
    hbody hiterations hcomplete hstatusRecord old tp qp source oldHeap B initEnd before x mem ω
    hregs hR hF hH hInit hInitBit hPrefix hqbits halloc hspace hFiveM hEight hE hm hU hsize
    hnums hFlo hκ hκ' hxlo ha ha' hres hr hflow hdata

/-- Execute the complete epoch through the real target-stage caller,
starting from the initialized cache and actual register values. -/
theorem targetEpoch_accepted_runs_widened_upTo_on_at {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
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
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (old : EpochLayout) (tp qp source oldHeap B initEnd : ℕ) (before : State) (x : R.τ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,before.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hR : before.regs 24=oldHeap+(8*I.m+3)*F.limbs)
    (hF : before.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : before.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hInit : before.regs 25=initEnd+I.m+3) (hInitBit : before.regs 26=1)
    (hPrefix : ∀ z<oldHeap,before.mem z=mem z)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hdata : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
      let s := A.init (namedInstance I)
        (readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let heap := initEnd+I.m+3
      EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
        L (U:ℝ) ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) before.mem ∧
      L.handle≤ initEnd ∧ epochVector F I before.mem L.base=epochVector F I mem source ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r before.mem ∧
      (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
        s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) before.mem ∧
      before.mem (heap-3)=5*I.m ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e before.mem) ∧
      (∀ e<I.m,Num.Valid before.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid before.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
        (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
        readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)) :
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
    ∃ out final cost,
      Runs w p ω (targetEpochAfterInit complete statusRecord) before (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤ initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2 ∧
      cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem := by
  dsimp only
  let a := Num.IPM.alphaPrime I.m U
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let L := old.next F I source rp fp (fp+I.m*F.limbs) initEnd
  let heap := initEnd+I.m+3
  obtain ⟨hstatic,hhandle,hbase,hsource,hpre,hbudget,hcache,hranges⟩ := hdata
  have hHandle : L.handle ≤ initEnd := hhandle
  have hhandleWord : L.handle<2^w := by omega
  have hHeapWord : heap<2^w := by change heap+_+2<2^w at hspace; omega
  have hM : I.m<2^w := by omega
  have hFP : fp<2^w := hstatic.1 fp (by simp [EpochLayout.packet,fp,EpochLayout.next])
  have hargs := targetEpoch_complete_args F I old tp qp source oldHeap rp fp (fp+I.m*F.limbs)
    initEnd heap before hregs hR hF hH hInit rfl hHeapWord (by omega) hhandleWord
  have hres' : r=residual I target (epochVector F I before.mem L.base) := by rw [hbase]; exact hres
  have hin := hbase.symm ▸ hflow.inside
  have hroute := hbase.symm ▸ hflow.2.1.1
  obtain ⟨v,st,c,y,loopEnd,loopState,loopCredit,hRun,hWord,hHi,hPost,hPromise,hLo,hBit,hZero,hFrame,hCost⟩ :=
    epochComplete_runs_with_potential_widened_upTo_on_at F A I U k κ target r rate allocation R hA hP L K q
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
      hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody hiterations
      heap I.m B x before.mem before.pos ω U hstatic halloc (by exact lt_of_le_of_lt (Nat.le_add_right _ 2) hspace)
      hFiveM (by omega) hM hpre hbudget hcache hranges hqbits hstatic.1 le_rfl hsource hE hm hU hsize
      hnums hFlo hκ hκ' hxlo hres' hr hin hroute
  have hmul := mul_pos hκ ha
  have hmul' : κ*a≤1 := (mul_le_mul_of_nonneg_left ha' hκ.le).trans (by simpa using hκ')
  have hq : 0<κ*a/32 := div_pos hmul (by norm_num)
  have hq' : κ*a/32≤1/2 := by linarith only [hmul']
  have hWide : ipmRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  obtain ⟨hNo,hYes⟩ := targetEpoch_complete_result_at_range_upTo_on F A I U (ipmQualityRangeExponent I.m U k) κ target r hA hP rate allocation R L q K
    heap (budgetedIterationSpace F I.m old.exponent B) loopEnd before.mem loopState loopCredit
    hPost hPromise hFrame hsource hstatic.2.2.2.2.2.1
    ⟨hstatic.2.2.2.2.2.2.1 rp (by simp [EpochLayout.next,rp]),
      hstatic.2.2.2.2.2.2.1 old.alpha (by simp [EpochLayout.next])⟩
    hm hU hsize hnums hFlo hq hq' hres'.symm hr hin hroute hE hWide
  rw [hbase] at hNo hYes
  have hOld : oldHeap≤fp := Nat.le_add_right _ _
  have hNon : 1/4<residual I target (epochVector F I mem source) := hres ▸ hr
  have hFrame' : ∀ z<oldHeap,st.mem z=mem z :=
    fun z hz => (hFrame z (hz.trans_le hOld)).trans (hPrefix z hz)
  have hFit : v+2<2^w := by
    change v≤heap+(I.m+1)*budgetedIterationSpace F I.m old.exponent B at hHi
    exact lt_of_le_of_lt (Nat.add_le_add_right hHi 2) hspace
  obtain ⟨out,final,cost,hActual,hResult,hEnd,hC⟩ :=
    targetEpoch_complete_tail before st hcomplete hargs hRun hstatusRecord F I U old.exponent fp κ target mem
      hF hInitBit (hOld.trans hLo) hFP hFit hZero hBit hFrame' hNon hNo hYes
  refine ⟨out,final,cost,hActual,hResult,?_,?_⟩
  · rw [hEnd]
    exact Nat.add_le_add_right hHi 2
  · change cost≤c+36+60 at hC
    change c+R.phi L.handle y st.mem≤(6*I.m+I.m)*budgetedIterationCharge F I.m old.exponent rate+
      46*I.m+I.m*reportedEdgesCharge F I.m old.exponent rate+200+R.phi L.handle x before.mem at hCost
    rw [show 6*I.m+I.m=7*I.m by omega] at hCost
    change cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
      I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem
    omega

theorem targetEpoch_accepted_runs_widened_upTo_on {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
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
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (old : EpochLayout) (tp qp source oldHeap B initEnd : ℕ) (before : State) (x : R.τ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,before.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hR : before.regs 24=oldHeap+(8*I.m+3)*F.limbs)
    (hF : before.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : before.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hInit : before.regs 25=initEnd+I.m+3) (hInitBit : before.regs 26=1)
    (hPrefix : ∀ z<oldHeap,before.mem z=mem z)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hdata : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
      let s := A.init (namedInstance I)
        (readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let heap := initEnd+I.m+3
      EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
        L (U:ℝ) ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) before.mem ∧
      L.handle≤ initEnd ∧ epochVector F I before.mem L.base=epochVector F I mem source ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r before.mem ∧
      (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
        s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) before.mem ∧
      before.mem (heap-3)=5*I.m ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e before.mem) ∧
      (∀ e<I.m,Num.Valid before.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid before.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
        (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
        readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)) :
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
    ∃ out final cost,
      Runs w p ω (targetEpochAfterInit complete statusRecord) before (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤ initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2 ∧
      cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem :=
  targetEpoch_accepted_runs_widened_upTo_on_at F A I U k κ target r rate allocation R hA hP himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    hiterations hcomplete hstatusRecord old tp qp source oldHeap B initEnd before x mem ω hregs hR
    hF hH hInit hInitBit hPrefix hqbits halloc hspace hFiveM hEight hE hm hU hsize hnums hFlo hκ
    hκ' hxlo ha ha' hres hr hflow hdata

/-- Execute the complete epoch through the real target-stage caller,
starting from the initialized cache and actual register values. -/
theorem targetEpoch_accepted_runs_widened_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
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
    (hcomplete : p.procs[complete]?=some (epochCompleteBody iterations refresh))
    (hstatusRecord : MeetsContract w p statusRecord (boundedStatusRecordContract w 2))
    (old : EpochLayout) (tp qp source oldHeap B initEnd : ℕ) (before : State) (x : R.τ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,before.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hR : before.regs 24=oldHeap+(8*I.m+3)*F.limbs)
    (hF : before.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : before.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hInit : before.regs 25=initEnd+I.m+3) (hInitBit : before.regs 26=1)
    (hPrefix : ∀ z<oldHeap,before.mem z=mem z)
    (hqbits : q=ipmQualityErrorBits I.m U k)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2<2^w)
    (hFiveM : 5*I.m<2^w) (hEight : 8<2^w)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (ha : 0<Num.IPM.alphaPrime I.m U) (ha' : Num.IPM.alphaPrime I.m U≤1)
    (hres : r=residual I target (epochVector F I mem source)) (hr : 1/4<r)
    (hflow : TargetStageFlow F I old.exponent source oldHeap mem)
    (hdata : let fp := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
      let s := A.init (namedInstance I)
        (readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let heap := initEnd+I.m+3
      EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
        L (U:ℝ) ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) before.mem ∧
      L.handle≤ initEnd ∧ epochVector F I before.mem L.base=epochVector F I mem source ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r before.mem ∧
      (detectRefreshContract F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L.handle
        s x q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) before.mem ∧
      before.mem (heap-3)=5*I.m ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e before.mem) ∧
      (∀ e<I.m,Num.Valid before.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid before.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |readVector before.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
        (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
        readVector before.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)) :
    let fp := epochResidualEnd I.m F.limbs oldHeap
    let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) fp (fp+I.m*F.limbs) initEnd
    ∃ out final cost,
      Runs w p ω (targetEpochAfterInit complete statusRecord) before (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤ initEnd+I.m+3+(I.m+1)*budgetedIterationSpace F I.m old.exponent B+2 ∧
      cost≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x before.mem :=
  targetEpoch_accepted_runs_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) himpl hrawDetect hdetect hstore hquery hcoefficient
    hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
    hreportBody hreport hchecked hbudgetRecord hbody hiterations hcomplete hstatusRecord old tp qp
    source oldHeap B initEnd before x mem ω hregs hR hF hH hInit hInitBit hPrefix hqbits halloc
    hspace hFiveM hEight hE hm hU hsize hnums hFlo hκ hκ' hxlo ha ha' hres hr hflow hdata

end MinCostFlow.IPM.Machine
