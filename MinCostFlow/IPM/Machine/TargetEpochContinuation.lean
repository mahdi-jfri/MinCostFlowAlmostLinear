module

public import MinCostFlow.IPM.Machine.TargetEpochAcceptedRun
public import MinCostFlow.IPM.Machine.TargetEpochStartupOutput
public import MinCostFlow.IPM.Machine.TargetEpochNumericalInput
public import MinCostFlow.IPM.Machine.TargetEpochResources
public import MinCostFlow.IPM.Machine.TargetEpochBranchRun
public import MinCostFlow.IPM.Machine.TargetEpochWordInputs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Executing the continuing residual branch

The residual guard supplies a fresh exact copy of the current flow.
Startup can reject before the lazy loop. If it accepts, the complete
epoch returns either a failure or the next materialized flow. The
actual data structure credit is charged once over the full branch.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

theorem targetEpoch_continuation_of_startup_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContractAt F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation initPre))
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
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (_hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : checked.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (_hLarge : 2<epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
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
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) checked.mem)
    (initStmt branch : Stmt)
    (hBranchContinue : ∀ after out final c₁ c₂,
      Runs w p ω initStmt checked .normal after c₁ →
      Runs w p ω (targetEpochAfterInit complete statusRecord) after (.returned out) final c₂ →
      Runs w p ω branch checked (.returned out) final (c₁+c₂+5))
    (hStartupCall : TargetEpochStartupPost (q:=q) (K:=K) F A I κ (Num.IPM.alphaPrime I.m U/8)
      rate allocation R p initStmt old source oldHeap 931 checked ω) :
    ∃ out final cost,
      Runs w p ω branch checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate := by
  let a := Num.IPM.alphaPrime I.m U
  let eps := κ*a/1024
  let norm := (25/32:ℝ)*(κ*a/32)^2/50
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := fp+I.m*F.limbs
  let space := budgetedIterationSpace F I.m old.exponent B
  let startSpace := epochStartSpace F I old.exponent old.initGraph heap allocation
  have hsplit : heap+startSpace+I.m+4+(I.m+1)*space+2≤oldHeap+targetStageSpace F I.m old.exponent B :=
    targetStage_space_split F I old oldHeap B allocation halloc
  have hbound : heap+startSpace+I.m+4+(I.m+1)*space+2<2^w := hsplit.trans_lt hspace
  have hfp : oldHeap≤fp := Nat.le_add_right _ _
  have hfpHeap : fp≤heap := Nat.le_add_right _ _
  have hOld : oldHeap≤heap := hfp.trans hfpHeap
  have hRend : rp+F.limbs=fp := by
    simp [rp,fp,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hfpWord : fp<2^w := by omega
  have hrpWord : rp<2^w := by omega
  have hHeapWord : heap<2^w := by omega
  have hchecked := hfixed.frozen hframe hfp
  obtain ⟨end_,after,startCost,bit,coeffMem,hInit,hfixedRegs,
    hFlowReg,hResReg,hHeapReg,hBitReg,hCoeffReg,hRpost,hSpost,hBit,hz,hLo,hHi,
    hAfterFrame,hZeroCost,hSuccess⟩ := hStartupCall
  have hArrays : ∀ p∈[source,old.cost,old.lower,old.upper],p+I.m*F.limbs≤oldHeap := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | h
    · exact hflow.1
    · exact hfixed.arrays p h
  obtain ⟨hsource,hBase,hCopy,hBaseValid,_,hAEnd⟩ := targetEpoch_copied_sources F I old source oldHeap 0
    hframe hArrays hfixed.alpha (hfixed.scalars old.alpha (by simp)) hfixed.lower hfixed.upper hfixed.cost
    (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hR hcopy
  change epochVector F I checked.mem source=epochVector F I mem source at hBase
  change epochVector F I checked.mem fp=epochVector F I mem source at hCopy
  have hCopied : TargetStageFlow F I old.exponent fp heap checked.mem := by
    refine ⟨le_rfl,by rw [hCopy]; exact hflow.2.1,?_⟩
    intro e
    rw [hCopy]
    exact ⟨(hcopy e).1,(hflow.2.2 e).2⟩
  have hPair : epochVector F I checked.mem source=epochVector F I checked.mem fp := hBase.trans hCopy.symm
  have hResChecked : residual I target (epochVector F I checked.mem fp)=r := by rw [hCopy,← hres]
  have hAfterOld : ∀ z<oldHeap,after.mem z=mem z :=
    fun z hz' => (hAfterFrame z (hz'.trans_le hOld)).trans (hframe z hz')
  have hNon : 1/4<residual I target (epochVector F I mem source) := hres ▸ hr
  have hLo' : oldHeap≤end_ := hOld.trans hLo
  have hHi' : end_≤heap+startSpace+I.m+4 := hHi
  have hEndWord : end_+2<2^w := by omega
  by_cases hb : bit=1
  · obtain ⟨s,x,initEnd,initialized,named,hEnd,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hScan,hStartCost⟩ := hSuccess hb
    let L := old.next F I source rp fp heap initEnd
    obtain ⟨_,hbaseStarted,_,hsourceStarted,hcache⟩ :=
      targetEpoch_startup_output_upTo F A I U κ (a/8) _ eps hA hI rate allocation R old tp qp source rp fp heap initEnd
        1 checked.mem initialized named after.mem target norm r hchecked hOut hN hB hList hAfterFrame hScan
        ((hArrays source (by simp)).trans hfp) hRend.le le_rfl hCopied hPair hsource hResChecked hr
        hfmt hm hU hsize hnums hFlo ha.le ha'
    have hStarted : ∀ z<fp,after.mem z=checked.mem z := fun z hz' => hAfterFrame z (hz'.trans_le hfpHeap)
    have hfixed' := hchecked.frozen hStarted le_rfl
    have hBaseEq : epochVector F I after.mem L.base=epochVector F I mem source := hbaseStarted.trans hCopy
    have hStageCost : startCost+R.phi L.handle x after.mem≤
        Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
          Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
          I.m*(164*F.limbs+530)+931 := hStartCost
    have hInitEnd := hOut
    obtain ⟨_,_,_,_,_,_,hhandle,_⟩ := epochStart_output F A I κ (a/8) rate allocation R hInitEnd
    have hHandle : L.handle≤ initEnd := hhandle
    have hWordInit : initEnd<2^w := by omega
    have hNewWords := targetEpoch_complete_words F I old tp qp source oldHeap rp fp heap initEnd
      hwords hrpWord hfpWord hWordInit hHandle
    have hSmall : κ*a≤1 := (mul_le_mul_of_nonneg_left ha' hκ.le).trans (by simpa using hκ')
    have hEps : 0<eps := div_pos (mul_pos hκ ha) (by norm_num)
    have hEps' : eps≤1 := by dsimp only [eps]; linarith only [hSmall]
    have hstatic := hfixed'.epoch_static hI hnums hU hm hLower (hBaseEq.symm ▸ hflow.2.1)
      ((hArrays source (by simp)).trans hfp) hRend.le ha.le ha' hEps hEps' hfmt hNormLo hNormHi
      hquality hprecision hNewWords
    have hSpaceInit : initEnd+I.m+3+(I.m+1)*space+2<2^w := by omega
    have hSpaceFirst : initEnd+I.m+3+space<2^w := by
      have hz' : space≤(I.m+1)*space := Nat.le_mul_of_pos_left space (by omega)
      omega
    have hWidth (e : ℕ) (he : e<I.m) :
        Num.fixVal checked.mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
          Num.fixVal checked.mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^old.exponent := by
      let j : Fin I.m := ⟨e,he⟩
      rw [(hchecked.upper j).2,(hchecked.lower j).2,hE]
      obtain ⟨hlo,hup,_⟩ := hnums.2 j
      have htwice := twice_capacity_le_dyadic I.m U hm hU
      have hpow : (2:ℝ)^(slackRangeExponent I.m U)≤(2:ℝ)^(ipmRangeExponent I.m U) :=
        pow_le_pow_right₀ (by norm_num) (by unfold ipmRangeExponent; omega)
      linarith only [(abs_le.mp hlo).1,(abs_le.mp hup).2, htwice.trans hpow]
    have hEqual : ∀ e<I.m,
        Num.fixVal checked.mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
          Num.fixVal checked.mem (source+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision :=
      fun e he => congrFun hPair.symm ⟨e,he⟩
    have hInside (e : ℕ) (he : e<I.m) :
        Num.fixVal checked.mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
          Num.fixVal checked.mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
        Num.fixVal checked.mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
          Num.fixVal checked.mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
      let j : Fin I.m := ⟨e,he⟩
      rw [(hchecked.lower j).2,(hchecked.upper j).2]
      exact hCopied.inside j
    rw [hState] at hFit hRep
    obtain ⟨hpre,hbudget,hinitial,hranges⟩ := epochStartup_handoff_upTo F A I κ (a/8) _ eps hA hEps hI rate allocation R
      old source rp fp heap initEnd B x checked.mem initialized named after.mem hOut hN hB hList hAfterFrame hFit hRep hFoot
      hScan hchecked.slackMin hchecked.slackMax hfixed'.lengthMin hfixed'.gradientMin hfixed'.gradientMax
      hcoefficientPre hAEnd hstatic.2.2.2.2.2.2.1 le_rfl (fun e he => (hcopy ⟨e,he⟩).1)
      (fun e he => hBaseValid ⟨e,he⟩) hEqual hInside hWidth halloc hSpaceFirst
    obtain ⟨out,final,c,hTail,hResult,hEndOut,hCostOut⟩ :=
      targetEpoch_accepted_runs_upTo_at F A I U κ target r rate allocation R hA himpl hrawDetect hdetect hstore hquery
        hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
        hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
        old tp qp source oldHeap B initEnd after x mem ω
        (fun j hj => (hfixedRegs j hj).trans (hregs j hj)) hResReg hFlowReg hCoeffReg (hHeapReg.trans hEnd)
        (hBitReg.trans hb) hAfterOld hqbits halloc hSpaceInit hFiveM hEight hE hm hU hsize hnums hFlo hκ hκ' hxlo
        ha ha' hres hr hflow ⟨hstatic,hHandle,hBaseEq,hsourceStarted,hpre,hbudget,hinitial,hranges⟩
    refine ⟨out,final,startCost+c+5,hBranchContinue after out final startCost c hInit hTail,
      hResult,?_,?_⟩
    · change out ≤ initEnd+I.m+3+(I.m+1)*space+2 at hEndOut
      omega
    · change c≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x after.mem at hCostOut
      unfold targetStageContinuationCost
      omega
  · have hbitZero : bit=0 := by omega
    have hsourceWord := hwords source (by simp [targetEpochPacket])
    have hsrc : after.regs 20=source := (hfixedRegs 20 (by decide)).trans (hregs 20 (by decide))
    obtain ⟨out,final,c,hTail,hRecord,hFitOut,hCostOut⟩ :=
      targetEpochAfterInit_reject_runs after ω hstatusRecord hsrc hHeapReg (hBitReg.trans hbitZero)
        hsourceWord hEndWord hz
    have hNo : ¬TargetStagePromise I U target (epochVector F I mem source) := by
      rw [← hCopy]
      intro hp
      exact hb (targetEpoch_fullScan_accepts_at_range F I U old source rp fp heap bit target r
        checked.mem coeffMem hfmt.ge hsource hResChecked hr hm hU hsize hnums hFlo ha.le ha'
        hCopied.inside hCopied.2.1.1
        ((hchecked.scalars old.gradientMin (by simp)).trans hfpHeap)
        ((hchecked.scalars old.gradientMax (by simp)).trans hfpHeap)
        ((hchecked.scalars old.lengthMin (by simp)).trans hfpHeap)
        hchecked.gradientMin hchecked.gradientMax hchecked.lengthMin hRpost hSpost hp)
    have hResult := targetEpoch_continue_result F I U old.exponent κ target source oldHeap source end_ out 0
      hAfterOld hLo' hFitOut (by decide) hNon (fun _ => hNo)
      (fun h => by omega) hRecord
    have hStageCost := hZeroCost hbitZero
    refine ⟨out,final,startCost+c+5,hBranchContinue after out final startCost c hInit hTail,
      hResult,?_,?_⟩
    · have hEnd : out=end_+2 := hRecord.2
      omega
    · unfold targetStageContinuationCost
      omega

set_option maxHeartbeats 800000 in
/-- Run a new epoch after the exact residual test has requested one.
On every branch the result is the stage's actual fixed-point output. -/
theorem targetEpoch_continuation_runs_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
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
      Runs w p ω (targetEpochBranch startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate := by
  refine targetEpoch_continuation_of_startup_upTo F A I U κ target r rate allocation R hA
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord
    hbody hiterations hcomplete hstatusRecord old tp qp source oldHeap B checked mem ω hregs hF hH
    hLarge hwords hframe hqbits halloc hspace hFiveM hEight hE hm hU hsize hnums hI hLower hFlo hκ
    hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision hquality hNormLo hNormHi hR hcopy
    hcoefficientPre (targetEpochInit startup) (targetEpochBranch startup complete statusRecord)
    (fun after out final c₁ c₂ hInit hTail =>
      targetEpochBranch_continue_runs hH (by omega) (by omega) hInit hTail) ?_
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := fp+I.m*F.limbs
  let space := budgetedIterationSpace F I.m old.exponent B
  let startSpace := epochStartSpace F I old.exponent old.initGraph heap allocation
  have hsplit : heap+startSpace+I.m+4+(I.m+1)*space+2≤oldHeap+targetStageSpace F I.m old.exponent B :=
    targetStage_space_split F I old oldHeap B allocation halloc
  have hbound : heap+startSpace+I.m+4+(I.m+1)*space+2<2^w := hsplit.trans_lt hspace
  have hfp : oldHeap≤fp := Nat.le_add_right _ _
  have hfpHeap : fp≤heap := Nat.le_add_right _ _
  have hRend : rp+F.limbs=fp := by
    simp [rp,fp,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hfpWord : fp<2^w := by omega
  have hrpWord : rp<2^w := by omega
  have hHeapWord : heap<2^w := by omega
  have hchecked := hfixed.frozen hframe hfp
  obtain ⟨end_,after,startCost,bit,coeffMem,hInit,hfixedRegs,
    hFlowReg,hResReg,hHeapReg,hBitReg,hCoeffReg,hRpost,hSpost,hBit,hz,hLo,hHi,
    hAfterFrame,hZeroCost,hSuccess⟩ :=
    targetEpoch_startup_call F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R himpl hrefreshArrays
      hfullScan hinit hinitNames hnames hinitBudget hflag hstartup old tp qp source oldHeap checked ω
      hregs hF hH
      (targetEpoch_startup_words F I old tp qp source oldHeap rp fp heap 0 hwords hrpWord hfpWord hHeapWord)
      hI hchecked.graph hchecked.graphWordsFit (hchecked.graphEnd.trans hfpHeap)
      hquality hprecision hcoefficientPre (by omega) hFiveM (show heap+startSpace+I.m+4<2^w by omega)
      ((hchecked.scalars old.gradientMin (by simp)).trans hfpHeap)
      ((hchecked.scalars old.gradientMax (by simp)).trans hfpHeap)
      ((hchecked.scalars old.lengthMin (by simp)).trans hfpHeap)
      hchecked.gradientMin hchecked.gradientMax hchecked.lengthMin
  refine ⟨end_,after,startCost,bit,coeffMem,hInit,hfixedRegs,
    hFlowReg,hResReg,hHeapReg,hBitReg,hCoeffReg,hRpost,hSpost,hBit,hz,hLo,hHi,
    hAfterFrame,fun h0 => (hZeroCost h0).trans (by omega),fun h1 => ?_⟩
  obtain ⟨s,x,initEnd,initialized,named,hEnd,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hScan,hStartCost⟩ := hSuccess h1
  exact ⟨s,x,initEnd,initialized,named,hEnd,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hScan,by omega⟩

/-- Run a new epoch after the exact residual test has requested one.
On every branch the result is the stage's actual fixed-point output. -/
theorem targetEpoch_continuation_runs {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
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
      Runs w p ω (targetEpochBranch startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate :=
  targetEpoch_continuation_runs_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n)
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc
    hbudgetRecord hbody hiterations hcomplete hstatusRecord hrefreshArrays hfullScan hinit
    hinitNames hnames hinitBudget hstartup old tp qp source oldHeap B checked mem ω hregs
    hF hH hLarge hwords hframe hqbits halloc hspace hFiveM hEight hE hm hU hsize hnums hI hLower
    hFlo hκ hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision hquality hNormLo hNormHi hR
    hcopy hcoefficientPre

/-- Run a new epoch after the exact residual test has requested one.
Parameterized on the startup call so both 6-argument and `V`-passing startup share the body. -/
theorem targetEpoch_continuation_of_startup_widened_upTo_on {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContractAt F A (namedInstance I) I.m κ (Num.IPM.alphaPrime I.m U/8) rate allocation initPre))
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
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (_hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hH : checked.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (_hLarge : 2<epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
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
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) checked.mem)
    (initStmt branch : Stmt)
    (hBranchContinue : ∀ after out final c₁ c₂,
      Runs w p ω initStmt checked .normal after c₁ →
      Runs w p ω (targetEpochAfterInit complete statusRecord) after (.returned out) final c₂ →
      Runs w p ω branch checked (.returned out) final (c₁+c₂+5))
    (hStartupCall : TargetEpochStartupPost (q:=q) (K:=K) F A I κ (Num.IPM.alphaPrime I.m U/8)
      rate allocation R p initStmt old source oldHeap 931 checked ω) :
    ∃ out final cost,
      Runs w p ω branch checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate := by
  let a := Num.IPM.alphaPrime I.m U
  let eps := κ*a/1024
  let norm := (25/32:ℝ)*(κ*a/32)^2/50
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := fp+I.m*F.limbs
  let space := budgetedIterationSpace F I.m old.exponent B
  let startSpace := epochStartSpace F I old.exponent old.initGraph heap allocation
  have hsplit : heap+startSpace+I.m+4+(I.m+1)*space+2≤oldHeap+targetStageSpace F I.m old.exponent B :=
    targetStage_space_split F I old oldHeap B allocation halloc
  have hbound : heap+startSpace+I.m+4+(I.m+1)*space+2<2^w := hsplit.trans_lt hspace
  have hfp : oldHeap≤fp := Nat.le_add_right _ _
  have hfpHeap : fp≤heap := Nat.le_add_right _ _
  have hOld : oldHeap≤heap := hfp.trans hfpHeap
  have hRend : rp+F.limbs=fp := by
    simp [rp,fp,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hfpWord : fp<2^w := by omega
  have hrpWord : rp<2^w := by omega
  have hHeapWord : heap<2^w := by omega
  have hchecked := hfixed.frozen hframe hfp
  obtain ⟨end_,after,startCost,bit,coeffMem,hInit,hfixedRegs,
    hFlowReg,hResReg,hHeapReg,hBitReg,hCoeffReg,hRpost,hSpost,hBit,hz,hLo,hHi,
    hAfterFrame,hZeroCost,hSuccess⟩ := hStartupCall
  have hArrays : ∀ p∈[source,old.cost,old.lower,old.upper],p+I.m*F.limbs≤oldHeap := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | h
    · exact hflow.1
    · exact hfixed.arrays p h
  obtain ⟨hsource,hBase,hCopy,hBaseValid,_,hAEnd⟩ := targetEpoch_copied_sources F I old source oldHeap 0
    hframe hArrays hfixed.alpha (hfixed.scalars old.alpha (by simp)) hfixed.lower hfixed.upper hfixed.cost
    (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hR hcopy
  change epochVector F I checked.mem source=epochVector F I mem source at hBase
  change epochVector F I checked.mem fp=epochVector F I mem source at hCopy
  have hCopied : TargetStageFlow F I old.exponent fp heap checked.mem := by
    refine ⟨le_rfl,by rw [hCopy]; exact hflow.2.1,?_⟩
    intro e
    rw [hCopy]
    exact ⟨(hcopy e).1,(hflow.2.2 e).2⟩
  have hPair : epochVector F I checked.mem source=epochVector F I checked.mem fp := hBase.trans hCopy.symm
  have hResChecked : residual I target (epochVector F I checked.mem fp)=r := by rw [hCopy,← hres]
  have hWide : ipmRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    have h := slackRangeExponent_le_qualitySlackExponent I.m U k
    unfold ipmRangeExponent ipmQualityRangeExponent
    omega
  have hAfterOld : ∀ z<oldHeap,after.mem z=mem z :=
    fun z hz' => (hAfterFrame z (hz'.trans_le hOld)).trans (hframe z hz')
  have hNon : 1/4<residual I target (epochVector F I mem source) := hres ▸ hr
  have hLo' : oldHeap≤end_ := hOld.trans hLo
  have hHi' : end_≤heap+startSpace+I.m+4 := hHi
  have hEndWord : end_+2<2^w := by omega
  by_cases hb : bit=1
  · obtain ⟨s,x,initEnd,initialized,named,hEnd,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hScan,hStartCost⟩ := hSuccess hb
    let L := old.next F I source rp fp heap initEnd
    obtain ⟨_,hbaseStarted,_,hsourceStarted,hcache⟩ :=
      targetEpoch_startup_output_at_range_upTo_on F A I U κ (a/8) _ eps hA hP hI rate allocation R old tp qp source rp fp heap initEnd
        1 checked.mem initialized named after.mem target norm r hchecked hOut hN hB hList hAfterFrame hScan
        ((hArrays source (by simp)).trans hfp) hRend.le le_rfl hCopied hPair hsource hResChecked hr
        (hWide.trans_eq hfmt.symm) hm hU hsize hnums hFlo ha.le ha'
    have hStarted : ∀ z<fp,after.mem z=checked.mem z := fun z hz' => hAfterFrame z (hz'.trans_le hfpHeap)
    have hfixed' := hchecked.frozen hStarted le_rfl
    have hBaseEq : epochVector F I after.mem L.base=epochVector F I mem source := hbaseStarted.trans hCopy
    have hStageCost : startCost+R.phi L.handle x after.mem≤
        Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
          Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
          I.m*(164*F.limbs+530)+931 := hStartCost
    have hInitEnd := hOut
    obtain ⟨_,_,_,_,_,_,hhandle,_⟩ := epochStart_output F A I κ (a/8) rate allocation R hInitEnd
    have hHandle : L.handle≤ initEnd := hhandle
    have hWordInit : initEnd<2^w := by omega
    have hNewWords := targetEpoch_complete_words F I old tp qp source oldHeap rp fp heap initEnd
      hwords hrpWord hfpWord hWordInit hHandle
    have hSmall : κ*a≤1 := (mul_le_mul_of_nonneg_left ha' hκ.le).trans (by simpa using hκ')
    have hEps : 0<eps := div_pos (mul_pos hκ ha) (by norm_num)
    have hEps' : eps≤1 := by dsimp only [eps]; linarith only [hSmall]
    have hstatic := hfixed'.epoch_static_at hI hnums hU hm hLower (hBaseEq.symm ▸ hflow.2.1)
      ((hArrays source (by simp)).trans hfp) hRend.le ha.le ha' hEps hEps' hfmt hNormLo hNormHi
      hquality hprecision hNewWords
    have hSpaceInit : initEnd+I.m+3+(I.m+1)*space+2<2^w := by omega
    have hSpaceFirst : initEnd+I.m+3+space<2^w := by
      have hz' : space≤(I.m+1)*space := Nat.le_mul_of_pos_left space (by omega)
      omega
    have hWidth (e : ℕ) (he : e<I.m) :
        Num.fixVal checked.mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
          Num.fixVal checked.mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^old.exponent := by
      let j : Fin I.m := ⟨e,he⟩
      rw [(hchecked.upper j).2,(hchecked.lower j).2,hE]
      obtain ⟨hlo,hup,_⟩ := hnums.2 j
      have htwice := twice_capacity_le_dyadic I.m U hm hU
      have hpow : (2:ℝ)^(slackRangeExponent I.m U)≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) :=
        pow_le_pow_right₀ (by norm_num) (by
          have hs := slackRangeExponent_le_qualitySlackExponent I.m U k
          unfold ipmQualityRangeExponent
          omega)
      linarith only [(abs_le.mp hlo).1,(abs_le.mp hup).2, htwice.trans hpow]
    have hEqual : ∀ e<I.m,
        Num.fixVal checked.mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
          Num.fixVal checked.mem (source+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision :=
      fun e he => congrFun hPair.symm ⟨e,he⟩
    have hInside (e : ℕ) (he : e<I.m) :
        Num.fixVal checked.mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
          Num.fixVal checked.mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
        Num.fixVal checked.mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
          Num.fixVal checked.mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
      let j : Fin I.m := ⟨e,he⟩
      rw [(hchecked.lower j).2,(hchecked.upper j).2]
      exact hCopied.inside j
    rw [hState] at hFit hRep
    obtain ⟨hpre,hbudget,hinitial,hranges⟩ := epochStartup_handoff_upTo_on F A I κ (a/8) _ eps hA hP hEps hI rate allocation R
      old source rp fp heap initEnd B x checked.mem initialized named after.mem hOut hN hB hList hAfterFrame hFit hRep hFoot
      hScan hchecked.slackMin hchecked.slackMax hfixed'.lengthMin hfixed'.gradientMin hfixed'.gradientMax
      hcoefficientPre hAEnd hstatic.2.2.2.2.2.2.1 le_rfl (fun e he => (hcopy ⟨e,he⟩).1)
      (fun e he => hBaseValid ⟨e,he⟩) hEqual hInside hWidth halloc hSpaceFirst
    obtain ⟨out,final,c,hTail,hResult,hEndOut,hCostOut⟩ :=
      targetEpoch_accepted_runs_widened_upTo_on_at F A I U k κ target r rate allocation R hA hP himpl hrawDetect hdetect hstore hquery
        hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
        hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
        old tp qp source oldHeap B initEnd after x mem ω
        (fun j hj => (hfixedRegs j hj).trans (hregs j hj)) hResReg hFlowReg hCoeffReg (hHeapReg.trans hEnd)
        (hBitReg.trans hb) hAfterOld hqbits halloc hSpaceInit hFiveM hEight hE hm hU hsize hnums hFlo hκ hκ' hxlo
        ha ha' hres hr hflow ⟨hstatic,hHandle,hBaseEq,hsourceStarted,hpre,hbudget,hinitial,hranges⟩
    refine ⟨out,final,startCost+c+5,hBranchContinue after out final startCost c hInit hTail,
      hResult,?_,?_⟩
    · change out ≤ initEnd+I.m+3+(I.m+1)*space+2 at hEndOut
      omega
    · change c≤7*I.m*budgetedIterationCharge F I.m old.exponent rate+46*I.m+
        I.m*reportedEdgesCharge F I.m old.exponent rate+296+R.phi L.handle x after.mem at hCostOut
      unfold targetStageContinuationCost
      omega
  · have hbitZero : bit=0 := by omega
    have hsourceWord := hwords source (by simp [targetEpochPacket])
    have hsrc : after.regs 20=source := (hfixedRegs 20 (by decide)).trans (hregs 20 (by decide))
    obtain ⟨out,final,c,hTail,hRecord,hFitOut,hCostOut⟩ :=
      targetEpochAfterInit_reject_runs after ω hstatusRecord hsrc hHeapReg (hBitReg.trans hbitZero)
        hsourceWord hEndWord hz
    have hNo : ¬TargetStagePromise I U target (epochVector F I mem source) := by
      rw [← hCopy]
      intro hp
      exact hb (targetEpoch_fullScan_accepts_at_range F I U old source rp fp heap bit target r
        checked.mem coeffMem (hWide.trans_eq hfmt.symm) hsource hResChecked hr hm hU hsize hnums hFlo ha.le ha'
        hCopied.inside hCopied.2.1.1
        ((hchecked.scalars old.gradientMin (by simp)).trans hfpHeap)
        ((hchecked.scalars old.gradientMax (by simp)).trans hfpHeap)
        ((hchecked.scalars old.lengthMin (by simp)).trans hfpHeap)
        hchecked.gradientMin hchecked.gradientMax hchecked.lengthMin hRpost hSpost hp)
    have hResult := targetEpoch_continue_result F I U old.exponent κ target source oldHeap source end_ out 0
      hAfterOld hLo' hFitOut (by decide) hNon (fun _ => hNo)
      (fun h => by omega) hRecord
    have hStageCost := hZeroCost hbitZero
    refine ⟨out,final,startCost+c+5,hBranchContinue after out final startCost c hInit hTail,
      hResult,?_,?_⟩
    · have hEnd : out=end_+2 := hRecord.2
      omega
    · unfold targetStageContinuationCost
      omega

/-- Run a new epoch after the exact residual test has requested one.
On every branch the result is the stage's actual fixed-point output. -/
theorem targetEpoch_continuation_runs_widened_upTo_on {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
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
      Runs w p ω (targetEpochBranch startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate := by
  refine targetEpoch_continuation_of_startup_widened_upTo_on F A I U k κ target r rate allocation R hA
    hP himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hcheckedProc hbudgetRecord
    hbody hiterations hcomplete hstatusRecord old tp qp source oldHeap B checked mem ω hregs hF hH
    hLarge hwords hframe hqbits halloc hspace hFiveM hEight hE hm hU hsize hnums hI hLower hFlo hκ
    hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision hquality hNormLo hNormHi hR hcopy
    hcoefficientPre (targetEpochInit startup) (targetEpochBranch startup complete statusRecord)
    (fun after out final c₁ c₂ hInit hTail =>
      targetEpochBranch_continue_runs hH (by omega) (by omega) hInit hTail) ?_
  let fp := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := fp+I.m*F.limbs
  let space := budgetedIterationSpace F I.m old.exponent B
  let startSpace := epochStartSpace F I old.exponent old.initGraph heap allocation
  have hsplit : heap+startSpace+I.m+4+(I.m+1)*space+2≤oldHeap+targetStageSpace F I.m old.exponent B :=
    targetStage_space_split F I old oldHeap B allocation halloc
  have hbound : heap+startSpace+I.m+4+(I.m+1)*space+2<2^w := hsplit.trans_lt hspace
  have hfp : oldHeap≤fp := Nat.le_add_right _ _
  have hfpHeap : fp≤heap := Nat.le_add_right _ _
  have hRend : rp+F.limbs=fp := by
    simp [rp,fp,epochResidualEnd,Nat.add_mul,Nat.add_assoc,Nat.succ_mul]
  have hfpWord : fp<2^w := by omega
  have hrpWord : rp<2^w := by omega
  have hHeapWord : heap<2^w := by omega
  have hchecked := hfixed.frozen hframe hfp
  obtain ⟨end_,after,startCost,bit,coeffMem,hInit,hfixedRegs,
    hFlowReg,hResReg,hHeapReg,hBitReg,hCoeffReg,hRpost,hSpost,hBit,hz,hLo,hHi,
    hAfterFrame,hZeroCost,hSuccess⟩ :=
    targetEpoch_startup_call F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R himpl hrefreshArrays
      hfullScan hinit hinitNames hnames hinitBudget hflag hstartup old tp qp source oldHeap checked ω
      hregs hF hH
      (targetEpoch_startup_words F I old tp qp source oldHeap rp fp heap 0 hwords hrpWord hfpWord hHeapWord)
      hI hchecked.graph hchecked.graphWordsFit (hchecked.graphEnd.trans hfpHeap)
      hquality hprecision hcoefficientPre (by omega) hFiveM (show heap+startSpace+I.m+4<2^w by omega)
      ((hchecked.scalars old.gradientMin (by simp)).trans hfpHeap)
      ((hchecked.scalars old.gradientMax (by simp)).trans hfpHeap)
      ((hchecked.scalars old.lengthMin (by simp)).trans hfpHeap)
      hchecked.gradientMin hchecked.gradientMax hchecked.lengthMin
  refine ⟨end_,after,startCost,bit,coeffMem,hInit,hfixedRegs,
    hFlowReg,hResReg,hHeapReg,hBitReg,hCoeffReg,hRpost,hSpost,hBit,hz,hLo,hHi,
    hAfterFrame,fun h0 => (hZeroCost h0).trans (by omega),fun h1 => ?_⟩
  obtain ⟨s,x,initEnd,initialized,named,hEnd,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hScan,hStartCost⟩ := hSuccess h1
  exact ⟨s,x,initEnd,initialized,named,hEnd,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hScan,by omega⟩

/-- Run a new epoch after the exact residual test has requested one.
On every branch the result is the stage's actual fixed-point output. -/
theorem targetEpoch_continuation_runs_widened_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration iterations complete statusRecord startup fullScan initEntry initNames names budget refreshArrays : ℕ}
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
    (old : EpochLayout) (tp qp source oldHeap B : ℕ) (checked : State)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hregs : ∀ j<23,checked.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hF : checked.regs 23=epochResidualEnd I.m F.limbs oldHeap)
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
      Runs w p ω (targetEpochBranch startup complete statusRecord) checked (.returned out) final cost ∧
      TargetStageResult F I U old.exponent κ target source oldHeap out mem final.mem ∧
      out≤oldHeap+targetStageSpace F I.m old.exponent B ∧
      cost≤targetStageContinuationCost F I.m old.exponent rate :=
  targetEpoch_continuation_runs_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) himpl hrawDetect hdetect hstore hquery hcoefficient
    hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
    hreportBody hreport hcheckedProc hbudgetRecord hbody hiterations hcomplete hstatusRecord
    hrefreshArrays hfullScan hinit hinitNames hnames hinitBudget hstartup old tp qp source
    oldHeap B checked mem ω hregs hF hH hLarge hwords hframe hqbits halloc hspace hFiveM hEight
    hE hm hU hsize hnums hI hLower hFlo hκ hκ' hxlo ha ha' hres hr hflow hfixed hfmt hprecision
    hquality hNormLo hNormHi hR hcopy hcoefficientPre

end MinCostFlow.IPM.Machine
