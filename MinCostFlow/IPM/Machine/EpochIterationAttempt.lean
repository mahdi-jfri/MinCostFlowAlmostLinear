module

public import MinCostFlow.IPM.Machine.EpochCoefficientGuard
public import MinCostFlow.IPM.Machine.EpochRefreshGuard
public import MinCostFlow.IPM.Machine.EpochReportBalance
public import MinCostFlow.IPM.Machine.EpochStaticInputs
import MinCostFlow.IPM.Machine.DetectCheckedHistory
import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.IPM.Machine.DetectRefreshOutput
import MinCostFlow.IPM.Machine.EpochGuardRanges
import MinCostFlow.IPM.Machine.EpochInitialFlow
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Recovering the next actual Update before assuming its answer

The safe current flow forces refresh acceptance. The movement account
pays for its report, and the numerical ranges force the coefficient
scan to accept. Decode the Update and build its valid input history.
The actual status is still allowed to indicate a failed Update.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 350000 in
/-- All pre-Update machine guards under `P` accept under the numerical ranges and
the movement balance. The returned state, bit, and rounded scalar then
refer to the actual next Update of Definition 4.5 (page 14). -/
theorem epoch_iteration_attempt_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (q K i v : ℕ) (Pt : EpochPoint R.τ)
    (final : ℕ → ℕ) (s' : A.State)
    (a r capacity normalization : ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i Pt)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization Pt.machine.mem)
    (hsource : epochSourcesAt F I L a r Pt.machine.mem)
    (hlo : L.exponent=E) (hWide : ipmRangeExponent I.m U≤E)
    (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hi : i≤I.m)
    (hbal : EpochReportBalance A.eraseFailure I.m eps i Pt)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A Pt.history Pt.eta Pt.op (2*i) (epochVector F I Pt.machine.mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure Pt.history Pt.eta Pt.op (2*i)) s' Pt.credit
      q K L.sourceEnd L.tableEnd (L.packet F I (Pt.machine.regs 8)) Pt.machine.mem v final) :
    let T := 2*i
    let heap := Pt.machine.regs 8
    let s := minRatioState A.eraseFailure Pt.history Pt.eta Pt.op T
    ∃ refreshedEnd refreshed es actual,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s Pt.credit
        q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) Pt.machine.mem refreshedEnd refreshed ∧
      refreshed (refreshedEnd-1)=1 ∧ es.Nodup ∧ es.toFinset=(A.detect s).1 ∧
      NormalizationWithin normalization actual ∧
      (∀ e : Fin I.m,1/(2:ℝ)^(E)≤epochVector F I refreshed L.lengths e ∧
        epochVector F I refreshed L.lengths e≤(2:ℝ)^(E)) ∧
      let D := appendHistoryIteration Pt.history T es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let nu := appendHistoryIterationEta Pt.eta T actual
      let op := appendHistoryIterationOp Pt.op T
      MinRatioHistoryValid D op (T+1+1) ∧
      s'=minRatioState A.eraseFailure D nu op (T+1+1) ∧
      final (v-1)=(if (minRatioFailureDirection A D nu op (T+1)).isSome then 1 else 0) := by
  dsimp only
  let T := 2*i
  let heap := Pt.machine.regs 8
  let mem := Pt.machine.mem
  let s := minRatioState A.eraseFailure Pt.history Pt.eta Pt.op T
  have hg := hcond
  obtain ⟨_,_,_,_,_,hbudget,_,hv,hG,hpre,hgOld,hlOld,_,_⟩ := hg
  have hPD : ∀ j ≤ T, P (Pt.history.G j) (Pt.history.ℓ j) := hcond.stages hP
  obtain ⟨_,_,_,_,_,harrays,hscalars,hguards,hrequest,_,_,_,_,_,_,_,_,_,_,halpha,hfmt,heps,_⟩ := hstatic
  obtain ⟨cEnd,cMem,mid,hCpost,_,_,hbranch⟩ := hout
  have hSize := hcond.history_bounded
  have hS := minRatio_valid_detect_subset_upTo_on A κ α Ψ eps hA Pt.history Pt.eta Pt.op T hv hSize hPD
  rw [show Pt.history.G T=namedInstance I from hG T le_rfl] at hS
  have hsafe := epoch_reported_candidate_safe_upTo_on F I A κ α Ψ eps hA L a r mem hsource
    Pt.history Pt.eta Pt.op T hv hSize hPD (hG T le_rfl) (by
      intro e
      rw [hlo]
      exact ⟨strict_guard_range_mono hWide (strict_guard_range_of_slack_range I.m U (hslacks e).1),
        strict_guard_range_mono hWide (strict_guard_range_of_slack_range I.m U (hslacks e).2)⟩)
  have hCbit := detectRefresh_accepts_safe F A (namedInstance I) I.m κ α rate allocation R
    hpre hCpost (fun e he => hsafe e (hS he))
  have hPD' := appendHistoryStage_stage_on (D:=Pt.history) (T:=T) [] (Pt.history.g T) (Pt.history.ℓ T) hPD (hPD T le_rfl)
  have hDetect := (hA
    (appendHistoryStage Pt.history T [] (Pt.history.g T) (Pt.history.ℓ T))
    (Function.update Pt.eta (T+1) 0) (Function.update Pt.op (T+1) false) (T+1)
    (appendHistoryStage_valid_detect Pt.history Pt.op T hv)
    (appendHistoryStage_bounded [] _ _ hSize) hPD').1
  have hfits := epochReportBalance_detect_fits_on A.eraseFailure I.m i Pt κ α Ψ eps
    hDetect heps hi hv hbudget hbal
  have hbranch' := hbranch
  change (if cMem (cEnd-1)=1 ∧ (A.detect s).1.card≤mem (heap-3) then _ else _) at hbranch'
  rw [ite_eq_left ⟨hCbit,hfits⟩] at hbranch'
  obtain ⟨coreEnd,coreMem,hCheckedPre,_,hTransition,hrecord⟩ := hbranch'
  simp only [EpochLayout.packet,List.getD_cons_zero,List.getD_cons_succ] at hCheckedPre hTransition hrecord
  have hFrame : ∀ z<L.flow,cMem z=mem z :=
    detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hCpost
  have hSrc := hsource.frozen hFrame harrays ⟨hscalars _ (by simp),hscalars _ (by simp)⟩
  have hcache := (detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hCpost).2.2.2.2 hCbit
  have hEnd (e : Fin I.m) : L.base+e.val*F.limbs+F.limbs≤L.flow :=
    (reported_entry_end L.base F.limbs e.val I.m e.isLt).trans (harrays _ (by simp))
  have hRange := epoch_reported_coefficients_in_range_upTo_on F I A κ α Ψ eps hA L U q a r cMem hSrc
    Pt.history Pt.eta Pt.op T hv hSize hPD (hG T le_rfl) (hsource.1 ▸ halpha.1) (hsource.1 ▸ halpha.2) hnums hr
    (by
      intro e
      have hSame : epochVector F I cMem L.base e=epochVector F I mem L.base e :=
        Num.IPM.fixVal_frozen hFrame (hEnd e)
      dsimp only
      simpa only [epochHistoryFlow,hSame] using hslacks e) hcache
  obtain ⟨checkedEnd,checkedMem,hCheck,hcheckBranch⟩ := hTransition
  have hScan := checkedUpdate_scan_accepts F A I κ α rate allocation R hCheckedPre hCheck
    (by
      intro e he
      rw [hfmt]
      obtain ⟨hg,hl,hu⟩ := hRange e he
      have hp : (2:ℝ)^(ipmRangeExponent I.m U)≤(2:ℝ)^E := pow_le_pow_right₀ (by norm_num) hWide
      have hrange := strict_guard_range_mono hWide ⟨hl,hu⟩
      exact ⟨hg.trans_le hp,hrange.1,hrange.2⟩)
  rw [ite_eq_left hScan] at hcheckBranch
  obtain ⟨batchEnd,batchMem,hbatch,hupdate,hbit⟩ := hcheckBranch
  have hbounds : L.gradient+I.m*F.limbs≤heap ∧ L.lengths+I.m*F.limbs≤heap ∧ L.flow≤heap := by
    obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
    change [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,
      L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m]=_ at heq
    simp only [List.cons.injEq,and_true,true_and] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    change (reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s Pt.credit
      q K L.sourceEnd L.tableEnd).pre
      [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,
        L.alpha,L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m] mem at hfull
    obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
      _,_,_,_,_,_,_,_,_,_,htEnd,hnEnd,hends,_,_,_,_,_,hL,hG,_⟩ := hfull
    simp only [List.cons.injEq,and_true,true_and] at heq
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
    have hf := hends L.flow (by simp)
    exact ⟨by omega,by omega,by omega⟩
  obtain ⟨es,actual,_,hnd,hlist,_,hnorm,hvalid,hstate,hmodelBit⟩ :=
    detectChecked_attempt_history F A I κ α rate allocation R Pt.history Pt.eta Pt.op T
      hv (hG T le_rfl) hpre hCpost hCheckedPre hCheck hScan hbatch hupdate hbit
      hbounds.1 hbounds.2.1 (hguards L.request (by simp)) hbounds.2.2 hgOld hlOld
  change NormalizationWithin (Num.fixVal mem L.request F.fmt.limbBits F.limbs F.fmt.precision) actual at hnorm
  rw [hrequest.2] at hnorm
  have hcRanges := checkedUpdateCalls_input_ranges F A I κ α rate allocation R hCheckedPre hCheck hScan
  have hlengths (e : Fin I.m) : 1/(2:ℝ)^(E)≤epochVector F I cMem L.lengths e ∧
      epochVector F I cMem L.lengths e≤(2:ℝ)^(E) := by
    have h := (hcRanges e.val (Finset.mem_range.mpr e.isLt)).2
    simpa only [readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using h
  refine ⟨cEnd,cMem,es,actual,hCpost,hCbit,hnd,hlist,hnorm,hlengths,hvalid,hstate,?_⟩
  exact (epochBudgetRecord_output hrecord).2.2.trans hmodelBit

/-- All pre-Update machine guards accept under the numerical ranges and
the movement balance. The returned state, bit, and rounded scalar then
refer to the actual next Update of Definition 4.5 (page 14). -/
theorem epoch_iteration_attempt_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (q K i v : ℕ) (P : EpochPoint R.τ)
    (final : ℕ → ℕ) (s' : A.State)
    (a r capacity normalization : ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization P.machine.mem)
    (hsource : epochSourcesAt F I L a r P.machine.mem)
    (hlo : L.exponent=E) (hWide : ipmRangeExponent I.m U≤E)
    (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hi : i≤I.m)
    (hbal : EpochReportBalance A.eraseFailure I.m eps i P)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A P.history P.eta P.op (2*i) (epochVector F I P.machine.mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit
      q K L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    let T := 2*i
    let heap := P.machine.regs 8
    let s := minRatioState A.eraseFailure P.history P.eta P.op T
    ∃ refreshedEnd refreshed es actual,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s P.credit
        q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) P.machine.mem refreshedEnd refreshed ∧
      refreshed (refreshedEnd-1)=1 ∧ es.Nodup ∧ es.toFinset=(A.detect s).1 ∧
      NormalizationWithin normalization actual ∧
      (∀ e : Fin I.m,1/(2:ℝ)^(E)≤epochVector F I refreshed L.lengths e ∧
        epochVector F I refreshed L.lengths e≤(2:ℝ)^(E)) ∧
      let D := appendHistoryIteration P.history T es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let nu := appendHistoryIterationEta P.eta T actual
      let op := appendHistoryIterationOp P.op T
      MinRatioHistoryValid D op (T+1+1) ∧
      s'=minRatioState A.eraseFailure D nu op (T+1+1) ∧
      final (v-1)=(if (minRatioFailureDirection A D nu op (T+1)).isSome then 1 else 0) :=
  epoch_iteration_attempt_at_range_upTo_on F A I U E κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L q K i v P final s' a r capacity normalization
    hcond hstatic hsource hlo hWide hnums hr hi hbal hslacks hout

set_option maxHeartbeats 350000 in
/-- All pre-Update machine guards accept under the numerical ranges and
the movement balance. The returned state, bit, and rounded scalar then
refer to the actual next Update of Definition 4.5 (page 14). -/
theorem epoch_iteration_attempt_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (L : EpochLayout) (q K i v : ℕ) (P : EpochPoint R.τ)
    (final : ℕ → ℕ) (s' : A.State)
    (a r capacity normalization : ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization P.machine.mem)
    (hsource : epochSourcesAt F I L a r P.machine.mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hi : i≤I.m)
    (hbal : EpochReportBalance A.eraseFailure I.m eps i P)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A P.history P.eta P.op (2*i) (epochVector F I P.machine.mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit
      q K L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    let T := 2*i
    let heap := P.machine.regs 8
    let s := minRatioState A.eraseFailure P.history P.eta P.op T
    ∃ refreshedEnd refreshed es actual,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s P.credit
        q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) P.machine.mem refreshedEnd refreshed ∧
      refreshed (refreshedEnd-1)=1 ∧ es.Nodup ∧ es.toFinset=(A.detect s).1 ∧
      NormalizationWithin normalization actual ∧
      (∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I refreshed L.lengths e ∧
        epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U)) ∧
      let D := appendHistoryIteration P.history T es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let nu := appendHistoryIterationEta P.eta T actual
      let op := appendHistoryIterationOp P.op T
      MinRatioHistoryValid D op (T+1+1) ∧
      s'=minRatioState A.eraseFailure D nu op (T+1+1) ∧
      final (v-1)=(if (minRatioFailureDirection A D nu op (T+1)).isSome then 1 else 0) :=
  epoch_iteration_attempt_at_range_upTo F A I U _ κ α Ψ eps rate allocation R hA L q K i v P final
    s' a r capacity normalization hcond hstatic hsource hlo le_rfl hnums hr hi hbal hslacks hout

/-- All pre-Update machine guards accept under the numerical ranges and
the movement balance. The returned state, bit, and rounded scalar then
refer to the actual next Update of Definition 4.5 (page 14). -/
theorem epoch_iteration_attempt {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (L : EpochLayout) (q K i v : ℕ) (P : EpochPoint R.τ)
    (final : ℕ → ℕ) (s' : A.State)
    (a r capacity normalization : ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization P.machine.mem)
    (hsource : epochSourcesAt F I L a r P.machine.mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hnums : NumbersBounded I U)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hi : i≤I.m)
    (hbal : EpochReportBalance A.eraseFailure I.m eps i P)
    (hslacks : ∀ e : Fin I.m,
      let f := epochHistoryFlow I A P.history P.eta P.op (2*i) (epochVector F I P.machine.mem L.base) e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit
      q K L.sourceEnd L.tableEnd (L.packet F I (P.machine.regs 8)) P.machine.mem v final) :
    let T := 2*i
    let heap := P.machine.regs 8
    let s := minRatioState A.eraseFailure P.history P.eta P.op T
    ∃ refreshedEnd refreshed es actual,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s P.credit
        q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) P.machine.mem refreshedEnd refreshed ∧
      refreshed (refreshedEnd-1)=1 ∧ es.Nodup ∧ es.toFinset=(A.detect s).1 ∧
      NormalizationWithin normalization actual ∧
      (∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I refreshed L.lengths e ∧
        epochVector F I refreshed L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U)) ∧
      let D := appendHistoryIteration P.history T es
        (readVector refreshed L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector refreshed L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
      let nu := appendHistoryIterationEta P.eta T actual
      let op := appendHistoryIterationOp P.op T
      MinRatioHistoryValid D op (T+1+1) ∧
      s'=minRatioState A.eraseFailure D nu op (T+1+1) ∧
      final (v-1)=(if (minRatioFailureDirection A D nu op (T+1)).isSome then 1 else 0) :=
  epoch_iteration_attempt_upTo F A I U κ α Ψ eps rate allocation R (hA.upTo I.m I.n) L q K i v P
    final s' a r capacity normalization hcond hstatic hsource hlo hnums hr hi hbal hslacks hout

end MinCostFlow.IPM.Machine
