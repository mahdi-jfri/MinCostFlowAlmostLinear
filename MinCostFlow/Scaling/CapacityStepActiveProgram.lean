module

public import MinCostFlow.Scaling.CapacityStepContract
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.PolyApproxProgram
import MinCostFlow.Scaling.CapacitySolverModel
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing an active capacity-scaling iteration

Construct the exact residual graph and approximation. A zero magnitude
writes the stop flag beside the unchanged flow pointer. Otherwise solve
the rounded residual problem, augment its two correction halves into a
fresh flow array, and write the new state header. Feasibility of the
actual correction proves the unsigned augmentation premises.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option maxHeartbeats 200000 in
/-- An active capacity iteration computes exactly the model step with
its stated branch cost, fresh-space reserve, and source-memory frame. -/
theorem capacityStep_active_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityStepModule solver entry b))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hstop : s.stopped=false) : MeetsContract w p b (capacityStepContract w solver entry T hproc J s C U) := by
  let solve := canonicalSolver solver entry T hproc
  let R := J.residual s.flow
  let B := (polyApproxModel solve R).value.magnitude
  let AP := capacityApproxSpace R
  let QS := capacityRoundedSpace R B
  have hRm : R.m=J.m+J.m := rfl
  have hpolyR := J.residual_polynomialCosts s.flow hc
  have ht := hasAt_tail hp
  have hl := hasAt_append_left ht
  have hll := hasAt_append_left hl
  have hlll := hasAt_append_left hll
  let approxEntry := b+1+(residualModule (b+1)).length
  let roundedEntry := approxEntry+(polyApproxModule solver entry approxEntry).length
  let augmentEntry := roundedEntry+(capacityRoundedSolveModule solver entry roundedEntry).length
  let pairEntry := augmentEntry+(residualAugmentModule augmentEntry).length
  have hRounded : p.HasAt roundedEntry (capacityRoundedSolveModule solver entry roundedEntry) := by
    simpa only [roundedEntry,approxEntry,List.length_append,Nat.add_assoc] using hasAt_append_right hll
  have hAugment : p.HasAt augmentEntry (residualAugmentModule augmentEntry) := by
    simpa only [augmentEntry,roundedEntry,approxEntry,List.length_append,Nat.add_assoc] using hasAt_append_right hl
  have hPair : p.HasAt pairEntry wordPairModule := by
    simpa only [pairEntry,augmentEntry,roundedEntry,approxEntry,List.length_append,Nat.add_assoc] using hasAt_append_right ht
  have hkR := residual_meetsContract (w := w) (hasAt_append_left hlll) J s.flow
  have hkQ := capacityRoundedSolve_meetsContract (w := w) hproc hdet hRounded R B hpolyR
  have hkA := residualAugment_meetsContract (w := w) hAugment s.flow
    (R.solveCapacityRoundedModel solve B).value
  have hkH := wordPair_meetsContract (w := w) hPair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hinput,hRinput,hf,hC,hu,hm,hzero,
    hspace,hsmall,hmass,hguest,hbudget,hproduct,hround,hroundGuest,haddition,hw⟩ := hpre
  have hspaceNum : heap+(2+10*J.m+AP+QS+J.m+2+4)<2^w := hspace
  have hAP : AP=bottleneckSearchSpace R+10+3*R.n+33*R.m+12 := rfl
  have hC_R := J.residual_costsBounded s.flow C hC
  have hRcap := J.residual_capacities_le s.flow (integral_capacity_bounds_cast J s.flow hf) U hu
  have hkP := polyApprox_meetsContract (w := w) hproc hdet (hasAt_append_right hlll) R C U hpolyR hC_R
  have hBbound : B≤R.m*(C*U) := polyApprox_magnitude_le solver entry T hproc R C U hpolyR hC_R hRcap
  have hBword : B<2^w := hBbound.trans_lt hproduct
  obtain ⟨ptr,hheader,hptrEnd,hread⟩ := hstate
  have hflow := solverOutput_listAt J hread
  have hs1 : state+1<2^w := by omega
  have hptrWord : ptr<2^w := by omega
  have hh : heap<2^w := by omega
  have hmWord : J.m<2^w := by omega
  have h2mWord : J.m+J.m<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hflag : mem (state+1)=0 := by
    have h : mem (state+1)=s.stopped.toNat := hheader 1 (by change 1<2; decide)
    simpa only [hstop,Bool.toNat_false] using h
  have hptrCell : mem state=ptr := by
    have h : mem (state+0)=ptr := hheader 0 (by change 0<2; decide)
    simpa only [Nat.add_zero] using h
  have hM := (solver_header_at J hgraph).2
  apply runs_start_le
  unfold capacityStepBody
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  wram_step
  refine runs_seq_assign_le (v := ptr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by eval_expr) ?_
  refine runs_seq_call_le hkR (vs := [a,ptr,heap]) (by eval_expr) (by wram_words)
    ⟨⟨a,ptr,heap,rfl,hgraph,hflow,hgraphEnd,hptrEnd,hf,hinput,by omega⟩,
      hzero,by change heap+(2+10*J.m)<2^w; omega⟩ ?_
  intro resEnd memR posR hpostR
  obtain ⟨⟨_,_,hframeR,hzR,hresidual⟩,hresEnd⟩ := hpostR
  change resEnd=heap+2+10*J.m at hresEnd
  change (∀ x<heap,memR x=mem x) at hframeR
  change ZeroFrom memR resEnd at hzR
  change ListAt memR heap R.solverWords at hresidual
  have hresWord : resEnd<2^w := by omega
  have hresGraphEnd : heap+R.solverWords.length≤resEnd := by
    rw [R.solverWords_length,hRm]
    omega
  have happroxReserve : resEnd+AP<2^w := by omega
  refine runs_seq_call_le hkP (vs := [heap,resEnd]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨heap,resEnd,rfl,?_,hRcap,?_,hbudget,hproduct,hw⟩
    · refine ⟨⟨heap,resEnd,rfl,hresidual,hresGraphEnd,hRinput,hsmall,hmass,hguest,by omega⟩,hzR,?_⟩
      change resEnd+bottleneckSearchSpace R<2^w
      omega
    · omega
  · intro canEnd memP posP hpostP
    obtain ⟨hloP,hhiP,hcandidate,hzP,hframeP⟩ := hpostP
    change resEnd≤canEnd at hloP
    change canEnd≤resEnd+bottleneckSearchSpace R+10+3*R.n+33*R.m+8 at hhiP
    change ApproximationResultAt memP (canEnd-2) canEnd (polyApproxModel solve R).value at hcandidate
    change ZeroFrom memP canEnd at hzP
    change (∀ x<resEnd,memP x=memR x) at hframeP
    have hcanReserve : canEnd+4≤resEnd+AP := by omega
    have hcanWord : canEnd<2^w := by omega
    obtain ⟨unusedFlow,hcanHeader,_,_⟩ := hcandidate
    have hmagCell : memP (canEnd-1)=B := by
      have h : memP (canEnd-2+1)=B := hcanHeader 1 (by change 1<2; decide)
      have heq : canEnd-2+1=canEnd-1 := by omega
      simpa only [heq] using h
    have hcan1 : canEnd-1<2^w := by omega
    have hframeOldP : ∀ x<heap,memP x=mem x := fun x hx =>
      (hframeP x (by omega)).trans (hframeR x hx)
    have hflowP := hflow.of_agree_below (h₀ := heap) (by simpa only [List.length_ofFn] using hptrEnd) hframeOldP
    refine runs_seq_assign_le (v := B) (by eval_expr) ?_
    wram_step
    · have hB : B=0 := hcond
      have hBraw : (polyApproxModel (canonicalSolver solver entry T hproc) (J.residual s.flow)).value.magnitude=0 := hB
      have hBsolve : (polyApproxModel solve (J.residual s.flow)).value.magnitude=0 := hB
      have hmodel : (s.step solve).value={s with stopped:=true} := by
        simp only [CapacityState.step,hstop,Bool.false_eq_true,↓reduceIte,hBsolve]
      refine runs_seq_call_le hkH (vs := [ptr,1,canEnd]) (by eval_expr) (by wram_words)
        ⟨⟨ptr,1,canEnd,rfl⟩,hzP,by change canEnd+2<2^w; omega⟩ ?_
      intro ret memH posH hpostH
      obtain ⟨⟨_,_,hframeH,hzH,hpairH⟩,hret⟩ := hpostH
      change ret=canEnd+2 at hret
      change (∀ x<canEnd,memH x=memP x) at hframeH
      change ListAt memH canEnd [ptr,1] at hpairH
      change ZeroFrom memH ret at hzH
      have hflowH := hflowP.of_agree_below (h₀ := canEnd) (by simp only [List.length_ofFn]; omega) hframeH
      have hstateH : CapacityStateAt memH (ret-2) ret (s.step solve).value := by
        rw [hmodel,show ret-2=canEnd by omega]
        apply capacityStateAt_of_array (s := {s with stopped:=true}) hpairH (by omega) hflowH
        exact fun e => (hf e).1
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+capacityStepSpace solver entry T hproc J s ∧
          CapacityStateAt memH (ret-2) ret (s.step solve).value ∧ ZeroFrom memH ret ∧ ∀ x<heap,memH x=mem x
        have hreserve : capacityStepSpace solver entry T hproc J s=2+10*J.m+AP+QS+J.m+2+4 := rfl
        rw [hreserve]
        refine ⟨by omega,by omega,hstateH,hzH,?_⟩
        intro x hx
        exact (hframeH x (by omega)).trans (hframeOldP x hx)
      · simp only [capacityStepContract,R,hstop,Bool.false_eq_true,↓reduceIte,hBraw,residualContract,
          wordPairContract,heapContract,polyApproxContract,bottleneckSearchContract,startState,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega
    · have hB : B≠0 := hcond
      have hBraw : (polyApproxModel (canonicalSolver solver entry T hproc) (J.residual s.flow)).value.magnitude≠0 := hB
      have hQS : QS=5+12*R.m+2^wordSize 5 (R.scaledRoundedInstance B).positiveInstance.solverWords := by
        simp only [QS,capacityRoundedSpace,hB,↓reduceIte]
      have hguestPositive : 0<2^wordSize 5 (R.scaledRoundedInstance B).positiveInstance.solverWords := Nat.two_pow_pos _
      have hQSsize : R.m≤QS := by rw [hQS]; omega
      have hresidualP := hresidual.of_agree_below (h₀ := resEnd) hresGraphEnd hframeP
      refine runs_seq_call_le hkQ (vs := [heap,B,canEnd]) (by eval_expr) (by wram_words)
        ⟨⟨heap,canEnd,rfl,hresidualP,by omega,hRinput,by omega,hround,hroundGuest,by omega⟩,
          hzP,by change canEnd+QS<2^w; omega⟩ ?_
      intro solveEnd memQ posQ hpostQ
      obtain ⟨⟨_,_,hframeQ,hzQ,_⟩,hsolveEnd,hdeltaArray⟩ := hpostQ
      change solveEnd=canEnd+QS at hsolveEnd
      change (∀ x<canEnd,memQ x=memP x) at hframeQ
      change ZeroFrom memQ solveEnd at hzQ
      let delta := (R.solveCapacityRoundedModel solve B).value
      change ListAt memQ (solveEnd-R.m) (List.ofFn (fun e => (delta e).toNat)) at hdeltaArray
      have hsolveWord : solveEnd<2^w := by omega
      have hdeltaPtr : solveEnd-R.m<2^w := by omega
      have hdeltaEnd : solveEnd-R.m+(J.m+J.m)≤solveEnd := by omega
      have hframeOldQ : ∀ x<heap,memQ x=mem x := fun x hx =>
        (hframeQ x (by omega)).trans (hframeOldP x hx)
      have hflowQ := hflow.of_agree_below (h₀ := heap) (by simpa only [List.length_ofFn] using hptrEnd) hframeOldQ
      have hsolve := fun K (_ : K.CostsBounded (K.m^10))
        (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => canonicalSolver_optimal solver entry T hproc K
      have hdeltaFeas := R.solveCapacityRoundedModel_feasible solve hsolve B hpolyR
      have hdeltaBounds := feasible_unsigned_bounds R delta U hdeltaFeas hRcap
      have hnextBounds := residualAugment_integral_bounds J s.flow delta hf hdeltaFeas
      have hflowNat : ∀ e,(s.flow e).toNat≤U := by
        intro e
        have h : (s.flow e).toNat≤J.capacity e := by
          simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (hf e).2
        exact h.trans (hu e)
      have haugValues : ∀ e,(s.flow e).toNat+(delta (Fin.castAdd J.m e)).toNat<2^w ∧
          (delta (Fin.natAdd J.m e)).toNat<2^w := by
        intro e
        have h1 := hflowNat e
        have h2 := (hdeltaBounds (Fin.castAdd J.m e)).2
        have h3 := (hdeltaBounds (Fin.natAdd J.m e)).2
        exact ⟨by omega,by omega⟩
      refine runs_seq_assign_le (v := solveEnd-R.m) (by rw [hRm]; eval_expr) ?_
      refine runs_seq_call_le hkA (vs := [ptr,solveEnd-R.m,J.m,solveEnd]) (by eval_expr) (by wram_words)
        ⟨⟨ptr,solveEnd-R.m,solveEnd,rfl,hflowQ,hdeltaArray,by omega,hdeltaEnd,
          (fun e => (hf e).1),(fun e => (hdeltaBounds e).1),(fun e => (hnextBounds e).1),haugValues,by omega⟩,
          hzQ,by change solveEnd+J.m<2^w; omega⟩ ?_
      intro augEnd memA posA hpostA
      obtain ⟨⟨_,_,hframeA,hzA,hnewFlow⟩,haugEnd⟩ := hpostA
      change augEnd=solveEnd+J.m at haugEnd
      change (∀ x<solveEnd,memA x=memQ x) at hframeA
      change ZeroFrom memA augEnd at hzA
      let next : CapacityState J := ⟨fun e => s.flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e),false⟩
      change ListAt memA solveEnd (List.ofFn (fun e => (next.flow e).toNat)) at hnewFlow
      have hBsolve : (polyApproxModel solve (J.residual s.flow)).value.magnitude≠0 := hB
      have hmodel : (s.step solve).value=next := by
        simp only [CapacityState.step,hstop,Bool.false_eq_true,↓reduceIte,hBsolve]
        rfl
      have haugWord : augEnd<2^w := by omega
      have hnewPtr : augEnd-J.m=solveEnd := by omega
      refine runs_seq_call_le hkH (vs := [solveEnd,0,augEnd]) (by rw [←hnewPtr]; eval_expr) (by wram_words)
        ⟨⟨solveEnd,0,augEnd,rfl⟩,hzA,by change augEnd+2<2^w; omega⟩ ?_
      intro ret memH posH hpostH
      obtain ⟨⟨_,_,hframeH,hzH,hpairH⟩,hret⟩ := hpostH
      change ret=augEnd+2 at hret
      change (∀ x<augEnd,memH x=memA x) at hframeH
      change ListAt memH augEnd [solveEnd,0] at hpairH
      change ZeroFrom memH ret at hzH
      have hflowH := hnewFlow.of_agree_below (h₀ := augEnd) (by simp only [List.length_ofFn]; omega) hframeH
      have hstateH : CapacityStateAt memH (ret-2) ret (s.step solve).value := by
        rw [hmodel,show ret-2=augEnd by omega]
        apply capacityStateAt_of_array (s := next) hpairH (by omega) hflowH
        exact fun e => (hnextBounds e).1
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+capacityStepSpace solver entry T hproc J s ∧
          CapacityStateAt memH (ret-2) ret (s.step solve).value ∧ ZeroFrom memH ret ∧ ∀ x<heap,memH x=mem x
        have hreserve : capacityStepSpace solver entry T hproc J s=2+10*J.m+AP+QS+J.m+2+4 := rfl
        rw [hreserve]
        refine ⟨by omega,by omega,hstateH,hzH,?_⟩
        intro x hx
        exact (hframeH x (by omega)).trans ((hframeA x (by omega)).trans (hframeOldQ x hx))
      · simp only [capacityStepContract,R,B,solve,hstop,Bool.false_eq_true,↓reduceIte,hBraw,residualContract,
          residualAugmentContract,wordPairContract,heapContract,polyApproxContract,bottleneckSearchContract,
          capacityRoundedSolveContract,startState,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega

end MinCostFlow.Scaling.Machine
