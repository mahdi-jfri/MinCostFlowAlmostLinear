module

public import MinCostFlow.Final.ScratchPolyApprox
public import MinCostFlow.Final.ScratchCapacityRoundedSolve
public import MinCostFlow.Scaling.CapacityStepContract
import MinCostFlow.Scaling.CapacityNumericFacts
import MinCostFlow.Scaling.ApproximationCorrectness
import MinCostFlow.Scaling.ObjectiveScanFacts
import MinCostFlow.Scaling.CapacitySolverModel
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# A capacity-scaling step with polynomial scratch

The active step builds the residual and runs the bottleneck approximation.
A positive result starts the rounded solve and augmentation. The space
bound covers both guest allocations and the next state header.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Residual construction, approximation, rounded solving, augmentation,
and state-header writing follow the capacity-step entry. -/
def scratchCapacityStepModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let approx := b+1+(residualModule (b+1)).length
  let rounded := approx+(scratchPolyApproxModule solver entry approx c d).length
  let augment := rounded+(scratchCapacityRoundedSolveModule solver entry rounded c d).length
  let pair := augment+(residualAugmentModule augment).length
  capacityStepBody (b+1) approx rounded augment pair ::
    (residualModule (b+1) ++ scratchPolyApproxModule solver entry approx c d ++
      scratchCapacityRoundedSolveModule solver entry rounded c d ++ residualAugmentModule augment ++ wordPairModule)

/-- The complete approximation reserve, including its final four-cell margin. -/
def scratchCapacityApproxSpace (c d : ℕ) (J : Circulation) : ℕ := scratchBottleneckSearchSpace c d J+10+3*J.n+33*J.m+12

/-- Fresh-space reserve for a rounded solve at magnitude `B`. -/
def scratchCapacityRoundedSpace (c d : ℕ) (J : Circulation) (B : ℕ) : ℕ :=
  if B=0 then J.m else 5+12*J.m+2^wordSize (scratchWordMultiplier c d) (J.scaledRoundedInstance B).positiveInstance.solverWords

/-- One step's reserve includes both residual optimization phases and a
fresh flow and header, with four additional cells. -/
noncomputable def scratchCapacityStepSpace (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (s : CapacityState J) : ℕ :=
  let R := J.residual s.flow
  let B := (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) R).value.magnitude
  2+10*J.m+scratchCapacityApproxSpace c d R+scratchCapacityRoundedSpace c d R B+J.m+2+4

/-- Numerical premises describe actual stored values and intermediate
arithmetic budgets. Feasibility of solver outputs is proved from the
primitive solver contract, rather than required as a premise. -/
noncomputable def scratchCapacityStepContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (s : CapacityState J) (C U : ℕ) : Contract :=
  let R := J.residual s.flow
  let B := (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) R).value.magnitude
  let G := scratchBottleneckGuestBound c d R (sortCapacities (List.ofFn R.capacity)).1
  let g := wordSize (scratchWordMultiplier c d) (R.scaledRoundedInstance B).positiveInstance.solverWords
  { pre := fun args mem => ∃ a state heap,args=[a,state,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ state+2=heap ∧ CapacityStateAt mem state heap s ∧
      (∀ x ∈ J.solverWords,x<2^w) ∧ (∀ x ∈ R.solverWords,x<2^w) ∧
      (∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      0<J.m ∧ ZeroFrom mem heap ∧ heap+scratchCapacityStepSpace solver entry T S c d hproc J s<2^w ∧
      R.m+2<2^w ∧ R.m*C<2^w ∧ 2^(G+1)+2≤2^w ∧ (6*R.m+2)*C<2^w ∧
      R.m*(C*U)<2^w ∧ B*R.m^20<2^w ∧ (B=0 ∨ 2^(g+1)+2≤2^w) ∧ 2*U<2^w ∧ 9<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧
      ret≤heapArg args+scratchCapacityStepSpace solver entry T S c d hproc J s ∧
      CapacityStateAt mem' (ret-2) ret (s.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K))).value ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ mem => if s.stopped then 100 else
      600*J.m+200+(scratchPolyApproxContract w solver entry T S c d hproc R C U).cost [] mem+
        if B=0 then 400 else (scratchCapacityRoundedSolveContract w solver entry T S c d hproc R B).cost [] mem+100*J.m+100+400 }

/-- The step and all callees have no random instruction when the solver is deterministic. -/
theorem scratchCapacityStepModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityStepModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityStepBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hp
    · rcases List.mem_append.mp hb with hb | ha
      · rcases List.mem_append.mp hb with hb | hr
        · rcases List.mem_append.mp hb with he | hc
          · exact residualModule_noRand _ body he
          · exact scratchPolyApproxModule_noRand solver entry _ c d hdet body hc
        · exact scratchCapacityRoundedSolveModule_noRand solver entry _ c d hdet body hr
      · exact residualAugmentModule_noRand _ body ha
    · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hp
      subst body
      exact wordPairBody_noRand

private theorem neg_toNat_le_natAbs (z : ℤ) : (-z).toNat≤z.natAbs := by
  cases z <;> simp

/-- The actual canonical approximation magnitude is bounded by the
capacity times cost budget summed over all edge slots. -/
theorem scratchPolyApprox_magnitude_le (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U) :
    (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J).value.magnitude≤J.m*(C*U) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let F := (polyApproxModel solve J).value.flow
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc K) K
  have hfeas := (lemma_C_10 solve hsolve J hc).1
  have hvalues := feasible_unsigned_bounds J F U hfeas hu
  have hcast : (fun e => ((F e).toNat : ℤ))=F := by
    funext e
    exact Int.toNat_of_nonneg (hvalues e).1
  have hmass := objectiveScanMass_le J (fun e => (F e).toNat) (List.finRange J.m) C U
    (fun e _ => hC e) (fun e _ => (hvalues e).2)
  have habs := objectiveScan_natAbs_le J (fun e => (F e).toNat) (List.finRange J.m)
  rw [objectiveScan_finRange,hcast] at habs
  rw [List.length_finRange] at hmass
  rw [polyApproxModel_magnitude]
  exact (neg_toNat_le_natAbs (J.integerObjective F)).trans (habs.trans hmass)

/-- Any feasible integral residual correction gives a nonnegative
augmented flow within the original capacities, even without conservation
of the starting flow. -/
theorem residualAugment_integral_bounds (J : Circulation) (flow : Fin J.m → ℤ)
    (delta : Fin (J.m+J.m) → ℤ) (hf : ∀ e,0≤flow e ∧ flow e≤J.capacity e)
    (hd : (J.residual flow).Feasible (fun e => (delta e : ℝ))) :
    ∀ e,0≤flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) ∧
      flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e)≤J.capacity e := by
  have hreal := integral_capacity_bounds_cast J flow hf
  intro e
  have h := J.augment_bounds flow hreal (fun e => (delta e : ℝ)) hd e
  have heq : ((flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) : ℤ) : ℝ)=
      J.augment flow (fun e => (delta e : ℝ)) e := by
    simp only [Int.cast_add,Int.cast_sub,Circulation.augment,Circulation.project]
    ring
  have hlo : 0≤((flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) : ℤ) : ℝ) := by rw [heq]; exact h.1
  have hhi : ((flow e+delta (Fin.castAdd J.m e)-delta (Fin.natAdd J.m e) : ℤ) : ℝ)≤
      ((J.capacity e : ℤ) : ℝ) := by rw [Int.cast_natCast,heq]; exact h.2
  exact ⟨Int.cast_nonneg_iff.mp hlo,Int.cast_le.mp hhi⟩

set_option maxHeartbeats 200000 in
/-- An active capacity iteration computes exactly the model step with
its stated branch cost, fresh-space reserve, and source-memory frame. -/
theorem scratchCapacityStep_active_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityStepModule solver entry b c d))
    (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (s : CapacityState J) (C U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hstop : s.stopped=false) : MeetsContract w p b (scratchCapacityStepContract w solver entry T S c d hproc J s C U) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let R := J.residual s.flow
  let B := (polyApproxModel solve R).value.magnitude
  let AP := scratchCapacityApproxSpace c d R
  let QS := scratchCapacityRoundedSpace c d R B
  have hRm : R.m=J.m+J.m := rfl
  have hpolyR := J.residual_polynomialCosts s.flow hc
  have ht := hasAt_tail hp
  have hl := hasAt_append_left ht
  have hll := hasAt_append_left hl
  have hlll := hasAt_append_left hll
  let approxEntry := b+1+(residualModule (b+1)).length
  let roundedEntry := approxEntry+(scratchPolyApproxModule solver entry approxEntry c d).length
  let augmentEntry := roundedEntry+(scratchCapacityRoundedSolveModule solver entry roundedEntry c d).length
  let pairEntry := augmentEntry+(residualAugmentModule augmentEntry).length
  have hRounded : p.HasAt roundedEntry (scratchCapacityRoundedSolveModule solver entry roundedEntry c d) := by
    simpa only [roundedEntry,approxEntry,List.length_append,Nat.add_assoc] using hasAt_append_right hll
  have hAugment : p.HasAt augmentEntry (residualAugmentModule augmentEntry) := by
    simpa only [augmentEntry,roundedEntry,approxEntry,List.length_append,Nat.add_assoc] using hasAt_append_right hl
  have hPair : p.HasAt pairEntry wordPairModule := by
    simpa only [pairEntry,augmentEntry,roundedEntry,approxEntry,List.length_append,Nat.add_assoc] using hasAt_append_right ht
  have hkR := residual_meetsContract (w := w) (hasAt_append_left hlll) J s.flow
  have hkQ := scratchCapacityRoundedSolve_meetsContract (w := w) hproc hS hdet hRounded R (by change J.n ≤ 2*(J.m+J.m); omega) B hpolyR
  have hkA := residualAugment_meetsContract (w := w) hAugment s.flow
    (R.solveCapacityRoundedModel solve B).value
  have hkH := wordPair_meetsContract (w := w) hPair
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hinput,hRinput,hf,hC,hu,hm,hzero,
    hspace,hsmall,hmass,hguest,hbudget,hproduct,hround,hroundGuest,haddition,hw⟩ := hpre
  have hspaceNum : heap+(2+10*J.m+AP+QS+J.m+2+4)<2^w := hspace
  have hAP : AP=scratchBottleneckSearchSpace c d R+10+3*R.n+33*R.m+12 := rfl
  have hC_R := J.residual_costsBounded s.flow C hC
  have hRcap := J.residual_capacities_le s.flow (integral_capacity_bounds_cast J s.flow hf) U hu
  have hkP := scratchPolyApprox_meetsContract (w := w) hproc hS hdet (hasAt_append_right hlll) R (by change J.n ≤ 2*(J.m+J.m); omega) C U hpolyR hC_R
  have hBbound : B≤R.m*(C*U) := scratchPolyApprox_magnitude_le solver entry T S c d hproc R C U hpolyR hC_R hRcap
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
      change resEnd+scratchBottleneckSearchSpace c d R<2^w
      omega
    · omega
  · intro canEnd memP posP hpostP
    obtain ⟨hloP,hhiP,hcandidate,hzP,hframeP⟩ := hpostP
    change resEnd≤canEnd at hloP
    change canEnd≤resEnd+scratchBottleneckSearchSpace c d R+10+3*R.n+33*R.m+8 at hhiP
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
      have hBraw : (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) (J.residual s.flow)).value.magnitude=0 := hB
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
      · change heap≤ret ∧ ret≤heap+scratchCapacityStepSpace solver entry T S c d hproc J s ∧
          CapacityStateAt memH (ret-2) ret (s.step solve).value ∧ ZeroFrom memH ret ∧ ∀ x<heap,memH x=mem x
        have hreserve : scratchCapacityStepSpace solver entry T S c d hproc J s=2+10*J.m+AP+QS+J.m+2+4 := rfl
        rw [hreserve]
        refine ⟨by omega,by omega,hstateH,hzH,?_⟩
        intro x hx
        exact (hframeH x (by omega)).trans (hframeOldP x hx)
      · simp only [scratchCapacityStepContract,R,hstop,Bool.false_eq_true,↓reduceIte,hBraw,residualContract,
          wordPairContract,heapContract,scratchPolyApproxContract,scratchBottleneckSearchContract,startState,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega
    · have hB : B≠0 := hcond
      have hBraw : (polyApproxModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) (J.residual s.flow)).value.magnitude≠0 := hB
      have hQS : QS=5+12*R.m+2^wordSize (scratchWordMultiplier c d) (R.scaledRoundedInstance B).positiveInstance.solverWords := by
        simp only [QS,scratchCapacityRoundedSpace,hB,↓reduceIte]
      have hguestPositive : 0<2^wordSize (scratchWordMultiplier c d) (R.scaledRoundedInstance B).positiveInstance.solverWords := Nat.two_pow_pos _
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
        (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc K) K
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
      · change heap≤ret ∧ ret≤heap+scratchCapacityStepSpace solver entry T S c d hproc J s ∧
          CapacityStateAt memH (ret-2) ret (s.step solve).value ∧ ZeroFrom memH ret ∧ ∀ x<heap,memH x=mem x
        have hreserve : scratchCapacityStepSpace solver entry T S c d hproc J s=2+10*J.m+AP+QS+J.m+2+4 := rfl
        rw [hreserve]
        refine ⟨by omega,by omega,hstateH,hzH,?_⟩
        intro x hx
        exact (hframeH x (by omega)).trans ((hframeA x (by omega)).trans (hframeOldQ x hx))
      · simp only [scratchCapacityStepContract,R,B,solve,hstop,Bool.false_eq_true,↓reduceIte,hBraw,residualContract,
          residualAugmentContract,wordPairContract,heapContract,scratchPolyApproxContract,scratchBottleneckSearchContract,
          scratchCapacityRoundedSolveContract,startState,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega

/-- A stopped capacity state takes constant cost and leaves every memory
cell unchanged, exactly as the model's early-stop branch. -/
theorem scratchCapacityStep_stopped_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hp : p.HasAt b (scratchCapacityStepModule solver entry b c d)) (J : Circulation) (s : CapacityState J)
    (C U : ℕ) (hstop : s.stopped=true) :
    MeetsContract w p b (scratchCapacityStepContract w solver entry T S c d hproc J s C U) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hinput,hRinput,hf,hC,hu,hm,hzero,
    hspace,hsmall,hmass,hguest,hbudget,hproduct,hround,hroundGuest,haddition,hw⟩ := hpre
  obtain ⟨ptr,hheader,hptrEnd,hread⟩ := hstate
  have hs1 : state+1<2^w := by omega
  have hflag : mem (state+1)=1 := by
    have h : mem (state+1)=s.stopped.toNat := hheader 1 (by change 1<2; decide)
    simpa only [hstop,Bool.toNat_true] using h
  have hbase : heap-2=state := by omega
  have hmodel : (s.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K))).value=s := by
    simp only [CapacityState.step,hstop,↓reduceIte]
  apply runs_start_le
  unfold capacityStepBody
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
  wram_step
  refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤heap ∧ heap≤heap+scratchCapacityStepSpace solver entry T S c d hproc J s ∧
      CapacityStateAt mem (heap-2) heap (s.step ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K))).value ∧
      ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
    rw [hbase,hmodel]
    exact ⟨le_rfl,Nat.le_add_right _ _,⟨ptr,hheader,hptrEnd,hread⟩,hzero,fun _ _ => rfl⟩
  · simp only [scratchCapacityStepContract,hstop,↓reduceIte,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    decide

/-- Every represented capacity state executes exactly one model iteration
with its explicit branch cost and complete temporary-space reserve. -/
theorem scratchCapacityStep_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityStepModule solver entry b c d))
    (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (s : CapacityState J) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityStepContract w solver entry T S c d hproc J s C U) := by
  cases hstop : s.stopped with
  | false => exact scratchCapacityStep_active_meetsContract hproc hS hdet hp J hnGraph s C U hc hstop
  | true => exact scratchCapacityStep_stopped_meetsContract hproc hp J s C U hstop

end MinCostFlow.Final
