module

public import MinCostFlow.Scaling.CostRoundsLoopContract
import MinCostFlow.Scaling.CostStepProgram
import MinCostFlow.Scaling.CostStepCountedCost
import MinCostFlow.Scaling.CostStepWords
import MinCostFlow.Scaling.CostPrefixWordBounds
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing every prescribed measured cost prefix

Induct on the prefix length. Recursion returns the preceding exact model
state. Its proved power, potential, and flow bounds supply the next
round's complete word premises from the common reserve. The model's
one-unit control charge pays for the recursive entry's fixed overhead.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem cost_rounds_padding (a b Q W V S K : ℕ) (hK : 100≤K) (hS : S≤b*Q+K*V) :
    0+(1+1+1)+1+(1+(1+(1+1+1+(1+(1+(1+0))))))+(a*Q+K*W+100)+2+
      (1+1+1)+2+(1+(1+(1+(1+(1+0)))))+S+2+(1+1)≤
      (a+b)*Q+K*(W+(V+1))+100 := by
  rw [Nat.add_mul,Nat.mul_add,Nat.mul_add,Nat.mul_one]
  omega

private theorem cost_rounds_recursive_args {w a state fuel C U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=state) (h2 : st.regs 2=fuel+1)
    (h3 : st.regs 3=C) (h4 : st.regs 4=U) (h5 : st.regs 5=heap) (hf : fuel+1<2^w) :
    evalArgs w st [.reg 0,.reg 1,.bin .sub (.reg 2) (.const 1),.reg 3,.reg 4,.reg 5]=some [a,state,fuel,C,U,heap] := by
  have heq : fuel+1-1=fuel := rfl
  rw [←heq]
  eval_expr

private theorem cost_rounds_state_eval {w heap : ℕ} {st : State} (h6 : st.regs 6=heap)
    (hh : heap<2^w) (h3 : 3<2^w) : Expr.eval w st (.bin .sub (.reg 6) (.const 3))=some (heap-3) := by eval_expr

private theorem cost_rounds_step_args {w a state C U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h7 : st.regs 7=state) (h3 : st.regs 3=C) (h4 : st.regs 4=U) (h6 : st.regs 6=heap) :
    evalArgs w st [.reg 0,.reg 7,.reg 3,.reg 4,.reg 6]=some [a,state,C,U,heap] := by eval_expr

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- The repeated machine computes exactly the measured initial-state
prefix, with its actual call/work cost and uniform per-round workspace. -/
theorem costRoundsLoop_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (costRoundsLoopModule solver entry b)) (J : Circulation) (C U fuel : ℕ) :
    MeetsContract w p b (costRoundsLoopContract w solver entry T hproc J C U fuel) := by
  let inner := fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U
  let N := (costStepNumberBase J C U)^524
  have hD8 : 8≤costStepNumberBase J C U := by dsimp only [costStepNumberBase]; omega
  have hN : 1≤N := Nat.one_le_pow 524 _ (by omega)
  induction fuel with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hC,hu,hm,hnU,ht,hz,hs⟩ := hpre
    have hbase : heap-3=state := by omega
    apply runs_start_le
    unfold costRoundsLoopBody
    wram_step
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+0*N ∧ CostStateAt mem (heap-3) heap (CostState.initial J) ∧
        ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
      rw [hbase]
      exact ⟨le_rfl,by omega,hstate,hz,fun _ _ => rfl⟩
    · simp only [costRoundsLoopContract,CallResult.forRounds,CallResult.pure,List.length_nil,
        Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Expr.size_bin,Expr.size_reg,Expr.size_const]
      decide
  | succ fuel ih =>
    let r := CallResult.forRounds (CostState.stepMeasured inner C) fuel (CostState.initial J)
    have hkS := costStep_meetsContract (w := w) hproc hdet (hasAt_tail hp) r.value C U
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hC,hu,hm,hnU,ht,hz,hs⟩ := hpre
    have hspaceNum : heap+(fuel+1+1)*N<2^w := hs
    simp only [Nat.add_mul,Nat.one_mul] at hspaceNum
    have hNword : N<2^w := by omega
    have hh : heap<2^w := by omega
    have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
    have hstateWord : state<2^w := by omega
    have hCword : C<2^w := hwords C (by simp)
    have hUword : U<2^w := hwords U (by simp)
    have hcountWord : fuel+1<2^w := hwords _ (by simp)
    have hfuelWord : fuel<2^w := by omega
    have hprefix : fuel≤costRounds J.n C := by omega
    have hf := costMeasuredPrefix_flow_bounds solver entry T hproc J C U fuel hu (by omega)
    have hp := costMeasuredPrefix_power_le inner J C U fuel hprefix
    have hpot := costMeasuredPrefix_potential_le inner J C U fuel hprefix
    apply runs_start_le
    unfold costRoundsLoopBody
    wram_step
    refine runs_seq_call_le ih (vs := [a,state,fuel,C,U,heap])
      (cost_rounds_recursive_args (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hcountWord)
      (by wram_words) ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hC,hu,hm,hnU,hprefix,hz,?_⟩ ?_
    · change heap+(fuel+1)*N<2^w
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · intro midHeap memR posR hpostR
      obtain ⟨hloR,hhiR,hstateR,hzR,hframeR⟩ := hpostR
      change heap≤midHeap at hloR
      change midHeap≤heap+fuel*N at hhiR
      change CostStateAt memR (midHeap-3) midHeap r.value at hstateR
      change ZeroFrom memR midHeap at hzR
      change (∀ x<heap,memR x=mem x) at hframeR
      have hmidWord : midHeap<2^w := by omega
      have hmidStateWord : midHeap-3<2^w := by omega
      have hmidStateEnd : midHeap-3+3=midHeap := by omega
      have hgraphR := hgraph.of_agree_below hgraphEnd hframeR
      have hstepPre := costStep_pre_of_space solver entry T hproc r.value C U a (midHeap-3) midHeap memR
        hgraphR (by omega) hmidStateEnd hstateR hf hC hu hm hnU hp hpot hzR (by change midHeap+N<2^w; omega)
      have hstepCost := costStep_cost_counted w solver entry T hproc hmono r.value C U
        [a,midHeap-3,C,U,midHeap] memR
      have hstepSpace : costStepSpace solver entry T hproc r.value C U≤N := costStepSpace_le solver entry T hproc r.value C U
      have h3 : 3<2^w := by omega
      refine runs_seq_assign_le (v := midHeap-3) (cost_rounds_state_eval (by rfl) hmidWord h3) ?_
      refine runs_seq_call_le hkS (vs := [a,midHeap-3,C,U,midHeap])
        (cost_rounds_step_args (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words) hstepPre ?_
      intro ret memS posS hpostS
      obtain ⟨hloS,hhiS,hstateS,hzS,hframeS⟩ := hpostS
      change midHeap≤ret at hloS
      change ret≤midHeap+costStepSpace solver entry T hproc r.value C U at hhiS
      change (∀ x<midHeap,memS x=memR x) at hframeS
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+(fuel+1)*N ∧
          CostStateAt memS (ret-3) ret (CallResult.forRounds (CostState.stepMeasured inner C) (fuel+1) (CostState.initial J)).value ∧
          ZeroFrom memS ret ∧ ∀ x<heap,memS x=mem x
        refine ⟨by omega,?_,hstateS,hzS,?_⟩
        · rw [Nat.add_mul,Nat.one_mul]
          omega
        · intro x hx
          exact (hframeS x (by omega)).trans (hframeR x hx)
      · have hK : 100≤300000*(solver.regBound+1) := by omega
        have hpad := cost_rounds_padding r.calls.length (CostState.stepMeasured inner C r.value).calls.length
          ((solver.regBound+6)*T (J.n+3) (16*J.m+4*J.n)) r.work (CostState.stepMeasured inner C r.value).work
          ((costStepContract w solver entry T hproc r.value C U).cost [a,midHeap-3,C,U,midHeap] memR)
          (300000*(solver.regBound+1)) hK hstepCost
        simpa only [costRoundsLoopContract,CallResult.forRounds,CallResult.bind,CallResult.charge,
          List.length_append,startState,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const,
          Nat.add_assoc,Nat.reduceAdd] using hpad

end MinCostFlow.Scaling.Machine
