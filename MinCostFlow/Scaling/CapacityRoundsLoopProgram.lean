module

public import MinCostFlow.Scaling.CapacityRoundsLoopContract
import MinCostFlow.Scaling.CapacityStepCountedCost
import MinCostFlow.Scaling.CapacityStepInvariant
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing all bounded capacity rounds

Induct on the number of rounds. The recursive call returns the exact
preceding model state, whose capacity bounds follow from the proved step
invariant. The uniform reserve supplies every numerical premise of the
next step. Source frames compose, and the model's extra work charge pays
for the loop's constant call and header-address overhead.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem rounds_cost_padding (a b Q W V S K : ℕ) (hK : 100≤K)
    (hS : S≤b*Q+K*V) :
    0+(1+1+1)+1+(1+(1+(1+1+1+(1+0))))+(a*Q+K*W+100)+2+
      (1+1+1)+2+(1+(1+(1+0)))+S+2+(1+1)≤
      (a+b)*Q+K*(W+(V+1))+100 := by
  rw [Nat.add_mul,Nat.mul_add,Nat.mul_add,Nat.mul_one]
  omega

private theorem rounds_recursive_args {w a state fuel heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=state) (h2 : st.regs 2=fuel+1) (h3 : st.regs 3=heap)
    (hf : fuel+1<2^w) :
    evalArgs w st [.reg 0,.reg 1,.bin .sub (.reg 2) (.const 1),.reg 3]=some [a,state,fuel,heap] := by
  have hsub : fuel+1-1=fuel := rfl
  rw [←hsub]
  eval_expr

private theorem rounds_state_eval {w mid : ℕ} {st : State} (hr : st.regs 4=mid)
    (hm : mid<2^w) (h2 : 2<2^w) :
    Expr.eval w st (.bin .sub (.reg 4) (.const 2))=some (mid-2) := by eval_expr

private theorem rounds_step_args {w a state heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h5 : st.regs 5=state) (h4 : st.regs 4=heap) :
    evalArgs w st [.reg 0,.reg 5,.reg 4]=some [a,state,heap] := by eval_expr

/-- The repeated machine step computes the exact finite capacity model
loop, with its actual call/work bound and uniform per-round workspace. -/
theorem capacityRoundsLoop_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityRoundsLoopModule solver entry b))
    (J : Circulation) (s : CapacityState J) (C U fuel : ℕ)
    (hn : J.n≤2*J.m) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityRoundsLoopContract w solver entry T hproc J s C U fuel) := by
  let solve := canonicalSolver solver entry T hproc
  let N := (capacityStepNumberBase J C U)^256
  have hD4 : 4≤capacityStepNumberBase J C U := by dsimp only [capacityStepNumberBase]; omega
  have hN : 1≤N := Nat.one_le_pow 256 _ (by omega)
  induction fuel generalizing s with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hf,hC,hu,hm,hz,hspace,hfuel⟩ := hpre
    have hbase : heap-2=state := by omega
    apply runs_start_le
    unfold capacityRoundsLoopBody
    wram_step
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+0*N ∧ CapacityStateAt mem (heap-2) heap s ∧
        ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
      rw [hbase]
      exact ⟨le_rfl,by omega,hstate,hz,fun _ _ => rfl⟩
    · simp only [capacityRoundsLoopContract,CallResult.forRounds,CallResult.pure,List.length_nil,
        Nat.zero_mul,Nat.mul_zero,Nat.zero_add,Expr.size_bin,Expr.size_reg,Expr.size_const]
      decide
  | succ fuel ih =>
    have hkR := ih s
    let r := CallResult.forRounds (CapacityState.step solve) fuel s
    have hkS := capacityStep_meetsContract (w := w) hproc hdet (hasAt_tail hp) J r.value C U hc
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hf,hC,hu,hm,hz,hspace,hfuel⟩ := hpre
    have hspaceNum : heap+(fuel+1+1)*N<2^w := hspace
    simp only [Nat.add_mul,Nat.one_mul] at hspaceNum
    have hh : heap<2^w := by omega
    have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
    have hstateWord : state<2^w := by omega
    have hfuelWord : fuel<2^w := by omega
    have hfR : ∀ e,0≤r.value.flow e ∧ r.value.flow e≤J.capacity e :=
      CallResult.forRounds_invariant (CapacityState.step solve)
        (fun s => ∀ e,0≤s.flow e ∧ s.flow e≤J.capacity e)
        (fun s hs => capacityStep_flow_bounds solver entry T hproc J s hc hs) fuel s hf
    apply runs_start_le
    unfold capacityRoundsLoopBody
    wram_step
    refine runs_seq_call_le hkR (vs := [a,state,fuel,heap]) ?_ (by wram_words)
      ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hf,hC,hu,hm,hz,?_,hfuelWord⟩ ?_
    · exact rounds_recursive_args (by rfl) (by rfl) (by rfl) (by rfl) hfuel
    · change heap+(fuel+1)*N<2^w
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · intro midHeap memR posR hpostR
      obtain ⟨hloR,hhiR,hstateR,hzR,hframeR⟩ := hpostR
      change heap≤midHeap at hloR
      change midHeap≤heap+fuel*N at hhiR
      change CapacityStateAt memR (midHeap-2) midHeap r.value at hstateR
      change ZeroFrom memR midHeap at hzR
      change (∀ x<heap,memR x=mem x) at hframeR
      have hmidWord : midHeap<2^w := by omega
      have hmidStateWord : midHeap-2<2^w := by omega
      have hmidStateEnd : midHeap-2+2=midHeap := by omega
      have hgraphR : ListAt memR a J.solverWords := hgraph.of_agree_below (h₀ := heap) hgraphEnd hframeR
      have hstepPre := capacityStep_pre_of_space solver entry T hproc J r.value C U hc hm hfR hC hu
        a (midHeap-2) midHeap memR hgraphR (by omega) hmidStateEnd hstateR hzR (by
          change midHeap+N<2^w
          omega)
      have hstepCost := capacityStep_cost_counted w solver entry T hproc J r.value C U
        [a,midHeap-2,midHeap] memR hm hn hc
      have hstepSpace : capacityStepSpace solver entry T hproc J r.value≤N :=
        capacityStepSpace_le solver entry T hproc J r.value C U hm hfR hC hu
      have htwo : 2<2^w := by omega
      refine runs_seq_assign_le (v := midHeap-2) (rounds_state_eval (by rfl) hmidWord htwo) ?_
      refine runs_seq_call_le hkS (vs := [a,midHeap-2,midHeap])
        (rounds_step_args (by rfl) (by rfl) (by rfl)) (by wram_words) hstepPre ?_
      intro ret memS posS hpostS
      obtain ⟨hloS,hhiS,hstateS,hzS,hframeS⟩ := hpostS
      change midHeap≤ret at hloS
      change ret≤midHeap+capacityStepSpace solver entry T hproc J r.value at hhiS
      change (∀ x<midHeap,memS x=memR x) at hframeS
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+(fuel+1)*N ∧
          CapacityStateAt memS (ret-2) ret (CallResult.forRounds (CapacityState.step solve) (fuel+1) s).value ∧
          ZeroFrom memS ret ∧ ∀ x<heap,memS x=mem x
        refine ⟨by omega,?_,hstateS,hzS,?_⟩
        · rw [Nat.add_mul,Nat.one_mul]
          omega
        · intro x hx
          exact (hframeS x (by omega)).trans (hframeR x hx)
      · have hK : 100≤100000*(solver.regBound+1) := by omega
        have hpad := rounds_cost_padding r.calls.length (r.value.step solve).calls.length
          ((solver.regBound+6)*T (J.n+1) (J.m+J.m)) r.work (r.value.step solve).work
          ((capacityStepContract w solver entry T hproc J r.value C U).cost [a,midHeap-2,midHeap] memR)
          (100000*(solver.regBound+1)) hK hstepCost
        simpa only [capacityRoundsLoopContract,CallResult.forRounds,CallResult.bind,CallResult.charge,
          List.length_append,startState,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg,Expr.size_const,
          Nat.add_assoc,Nat.reduceAdd] using hpad

end MinCostFlow.Scaling.Machine
