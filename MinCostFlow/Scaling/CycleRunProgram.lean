module

public import MinCostFlow.Scaling.CycleRunContract
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing the bounded cycle traversal

Induct on the fuel. With no fuel or a completed state, return immediately.
Otherwise the proved dispatcher computes one exact step. Its frames keep
the graph available, and its magnitude and potential bounds supply the
recursive call's premises. The two allocation bounds add to four cells
per round, and each round has a constant execution cost.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Every finite fuel budget computes the model traversal, with cost at
most `1200*fuel+20` and at most `4*fuel` fresh cells. -/
theorem cycleRun_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleRunModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C fuel : ℕ) : MeetsContract w p b (cycleRunContract w J s B C fuel) := by
  induction fuel generalizing s B with
  | zero =>
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,
      hbudget,hpotential,hz,hs,hfuel,hw⟩ := hpre
    apply runs_start_le
    unfold cycleRunBody
    wram_step
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+4*0 ∧ CycleStateAt mem base heap s ∧ ZeroFrom mem heap ∧
        (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → mem x=mem x) ∧ ∀ i<9,mem (base+i)<2^w
      exact ⟨le_rfl,by omega,hstate,hz,fun _ _ _ => rfl,hheaderWords⟩
    · simp only [cycleRunContract,Nat.mul_zero,Nat.zero_add,Expr.size_bin,Expr.size_reg,Expr.size_const]
      decide
  | succ fuel ih =>
    have hkS := cycleStep_meetsContract (w := w) (hasAt_tail hp) J s B C
    have hkR := ih s.step (B+C)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,
      hbudget,hpotential,hz,hs,hfuel,hw⟩ := hpre
    have hnodeNum : base+10+3*J.n≤heap := hnodes
    have hb : base<2^w := by omega
    have hh : heap<2^w := by omega
    have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
    have hf : fuel<2^w := by omega
    have hbudgetStep : B+C<2^w := by
      have hC : C≤(fuel+1+1)*C := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right C (by omega : 1≤fuel+1+1)
      omega
    obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
    have htag : mem base=cycleModeTag s.mode := by
      have h : mem (base+0)=cycleModeTag s.mode := hheader 0 (by change 0<9; decide)
      simpa only [Nat.add_zero] using h
    have htagWord : cycleModeTag s.mode<2^w := by rw [←htag]; exact hheaderWords 0 (by decide)
    have hstateOld : CycleStateAt mem base heap s :=
      ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩
    apply runs_start_le
    unfold cycleRunBody
    wram_step
    refine runs_seq_assign_le (v := cycleModeTag s.mode) (by eval_expr) ?_
    wram_step
    · have hdone : s.mode=.done := by
        cases hm : s.mode <;> simp_all [cycleModeTag]
      refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤heap ∧ heap≤heap+4*(fuel+1) ∧
          CycleStateAt mem base heap (Circulation.CycleState.run (fuel+1) s).1 ∧ ZeroFrom mem heap ∧
          (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → mem x=mem x) ∧ ∀ i<9,mem (base+i)<2^w
        refine ⟨le_rfl,by omega,?_,hz,fun _ _ _ => rfl,hheaderWords⟩
        simpa only [Circulation.CycleState.run,hdone,↓reduceIte] using hstateOld
      · simp only [cycleRunContract,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        omega
    · have hnotdone : s.mode≠.done := by
        intro heq
        simp [heq,cycleModeTag] at hcond
      refine runs_seq_call_le hkS (vs := [a,base,heap]) (by eval_expr) (by wram_words)
        ⟨a,base,heap,rfl,hgraph,hgraphEnd,hstateOld,hnodes,hheaderWords,hcost,hcosts,
          hbudgetStep,hpotential,hz,by omega,hw⟩ ?_
      intro midHeap memS posS hpostS
      obtain ⟨hlo,hhi,hstateS,hzS,hframeS,hheaderS⟩ := hpostS
      change heap≤midHeap at hlo
      change midHeap≤heap+4 at hhi
      change CycleStateAt memS base midHeap s.step at hstateS
      change ZeroFrom memS midHeap at hzS
      change (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → memS x=mem x) at hframeS
      change (∀ i<9,memS (base+i)<2^w) at hheaderS
      have hgraphS : ListAt memS a J.solverWords := by
        intro i hi
        rw [hframeS _ (by omega) (Or.inl (by omega))]
        exact hgraph i hi
      have hmidWord : midHeap<2^w := by omega
      have hbudgetR : B+C+(fuel+1)*C<2^w := by
        rw [Nat.succ_mul] at hbudget
        omega
      have hspaceR : midHeap+4*fuel+4<2^w := by
        rw [Nat.mul_succ] at hs
        omega
      have hpotentialS : s.step.potential+1<2^w := by
        have h := s.step_potential_le
        omega
      refine runs_seq_call_le hkR (vs := [a,base,fuel,midHeap]) ?_ (by wram_words)
        ⟨a,base,midHeap,rfl,hgraphS,hgraphEnd,hstateS,hnodes.trans hlo,hheaderS,
          s.step_cost_bound B C hcost hcosts,hcosts,hbudgetR,hpotentialS,hzS,hspaceR,hf,hw⟩ ?_
      · have heq : fuel+1-1=fuel := rfl
        rw [←heq]
        eval_expr
      · intro ret memR posR hpostR
        obtain ⟨hloR,hhiR,hstateR,hzR,hframeR,hheaderR⟩ := hpostR
        change midHeap≤ret at hloR
        change ret≤midHeap+4*fuel at hhiR
        change CycleStateAt memR base ret (Circulation.CycleState.run fuel s.step).1 at hstateR
        change ZeroFrom memR ret at hzR
        change (∀ x<midHeap,x<base ∨ cycleNodes J.n base≤x → memR x=memS x) at hframeR
        change (∀ i<9,memR (base+i)<2^w) at hheaderR
        refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
        · change heap≤ret ∧ ret≤heap+4*(fuel+1) ∧
            CycleStateAt memR base ret (Circulation.CycleState.run (fuel+1) s).1 ∧ ZeroFrom memR ret ∧
            (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → memR x=mem x) ∧ ∀ i<9,memR (base+i)<2^w
          refine ⟨by omega,by omega,?_,hzR,?_,hheaderR⟩
          · simpa only [Circulation.CycleState.run,hnotdone,↓reduceIte] using hstateR
          · intro x hx houtside
            exact (hframeR x (by omega) houtside).trans (hframeS x hx houtside)
        · simp only [cycleRunContract,cycleDispatchContract,argsSize_cons,argsSize_nil,
            Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega

end MinCostFlow.Scaling.Machine
