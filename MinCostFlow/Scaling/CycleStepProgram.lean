module

public import MinCostFlow.Scaling.CycleChooseCode
public import MinCostFlow.Scaling.CycleWalkCode
public import MinCostFlow.Scaling.CyclePeelCode
import MinCostFlow.Scaling.CycleChooseProgram
import MinCostFlow.Scaling.CycleWalkProgram
import MinCostFlow.Scaling.CyclePeelProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Dispatching a complete cycle traversal step

Read the stored mode tag and call the corresponding choose, walk, or
peel entry. Done states return their unchanged heap and state. The mode
procedures share one layout and preserve the same traversal frame.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Call a mode entry with the unchanged graph, state, and heap arguments. -/
def cycleStepCall (entry : ℕ) : Stmt :=
  .call 4 entry [.reg 0,.reg 1,.reg 2] ;; .ret (.reg 4)

/-- Dispatch the four stored mode tags. -/
def cycleStepBody (choose walk peel : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;
  .cond (.bin .eq (.reg 3) (.const 0)) (cycleStepCall choose)
    (.cond (.bin .eq (.reg 3) (.const 1)) (cycleStepCall walk)
      (.cond (.bin .eq (.reg 3) (.const 2)) (cycleStepCall peel) (.ret (.reg 2))))

/-- Consecutive entries for dispatch, choose, walk, and peel. -/
def cycleStepModule (b : ℕ) : List Stmt :=
  cycleStepBody (b+1) (b+6) (b+12) ::
    (cycleChooseModule (b+1) ++ cycleWalkModule (b+6) ++ cyclePeelModule (b+12))

/-- Dispatch adds at most 100 steps to the common mode cost. -/
def cycleDispatchContract (w : ℕ) (J : Circulation) (s : Circulation.CycleState J) (B C : ℕ) : Contract :=
  { cycleStepContract w J s B C with cost := fun _ _ => 1100 }

/-- Every mode and the dispatcher have no random instruction. -/
theorem cycleStepModule_noRand (b : ℕ) : ∀ body ∈ cycleStepModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [cycleStepBody,cycleStepCall,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hp
    · rcases List.mem_append.mp hb with hc | hw
      · exact cycleChooseModule_noRand _ body hc
      · exact cycleWalkModule_noRand _ body hw
    · exact cyclePeelModule_noRand _ body hp

/-- Mode dispatch computes exactly one model step with four-cell reserve,
unchanged source data, and reusable header word bounds. -/
theorem cycleStep_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleStepModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) : MeetsContract w p b (cycleDispatchContract w J s B C) := by
  have ht := hasAt_tail hp
  have hl := hasAt_append_left ht
  have hChoose := hasAt_append_left hl
  have hWalk : p.HasAt (b+6) (cycleWalkModule (b+6)) := by
    simpa only [cycleChooseModule,cycleHeaderModule,boolTableSetModule,List.length_append,
      List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hl
  have hPeel : p.HasAt (b+12) (cyclePeelModule (b+12)) := by
    simpa only [cycleChooseModule,cycleWalkModule,cycleHeaderModule,boolTableSetModule,wordPairModule,
      List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right ht
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  have hpreOld := hpre
  obtain ⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,hbudget,
    hpotential,hz,hs,hw⟩ := hpre
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
  have htag : mem base=cycleModeTag s.mode := by
    have h : mem (base+0)=cycleModeTag s.mode := hheader 0 (by change 0<9; decide)
    simpa only [Nat.add_zero] using h
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hb : base<2^w := by omega
  have htagWord : cycleModeTag s.mode<2^w := by rw [←htag]; exact hheaderWords 0 (by decide)
  apply runs_start_le
  unfold cycleStepBody
  refine runs_seq_assign_le (v := cycleModeTag s.mode) (by eval_expr) ?_
  cases hmode : s.mode with
  | choose =>
    simp only [cycleModeTag]
    wram_step
    unfold cycleStepCall
    refine runs_seq_call_le (cycleChoose_meetsContract hChoose J s B C)
      (vs := [a,base,heap]) (by eval_expr) hwords ⟨hpreOld,hmode⟩ ?_
    intro ret mem' pos' hpost
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) hpost ?_
    simp only [cycleDispatchContract,cycleChooseContract,cycleStepContract,
      argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,Expr.size_const]
    decide
  | walk v =>
    simp only [cycleModeTag]
    wram_step
    wram_step
    unfold cycleStepCall
    refine runs_seq_call_le (cycleWalk_meetsContract hWalk J s B C v)
      (vs := [a,base,heap]) (by eval_expr) hwords ⟨hpreOld,hmode⟩ ?_
    intro ret mem' pos' hpost
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) hpost ?_
    simp only [cycleDispatchContract,cycleWalkContract,cycleStepContract,
      argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,Expr.size_const]
    decide
  | peel v =>
    simp only [cycleModeTag]
    wram_step
    wram_step
    wram_step
    unfold cycleStepCall
    refine runs_seq_call_le (cyclePeel_meetsContract hPeel J s B C v)
      (vs := [a,base,heap]) (by eval_expr) hwords ⟨hpreOld,hmode⟩ ?_
    intro ret mem' pos' hpost
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) hpost ?_
    simp only [cycleDispatchContract,cyclePeelContract,cycleStepContract,
      argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,Expr.size_const]
    decide
  | done =>
    simp only [cycleModeTag]
    wram_step
    wram_step
    wram_step
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+4 ∧ CycleStateAt mem base heap s.step ∧ ZeroFrom mem heap ∧
        (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → mem x=mem x) ∧ ∀ i<9,mem (base+i)<2^w
      refine ⟨le_rfl,by omega,?_,hz,fun _ _ _ => rfl,hheaderWords⟩
      simpa only [Circulation.CycleState.step,hmode] using
        (show CycleStateAt mem base heap s from ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩)
    · simp only [cycleDispatchContract]
      decide

end MinCostFlow.Scaling.Machine
