module

public import MinCostFlow.Scaling.CyclePeelFinishCode
import MinCostFlow.Scaling.CyclePeelFlags
import MinCostFlow.Scaling.CycleHeaderState
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing the peeled-edge finishing cases

The prepared path flag makes the remaining model update a header change.
The tail/target comparison decides whether a closed part is complete, and
its canonical sign decides whether to retain it. All three machine
branches write exactly the corresponding model state.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The prepared peeled-edge procedure computes exactly the model step,
retains the exact negative closed part when found, and preserves every
cell outside the header, with no fresh allocation and cost at most 600. -/
theorem cyclePeelFinish_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cyclePeelFinishModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (target : Fin J.n) (e : Fin J.m) (rest : List (Fin J.m)) :
    MeetsContract w p b (cyclePeelFinishContract w J s target e rest) := by
  have hkH := cycleHeader_meetsContract (w := w) (hasAt_tail hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base,tail,cycle,heap,rfl,hstate,htail,hcycle,hmode,hstack,hseenPrepared,hnodes,
    hheaderWords,hz,hh,hw⟩ := hpre
  obtain ⟨candidates,oldStack,oldEdges,flag,result,hheader,hcandidates,hstackOld,hedgesOld,hresult,hseen,hout⟩ := hstate
  let cost := s.cycleCost+J.cost e
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hb : base<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hb7 : base+7<2^w := by omega
  have hb8 : base+8<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have hn : J.n<2^w := by omega
  have htargetWord : target.val<2^w := target.isLt.trans hn
  have htailWord : (J.tail e).val<2^w := (J.tail e).isLt.trans hn
  have hstackTailWord : tail<2^w := htail.pointer_le.trans_lt hh
  have hcycleWord : cycle<2^w := hcycle.pointer_le.trans_lt hh
  have hcandidatesWord : candidates<2^w := hcandidates.pointer_le.trans_lt hh
  have hsignWord : (if cost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hcostWord : cost.natAbs<2^w := hwords _ (by simp [cost])
  have h2 : mem (base+2)=candidates := hheader 2 (by change 2<9; decide)
  have h7 : mem (base+7)=flag := hheader 7 (by change 7<9; decide)
  have h8 : mem (base+8)=result := hheader 8 (by change 8<9; decide)
  have hflagWord : flag<2^w := by rw [←h7]; exact hheaderWords 7 (by decide)
  have hresultWord : result<2^w := by rw [←h8]; exact hheaderWords 8 (by decide)
  have hmodel := s.peel_step_of_prepared_flag target e rest hmode hstack hseenPrepared
  apply runs_start_le
  unfold cyclePeelFinishBody
  wram_step
  · have hclose : J.tail e=target := Fin.ext hcond
    wram_step
    · have hneg : s.cycleCost+J.cost e<0 := hcond
      let next : Circulation.CycleState J := {s with mode:=.done,stack:=rest,cycleEdges:=e::s.cycleEdges,cycleCost:=cost,result:=some (e::s.cycleEdges)}
      have hnext : s.step=next := by simpa only [hclose,hneg,↓reduceIte] using hmodel
      unfold cyclePeelFinishWrite
      refine runs_seq_call_le hkH
        (vs := [3,0,candidates,tail,cycle,if cost<0 then 1 else 0,cost.natAbs,1,cycle,base])
        (by simp only [List.cons_append,List.nil_append]; eval_expr) (by wram_words)
        ⟨3,0,candidates,tail,cycle,_,_,1,cycle,base,rfl,hb9⟩ ?_
      intro headerEnd memH posH hpostH
      have hsuccess : CycleResultAt mem (cycleNodes J.n base) heap 1 cycle next.result := ⟨rfl,hcycle⟩
      obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next hcandidates htail hcycle
        hsuccess hseen hout hnodes hz hpostH
      refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap=heap ∧ CycleStateAt memH base heap s.step ∧ ZeroFrom memH heap ∧
          (∀ x,x<base ∨ base+9≤x → memH x=mem x) ∧ ∀ i<9,memH (base+i)<2^w
        rw [hnext]
        exact ⟨rfl,hstateH,hzH,hframeH,hwordsH⟩
      · simp only [cyclePeelFinishContract,cycleHeaderContract,List.cons_append,List.nil_append,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        decide
    · have hnonneg : ¬s.cycleCost+J.cost e<0 := hcond
      let next : Circulation.CycleState J := {s with mode:=.walk target,stack:=rest,cycleEdges:=[],cycleCost:=0}
      have hnext : s.step=next := by simpa only [hclose,hnonneg,↓reduceIte] using hmodel
      unfold cyclePeelFinishWrite
      refine runs_seq_call_le hkH (vs := [1,target.val,candidates,tail,0,0,0,flag,result,base])
        (by simp only [List.cons_append,List.nil_append]; eval_expr) (by wram_words)
        ⟨1,target.val,candidates,tail,0,0,0,flag,result,base,rfl,hb9⟩ ?_
      intro headerEnd memH posH hpostH
      obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next hcandidates htail (.nil)
        hresult hseen hout hnodes hz hpostH
      refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap=heap ∧ CycleStateAt memH base heap s.step ∧ ZeroFrom memH heap ∧
          (∀ x,x<base ∨ base+9≤x → memH x=mem x) ∧ ∀ i<9,memH (base+i)<2^w
        rw [hnext]
        exact ⟨rfl,hstateH,hzH,hframeH,hwordsH⟩
      · simp only [cyclePeelFinishContract,cycleHeaderContract,List.cons_append,List.nil_append,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        decide
  · have hnotclose : J.tail e≠target := fun heq => hcond (congrArg Fin.val heq)
    let next : Circulation.CycleState J := {s with stack:=rest,cycleEdges:=e::s.cycleEdges,cycleCost:=cost}
    have hnext : s.step=next := by simpa only [hnotclose,↓reduceIte] using hmodel
    unfold cyclePeelFinishWrite
    refine runs_seq_call_le hkH
      (vs := [2,target.val,candidates,tail,cycle,if cost<0 then 1 else 0,cost.natAbs,flag,result,base])
      (by simp only [List.cons_append,List.nil_append]; eval_expr) (by wram_words)
      ⟨2,target.val,candidates,tail,cycle,_,_,flag,result,base,rfl,hb9⟩ ?_
    intro headerEnd memH posH hpostH
    have hheaderPost : (cycleHeaderContract w).post
        [cycleModeTag next.mode,cycleModeVertex next.mode,candidates,tail,cycle,
          if next.cycleCost<0 then 1 else 0,next.cycleCost.natAbs,flag,result,base] mem headerEnd memH := by
      simpa only [next,hmode,cycleModeTag,cycleModeVertex,startState] using hpostH
    obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next hcandidates htail hcycle
      hresult hseen hout hnodes hz hheaderPost
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap=heap ∧ CycleStateAt memH base heap s.step ∧ ZeroFrom memH heap ∧
        (∀ x,x<base ∨ base+9≤x → memH x=mem x) ∧ ∀ i<9,memH (base+i)<2^w
      rw [hnext]
      exact ⟨rfl,hstateH,hzH,hframeH,hwordsH⟩
    · simp only [cyclePeelFinishContract,cycleHeaderContract,List.cons_append,List.nil_append,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      decide

end MinCostFlow.Scaling.Machine
