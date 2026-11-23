module

public import MinCostFlow.Scaling.CyclePeelCode
import MinCostFlow.Scaling.CycleHeaderState
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Completing the cycle scan when the peel stack is empty

In peel mode with an empty stack, the model enters done mode
and reports no result. The machine writes that header, preserves all other
state data, and returns its unchanged traversal heap.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The empty-stack branch computes exactly the peel-mode model step
without allocating a list node or changing any vertex table. -/
theorem cyclePeel_empty_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cyclePeelModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (target : Fin J.n) (hstacknil : s.stack=[]) :
    MeetsContract w p b (cyclePeelContract w J s B C target) := by
  have hkH := cycleHeader_meetsContract (w := w) (hasAt_append_left (hasAt_append_left (hasAt_append_left (hasAt_append_left (hasAt_tail hp)))))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,hbudget,
    hpotential,hz,hs,hw⟩,hmode⟩ := hpre
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
  have hnull : stack=0 := hstack.pointer_zero_iff.mpr hstacknil
  subst stack
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hh : heap<2^w := by omega
  have hb : base<2^w := by omega
  have hb1 : base+1<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hb3 : base+3<2^w := by omega
  have hb4 : base+4<2^w := by omega
  have hb5 : base+5<2^w := by omega
  have hb6 : base+6<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have hcandidatesWord : candidates<2^w := hcandidates.pointer_le.trans_lt hh
  have hn : J.n<2^w := by omega
  have htargetWord : target.val<2^w := target.isLt.trans hn
  have hedgesWord : edges<2^w := hedges.pointer_le.trans_lt hh
  have hsignWord : (if s.cycleCost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hmagWord : s.cycleCost.natAbs<2^w := by omega
  have h1 : mem (base+1)=target.val := by simpa only [hmode,cycleModeVertex,List.getElem_cons_succ,List.getElem_cons_zero] using hheader 1 (by change 1<9; decide)
  have h2 : mem (base+2)=candidates := hheader 2 (by change 2<9; decide)
  have h3 : mem (base+3)=0 := hheader 3 (by change 3<9; decide)
  have h4 : mem (base+4)=edges := hheader 4 (by change 4<9; decide)
  have h5 : mem (base+5)=(if s.cycleCost<0 then 1 else 0) := hheader 5 (by change 5<9; decide)
  have h6 : mem (base+6)=s.cycleCost.natAbs := hheader 6 (by change 6<9; decide)
  let next : Circulation.CycleState J := {s with mode:=.done,result:=none}
  have hmodel : s.step=next := by simp only [Circulation.CycleState.step,hmode,hstacknil,next]
  apply runs_start_le
  unfold cyclePeelBody
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := target.val) (by eval_expr) ?_
  wram_step
  refine runs_seq_call_le hkH
    (vs := [3,0,candidates,0,edges,if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,0,0,base])
    (by eval_expr) (by wram_words) ⟨3,0,candidates,0,edges,_,_,0,0,base,rfl,hb9⟩ ?_
  intro headerEnd memH posH hpostH
  obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next hcandidates (by change IndexListAt mem (cycleNodes J.n base) heap 0 s.stack; rw [hstacknil]; exact .nil) hedges
    (show CycleResultAt mem (cycleNodes J.n base) heap 0 0 next.result from rfl) hseen hout hnodes hz hpostH
  refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
  · change heap≤heap ∧ heap≤heap+4 ∧ CycleStateAt memH base heap s.step ∧ ZeroFrom memH heap ∧
      (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → memH x=mem x) ∧
      ∀ i<9,memH (base+i)<2^w
    refine ⟨le_rfl,by omega,?_,hzH,?_,hwordsH⟩
    · rw [hmodel]; exact hstateH
    · intro x _ hx
      rcases hx with hx | hx
      · exact hframeH x (Or.inl hx)
      · exact hframeH x (Or.inr (by dsimp only [cycleNodes] at hx; omega))
  · simp only [cyclePeelContract,cycleStepContract,cycleHeaderContract,
      argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    decide

end MinCostFlow.Scaling.Machine
