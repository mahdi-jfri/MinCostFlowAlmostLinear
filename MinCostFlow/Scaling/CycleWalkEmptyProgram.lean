module

public import MinCostFlow.Scaling.CycleWalkCode
import MinCostFlow.Scaling.CycleHeaderState
import MinCostFlow.Scaling.CycleStateFrames
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Returning from an exhausted cycle walk

When the current vertex has no outgoing unused edge, clear its path flag,
empty the walk stack, and return to choose mode. The shared Boolean store
and header writer implement exactly these model updates. No node is
allocated, and all outgoing lists and other path flags remain unchanged.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The exhausted-walk branch computes exactly the model step with the
common cycle-step frame, word bounds, and constant cost. -/
theorem cycleWalk_empty_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleWalkModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (v : Fin J.n) (houtnil : s.outgoing v=[]) :
    MeetsContract w p b (cycleWalkContract w J s B C v) := by
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hkH := cycleHeader_meetsContract (w := w) (hasAt_append_left hleft)
  have hflags : p.HasAt (b+4) boolTableSetModule := by
    simpa only [cycleHeaderModule,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hleft
  have hkF := boolTableSet_meetsContract (w := w) hflags s.onPath v false
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,hbudget,
    hpotential,hz,hs,hw⟩,hmode⟩ := hpre
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
  let heads := cycleHeads J.n base
  let headAddr := heads+2*v.val
  obtain ⟨outPtr,houtHeader,houtList⟩ := hout v
  have houtPtr : outPtr=0 := houtList.pointer_zero_iff.mpr houtnil
  have houtCell : mem headAddr=0 := by
    have h := houtHeader 0 (by change 0<2; decide)
    change mem (headAddr+0)=outPtr at h
    simpa only [Nat.add_zero,houtPtr] using h
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hN := (solver_header_at J hgraph).1
  have hh : heap<2^w := by omega
  have hb : base<2^w := by omega
  have hb1 : base+1<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hb4 : base+4<2^w := by omega
  have hb5 : base+5<2^w := by omega
  have hb6 : base+6<2^w := by omega
  have hb7 : base+7<2^w := by omega
  have hb8 : base+8<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have hn : J.n<2^w := by omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hv : v.val<2^w := by have hi := v.isLt; omega
  have h2v : 2*v.val<2^w := by have hi := v.isLt; omega
  have hheads : heads<2^w := by dsimp only [heads,cycleHeads]; omega
  have haddr : headAddr<2^w := by dsimp only [headAddr,heads,cycleHeads]; have hi := v.isLt; omega
  have hcandidatesWord : candidates<2^w := hcandidates.pointer_le.trans_lt hh
  have hedgesWord : edges<2^w := hedges.pointer_le.trans_lt hh
  have hsignWord : (if s.cycleCost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hmagWord : s.cycleCost.natAbs<2^w := by omega
  have h1 : mem (base+1)=v.val := by simpa only [hmode,cycleModeVertex,List.getElem_cons_succ,List.getElem_cons_zero] using hheader 1 (by change 1<9; decide)
  have h2 : mem (base+2)=candidates := hheader 2 (by change 2<9; decide)
  have h4 : mem (base+4)=edges := hheader 4 (by change 4<9; decide)
  have h5 : mem (base+5)=(if s.cycleCost<0 then 1 else 0) := hheader 5 (by change 5<9; decide)
  have h6 : mem (base+6)=s.cycleCost.natAbs := hheader 6 (by change 6<9; decide)
  have h7 : mem (base+7)=flag := hheader 7 (by change 7<9; decide)
  have h8 : mem (base+8)=result := hheader 8 (by change 8<9; decide)
  have hflagWord : flag<2^w := by rw [←h7]; exact hheaderWords 7 (by decide)
  have hresultWord : result<2^w := by rw [←h8]; exact hheaderWords 8 (by decide)
  have hseenEnd : base+9+J.n<2^w := by omega
  have hflagAddr : base+9+v.val<heap := by have hi := v.isLt; omega
  let next : Circulation.CycleState J := {s with mode:=.choose,stack:=[],onPath:=Function.update s.onPath v false}
  have hmodel : s.step=next := by simp only [Circulation.CycleState.step,hmode,houtnil,next]
  apply runs_start_le
  unfold cycleWalkBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := v.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heads) (by dsimp only [heads,cycleHeads]; eval_expr) ?_
  refine runs_seq_assign_le (v := headAddr) (by dsimp only [headAddr]; eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  wram_step
  refine runs_seq_call_le hkF (vs := [base+9,v.val,0]) (by eval_expr) (by wram_words)
    ⟨base+9,rfl,hseen,hseenEnd⟩ ?_
  intro flagRet memF posF hpostF
  obtain ⟨_,hseenF,hframeF⟩ := hpostF
  change BoolTableAt memF (base+9) (Function.update s.onPath v false) at hseenF
  change (∀ x,x≠base+9+v.val → memF x=mem x) at hframeF
  have hnodeFrame : ∀ x,cycleNodes J.n base≤x → x<heap → memF x=mem x := by
    intro x hx _
    exact hframeF x (by dsimp only [cycleNodes] at hx; have hi := v.isLt; omega)
  have hcandidatesF := hcandidates.of_agree hnodeFrame
  have hedgesF := hedges.of_agree hnodeFrame
  have hresultF := hresult.of_agree le_rfl hnodeFrame
  have houtF := hout.of_agree le_rfl (fun x hx _ => hframeF x
    (by dsimp only [cycleHeads] at hx; have hi := v.isLt; omega)) hnodeFrame
  have hzF : ZeroFrom memF heap := by
    intro x hx
    rw [hframeF x (by omega)]
    exact hz x hx
  have h2F : memF (base+2)=candidates := (hframeF _ (by omega)).trans h2
  have h4F : memF (base+4)=edges := (hframeF _ (by omega)).trans h4
  have h5F : memF (base+5)=(if s.cycleCost<0 then 1 else 0) := (hframeF _ (by omega)).trans h5
  have h6F : memF (base+6)=s.cycleCost.natAbs := (hframeF _ (by omega)).trans h6
  have h7F : memF (base+7)=flag := (hframeF _ (by omega)).trans h7
  have h8F : memF (base+8)=result := (hframeF _ (by omega)).trans h8
  unfold cycleWalkWrite
  refine runs_seq_call_le hkH
    (vs := [0,0,candidates,0,edges,if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result,base])
    (by simp only [List.cons_append,List.nil_append]; eval_expr) (by wram_words)
    ⟨0,0,candidates,0,edges,_,_,flag,result,base,rfl,hb9⟩ ?_
  intro headerEnd memH posH hpostH
  obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next hcandidatesF (.nil) hedgesF
    hresultF hseenF houtF hnodes hzF hpostH
  refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
  · change heap≤heap ∧ heap≤heap+4 ∧ CycleStateAt memH base heap s.step ∧ ZeroFrom memH heap ∧
      (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → memH x=mem x) ∧
      ∀ i<9,memH (base+i)<2^w
    refine ⟨le_rfl,by omega,?_,hzH,?_,hwordsH⟩
    · rw [hmodel]; exact hstateH
    · intro x _ hx
      have hframeHeader : memH x=memF x := by
        rcases hx with hx | hx
        · exact hframeH x (Or.inl hx)
        · exact hframeH x (Or.inr (by dsimp only [cycleNodes] at hx; omega))
      apply hframeHeader.trans
      apply hframeF
      rcases hx with hx | hx
      · omega
      · dsimp only [cycleNodes] at hx
        have hi := v.isLt
        omega
  · simp only [cycleWalkContract,cycleStepContract,cycleHeaderContract,boolTableSetContract,
      List.cons_append,List.nil_append,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    decide

end MinCostFlow.Scaling.Machine
