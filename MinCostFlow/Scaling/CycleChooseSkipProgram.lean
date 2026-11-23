module

public import MinCostFlow.Scaling.CycleChooseCode
import MinCostFlow.Scaling.CycleHeaderState
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Skipping an exhausted candidate tail in the cycle scan

Pop the first candidate edge and inspect its tail's outgoing list. When
that list is empty, retain choose mode, clear the walk stack, and continue
with the remaining candidates. The model's cycle data and flags remain
unchanged, and the machine allocates no cells.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The exhausted-tail branch computes exactly the model's choose step
and preserves all immutable nodes and vertex tables. -/
theorem cycleChoose_skip_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleChooseModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (e : Fin J.m) (rest : List (Fin J.m)) (hcan : s.candidates=e::rest)
    (houtnil : s.outgoing (J.tail e)=[]) : MeetsContract w p b (cycleChooseContract w J s B C) := by
  have hkH := cycleHeader_meetsContract (w := w) (hasAt_append_left (hasAt_tail hp))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,hbudget,
    hpotential,hz,hs,hw⟩,hmode⟩ := hpre
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
  rw [hcan] at hcandidates
  obtain ⟨hcPositive,_,hcEnd,heCell,tail,htailCell,htail⟩ := indexListAt_cons_iff.mp hcandidates
  let heads := cycleHeads J.n base
  let record := a+2+5*e.val
  let v := J.tail e
  let headAddr := heads+2*v.val
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hN := (solver_header_at J hgraph).1
  have hrecord := solver_edge_at J hgraph e
  have htailVertex : mem record=v.val := hrecord 0 (by change 0<5; decide)
  obtain ⟨outPtr,houtHeader,houtList⟩ := hout v
  have houtPtr : outPtr=0 := houtList.pointer_zero_iff.mpr houtnil
  have houtCell : mem headAddr=0 := by
    have h := houtHeader 0 (by change 0<2; decide)
    change mem (headAddr+0)=outPtr at h
    simpa only [Nat.add_zero,houtPtr] using h
  have hh : heap<2^w := by omega
  have hb : base<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hb4 : base+4<2^w := by omega
  have hb5 : base+5<2^w := by omega
  have hb6 : base+6<2^w := by omega
  have hb7 : base+7<2^w := by omega
  have hb8 : base+8<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have hcWord : candidates<2^w := by omega
  have hc1Word : candidates+1<2^w := by omega
  have htWord : tail<2^w := htail.pointer_le.trans_lt hh
  have hn : J.n<2^w := by omega
  have heWord : e.val<2^w := by rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have h5e : 5*e.val<2^w := by rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have ha2 : a+2<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha : a<2^w := by omega
  have hrWord : record<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hv : v.val<2^w := by have hi := v.isLt; omega
  have h2v : 2*v.val<2^w := by have hi := v.isLt; omega
  have hheads : heads<2^w := by dsimp only [heads,cycleHeads]; omega
  have haddr : headAddr<2^w := by dsimp only [headAddr,heads,cycleHeads]; have hi := v.isLt; omega
  have hedgesWord : edges<2^w := hedges.pointer_le.trans_lt hh
  have hsignWord : (if s.cycleCost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hmagWord : s.cycleCost.natAbs<2^w := by omega
  have h2 : mem (base+2)=candidates := hheader 2 (by change 2<9; decide)
  have h4 : mem (base+4)=edges := hheader 4 (by change 4<9; decide)
  have h5 : mem (base+5)=(if s.cycleCost<0 then 1 else 0) := hheader 5 (by change 5<9; decide)
  have h6 : mem (base+6)=s.cycleCost.natAbs := hheader 6 (by change 6<9; decide)
  have h7 : mem (base+7)=flag := hheader 7 (by change 7<9; decide)
  have h8 : mem (base+8)=result := hheader 8 (by change 8<9; decide)
  have hflagWord : flag<2^w := by rw [←h7]; exact hheaderWords 7 (by decide)
  have hresultWord : result<2^w := by rw [←h8]; exact hheaderWords 8 (by decide)
  let next : Circulation.CycleState J := {s with candidates:=rest,stack:=[]}
  have hmodel : s.step=next := by simp only [Circulation.CycleState.step,hmode,hcan,houtnil,next,↓reduceIte]
  apply runs_start_le
  unfold cycleChooseBody
  refine runs_seq_assign_le (v := candidates) (by eval_expr) ?_
  wram_step
  refine runs_seq_assign_le (v := e.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := tail) (by eval_expr) ?_
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := record) (by dsimp only [record]; eval_expr) ?_
  refine runs_seq_assign_le (v := v.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heads) (by dsimp only [heads,cycleHeads]; eval_expr) ?_
  refine runs_seq_assign_le (v := headAddr) (by dsimp only [headAddr]; eval_expr) ?_
  wram_step
  · unfold cycleChooseWrite
    refine runs_seq_call_le hkH
      (vs := [0,0,tail,0,edges,if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result,base])
      (by simp only [List.cons_append,List.nil_append]; eval_expr) (by wram_words)
      ⟨0,0,tail,0,edges,_,_,flag,result,base,rfl,hb9⟩ ?_
    intro headerEnd memH posH hpostH
    have hheaderPost : (cycleHeaderContract w).post
        [cycleModeTag next.mode,cycleModeVertex next.mode,tail,0,edges,
          if next.cycleCost<0 then 1 else 0,next.cycleCost.natAbs,flag,result,base] mem headerEnd memH := by
      simpa only [next,hmode,cycleModeTag,cycleModeVertex,startState] using hpostH
    obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next htail (.nil) hedges
      hresult hseen hout hnodes hz hheaderPost
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
    · simp only [cycleChooseContract,cycleStepContract,cycleHeaderContract,List.cons_append,List.nil_append,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      decide
  · apply False.elim
    apply hcond
    simpa only [startState] using houtCell

end MinCostFlow.Scaling.Machine
