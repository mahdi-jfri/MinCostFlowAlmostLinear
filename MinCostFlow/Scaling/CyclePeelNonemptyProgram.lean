module

public import MinCostFlow.Scaling.CyclePeelCode
import MinCostFlow.Scaling.CyclePeelFinishProgram
import MinCostFlow.Scaling.CyclePeelPrepareLayout
import MinCostFlow.Scaling.CyclePeelFlags
import MinCostFlow.Scaling.CycleStateFrames
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Preparing and finishing a nonempty peel step

Pop the stack, add the edge cost, and prepend the edge to the cycle list.
Clear its head's path flag unless it is the target. The finishing code
then writes exactly the model's resulting traversal state.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option maxHeartbeats 600000 in
/-- Nonempty peeling uses four fresh cells and computes the exact model
step, including the target-dependent path flag store. -/
theorem cyclePeel_nonempty_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cyclePeelModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (target : Fin J.n) (e : Fin J.m) (rest : List (Fin J.m))
    (hstackEq : s.stack=e::rest) : MeetsContract w p b (cyclePeelContract w J s B C target) := by
  have ht := hasAt_tail hp
  have hl := hasAt_append_left ht
  have hll := hasAt_append_left hl
  have hlll := hasAt_append_left hll
  have hAdd : p.HasAt (b+4) (signedAddModule (b+4)) := by
    simpa only [cycleHeaderModule,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hlll
  have hPair : p.HasAt (b+6) wordPairModule := by
    simpa only [cycleHeaderModule,signedAddModule,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hll
  have hFlag : p.HasAt (b+7) boolTableSetModule := by
    simpa only [cycleHeaderModule,signedAddModule,wordPairModule,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hl
  have hFinish : p.HasAt (b+8) (cyclePeelFinishModule (b+8)) := by
    simpa only [cycleHeaderModule,signedAddModule,wordPairModule,boolTableSetModule,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right ht
  have hkA := signedAdd_meetsContract (w := w) hAdd s.cycleCost (J.cost e)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,hbudget,
    hpotential,hz,hs,hw⟩,hmode⟩ := hpre
  have hstateOld := hstate
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
  rw [hstackEq] at hstack
  obtain ⟨hstackPositive,_,hstackEnd,heCell,tail,htailCell,htail⟩ := indexListAt_cons_iff.mp hstack
  let record := a+2+5*e.val
  have hr := solver_edge_at J hgraph e
  have htailV : mem record=(J.tail e).val := by simpa only [Circulation.solverEdgeWords,Nat.add_zero,List.getElem_cons_zero] using hr 0 (by change 0<5; decide)
  have hheadV : mem (record+1)=(J.head e).val := hr 1 (by change 1<5; decide)
  have hsignE : mem (record+3)=(if J.cost e<0 then 1 else 0) := hr 3 (by change 3<5; decide)
  have hmagE : mem (record+4)=(J.cost e).natAbs := hr 4 (by change 4<5; decide)
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hh : heap<2^w := by omega
  have hh2 : heap+2<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hb : base<2^w := by omega
  have hb1 : base+1<2^w := by omega
  have hb3 : base+3<2^w := by omega
  have hb4 : base+4<2^w := by omega
  have hb5 : base+5<2^w := by omega
  have hb6 : base+6<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have htarget : target.val<2^w := target.isLt.trans hn
  have he : e.val<2^w := e.isLt.trans hm
  have htailVWord : (J.tail e).val<2^w := (J.tail e).isLt.trans hn
  have hheadVWord : (J.head e).val<2^w := (J.head e).isLt.trans hn
  have hstackWord : stack<2^w := by omega
  have hstack1 : stack+1<2^w := by omega
  have htailWord : tail<2^w := htail.pointer_le.trans_lt hh
  have hedgesWord : edges<2^w := hedges.pointer_le.trans_lt hh
  have ha2 : a+2<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have h5e : 5*e.val<2^w := by rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hrecord : record<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hrecord1 : record+1<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hrecord3 : record+3<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hrecord4 : record+4<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hE := hcosts e
  have hmagnitudes : s.cycleCost.natAbs+(J.cost e).natAbs<2^w := by omega
  have hmagS : s.cycleCost.natAbs<2^w := by omega
  have hmagEWord : (J.cost e).natAbs<2^w := by omega
  have hsignS : (if s.cycleCost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hsignEWord : (if J.cost e<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have h1 : mem (base+1)=target.val := by
    simpa only [hmode,cycleModeVertex,List.getElem_cons_succ,List.getElem_cons_zero] using hheader 1 (by change 1<9; decide)
  have h3 : mem (base+3)=stack := hheader 3 (by change 3<9; decide)
  have h4 : mem (base+4)=edges := hheader 4 (by change 4<9; decide)
  have h5 : mem (base+5)=(if s.cycleCost<0 then 1 else 0) := hheader 5 (by change 5<9; decide)
  have h6 : mem (base+6)=s.cycleCost.natAbs := hheader 6 (by change 6<9; decide)
  have hkP := indexListCons_meetsContract (w := w) (lo := cycleNodes J.n base) hPair e s.cycleEdges
  apply runs_start_le
  unfold cyclePeelBody
  refine runs_seq_assign_le (v := stack) (by eval_expr) ?_
  refine runs_seq_assign_le (v := target.val) (by eval_expr) ?_
  wram_step
  refine runs_seq_assign_le (v := e.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := tail) (by eval_expr) ?_
  refine runs_seq_assign_le (v := record) (by dsimp only [record]; eval_expr) ?_
  refine runs_seq_assign_le (v := (J.tail e).val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (J.head e).val) (by eval_expr) ?_
  refine runs_seq_call_le hkA (vs := [if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,
      if J.cost e<0 then 1 else 0,(J.cost e).natAbs,heap])
    (by eval_expr) (by wram_words) ⟨⟨heap,rfl,hmagnitudes⟩,hz,hh2⟩ ?_
  intro addEnd memA posA hpostA
  have hpostAcopy := hpostA
  obtain ⟨⟨_,_,hframeA,hzA,hsumA⟩,haddEnd⟩ := hpostA
  change addEnd=heap+2 at haddEnd
  change ∀ x<heap,memA x=mem x at hframeA
  change ZeroFrom memA addEnd at hzA
  have h4A : memA (base+4)=edges := (hframeA _ (by omega)).trans h4
  have hedgesA := (hedges.of_agree (fun x _ hx => hframeA x hx)).mono le_rfl (by omega : heap≤addEnd)
  have haddWord : addEnd<2^w := by omega
  refine runs_seq_call_le hkP (vs := [e.val,edges,addEnd]) (by eval_expr) (by wram_words)
    ⟨⟨edges,addEnd,rfl,by omega,by omega,hedgesA⟩,hzA,by change addEnd+2<2^w; omega⟩ ?_
  intro newHeap memC posC hpostC
  obtain ⟨hnewHeap,hstateC,htailC,hcycleC,hsumC,hzC,hframeC⟩ :=
    cyclePeel_prepared_layout hstateOld htail hnodes hpostAcopy hpostC
  have hnewWord : newHeap<2^w := by omega
  have hsum0 : memC heap=(if s.cycleCost+J.cost e<0 then 1 else 0) := by
    simpa only [encodeInt,Nat.add_zero,List.getElem_cons_zero] using hsumC 0 (by change 0<2; decide)
  have hsum1 : memC (heap+1)=(s.cycleCost+J.cost e).natAbs := hsumC 1 (by change 1<2; decide)
  have hsumWord : (s.cycleCost+J.cost e).natAbs<2^w :=
    (Int.natAbs_add_le _ _).trans_lt hmagnitudes
  have hsumSign : (if s.cycleCost+J.cost e<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hh1 : heap+1<2^w := by omega
  have hnewNodes : cycleNodes J.n base≤newHeap := by omega
  have hstateC' : CycleStateAt memC base newHeap s := by simpa only [hnewHeap] using hstateC
  have htailC' : IndexListAt memC (cycleNodes J.n base) newHeap tail rest := by simpa only [hnewHeap] using htailC
  have hcycleC' : IndexListAt memC (cycleNodes J.n base) newHeap addEnd (e::s.cycleEdges) := by simpa only [hnewHeap,haddEnd] using hcycleC
  have hzC' : ZeroFrom memC newHeap := by simpa only [hnewHeap] using hzC
  have hheaderC : ∀ i<9,memC (base+i)<2^w := fun i hi => by rw [hframeC _ (by omega)]; exact hheaderWords i hi
  refine runs_seq_assign_le (v := if s.cycleCost+J.cost e<0 then 1 else 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (s.cycleCost+J.cost e).natAbs) (by eval_expr) ?_
  wram_step
  · have hheadTarget : J.head e=target := Fin.ext hcond
    have hkFinish := cyclePeelFinish_meetsContract (w := w) hFinish J s target e rest
    unfold cyclePeelContinue
    refine runs_seq_call_le hkFinish
      (vs := [base,target.val,(J.tail e).val,tail,addEnd,if s.cycleCost+J.cost e<0 then 1 else 0,
        (s.cycleCost+J.cost e).natAbs,newHeap]) (by eval_expr) (by wram_words)
      ⟨base,tail,addEnd,newHeap,rfl,hstateC',htailC',hcycleC',hmode,hstackEq,Or.inl hheadTarget,
        hnewNodes,hheaderC,hzC',hnewWord,hw⟩ ?_
    intro ret memF posF hpostF
    obtain ⟨hret,hstateF,hzF,hframeF,hheaderF⟩ := hpostF
    change ret=newHeap at hret
    change (∀ x,x<base ∨ base+9≤x → memF x=_) at hframeF
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+4 ∧ CycleStateAt memF base ret s.step ∧ ZeroFrom memF ret ∧
        (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → memF x=mem x) ∧ ∀ i<9,memF (base+i)<2^w
      refine ⟨by omega,by omega,hstateF,hzF,?_,hheaderF⟩
      intro x hx houtside
      apply (hframeF x ?_).trans (hframeC x hx)
      rcases houtside with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by dsimp only [cycleNodes] at hx; omega)
    · simp only [cyclePeelContract,cycleStepContract,cyclePeelFinishContract,signedAddContract,
        indexListConsContract,heapContract,argsSize_cons,argsSize_nil,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      decide
  · have hheadTarget : J.head e≠target := fun heq => hcond (congrArg Fin.val heq)
    have hkFlag := boolTableSet_meetsContract (w := w) hFlag s.onPath (J.head e) false
    have hseenC := hseen.of_agree_below (heap := heap) (by change base+9+J.n≤heap; omega) hframeC
    have hseenEnd : base+9+J.n<2^w := by omega
    refine runs_seq_call_le hkFlag (vs := [base+9,(J.head e).val,0]) (by eval_expr) (by wram_words)
      ⟨base+9,rfl,hseenC,hseenEnd⟩ ?_
    intro flagRet memG posG hpostG
    obtain ⟨_,hseenG,hframeG⟩ := hpostG
    change BoolTableAt memG (base+9) (Function.update s.onPath (J.head e) false) at hseenG
    change (∀ x,x≠base+9+(J.head e).val → memG x=memC x) at hframeG
    have hheadLt := (J.head e).isLt
    have hnodesG : ∀ x,cycleNodes J.n base≤x → x<newHeap → memG x=memC x := by
      intro x hx _
      exact hframeG x (by dsimp only [cycleNodes] at hx; omega)
    have houtC := hout.of_agree_below (by change base+9+J.n+2*J.n≤heap; omega)
      (by omega : heap≤newHeap) hframeC
    have houtG : AdjacencyAt memG (cycleHeads J.n base) (cycleNodes J.n base) newHeap s.outgoing := by
      intro u
      obtain ⟨ptr,hstored,hlist⟩ := houtC u
      refine ⟨ptr,?_,hlist.of_agree hnodesG⟩
      intro i hi
      have hi' : i<2 := hi
      rw [hframeG _ (by dsimp only [cycleHeads]; omega)]
      exact hstored i hi
    let cleared : Circulation.CycleState J := {s with onPath:=Function.update s.onPath (J.head e) false}
    have hstateG : CycleStateAt memG base newHeap cleared :=
      hstateC'.with_tables _ _ le_rfl hseenG houtG
        (fun x hx hxend => hframeG x (by omega)) hnodesG
    have htailG := htailC'.of_agree hnodesG
    have hcycleG := hcycleC'.of_agree hnodesG
    have hzG : ZeroFrom memG newHeap := by
      intro x hx
      rw [hframeG x (by have hg : base+10+3*J.n≤newHeap := hnewNodes; omega)]
      exact hzC' x hx
    have hheaderG : ∀ i<9,memG (base+i)<2^w := by
      intro i hi
      rw [hframeG _ (by omega)]
      exact hheaderC i hi
    have hkFinish := cyclePeelFinish_meetsContract (w := w) hFinish J cleared target e rest
    unfold cyclePeelContinue
    refine runs_seq_call_le hkFinish
      (vs := [base,target.val,(J.tail e).val,tail,addEnd,if s.cycleCost+J.cost e<0 then 1 else 0,
        (s.cycleCost+J.cost e).natAbs,newHeap]) (by eval_expr) (by wram_words)
      ⟨base,tail,addEnd,newHeap,rfl,hstateG,htailG,hcycleG,hmode,hstackEq,
        Or.inr (Function.update_self _ _ _),hnewNodes,hheaderG,hzG,hnewWord,hw⟩ ?_
    intro ret memF posF hpostF
    obtain ⟨hret,hstateF,hzF,hframeF,hheaderF⟩ := hpostF
    change ret=newHeap at hret
    change (∀ x,x<base ∨ base+9≤x → memF x=_) at hframeF
    have hmodel : cleared.step=s.step := s.peel_step_after_clear target e rest hmode hstackEq hheadTarget
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+4 ∧ CycleStateAt memF base ret s.step ∧ ZeroFrom memF ret ∧
        (∀ x<heap,x<base ∨ cycleNodes J.n base≤x → memF x=mem x) ∧ ∀ i<9,memF (base+i)<2^w
      refine ⟨by omega,by omega,?_,hzF,?_,hheaderF⟩
      · rw [hmodel] at hstateF; exact hstateF
      · intro x hx houtside
        have hheaderOutside : x<base ∨ base+9≤x := by
          rcases houtside with hx | hx
          · exact Or.inl hx
          · exact Or.inr (by dsimp only [cycleNodes] at hx; omega)
        have hflagOutside : x≠base+9+(J.head e).val := by
          rcases houtside with hx | hx
          · omega
          · dsimp only [cycleNodes] at hx; omega
        exact (hframeF x hheaderOutside).trans ((hframeG x hflagOutside).trans (hframeC x hx))
    · simp only [cyclePeelContract,cycleStepContract,cyclePeelFinishContract,signedAddContract,
        indexListConsContract,heapContract,boolTableSetContract,argsSize_cons,argsSize_nil,
        Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      decide

end MinCostFlow.Scaling.Machine
