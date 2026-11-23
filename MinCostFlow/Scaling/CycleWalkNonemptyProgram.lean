module

public import MinCostFlow.Scaling.CycleWalkCode
import MinCostFlow.Scaling.CycleHeaderState
import MinCostFlow.Scaling.CycleStateFrames
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Advancing a nonempty cycle walk

Remove the first unused outgoing edge and push it onto the immutable walk
stack. If its head is already on the path, start peeling there and clear
the cycle buffer. Otherwise mark that head and continue walking. The
machine follows these exact model branches and uses two fresh cells.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem walk_flag_true (b : Bool) (h : b.toNat=1) : b=true := by
  cases b <;> simp_all

private theorem walk_flag_false (b : Bool) (h : b.toNat≠1) : b=false := by
  cases b <;> simp_all

private theorem walk_repeat_args {w : ℕ} {st : State}
    {base heap vertex candidates flag result : ℕ}
    (hb : st.regs 1=base) (hh : st.regs 2=heap) (hv : st.regs 12=vertex)
    (hc : st.mem (base+2)=candidates) (hf : st.mem (base+7)=flag) (hr : st.mem (base+8)=result)
    (hbase : base+8<2^w) :
    evalArgs w st [.const 2,.reg 12,.load (.bin .add (.reg 1) (.const 2)),.reg 2,
      .const 0,.const 0,.const 0,.load (.bin .add (.reg 1) (.const 7)),
      .load (.bin .add (.reg 1) (.const 8)),.reg 1]=some [2,vertex,candidates,heap,0,0,0,flag,result,base] := by
  eval_expr

private theorem walk_new_args {w : ℕ} {st : State}
    {base heap vertex candidates edges sign magnitude flag result : ℕ}
    (hb : st.regs 1=base) (hh : st.regs 2=heap) (hv : st.regs 12=vertex)
    (hc : st.mem (base+2)=candidates) (he : st.mem (base+4)=edges)
    (hs : st.mem (base+5)=sign) (hm : st.mem (base+6)=magnitude)
    (hf : st.mem (base+7)=flag) (hr : st.mem (base+8)=result) (hbase : base+8<2^w) :
    evalArgs w st [.const 1,.reg 12,.load (.bin .add (.reg 1) (.const 2)),.reg 2,
      .load (.bin .add (.reg 1) (.const 4)),.load (.bin .add (.reg 1) (.const 5)),
      .load (.bin .add (.reg 1) (.const 6)),.load (.bin .add (.reg 1) (.const 7)),
      .load (.bin .add (.reg 1) (.const 8)),.reg 1]=some [1,vertex,candidates,heap,edges,sign,magnitude,flag,result,base] := by
  eval_expr

private theorem walk_header_words {w a b c d e f g h i j : ℕ}
    (ha : a<2^w) (hb : b<2^w) (hc : c<2^w) (hd : d<2^w) (he : e<2^w)
    (hf : f<2^w) (hg : g<2^w) (hh : h<2^w) (hi : i<2^w) (hj : j<2^w) :
    ∀ x ∈ [a,b,c,d,e,f,g,h,i,j],x<2^w := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ha,hb,hc,hd,he,hf,hg,hh,hi,hj]

set_option maxHeartbeats 600000 in
/-- A nonempty outgoing list is popped and its first edge is pushed onto
the walk stack. Both path-flag branches compute exactly the model step. -/
theorem cycleWalk_nonempty_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (cycleWalkModule b)) (J : Circulation) (s : Circulation.CycleState J)
    (B C : ℕ) (v : Fin J.n) (e : Fin J.m) (rest : List (Fin J.m))
    (houtlist : s.outgoing v=e::rest) : MeetsContract w p b (cycleWalkContract w J s B C v) := by
  have htail := hasAt_tail hp
  have hleft := hasAt_append_left htail
  have hkH := cycleHeader_meetsContract (w := w) (hasAt_append_left hleft)
  have hflags : p.HasAt (b+4) boolTableSetModule := by
    simpa only [cycleHeaderModule,List.length_cons,List.length_nil,Nat.add_assoc] using hasAt_append_right hleft
  have hpair : p.HasAt (b+5) wordPairModule := by
    simpa only [cycleHeaderModule,boolTableSetModule,List.length_append,List.length_cons,List.length_nil,Nat.add_assoc] using
      hasAt_append_right htail
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,base,heap,rfl,hgraph,hgraphEnd,hstate,hnodes,hheaderWords,hcost,hcosts,hbudget,
    hpotential,hz,hs,hw⟩,hmode⟩ := hpre
  obtain ⟨candidates,stack,edges,flag,result,hheader,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstate
  let heads := cycleHeads J.n base
  let nodes := cycleNodes J.n base
  let headAddr := heads+2*v.val
  let record := a+2+5*e.val
  let vertex := J.head e
  obtain ⟨outPtr,houtHeader,houtList⟩ := hout v
  rw [houtlist] at houtList
  obtain ⟨houtPositive,_,houtEnd,heCell,outTail,houtTailCell,houtTail⟩ := indexListAt_cons_iff.mp houtList
  have houtCell : mem headAddr=outPtr := by
    have h := houtHeader 0 (by change 0<2; decide)
    change mem (headAddr+0)=outPtr at h
    simpa only [Nat.add_zero] using h
  have houtLen : mem (headAddr+1)=rest.length+1 := by
    have h := houtHeader 1 (by change 1<2; decide)
    change mem (headAddr+1)=(s.outgoing v).length at h
    simpa only [houtlist,List.length_cons] using h
  have hrecordAt := solver_edge_at J hgraph e
  have hheadCell : mem (record+1)=vertex.val := hrecordAt 1 (by change 1<5; decide)
  have hflagCell : mem (base+9+vertex.val)=(s.onPath vertex).toNat := hseen vertex
  have hnodeNum : base+10+3*J.n≤heap := hnodes
  have hN := (solver_header_at J hgraph).1
  have hh : heap<2^w := by omega
  have hzero : 0<2^w := (by decide : 0<9).trans hw
  have hone : 1<2^w := (by decide : 1<9).trans hw
  have htwo : 2<2^w := (by decide : 2<9).trans hw
  have hh2 : heap+2<2^w := by omega
  have hpositive : 0<heap := by omega
  have hb : base<2^w := by omega
  have hb1 : base+1<2^w := by omega
  have hb2 : base+2<2^w := by omega
  have hb3 : base+3<2^w := by omega
  have hb4 : base+4<2^w := by omega
  have hb5 : base+5<2^w := by omega
  have hb6 : base+6<2^w := by omega
  have hb7 : base+7<2^w := by omega
  have hb8 : base+8<2^w := by omega
  have hb9 : base+9<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have ha2 : a+2<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hv : v.val<2^w := v.isLt.trans hn
  have h2v : 2*v.val<2^w := by have hi := v.isLt; omega
  have hheads : heads<2^w := by dsimp only [heads,cycleHeads]; omega
  have haddr : headAddr<2^w := by dsimp only [headAddr,heads,cycleHeads]; have hi := v.isLt; omega
  have haddr1 : headAddr+1<2^w := by dsimp only [headAddr,heads,cycleHeads]; have hi := v.isLt; omega
  have hheadsEnd : heads+2*J.n<2^w := by dsimp only [heads,cycleHeads]; omega
  have hheadsNodes : heads+2*J.n≤nodes := by dsimp only [heads,nodes,cycleHeads,cycleNodes]; omega
  have houtWord : outPtr<2^w := by omega
  have hout1Word : outPtr+1<2^w := by omega
  have houtTailWord : outTail<2^w := houtTail.pointer_le.trans_lt hh
  have hlength := s.outgoing_length_le_potential v
  rw [houtlist,List.length_cons] at hlength
  have hlenWord : rest.length+1<2^w := by omega
  have hrestWord : rest.length<2^w := by omega
  have heWord : e.val<2^w := e.isLt.trans hm
  have h5e : 5*e.val<2^w := by rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hrWord : record<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hr1Word : record+1<2^w := by dsimp only [record]; rw [J.solverWords_length] at hgraphEnd; have hi := e.isLt; omega
  have hvertexWord : vertex.val<2^w := vertex.isLt.trans hn
  have hflagAddr : base+9+vertex.val<heap := by have hi := vertex.isLt; omega
  have hflagAddrWord : base+9+vertex.val<2^w := by omega
  have hseenEnd : base+9+J.n<2^w := by omega
  have hflagValue : (s.onPath vertex).toNat<2^w := by cases s.onPath vertex <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
  have hstackWord : stack<2^w := hstack.pointer_le.trans_lt hh
  have hcandidatesWord : candidates<2^w := hcandidates.pointer_le.trans_lt hh
  have hedgesWord : edges<2^w := hedges.pointer_le.trans_lt hh
  have hsignWord : (if s.cycleCost<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
  have hmagWord : s.cycleCost.natAbs<2^w := by omega
  have h1 : mem (base+1)=v.val := by
    simpa only [hmode,cycleModeVertex,List.getElem_cons_succ,List.getElem_cons_zero] using hheader 1 (by change 1<9; decide)
  have h2 : mem (base+2)=candidates := hheader 2 (by change 2<9; decide)
  have h3 : mem (base+3)=stack := hheader 3 (by change 3<9; decide)
  have h4 : mem (base+4)=edges := hheader 4 (by change 4<9; decide)
  have h5 : mem (base+5)=(if s.cycleCost<0 then 1 else 0) := hheader 5 (by change 5<9; decide)
  have h6 : mem (base+6)=s.cycleCost.natAbs := hheader 6 (by change 6<9; decide)
  have h7 : mem (base+7)=flag := hheader 7 (by change 7<9; decide)
  have h8 : mem (base+8)=result := hheader 8 (by change 8<9; decide)
  have hflagWord : flag<2^w := by rw [←h7]; exact hheaderWords 7 (by decide)
  have hresultWord : result<2^w := by rw [←h8]; exact hheaderWords 8 (by decide)
  have hkP := adjacencySet_meetsContract (w := w) (heads := heads) (lo := nodes) (bound := heap)
    hpair s.outgoing v rest
  have hkC := indexListCons_meetsContract (w := w) (lo := nodes) hpair e s.stack
  have hkF := boolTableSet_meetsContract (w := w) hflags s.onPath vertex true
  apply runs_start_le
  unfold cycleWalkBody
  refine runs_seq_assign_le (v := J.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := v.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heads) (by dsimp only [heads,cycleHeads]; eval_expr) ?_
  refine runs_seq_assign_le (v := headAddr) (by dsimp only [headAddr]; eval_expr) ?_
  refine runs_seq_assign_le (v := outPtr) (by eval_expr) ?_
  wram_step
  refine runs_seq_assign_le (v := e.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := outTail) (by eval_expr) ?_
  refine runs_seq_assign_le (v := rest.length+1) (by eval_expr) ?_
  refine runs_seq_assign_le (v := record) (by dsimp only [record]; eval_expr) ?_
  refine runs_seq_assign_le (v := vertex.val) (by eval_expr) ?_
  refine runs_seq_assign_le (v := (s.onPath vertex).toNat) (by eval_expr) ?_
  refine runs_seq_call_le hkP (vs := [outTail,rest.length,headAddr]) (by
    conv_rhs => rw [←Nat.add_sub_cancel rest.length 1]
    eval_expr) (by wram_words) ⟨outTail,rfl,hout,houtTail,hheadsNodes,hheadsEnd⟩ ?_
  intro pairRet memP posP hpostP
  obtain ⟨_,houtP,hframeP⟩ := hpostP
  change AdjacencyAt memP heads nodes heap (Function.update s.outgoing v rest) at houtP
  change (∀ x,x<headAddr ∨ headAddr+2≤x → memP x=mem x) at hframeP
  have hnodeFrameP : ∀ x,nodes≤x → x<heap → memP x=mem x := by
    intro x hx _
    exact hframeP x (Or.inr (by dsimp only [nodes,headAddr,heads,cycleNodes,cycleHeads] at hx ⊢; have hi := v.isLt; omega))
  have hstackP := hstack.of_agree hnodeFrameP
  have hseenP := hseen.of_agree_below (heap := heads) (by dsimp only [heads,cycleHeads,cycleSeen]; omega)
    (fun x hx => hframeP x (Or.inl (by dsimp only [headAddr]; omega)))
  have hzP : ZeroFrom memP heap := by
    intro x hx
    rw [hframeP x (Or.inr (by dsimp only [headAddr,heads,cycleHeads]; have hi := v.isLt; omega))]
    exact hz x hx
  have h3P : memP (base+3)=stack := (hframeP _ (Or.inl (by dsimp only [headAddr,heads,cycleHeads]; omega))).trans h3
  refine runs_seq_call_le hkC (vs := [e.val,stack,heap]) (by eval_expr) (by wram_words)
    ⟨⟨stack,heap,rfl,hpositive,hnodes,hstackP⟩,hzP,hh2⟩ ?_
  intro newHeap memC posC hpostC
  obtain ⟨⟨_,_,hframeC,hzC,hnewStack⟩,hnewHeap⟩ := hpostC
  change newHeap=heap+2 at hnewHeap
  change (∀ x<heap,memC x=memP x) at hframeC
  change ZeroFrom memC newHeap at hzC
  change IndexListAt memC nodes (heap+2) heap (e::s.stack) at hnewStack
  have hnewWord : newHeap<2^w := by omega
  have hbound : heap≤newHeap := by omega
  have hnewNodes : cycleNodes J.n base≤newHeap := hnodes.trans hbound
  have hnodeFrame : ∀ x,nodes≤x → x<heap → memC x=mem x := by
    intro x hx hxend
    exact (hframeC x hxend).trans (hnodeFrameP x hx hxend)
  have hcandidatesC := (hcandidates.of_agree hnodeFrame).mono le_rfl hbound
  have hedgesC := (hedges.of_agree hnodeFrame).mono le_rfl hbound
  have hresultC := hresult.of_agree hbound hnodeFrame
  have hseenC := hseenP.of_agree_below (by dsimp only [cycleSeen]; omega) hframeC
  have houtC := houtP.of_agree_below (by dsimp only [heads,cycleHeads]; omega) hbound hframeC
  have hheaderFrame : ∀ i<9,memC (base+i)=mem (base+i) := by
    intro i hi
    exact (hframeC _ (by omega)).trans (hframeP _ (Or.inl
      (by dsimp only [headAddr,heads,cycleHeads]; omega)))
  have h2C : memC (base+2)=candidates := (hheaderFrame _ (by decide)).trans h2
  have h4C : memC (base+4)=edges := (hheaderFrame _ (by decide)).trans h4
  have h5C : memC (base+5)=(if s.cycleCost<0 then 1 else 0) := (hheaderFrame _ (by decide)).trans h5
  have h6C : memC (base+6)=s.cycleCost.natAbs := (hheaderFrame _ (by decide)).trans h6
  have h7C : memC (base+7)=flag := (hheaderFrame _ (by decide)).trans h7
  have h8C : memC (base+8)=result := (hheaderFrame _ (by decide)).trans h8
  have hsourceFrame : ∀ x<heap,x<base ∨ nodes≤x → memC x=mem x := by
    intro x hx hxout
    apply (hframeC x hx).trans
    apply hframeP
    rcases hxout with hxout | hxout
    · exact Or.inl (by dsimp only [headAddr,heads,cycleHeads]; omega)
    · exact Or.inr (by dsimp only [nodes,headAddr,heads,cycleNodes,cycleHeads] at hxout ⊢; have hi := v.isLt; omega)
  wram_step
  · have hseenTrue : s.onPath (J.head e)=true := walk_flag_true _ hcond
    let next : Circulation.CycleState J := {s with mode:=.peel vertex,outgoing:=Function.update s.outgoing v rest,stack:=e::s.stack,cycleEdges:=[],cycleCost:=0}
    have hmodel : s.step=next := by
      simp only [Circulation.CycleState.step,hmode,houtlist,hseenTrue,↓reduceIte,next,vertex]
    unfold cycleWalkWrite
    refine runs_seq_call_le hkH (vs := [2,vertex.val,candidates,heap,0,0,0,flag,result,base])
      (by simp only [List.cons_append,List.nil_append]
          exact walk_repeat_args (by rfl) (by rfl) (by rfl) h2C h7C h8C hb8)
      (walk_header_words htwo hvertexWord hcandidatesWord hh hzero hzero hzero hflagWord hresultWord hb)
      ⟨2,vertex.val,candidates,heap,0,0,0,flag,result,base,rfl,hb9⟩ ?_
    intro headerEnd memH posH hpostH
    have hnewStack' : IndexListAt memC nodes newHeap heap (e::s.stack) := by simpa only [hnewHeap] using hnewStack
    obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next (mem := memC) (mem' := memH)
      (base := base) (heap := newHeap) (candidates := candidates) (stack := heap)
      (edges := 0) (flag := flag) (result := result) hcandidatesC hnewStack' (.nil)
      hresultC hseenC houtC hnewNodes hzC hpostH
    refine runs_ret_le (v := newHeap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤newHeap ∧ newHeap≤heap+4 ∧ CycleStateAt memH base newHeap s.step ∧ ZeroFrom memH newHeap ∧
        (∀ x<heap,x<base ∨ nodes≤x → memH x=mem x) ∧ ∀ i<9,memH (base+i)<2^w
      refine ⟨by omega,by omega,?_,hzH,?_,hwordsH⟩
      · rw [hmodel]; exact hstateH
      · intro x hx hxout
        apply (hframeH x ?_).trans (hsourceFrame x hx hxout)
        rcases hxout with hxout | hxout
        · exact Or.inl hxout
        · exact Or.inr (by dsimp only [nodes,cycleNodes] at hxout; omega)
    · simp only [cycleWalkContract,cycleStepContract,cycleHeaderContract,adjacencySetContract,indexListConsContract,
        heapContract,List.cons_append,List.nil_append,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      decide
  · have hseenFalse : s.onPath (J.head e)=false := walk_flag_false _ hcond
    refine runs_seq_call_le hkF (vs := [base+9,vertex.val,1]) (by eval_expr) (by wram_words)
      ⟨base+9,rfl,hseenC,hseenEnd⟩ ?_
    intro flagRet memF posF hpostF
    obtain ⟨_,hseenF,hframeF⟩ := hpostF
    change BoolTableAt memF (base+9) (Function.update s.onPath vertex true) at hseenF
    change (∀ x,x≠base+9+vertex.val → memF x=memC x) at hframeF
    have hnodeFrameF : ∀ x,nodes≤x → x<newHeap → memF x=memC x := by
      intro x hx _
      exact hframeF x (by dsimp only [nodes,cycleNodes] at hx; have hi := vertex.isLt; omega)
    have hcandidatesF := hcandidatesC.of_agree hnodeFrameF
    have hedgesF := hedgesC.of_agree hnodeFrameF
    have hresultF := hresultC.of_agree le_rfl hnodeFrameF
    have hnewStack' : IndexListAt memF nodes newHeap heap (e::s.stack) := by
      have hstack' : IndexListAt memC nodes newHeap heap (e::s.stack) := by simpa only [hnewHeap] using hnewStack
      exact hstack'.of_agree hnodeFrameF
    have houtF := houtC.of_agree le_rfl (fun x hx _ => hframeF x
      (by dsimp only [heads,cycleHeads] at hx; have hi := vertex.isLt; omega)) hnodeFrameF
    have hzF : ZeroFrom memF newHeap := by
      intro x hx
      rw [hframeF x (by omega)]
      exact hzC x hx
    have h2F : memF (base+2)=candidates := (hframeF _ (by omega)).trans h2C
    have h4F : memF (base+4)=edges := (hframeF _ (by omega)).trans h4C
    have h5F : memF (base+5)=(if s.cycleCost<0 then 1 else 0) := (hframeF _ (by omega)).trans h5C
    have h6F : memF (base+6)=s.cycleCost.natAbs := (hframeF _ (by omega)).trans h6C
    have h7F : memF (base+7)=flag := (hframeF _ (by omega)).trans h7C
    have h8F : memF (base+8)=result := (hframeF _ (by omega)).trans h8C
    let next : Circulation.CycleState J := {s with mode:=.walk vertex,outgoing:=Function.update s.outgoing v rest,stack:=e::s.stack,onPath:=Function.update s.onPath vertex true}
    have hmodel : s.step=next := by
      simp only [Circulation.CycleState.step,hmode,houtlist,hseenFalse,Bool.false_eq_true,↓reduceIte,next,vertex]
    unfold cycleWalkWrite
    refine runs_seq_call_le hkH
      (vs := [1,vertex.val,candidates,heap,edges,if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result,base])
      (by simp only [List.cons_append,List.nil_append]
          exact walk_new_args (by rfl) (by rfl) (by rfl) h2F h4F h5F h6F h7F h8F hb8)
      (walk_header_words hone hvertexWord hcandidatesWord hh hedgesWord hsignWord hmagWord hflagWord hresultWord hb)
      ⟨1,vertex.val,candidates,heap,edges,_,_,flag,result,base,rfl,hb9⟩ ?_
    intro headerEnd memH posH hpostH
    obtain ⟨hstateH,hzH,hframeH,hwordsH⟩ := cycleHeader_post_state w next (mem := memF) (mem' := memH)
      (base := base) (heap := newHeap) (candidates := candidates) (stack := heap)
      (edges := edges) (flag := flag) (result := result) hcandidatesF hnewStack' hedgesF
      hresultF hseenF houtF hnewNodes hzF hpostH
    refine runs_ret_le (v := newHeap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤newHeap ∧ newHeap≤heap+4 ∧ CycleStateAt memH base newHeap s.step ∧ ZeroFrom memH newHeap ∧
        (∀ x<heap,x<base ∨ nodes≤x → memH x=mem x) ∧ ∀ i<9,memH (base+i)<2^w
      refine ⟨by omega,by omega,?_,hzH,?_,hwordsH⟩
      · rw [hmodel]; exact hstateH
      · intro x hx hxout
        apply (hframeH x ?_).trans
        · apply (hframeF x ?_).trans (hsourceFrame x hx hxout)
          rcases hxout with hxout | hxout
          · omega
          · dsimp only [nodes,cycleNodes] at hxout
            have hi := vertex.isLt
            omega
        · rcases hxout with hxout | hxout
          · exact Or.inl hxout
          · exact Or.inr (by dsimp only [nodes,cycleNodes] at hxout; omega)
    · simp only [cycleWalkContract,cycleStepContract,cycleHeaderContract,boolTableSetContract,adjacencySetContract,indexListConsContract,
        heapContract,List.cons_append,List.nil_append,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      decide

end MinCostFlow.Scaling.Machine
