module

public import MinCostFlow.Scaling.CapacityScalingContract
import MinCostFlow.Scaling.CapacityScalingSpace
import MinCostFlow.Scaling.CapacityLoopProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import Mathlib.Tactic.Ring
import WordRAM.Tactic

/-!
# Executing complete capacity scaling

The empty graph returns its empty flow. Otherwise compression constructs
exactly the model graph, the full capacity loop produces exactly its
model state, and copying returns that state's coordinates. The heap
frames compose, and the model's setup work pays for compression and copying.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem scaling_edge_count_eval {w a m : ℕ} {st : State} (h0 : st.regs 0=a)
    (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem scaling_compression_args {w a heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h2 : st.regs 2=heap) :
    evalArgs w st [.reg 0,.reg 2]=some [a,heap] := by eval_expr

private theorem scaling_loop_args {w graph U heap : ℕ} {st : State}
    (h2 : st.regs 2=graph) (h1 : st.regs 1=U) (h4 : st.regs 4=heap) :
    evalArgs w st [.reg 2,.reg 1,.reg 4]=some [graph,U,heap] := by eval_expr

private theorem scaling_state_eval {w heap : ℕ} {st : State} (h5 : st.regs 5=heap)
    (hh : heap<2^w) (h2 : 2<2^w) : Expr.eval w st (.bin .sub (.reg 5) (.const 2))=some (heap-2) := by eval_expr

private theorem scaling_copy_args {w state m heap : ℕ} {st : State}
    (h6 : st.regs 6=state) (h3 : st.regs 3=m) (h5 : st.regs 5=heap) :
    evalArgs w st [.reg 6,.reg 3,.reg 5]=some [state,m,heap] := by eval_expr

private theorem scaling_cost_padding (m n calls Q W reg : ℕ) :
    12+((500*m+500)+2+(1+(1+(1+0)))+
      (calls*Q+101000*(reg+1)*W)+2+(1+1+1)+2+(1+(1+(1+0)))+
      (17*m+60)+2+(1+1))≤calls*Q+102000*(reg+1)*(n+20*m+1+W) := by
  have hr : n+20*m+1+W≤(reg+1)*(n+20*m+1+W) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (n+20*m+1+W) (show 1≤reg+1 by omega)
  have hRW : (reg+1)*W≤(reg+1)*(n+20*m+1+W) := Nat.mul_le_mul_left _ (by omega)
  ring_nf at hr hRW ⊢
  omega

/-- The complete capacity-scaling program returns the exact counted model
flow, with the shared fresh-heap frame and its actual solver-call cost. -/
theorem capacityScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityScalingModule solver entry b))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityScalingContract w solver entry T hproc J C U) := by
  let solve := canonicalSolver solver entry T hproc
  let N := (capacityStepNumberBase J C U)^256
  let Nc := (capacityStepNumberBase J.compress C U)^256
  let fuel := capacityRounds J.m U
  let r := capacityLoop solve J.compress U
  have ht := hasAt_tail hp
  have hcl := hasAt_append_left ht
  have hComp : p.HasAt (b+1) (compressionModule (b+1)) := hasAt_append_left hcl
  have hLoop : p.HasAt (b+7) (capacityLoopModule solver entry (b+7)) := by
    simpa only [compressionModule,endpointLabelsModule,vertexScanModule,List.length_append,
      List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd] using hasAt_append_right hcl
  have hCopy : p.HasAt (b+7+(capacityLoopModule solver entry (b+7)).length)
      (capacityFlowCopyModule (b+7+(capacityLoopModule solver entry (b+7)).length)) := by
    have hraw := hasAt_append_right ht
    have he : b+1+(compressionModule (b+1) ++ capacityLoopModule solver entry (b+7)).length=
        b+7+(capacityLoopModule solver entry (b+7)).length := by
      rw [List.length_append]
      change b+1+(6+(capacityLoopModule solver entry (b+7)).length)=_
      omega
    rw [he] at hraw
    exact hraw
  have hkL := capacityLoop_meetsContract (w := w) hproc hdet hLoop J.compress C U J.endpointLabels_count_le hc
  have hkF := capacityFlowCopy_meetsContract (w := w) hCopy J.compress r.value
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hz,hspace⟩ := hpre
  have hspaceNum : heap+(J.solverWords.length+J.n+2+J.m+2+(fuel+1)*N+J.m)<2^w := hspace
  obtain ⟨h8,hinputWords⟩ := capacityScaling_words_of_space J C U heap hC hu hspace
  have hkC := compression_meetsContract (w := w) h8 hComp J
  have hh : heap<2^w := by omega
  have hU : U<2^w := hwords U (by simp)
  have hmWord : J.m<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hM := (solver_header_at J hgraph).2
  have hmComp : J.compress.m=J.m := rfl
  have hlenComp : J.compress.solverWords.length=J.solverWords.length := by rw [J.compress.solverWords_length,J.solverWords_length]
  have hNc : Nc≤N := capacityScaling_compressed_power_le J C U
  have hreserve : (fuel+1)*Nc≤(fuel+1)*N := Nat.mul_le_mul_left _ hNc
  apply runs_start_le
  unfold capacityScalingBody
  refine runs_seq_assign_le (v := J.m) (scaling_edge_count_eval (by rfl) ha1 hM) ?_
  wram_step
  · have hm : J.m=0 := by omega
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+capacityScalingSpace J C U ∧
        ListAt mem (heap-J.m) (List.ofFn (fun e => ((capacityScalingModel solve J U).value e).toNat)) ∧
        ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
      refine ⟨le_rfl,by omega,?_,hz,fun _ _ => rfl⟩
      intro i hi
      simp only [List.length_ofFn,hm] at hi
      omega
    · simp only [capacityScalingContract,capacityScalingModel,hm,↓reduceIte,List.length_nil,
        Nat.zero_mul,Nat.mul_one,Expr.size_bin,Expr.size_load,
        Expr.size_reg,Expr.size_const]
      omega
  · have hm : 0<J.m := by omega
    refine runs_seq_call_le hkC (vs := [a,heap]) (scaling_compression_args (by rfl) (by rfl))
      (by wram_words) ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinputWords⟩,hz,by change heap+(J.solverWords.length+J.n+2)<2^w; omega⟩ ?_
    intro compHeap memC posC hpostC
    obtain ⟨⟨hloC,hhiC,hframeC,hzC,hgraphC⟩,hretC⟩ := hpostC
    change compHeap=heap+J.solverWords.length+2+J.n at hretC
    change ListAt memC heap J.compress.solverWords at hgraphC
    change ZeroFrom memC compHeap at hzC
    change (∀ x<heap,memC x=mem x) at hframeC
    have hcompWord : compHeap<2^w := by omega
    have hgraphEndC : heap+J.compress.solverWords.length≤compHeap := by
      rw [hlenComp]
      omega
    have hloopSpace : compHeap+J.compress.m+2+(fuel+1)*Nc<2^w := by
      change compHeap+J.m+2+(fuel+1)*Nc<2^w
      omega
    refine runs_seq_call_le hkL (vs := [heap,U,compHeap])
      (scaling_loop_args (by rfl) (by rfl) (by rfl)) (by wram_words)
      ⟨heap,compHeap,rfl,hgraphC,hgraphEndC,hC,hu,hm,hzC,hloopSpace⟩ ?_
    intro loopHeap memL posL hpostL
    obtain ⟨hloL,hhiL,hstateL,hzL,hframeL⟩ := hpostL
    change compHeap≤loopHeap at hloL
    change loopHeap≤compHeap+J.m+2+fuel*Nc at hhiL
    change CapacityStateAt memL (loopHeap-2) loopHeap r.value at hstateL
    change ZeroFrom memL loopHeap at hzL
    change (∀ x<compHeap,memL x=memC x) at hframeL
    have hpartial : fuel*Nc≤(fuel+1)*N := by
      exact (Nat.mul_le_mul_right Nc (by omega)).trans hreserve
    have hloopWord : loopHeap<2^w := by omega
    have hstateWord : loopHeap-2<2^w := by omega
    have hloop2 : 2≤loopHeap := by omega
    refine runs_seq_assign_le (v := loopHeap-2) (scaling_state_eval (by rfl) hloopWord (by omega)) ?_
    refine runs_seq_call_le hkF (vs := [loopHeap-2,J.m,loopHeap])
      (scaling_copy_args (by rfl) (by rfl) (by rfl)) (by wram_words)
      ⟨⟨loopHeap-2,loopHeap,rfl,by omega,hstateL,by omega⟩,hzL,by change loopHeap+J.m<2^w; omega⟩ ?_
    intro ret memF posF hpostF
    obtain ⟨⟨hloF,hhiF,hframeF,hzF,houtput⟩,hretF⟩ := hpostF
    change ret=loopHeap+J.m at hretF
    change (∀ x<loopHeap,memF x=memL x) at hframeF
    change ListAt memF loopHeap (List.ofFn (fun e => (r.value.flow e).toNat)) at houtput
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+capacityScalingSpace J C U ∧
        ListAt memF (ret-J.m) (List.ofFn (fun e => ((capacityScalingModel solve J U).value e).toNat)) ∧
        ZeroFrom memF ret ∧ ∀ x<heap,memF x=mem x
      refine ⟨by omega,by change ret≤heap+(J.solverWords.length+J.n+2+J.m+2+(fuel+1)*N+J.m); omega,?_,hzF,?_⟩
      · simpa only [capacityScalingModel,show J.m≠0 by omega,↓reduceIte,hretF,Nat.add_sub_cancel_right] using houtput
      · intro x hx
        exact (hframeF x (by omega)).trans ((hframeL x (by omega)).trans (hframeC x hx))
    · have hpad := scaling_cost_padding J.m J.n r.calls.length
        ((solver.regBound+6)*T (J.compress.n+1) (J.m+J.m)) r.work solver.regBound
      simpa only [capacityScalingContract,capacityScalingModel,show J.m≠0 by omega,↓reduceIte,
        compressionContract,heapContract,capacityLoopContract,capacityFlowCopyContract,r,solve,
        startState,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,
        Nat.add_assoc,Nat.reduceAdd] using hpad

end MinCostFlow.Scaling.Machine
