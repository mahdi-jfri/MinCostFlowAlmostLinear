module

public import MinCostFlow.Final.ScratchCapacityLoop
public import MinCostFlow.Scaling.CapacityScalingContract
import MinCostFlow.Scaling.CapacityScalingSpace
import MinCostFlow.Scaling.VertexCompressionSize
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import Mathlib.Tactic.Ring
import WordRAM.Tactic

/-!
# Capacity scaling with polynomial scratch

Compression reduces the loop's vertex count. The complete loop computes
the model flow in a widened reservation, then the copy procedure exposes
it in the ordinary output layout.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Compression, the complete loop, and output copying at consecutive entries. -/
def scratchCapacityScalingModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  capacityScalingBody (b+1) (b+7) (b+7+(scratchCapacityLoopModule solver entry (b+7) c d).length) ::
    (compressionModule (b+1) ++ scratchCapacityLoopModule solver entry (b+7) c d ++
      capacityFlowCopyModule (b+7+(scratchCapacityLoopModule solver entry (b+7) c d).length))

/-- Original dimensions bound compression scratch, loop space, and the final array. -/
def scratchCapacityScalingSpace (c d : ℕ) (J : Circulation) (C U : ℕ) : ℕ :=
  J.solverWords.length+J.n+2+J.m+2+
    (capacityRounds J.m U+1)*(capacityStepNumberBase J C U)^(scratchCapacityExponent c d)+J.m

/-- Exact capacity-model output in the last `m` returned words, with the
actual primitive-call term and a linear charge to the model work. -/
noncomputable def scratchCapacityScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let r := capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) J U
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
      ZeroFrom mem heap ∧ heap+scratchCapacityScalingSpace c d J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchCapacityScalingSpace c d J C U ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.compress.n+1) (J.m+J.m))+
      102000*scratchWorkFactor solver c d*r.work }

/-- The complete capacity-scaling program is deterministic. -/
theorem scratchCapacityScalingModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityScalingModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityScalingBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hc
    · rcases List.mem_append.mp hb with hc | hl
      · exact compressionModule_noRand _ body hc
      · exact scratchCapacityLoopModule_noRand solver entry _ c d hdet body hl
    · exact capacityFlowCopyModule_noRand _ body hc

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
theorem scratchCapacityScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityScalingModule solver entry b c d))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityScalingContract w solver entry T S c d hproc J C U) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let N := (capacityStepNumberBase J C U)^(scratchCapacityExponent c d)
  let Nc := (capacityStepNumberBase J.compress C U)^(scratchCapacityExponent c d)
  let fuel := capacityRounds J.m U
  let r := capacityLoop solve J.compress U
  have ht := hasAt_tail hp
  have hcl := hasAt_append_left ht
  have hComp : p.HasAt (b+1) (compressionModule (b+1)) := hasAt_append_left hcl
  have hLoop : p.HasAt (b+7) (scratchCapacityLoopModule solver entry (b+7) c d) := by
    simpa only [compressionModule,endpointLabelsModule,vertexScanModule,List.length_append,
      List.length_cons,List.length_nil,Nat.add_assoc,Nat.reduceAdd] using hasAt_append_right hcl
  have hCopy : p.HasAt (b+7+(scratchCapacityLoopModule solver entry (b+7) c d).length)
      (capacityFlowCopyModule (b+7+(scratchCapacityLoopModule solver entry (b+7) c d).length)) := by
    have hraw := hasAt_append_right ht
    have he : b+1+(compressionModule (b+1) ++ scratchCapacityLoopModule solver entry (b+7) c d).length=
        b+7+(scratchCapacityLoopModule solver entry (b+7) c d).length := by
      rw [List.length_append]
      change b+1+(6+(scratchCapacityLoopModule solver entry (b+7) c d).length)=_
      omega
    rw [he] at hraw
    exact hraw
  have hkL := scratchCapacityLoop_meetsContract (w := w) hproc hS hdet hLoop J.compress C U J.endpointLabels_count_le hc
  have hkF := capacityFlowCopy_meetsContract (w := w) hCopy J.compress r.value
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hz,hspace⟩ := hpre
  have hspaceNum : heap+(J.solverWords.length+J.n+2+J.m+2+(fuel+1)*N+J.m)<2^w := hspace
  obtain ⟨h8,hinputWords⟩ := capacityScaling_words_of_space J C U heap hC hu (by
    have hD : 0 < capacityStepNumberBase J C U := by unfold capacityStepNumberBase; omega
    have hf := scratchWidthFactor_pos c d
    have he : 256 ≤ scratchCapacityExponent c d := by unfold scratchCapacityExponent; omega
    apply lt_of_le_of_lt _ hspace
    have h := Nat.mul_le_mul_left (capacityRounds J.m U+1) (Nat.pow_le_pow_right hD he)
    unfold capacityScalingSpace scratchCapacityScalingSpace
    omega)
  have hkC := compression_meetsContract (w := w) h8 hComp J
  have hh : heap<2^w := by omega
  have hU : U<2^w := hwords U (by simp)
  have hmWord : J.m<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hM := (solver_header_at J hgraph).2
  have hmComp : J.compress.m=J.m := rfl
  have hlenComp : J.compress.solverWords.length=J.solverWords.length := by rw [J.compress.solverWords_length,J.solverWords_length]
  have hNc : Nc≤N := by
    apply Nat.pow_le_pow_left
    have hn := J.compress_vertices_le
    change J.compress.n+2*J.m+C+U+4≤J.n+2*J.m+C+U+4
    omega
  have hreserve : (fuel+1)*Nc≤(fuel+1)*N := Nat.mul_le_mul_left _ hNc
  apply runs_start_le
  unfold capacityScalingBody
  refine runs_seq_assign_le (v := J.m) (scaling_edge_count_eval (by rfl) ha1 hM) ?_
  wram_step
  · have hm : J.m=0 := by omega
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+scratchCapacityScalingSpace c d J C U ∧
        ListAt mem (heap-J.m) (List.ofFn (fun e => ((capacityScalingModel solve J U).value e).toNat)) ∧
        ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
      refine ⟨le_rfl,by omega,?_,hz,fun _ _ => rfl⟩
      intro i hi
      simp only [List.length_ofFn,hm] at hi
      omega
    · simp only [scratchCapacityScalingContract,capacityScalingModel,hm,↓reduceIte,List.length_nil,
        Nat.zero_mul,Nat.mul_one,Expr.size_bin,Expr.size_load,
        Expr.size_reg,Expr.size_const]
      have hwork := scratchWorkFactor_pos solver c d
      omega
  · have hm : 0<J.m := by omega
    refine runs_seq_call_le hkC (vs := [a,heap]) (scaling_compression_args (by rfl) (by rfl))
      (by wram_words) ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinputWords⟩,hz,by
        change heap+(J.solverWords.length+J.n+2)<2^w
        apply lt_of_le_of_lt _ hspaceNum
        apply Nat.add_le_add_left
        omega⟩ ?_
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
    · change heap≤ret ∧ ret≤heap+scratchCapacityScalingSpace c d J C U ∧
        ListAt memF (ret-J.m) (List.ofFn (fun e => ((capacityScalingModel solve J U).value e).toNat)) ∧
        ZeroFrom memF ret ∧ ∀ x<heap,memF x=mem x
      refine ⟨by omega,by change ret≤heap+(J.solverWords.length+J.n+2+J.m+2+(fuel+1)*N+J.m); omega,?_,hzF,?_⟩
      · simpa only [capacityScalingModel,show J.m≠0 by omega,↓reduceIte,hretF,Nat.add_sub_cancel_right] using houtput
      · intro x hx
        exact (hframeF x (by omega)).trans ((hframeL x (by omega)).trans (hframeC x hx))
    · have hpad := scaling_cost_padding J.m J.n r.calls.length
        ((solver.regBound+6)*T (J.compress.n+1) (J.m+J.m)) r.work (scratchWorkFactor solver c d - 1)
      simpa only [scratchCapacityScalingContract,capacityScalingModel,show J.m≠0 by omega,↓reduceIte,
        compressionContract,heapContract,scratchCapacityLoopContract,capacityFlowCopyContract,r,solve,
        startState,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,
        Nat.add_assoc,Nat.reduceAdd,scratchWorkFactor_succ] using hpad

end MinCostFlow.Final
