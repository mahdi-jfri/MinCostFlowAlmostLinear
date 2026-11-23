module

public import MinCostFlow.Scaling.CostScalingContract
import MinCostFlow.Scaling.CostScalingSpace
import MinCostFlow.Scaling.VertexCompressionSize
import MinCostFlow.Scaling.CapacityPositiveProgram
import MinCostFlow.Scaling.CapacityPositiveCountedCost
import MinCostFlow.Scaling.CostLoopProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import Mathlib.Tactic.Ring
import WordRAM.Tactic

/-!
# Executing complete measured cost scaling

The empty branch returns its empty vector. Otherwise construct exactly the
compressed model graph and compare against the computed polynomial cost
threshold. The direct branch invokes the capacity model once. The other
branch runs the full measured cost loop and returns its copied state flow.
Both paths retain exact model outputs, traces, and source-memory frames.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem direct_cost_scaling_padding (m n Q W R S : ℕ) (hR : 1≤R)
    (hS : S≤Q+102000*R*W+400*m+900) :
    500*m+500+30+S+200≤Q+302000*R*(n+20*m+1+10*(m+1)+W) := by
  have hmR : m≤R*m := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right m hR
  have hlocal : 500*m+500+30+(Q+102000*R*W+400*m+900)+200≤
      Q+302000*R*(n+20*m+1+10*(m+1)+W) := by
    ring_nf at hmR ⊢
    omega
  exact (Nat.add_le_add_right (Nat.add_le_add_left hS _) _).trans hlocal

private theorem loop_cost_scaling_padding (m n Q W R S : ℕ) (hR : 1≤R)
    (hS : S=Q+301000*R*W) :
    500*m+500+30+S+(17*m+60)+200≤Q+302000*R*(n+20*m+1+W) := by
  rw [hS]
  have hmR : m≤R*m := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right m hR
  ring_nf at hmR ⊢
  omega

private theorem scaling_cost_count {w a m : ℕ} {st : State}
    (h0 : st.regs 0=a) (ha : a+1<2^w) (hm : st.mem (a+1)=m) :
    Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some m := by eval_expr

private theorem scaling_cost_compression_args {w a heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h3 : st.regs 3=heap) :
    evalArgs w st [.reg 0,.reg 3]=some [a,heap] := by eval_expr

private theorem scaling_cost_polynomial_args {w m : ℕ} {st : State} (h4 : st.regs 4=m) :
    evalArgs w st [.reg 4]=some [m] := by eval_expr

private theorem scaling_cost_loop_args {w a C U heap : ℕ} {st : State}
    (h3 : st.regs 3=a) (h1 : st.regs 1=C) (h2 : st.regs 2=U) (h5 : st.regs 5=heap) :
    evalArgs w st [.reg 3,.reg 1,.reg 2,.reg 5]=some [a,C,U,heap] := by eval_expr

private theorem scaling_cost_state_eval {w heap : ℕ} {st : State} (h7 : st.regs 7=heap)
    (hh : heap<2^w) (h3 : 3<2^w) : Expr.eval w st (.bin .sub (.reg 7) (.const 3))=some (heap-3) := by eval_expr

private theorem scaling_cost_copy_args {w state m heap : ℕ} {st : State}
    (h8 : st.regs 8=state) (h4 : st.regs 4=m) (h7 : st.regs 7=heap) :
    evalArgs w st [.reg 8,.reg 4,.reg 7]=some [state,m,heap] := by eval_expr

private theorem scaling_cost_positive_args {w a U heap : ℕ} {st : State}
    (h3 : st.regs 3=a) (h2 : st.regs 2=U) (h5 : st.regs 5=heap) :
    evalArgs w st [.reg 3,.reg 2,.reg 5]=some [a,U,heap] := by eval_expr

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- Complete cost scaling computes exactly the measured model flow in the
solver-array layout, with actual primitive-call cost and model work for
compression, branch selection, both solving paths, and final copying. -/
theorem costScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (costScalingModule solver entry b)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (costScalingContract w solver entry T hproc J C U) := by
  let inner := fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U
  let G := J.compress
  let N := (costStepNumberBase J C U)^524
  let Nc := (costStepNumberBase G C U)^524
  let fuel := costRounds J.n C
  let fc := costRounds G.n C
  let primal := G.invokePositive inner
  let loopResult := costLoopMeasured inner G C
  let Q := (solver.regBound+6)*T (G.n+3) (16*J.m+4*G.n)
  let pbase := b+8
  let lbase := pbase+(capacityPositiveModule solver entry pbase).length
  let fbase := lbase+(costLoopModule solver entry lbase).length
  have ht := hasAt_tail hp
  simp only [List.append_assoc] at ht
  have hComp : p.HasAt (b+1) (compressionModule (b+1)) := hasAt_append_left ht
  have htPoly := hasAt_append_right ht
  have he7 : b+1+(compressionModule (b+1)).length=b+7 := by change b+1+6=b+7; omega
  rw [he7] at htPoly
  have hPoly : p.HasAt (b+7) costPolynomialModule := hasAt_append_left htPoly
  have htP := hasAt_append_right htPoly
  have he8 : b+7+costPolynomialModule.length=pbase := by change b+7+1=b+8; omega
  rw [he8] at htP
  have hPositive : p.HasAt pbase (capacityPositiveModule solver entry pbase) := hasAt_append_left htP
  have htL := hasAt_append_right htP
  have hLoop : p.HasAt lbase (costLoopModule solver entry lbase) := hasAt_append_left htL
  have hCopy : p.HasAt fbase (costFlowCopyModule fbase) := hasAt_append_right htL
  have hkPoly := costPolynomial_meetsContract (w := w) hPoly J.m
  have hkLoop := costLoop_meetsContract (w := w) hproc hdet hmono hLoop G C U
  have hkCopy := costFlowCopy_meetsContract (w := w) hCopy G loopResult.value
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hU,hz,hs⟩ := hpre
  have hspace : heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*N+J.m+3)<2^w := hs
  obtain ⟨h8,hinput,hcompWords,hpolyWord⟩ := costScaling_words_of_space J C U heap hC hu hs
  have hkComp := compression_meetsContract (w := w) h8 hComp J
  have hh : heap<2^w := by omega
  have hCword : C<2^w := hwords C (by simp)
  have hUword : U<2^w := hwords U (by simp)
  have hmWord : J.m<2^w := by omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hM := (solver_header_at J hgraph).2
  have hcompN : G.n≤J.n := J.compress_vertices_le
  have hcompM : G.m=J.m := rfl
  have hcompLen : G.solverWords.length=J.solverWords.length := by rw [G.solverWords_length,J.solverWords_length]
  have hcompU : G.n+1≤U := by have hn := J.endpointLabels_count_le; change G.n≤2*J.m at hn; omega
  have hNc : Nc≤N := costScaling_compressed_power_le J C U
  have hfc : fc≤fuel := costScaling_compressed_rounds_le J C
  have hPCspace : capacityPositiveSpace G C U≤N := costScaling_positive_space_le J C U
  have hD8 : 8≤costStepNumberBase J C U := by dsimp only [costStepNumberBase]; omega
  have hNpos : 1≤N := Nat.one_le_pow 524 _ (by omega)
  have hNcells : N≤(fuel+2)*N := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤fuel+2 by omega)
  have hloopCells : (fc+1)*Nc≤(fuel+2)*N := Nat.mul_le_mul (by omega) hNc
  have hloopUsed : fc*Nc≤(fuel+2)*N := Nat.mul_le_mul (by omega) hNc
  apply runs_start_le
  unfold costScalingBody
  refine runs_seq_assign_le (v := J.m) (scaling_cost_count (by rfl) ha1 hM) ?_
  wram_step
  · have hm : J.m=0 := by omega
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+costScalingSpace J C U ∧
        ListAt mem (heap-J.m) (List.ofFn (fun e => ((costScalingMeasured inner J C).value e).toNat)) ∧
        ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
      refine ⟨le_rfl,by omega,?_,hz,fun _ _ => rfl⟩
      intro i hi
      simp only [List.length_ofFn,hm] at hi
      omega
    · simp only [costScalingContract,costScalingMeasured,hm,↓reduceIte,List.length_nil,
        Nat.zero_mul,Nat.mul_one,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega
  · have hm : 0<J.m := by omega
    have hmne : J.m≠0 := by omega
    refine runs_seq_call_le hkComp (vs := [a,heap]) (scaling_cost_compression_args (by rfl) (by rfl))
      (by wram_words) ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput⟩,hz,
        by change heap+(J.solverWords.length+J.n+2)<2^w; omega⟩ ?_
    intro compHeap memC posC hpostC
    obtain ⟨⟨_,_,hframeC,hzC,hgraphC⟩,hretC⟩ := hpostC
    change compHeap=heap+J.solverWords.length+2+J.n at hretC
    change (∀ x<heap,memC x=mem x) at hframeC
    change ZeroFrom memC compHeap at hzC
    change ListAt memC heap G.solverWords at hgraphC
    have hcompWord : compHeap<2^w := by omega
    have hgraphEndC : heap+G.solverWords.length≤compHeap := by rw [hcompLen]; omega
    have hpositiveSpace : compHeap+capacityPositiveSpace G C U<2^w := by omega
    have hfullLoopSpace : compHeap+G.m+2*G.n+3+(fc+1)*Nc<2^w := by change compHeap+J.m+2*G.n+3+(fc+1)*Nc<2^w; omega
    refine runs_seq_call_le hkPoly (vs := [J.m]) (scaling_cost_polynomial_args (by rfl)) (by wram_words) ⟨rfl,hpolyWord⟩ ?_
    intro threshold memT posT hpostT
    obtain ⟨hthreshold,hmemT⟩ := hpostT
    change threshold=J.m^10 at hthreshold
    subst threshold
    change memT=memC at hmemT
    subst memT
    wram_step
    · have hlarge : ¬C≤J.m^10 := by omega
      refine runs_seq_call_le hkLoop (vs := [heap,C,U,compHeap])
        (scaling_cost_loop_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
        ⟨heap,compHeap,rfl,hgraphC,hgraphEndC,hC,hu,hm,hcompU,hzC,hfullLoopSpace⟩ ?_
      intro loopHeap memL posL hpostL
      obtain ⟨hloL,hhiL,hstateL,hzL,hframeL⟩ := hpostL
      change compHeap≤loopHeap at hloL
      change loopHeap≤compHeap+J.m+2*G.n+3+fc*Nc at hhiL
      change CostStateAt memL (loopHeap-3) loopHeap loopResult.value at hstateL
      change ZeroFrom memL loopHeap at hzL
      change (∀ x<compHeap,memL x=memC x) at hframeL
      have hloopWord : loopHeap<2^w := by omega
      have hstateWord : loopHeap-3<2^w := by omega
      have hloop3 : 3≤loopHeap := by rw [J.solverWords_length] at hretC; omega
      refine runs_seq_assign_le (v := loopHeap-3) (scaling_cost_state_eval (by rfl) hloopWord (by omega)) ?_
      refine runs_seq_call_le hkCopy (vs := [loopHeap-3,J.m,loopHeap])
        (scaling_cost_copy_args (by rfl) (by rfl) (by rfl)) (by wram_words)
        ⟨⟨loopHeap-3,loopHeap,rfl,by omega,hstateL,by omega⟩,hzL,
          by change loopHeap+J.m<2^w; omega⟩ ?_
      intro ret memF posF hpostF
      obtain ⟨⟨_,_,hframeF,hzF,houtput⟩,hretF⟩ := hpostF
      change ret=loopHeap+J.m at hretF
      change (∀ x<loopHeap,memF x=memL x) at hframeF
      change ListAt memF loopHeap (List.ofFn (fun e => (loopResult.value.flow e).toNat)) at houtput
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+costScalingSpace J C U ∧
          ListAt memF (ret-J.m) (List.ofFn (fun e => ((costScalingMeasured inner J C).value e).toNat)) ∧
          ZeroFrom memF ret ∧ ∀ x<heap,memF x=mem x
        refine ⟨by omega,?_,?_,hzF,?_⟩
        · change ret≤heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*N+J.m+3)
          omega
        · simpa only [costScalingMeasured,hmne,hlarge,↓reduceIte,hretF,Nat.add_sub_cancel_right] using houtput
        · intro x hx
          exact (hframeF x (by omega)).trans ((hframeL x (by omega)).trans (hframeC x hx))
      · let S := (costLoopContract w solver entry T hproc G C U).cost [] (fun _ => 0)
        have hS : S=loopResult.calls.length*Q+301000*(solver.regBound+1)*loopResult.work := rfl
        have hpad := loop_cost_scaling_padding J.m J.n (loopResult.calls.length*Q) loopResult.work
          (solver.regBound+1) S (by omega) hS
        simp only [costScalingContract,costScalingMeasured,hmne,hlarge,↓reduceIte]
        change _≤loopResult.calls.length*Q+302000*(solver.regBound+1)*(J.n+20*J.m+1+loopResult.work)
        apply le_trans (b := 500*J.m+500+30+S+(17*J.m+60)+200) ?_ hpad
        simp only [compressionContract,costPolynomialContract,costFlowCopyContract,heapContract,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hcostArgs : (costLoopContract w solver entry T hproc G C U).cost [heap,C,U,compHeap] memC=S := rfl
        rw [hcostArgs]
        omega
    · have hsmall : C≤J.m^10 := by omega
      have hcG : G.CostsBounded (G.m^10) := fun e => (hC e).trans hsmall
      have hkP := capacityPositive_meetsContract (w := w) hproc hdet hPositive G C U hcG
      refine runs_seq_call_le hkP (vs := [heap,U,compHeap])
        (scaling_cost_positive_args (by rfl) (by rfl) (by rfl)) (by wram_words)
        ⟨heap,compHeap,rfl,hgraphC,hgraphEndC,hcompWords,by omega,by omega,
          hC,hu,by omega,hzC,hpositiveSpace⟩ ?_
      intro ret memP posP hpostP
      obtain ⟨hloP,hhiP,houtput,hzP,hframeP⟩ := hpostP
      change compHeap≤ret at hloP
      change ret≤compHeap+capacityPositiveSpace G C U at hhiP
      change ListAt memP (ret-J.m) (List.ofFn (fun e => (primal.value e).toNat)) at houtput
      change (∀ x<compHeap,memP x=memC x) at hframeP
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+costScalingSpace J C U ∧
          ListAt memP (ret-J.m) (List.ofFn (fun e => ((costScalingMeasured inner J C).value e).toNat)) ∧
          ZeroFrom memP ret ∧ ∀ x<heap,memP x=mem x
        refine ⟨by omega,?_,?_,hzP,?_⟩
        · change ret≤heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*N+J.m+3)
          omega
        · simpa only [costScalingMeasured,hmne,hsmall,↓reduceIte] using houtput
        · intro x hx
          exact (hframeP x (by omega)).trans (hframeC x hx)
      · let S := (capacityPositiveContract w solver entry T hproc G C U).cost [] (fun _ => 0)
        have hS : S≤primal.calls.length*Q+102000*(solver.regBound+1)*primal.work+400*J.m+900 :=
          capacityPositive_cost_counted w solver entry T hproc hmono G C U (G.n+3) (16*J.m+4*G.n)
            (by omega) (by change J.m+J.m≤16*J.m+4*G.n; omega) [] (fun _ => 0)
        have hpad := direct_cost_scaling_padding J.m J.n (primal.calls.length*Q) primal.work
          (solver.regBound+1) S (by omega) hS
        simp only [costScalingContract,costScalingMeasured,hmne,hsmall,↓reduceIte]
        change _≤primal.calls.length*Q+302000*(solver.regBound+1)*(J.n+20*J.m+1+10*(J.m+1)+primal.work)
        apply le_trans (b := 500*J.m+500+30+S+200) ?_ hpad
        simp only [compressionContract,costPolynomialContract,heapContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hcostArgs : (capacityPositiveContract w solver entry T hproc G C U).cost [heap,U,compHeap] memC=S := rfl
        rw [hcostArgs]
        omega

end MinCostFlow.Scaling.Machine
