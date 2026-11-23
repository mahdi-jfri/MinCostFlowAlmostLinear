module

public import MinCostFlow.Final.ScratchCostLoop
public import MinCostFlow.Scaling.CostScalingContract
import MinCostFlow.Scaling.CostScalingSpace
import MinCostFlow.Scaling.VertexCompressionSize
import MinCostFlow.Scaling.BottleneckGuestSpace
import WordRAM.LinkDefs
import MinCostFlow.Scaling.VertexCompressionSize
import MinCostFlow.Scaling.CapacityPositiveProgram
import MinCostFlow.Scaling.CapacityPositiveCountedCost
import MinCostFlow.Scaling.CostLoopProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.CirculationLayout
import Mathlib.Tactic.Ring
import WordRAM.Tactic

/-!
# Cost scaling with polynomial scratch

Compression preserves the input's cost and capacity bounds. The
program selects the measured cost loop or the single capacity call
and returns its integral model flow in the same output layout.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Compression, threshold, both exact solver branches, and flow copying. -/
def scratchCostScalingModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let positive := b+8
  let loop := positive+(scratchCapacityPositiveModule solver entry positive c d).length
  let copy := loop+(scratchCostLoopModule solver entry loop c d).length
  costScalingBody (b+1) (b+7) positive loop copy ::
    (compressionModule (b+1) ++ costPolynomialModule ++ scratchCapacityPositiveModule solver entry positive c d ++
      scratchCostLoopModule solver entry loop c d ++ costFlowCopyModule copy)

/-- Original dimensions cover compression scratch, either branch, and
one final flow array, including a spare per-round numerical margin. -/
def scratchCostScalingSpace (c d : ℕ) (J : Circulation) (C U : ℕ) : ℕ :=
  J.solverWords.length+J.n+2+J.m+2*J.n+3+
    (costRounds J.n C+2)*(costStepNumberBase J C U)^(524*scratchWidthFactor c d)+J.m+3

/-- Exact measured cost-model flow in the final `m` returned words, with
the actual primitive-call term and model work charged for all branches. -/
noncomputable def scratchCostScalingContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let r := costScalingMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) J C
  { pre := fun args mem => ∃ a heap,args=[a,C,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧ 2*J.m+1≤U ∧
      ZeroFrom mem heap ∧ heap+scratchCostScalingSpace c d J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchCostScalingSpace c d J C U ∧
      ListAt mem' (ret-J.m) (List.ofFn (fun e => (r.value e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => r.calls.length*((solver.regBound+6)*T (J.compress.n+3) (16*J.m+4*J.compress.n))+
      302000*scratchWorkFactor solver c d*r.work }

/-- Every cost-scaling branch and all nested calls are deterministic. -/
theorem scratchCostScalingModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCostScalingModule solver entry b c d,body.NoRand := by
  intro body hb
  simp only [scratchCostScalingModule,List.mem_cons,List.mem_append,or_assoc] at hb
  rcases hb with rfl | hc | hp | hs | hl | hf
  · simp only [costScalingBody,Stmt.NoRand,and_self]
  · exact compressionModule_noRand _ body hc
  · have heq : body=costPolynomialBody := List.mem_singleton.mp hp
    subst body
    exact costPolynomialBody_noRand
  · exact scratchCapacityPositiveModule_noRand solver entry _ c d hdet body hs
  · exact scratchCostLoopModule_noRand solver entry _ c d hdet body hl
  · exact costFlowCopyModule_noRand _ body hf

/-- Vertex compression cannot increase the cost loop's uniform round reserve. -/
theorem scratchCostScaling_compressed_power_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    (costStepNumberBase J.compress C U)^(524*scratchWidthFactor c d)≤(costStepNumberBase J C U)^(524*scratchWidthFactor c d) := by
  apply Nat.pow_le_pow_left
  have hn := J.compress_vertices_le
  change J.compress.n+4*J.m+(J.m+J.m)^10+C+U+8≤J.n+4*J.m+(J.m+J.m)^10+C+U+8
  omega

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- One uniform cost-round reserve also covers the direct positive
capacity-model branch on the compressed graph. -/
theorem scratchCostScaling_positive_space_le (c d : ℕ) (J : Circulation) (C U : ℕ) :
    scratchCapacityPositiveSpace c d J.compress C U≤(costStepNumberBase J C U)^(524*scratchWidthFactor c d) := by
  let D := costStepNumberBase J C U
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hn := J.compress_vertices_le
  have hbase : capacityGraphSpaceBase J.compress C U≤D := by
    change J.compress.n+2*J.m+C+U+8≤D
    omega
  have h260 : scratchCapacityPositiveSpace c d J.compress C U≤D^(260*scratchWidthFactor c d) :=
    (scratchCapacityPositiveSpace_le c d J.compress C U).trans (Nat.pow_le_pow_left hbase (260*scratchWidthFactor c d))
  exact h260.trans (Nat.pow_le_pow_right (by omega : 0<D) (by omega))

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- The complete wrapper reserve supplies fitting source words, the
`m^10` threshold, and the small constants for every branch. -/
theorem scratchCostScaling_words_of_space {w : ℕ} (c d : ℕ) (J : Circulation) (C U heap : ℕ)
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U)
    (hs : heap+scratchCostScalingSpace c d J C U<2^w) :
    8<2^w ∧ (∀ x∈J.solverWords,x<2^w) ∧ (∀ x∈J.compress.solverWords,x<2^w) ∧ J.m^10<2^w := by
  let D := costStepNumberBase J C U
  let N := D^(524*scratchWidthFactor c d)
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have h1N : D≤N := Nat.le_pow (by
    have hf := scratchWidthFactor_pos c d
    omega)
  have hNcells : N≤(costRounds J.n C+2)*N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤costRounds J.n C+2 by omega)
  change heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(costRounds J.n C+2)*N+J.m+3)<2^w at hs
  have hmax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D (by omega) (by omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hcompN := J.compress_vertices_le
  have hmaxComp : J.compress.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J.compress D
    (by omega) (by change J.m≤D; omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hpoly : J.m^10≤D := (Nat.pow_le_pow_left (show J.m≤J.m+J.m by omega) 10).trans (by omega)
  refine ⟨by omega,?_,?_,by omega⟩
  · intro x hx
    have h := Link.elem_le_foldr_max hx
    omega
  · intro x hx
    have h := Link.elem_le_foldr_max hx
    omega

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
theorem scratchCostScaling_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (scratchCostScalingModule solver entry b c d)) (J : Circulation) (C U : ℕ) :
    MeetsContract w p b (scratchCostScalingContract w solver entry T S c d hproc J C U) := by
  let inner := fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U
  let G := J.compress
  let N := (costStepNumberBase J C U)^(524*scratchWidthFactor c d)
  let Nc := (costStepNumberBase G C U)^(524*scratchWidthFactor c d)
  let fuel := costRounds J.n C
  let fc := costRounds G.n C
  let primal := G.invokePositive inner
  let loopResult := costLoopMeasured inner G C
  let Q := (solver.regBound+6)*T (G.n+3) (16*J.m+4*G.n)
  let pbase := b+8
  let lbase := pbase+(scratchCapacityPositiveModule solver entry pbase c d).length
  let fbase := lbase+(scratchCostLoopModule solver entry lbase c d).length
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
  have hPositive : p.HasAt pbase (scratchCapacityPositiveModule solver entry pbase c d) := hasAt_append_left htP
  have htL := hasAt_append_right htP
  have hLoop : p.HasAt lbase (scratchCostLoopModule solver entry lbase c d) := hasAt_append_left htL
  have hCopy : p.HasAt fbase (costFlowCopyModule fbase) := hasAt_append_right htL
  have hkPoly := costPolynomial_meetsContract (w := w) hPoly J.m
  have hkLoop := scratchCostLoop_meetsContract (w := w) hproc hScratch hdet hmono hLoop G C U
  have hkCopy := costFlowCopy_meetsContract (w := w) hCopy G loopResult.value
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hC,hu,hU,hz,hs⟩ := hpre
  have hspace : heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*N+J.m+3)<2^w := hs
  obtain ⟨h8,hinput,hcompWords,hpolyWord⟩ := scratchCostScaling_words_of_space c d J C U heap hC hu hs
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
  have hNc : Nc≤N := scratchCostScaling_compressed_power_le c d J C U
  have hfc : fc≤fuel := costScaling_compressed_rounds_le J C
  have hPCspace : scratchCapacityPositiveSpace c d G C U≤N := scratchCostScaling_positive_space_le c d J C U
  have hD8 : 8≤costStepNumberBase J C U := by dsimp only [costStepNumberBase]; omega
  have hNpos : 1≤N := Nat.one_le_pow _ _ (by omega)
  have hNcells : N≤(fuel+2)*N := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤fuel+2 by omega)
  have hloopCells : (fc+1)*Nc≤(fuel+2)*N := Nat.mul_le_mul (by omega) hNc
  have hloopUsed : fc*Nc≤(fuel+2)*N := Nat.mul_le_mul (by omega) hNc
  apply runs_start_le
  unfold costScalingBody
  refine runs_seq_assign_le (v := J.m) (scaling_cost_count (by rfl) ha1 hM) ?_
  wram_step
  · have hm : J.m=0 := by omega
    refine runs_ret_le (v := heap) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤heap ∧ heap≤heap+scratchCostScalingSpace c d J C U ∧
        ListAt mem (heap-J.m) (List.ofFn (fun e => ((costScalingMeasured inner J C).value e).toNat)) ∧
        ZeroFrom mem heap ∧ ∀ x<heap,mem x=mem x
      refine ⟨le_rfl,by omega,?_,hz,fun _ _ => rfl⟩
      intro i hi
      simp only [List.length_ofFn,hm] at hi
      omega
    · simp only [scratchCostScalingContract,costScalingMeasured,hm,↓reduceIte,List.length_nil,
        Nat.zero_mul,Nat.mul_one,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      have hw := scratchWorkFactor_pos solver c d
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
    have hpositiveSpace : compHeap+scratchCapacityPositiveSpace c d G C U<2^w := by omega
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
      · change heap≤ret ∧ ret≤heap+scratchCostScalingSpace c d J C U ∧
          ListAt memF (ret-J.m) (List.ofFn (fun e => ((costScalingMeasured inner J C).value e).toNat)) ∧
          ZeroFrom memF ret ∧ ∀ x<heap,memF x=mem x
        refine ⟨by omega,?_,?_,hzF,?_⟩
        · change ret≤heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*N+J.m+3)
          omega
        · simpa only [costScalingMeasured,hmne,hlarge,↓reduceIte,hretF,Nat.add_sub_cancel_right] using houtput
        · intro x hx
          exact (hframeF x (by omega)).trans ((hframeL x (by omega)).trans (hframeC x hx))
      · let charge := (scratchCostLoopContract w solver entry T S c d hproc G C U).cost [] (fun _ => 0)
        have hS : charge=loopResult.calls.length*Q+301000*scratchWorkFactor solver c d*loopResult.work := rfl
        have hpad := loop_cost_scaling_padding J.m J.n (loopResult.calls.length*Q) loopResult.work
          (scratchWorkFactor solver c d) charge (scratchWorkFactor_pos solver c d) hS
        simp only [scratchCostScalingContract,costScalingMeasured,hmne,hlarge,↓reduceIte]
        change _≤loopResult.calls.length*Q+302000*scratchWorkFactor solver c d*(J.n+20*J.m+1+loopResult.work)
        apply le_trans (b := 500*J.m+500+30+charge+(17*J.m+60)+200) ?_ hpad
        simp only [compressionContract,costPolynomialContract,costFlowCopyContract,heapContract,
          argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hcostArgs : (scratchCostLoopContract w solver entry T S c d hproc G C U).cost [heap,C,U,compHeap] memC=charge := rfl
        rw [hcostArgs]
        omega
    · have hsmall : C≤J.m^10 := by omega
      have hcG : G.CostsBounded (G.m^10) := fun e => (hC e).trans hsmall
      have hkP := scratchCapacityPositive_meetsContract (w := w) hproc hScratch hdet hPositive G C U hcG
      refine runs_seq_call_le hkP (vs := [heap,U,compHeap])
        (scaling_cost_positive_args (by rfl) (by rfl) (by rfl)) (by wram_words)
        ⟨heap,compHeap,rfl,hgraphC,hgraphEndC,hcompWords,by omega,by omega,
          hC,hu,by omega,hzC,hpositiveSpace⟩ ?_
      intro ret memP posP hpostP
      obtain ⟨hloP,hhiP,houtput,hzP,hframeP⟩ := hpostP
      change compHeap≤ret at hloP
      change ret≤compHeap+scratchCapacityPositiveSpace c d G C U at hhiP
      change ListAt memP (ret-J.m) (List.ofFn (fun e => (primal.value e).toNat)) at houtput
      change (∀ x<compHeap,memP x=memC x) at hframeP
      refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
      · change heap≤ret ∧ ret≤heap+scratchCostScalingSpace c d J C U ∧
          ListAt memP (ret-J.m) (List.ofFn (fun e => ((costScalingMeasured inner J C).value e).toNat)) ∧
          ZeroFrom memP ret ∧ ∀ x<heap,memP x=mem x
        refine ⟨by omega,?_,?_,hzP,?_⟩
        · change ret≤heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(fuel+2)*N+J.m+3)
          omega
        · simpa only [costScalingMeasured,hmne,hsmall,↓reduceIte] using houtput
        · intro x hx
          exact (hframeP x (by omega)).trans (hframeC x hx)
      · let charge := (scratchCapacityPositiveContract w solver entry T S c d hproc G C U).cost [] (fun _ => 0)
        have hS : charge≤primal.calls.length*Q+102000*scratchWorkFactor solver c d*primal.work+400*J.m+900 :=
          scratchCapacityPositive_cost_counted w solver entry T S c d hproc hmono G C U (G.n+3) (16*J.m+4*G.n)
            (by omega) (by change J.m+J.m≤16*J.m+4*G.n; omega) [] (fun _ => 0)
        have hpad := direct_cost_scaling_padding J.m J.n (primal.calls.length*Q) primal.work
          (scratchWorkFactor solver c d) charge (scratchWorkFactor_pos solver c d) hS
        simp only [scratchCostScalingContract,costScalingMeasured,hmne,hsmall,↓reduceIte]
        change _≤primal.calls.length*Q+302000*scratchWorkFactor solver c d*(J.n+20*J.m+1+10*(J.m+1)+primal.work)
        apply le_trans (b := 500*J.m+500+30+charge+200) ?_ hpad
        simp only [compressionContract,costPolynomialContract,heapContract,argsSize_cons,argsSize_nil,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
        have hcostArgs : (scratchCapacityPositiveContract w solver entry T S c d hproc G C U).cost [heap,U,compHeap] memC=charge := rfl
        rw [hcostArgs]
        omega

end MinCostFlow.Final
