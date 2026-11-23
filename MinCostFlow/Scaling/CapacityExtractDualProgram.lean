module

public import MinCostFlow.Scaling.CapacityExtractDualContract
import MinCostFlow.Scaling.CapacityRoutingLabelsProgram
import MinCostFlow.Scaling.ResidualWordBounds
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# Executing measured dual extraction with capacity scaling

The primal residual constructor gives exactly the graph in the measured
model. Its routed labels use the actual capacity-model output, so their
potential table is the model's exact value. Forwarding the stored table
pointer exposes this value at the enclosing procedure's original heap.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem dual_residual_args {w a flow heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=flow) (h3 : st.regs 3=heap) :
    evalArgs w st [.reg 0,.reg 1,.reg 3]=some [a,flow,heap] := by eval_expr

private theorem dual_labels_args {w a U heap : ℕ} {st : State}
    (h3 : st.regs 3=a) (h2 : st.regs 2=U) (h4 : st.regs 4=heap) :
    evalArgs w st [.reg 3,.reg 2,.reg 4]=some [a,U,heap] := by eval_expr

private theorem dual_pointer_eval {w a ptr : ℕ} {st : State}
    (h4 : st.regs 4=a) (hm : st.mem a=ptr) :
    Expr.eval w st (.load (.reg 4))=some ptr := by eval_expr

/-- Primal residual construction and capacity-backed routing labels
compute exactly the measured dual-extraction model, with linear additional
cost, full source framing, and a fitting signed-table output pointer. -/
theorem capacityExtractDual_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityExtractDualModule solver entry b))
    (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityExtractDualContract w solver entry T hproc J flow C U) := by
  let R := J.residual flow
  have ht := hasAt_tail hp
  have hR := hasAt_append_left ht
  have hL : p.HasAt (b+7) (capacityRoutingLabelsModule solver entry (b+7)) := by
    have hraw := hasAt_append_right ht
    have hlen : (residualModule (b+1)).length=6 := rfl
    simpa only [hlen,Nat.add_assoc,Nat.reduceAdd] using hraw
  have hkR := residual_meetsContract (w := w) hR J flow
  have hkL := capacityRoutingLabels_meetsContract (w := w) hproc hdet hL R C U
    (J.residual_polynomialCosts flow hc)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,fp,heap,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hf,hinput,hC,hu,hn2,hbudget,hz,hs⟩ := hpre
  have hspace : heap+(2+10*J.m+capacityRoutingLabelsSpace R C U)<2^w := hs
  have h8 : 8<2^w := by
    dsimp only [capacityExtractDualSpace,capacityRoutingLabelsSpace,capacityRoutingOptimizeSpace,
      capacityRoutingSolveSpace,capacityPositiveSpace,capacityScalingSpace] at hs
    omega
  have hh : heap<2^w := by omega
  have hdouble : J.m+J.m<2^w := by omega
  have hRwords := residual_words_fit J flow w hf hinput hdouble (by omega)
  have hRcost := J.residual_costsBounded flow C hC
  apply runs_start_le
  unfold capacityExtractDualBody
  refine runs_seq_call_le hkR (vs := [a,fp,heap])
    (dual_residual_args (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨⟨a,fp,heap,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hf,hinput,h8⟩,hz,
      by change heap+(2+10*J.m)<2^w; omega⟩ ?_
  intro residualHeap memR posR hpostR
  obtain ⟨⟨_,_,hframeR,hzR,hgraphR⟩,hretR⟩ := hpostR
  change residualHeap=heap+2+10*J.m at hretR
  change (∀ x<heap,memR x=mem x) at hframeR
  change ZeroFrom memR residualHeap at hzR
  change ListAt memR heap R.solverWords at hgraphR
  have hresWord : residualHeap<2^w := by omega
  have hUword : U<2^w := hwords U (by simp)
  refine runs_seq_call_le hkL (vs := [heap,U,residualHeap])
    (dual_labels_args (by rfl) (by rfl) (by rfl)) (by wram_words)
    ⟨heap,residualHeap,rfl,hgraphR,
      by rw [R.solverWords_length]; change heap+(2+5*(J.m+J.m))≤residualHeap; omega,
      hRwords,hRcost,hu,hn2,hbudget,hzR,
      by omega⟩ ?_
  intro ret memL posL hpostL
  obtain ⟨hloL,hhiL,hframeL,hzL,ptr,hptrLower,hptrWord,hptrEnd,hptrMem,htable⟩ := hpostL
  change residualHeap≤ret at hloL
  change ret≤residualHeap+capacityRoutingLabelsSpace R C U at hhiL
  change (∀ x<residualHeap,memL x=memR x) at hframeL
  change ZeroFrom memL ret at hzL
  change residualHeap<ptr at hptrLower
  change memL residualHeap=ptr at hptrMem
  have hheapPtr : heap<ptr := by omega
  have hanswer : SignedTableAt memL ptr
      (J.extractDualMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) flow).value := by
    rw [extractDualMeasured_value_eq_capacityRoutingPotentials]
    exact htable
  have htableF := hanswer.store_before (dst := heap) (value := ptr) hheapPtr
  refine runs_seq_assign_le (v := ptr) (dual_pointer_eval (by rfl) hptrMem) ?_
  refine runs_seq_store_le (x := heap) (v := ptr) (Expr.eval_reg_of_eq (by rfl)) (Expr.eval_reg_of_eq (by rfl)) ?_
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+capacityExtractDualSpace J flow C U ∧
      (∀ x<heap,Function.update memL heap ptr x=mem x) ∧ ZeroFrom (Function.update memL heap ptr) ret ∧
      ∃ ptr',heap<ptr' ∧ ptr'<2^w ∧ ptr'+2*J.n≤ret ∧ Function.update memL heap ptr heap=ptr' ∧
        SignedTableAt (Function.update memL heap ptr) ptr'
          (J.extractDualMeasured (fun K => capacityScalingModel (canonicalSolver solver entry T hproc) K U) flow).value
    refine ⟨by omega,by change ret≤heap+(2+10*J.m+capacityRoutingLabelsSpace R C U); omega,
      ?_,?_,ptr,hheapPtr,hptrWord,hptrEnd,Function.update_self _ _ _,htableF⟩
    · intro x hx
      rw [Function.update_of_ne (by omega : x≠heap)]
      exact (hframeL x (by omega)).trans (hframeR x hx)
    · intro x hx
      rw [Function.update_of_ne (by omega : x≠heap)]
      exact hzL x hx
  · simp only [capacityExtractDualContract,residualContract,capacityRoutingLabelsContract,
      heapContract,argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_reg,R]
    omega

end MinCostFlow.Scaling.Machine
