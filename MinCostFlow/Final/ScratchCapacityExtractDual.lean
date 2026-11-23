module

public import MinCostFlow.Final.ScratchCapacityRoutingLabels
public import MinCostFlow.Scaling.CapacityExtractDualContract
import Mathlib.Tactic.ClearExclamation
import MinCostFlow.Scaling.CapacityRoutingLabelsProgram
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.ResidualWordBounds
import WordRAM.Tactic

/-!
# Dual extraction using the widened capacity solver

The residual construction and routing labels implement the measured
dual extraction used by cost scaling.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Primal residual construction followed by capacity-backed routed labels. -/
def scratchCapacityExtractDualModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  capacityExtractDualBody (b+1) (b+7) ::
    (residualModule (b+1) ++ scratchCapacityRoutingLabelsModule solver entry (b+7) c d)

/-- Residual storage followed by the exact capacity-backed label reserve. -/
def scratchCapacityExtractDualSpace (c d : ℕ) (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) : ℕ :=
  2+10*J.m+scratchCapacityRoutingLabelsSpace c d (J.residual flow) C U

/-- Exact measured dual-extraction value through a fitting output pointer,
with the source graph and primal array below the fresh heap. -/
noncomputable def scratchCapacityExtractDualContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) : Contract :=
  let R := J.residual flow
  { pre := fun args mem => ∃ a fp heap,args=[a,fp,U,heap] ∧ ListAt mem a J.solverWords ∧
      ListAt mem fp (List.ofFn (fun e => (flow e).toNat)) ∧ a+J.solverWords.length≤heap ∧ fp+J.m≤heap ∧
      (∀ e,0≤flow e ∧ flow e≤J.capacity e) ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ (R.m+R.n+1)*C<2^w ∧ ZeroFrom mem heap ∧
      heap+scratchCapacityExtractDualSpace c d J flow C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchCapacityExtractDualSpace c d J flow C U ∧
      (∀ x<heapArg args,mem' x=mem x) ∧ ZeroFrom mem' ret ∧
      ∃ ptr,heapArg args<ptr ∧ ptr<2^w ∧ ptr+2*J.n≤ret ∧ mem' (heapArg args)=ptr ∧
        SignedTableAt mem' ptr
          (J.extractDualMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) flow).value
    cost := fun _ _ => (scratchCapacityRoutingLabelsContract w solver entry T S c d hproc R C U).cost [] (fun _ => 0)+
      600*J.m+400 }

/-- Residual construction and all nested model calls use no random instruction. -/
theorem scratchCapacityExtractDualModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityExtractDualModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityExtractDualBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hr | hl
    · exact residualModule_noRand _ body hr
    · exact scratchCapacityRoutingLabelsModule_noRand solver entry _ c d hdet body hl

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
theorem scratchCapacityExtractDual_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityExtractDualModule solver entry b c d))
    (J : Circulation) (flow : Fin J.m → ℤ) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityExtractDualContract w solver entry T S c d hproc J flow C U) := by
  let R := J.residual flow
  have ht := hasAt_tail hp
  have hR := hasAt_append_left ht
  have hL : p.HasAt (b+7) (scratchCapacityRoutingLabelsModule solver entry (b+7) c d) := by
    have hraw := hasAt_append_right ht
    have hlen : (residualModule (b+1)).length=6 := rfl
    simpa only [hlen,Nat.add_assoc,Nat.reduceAdd] using hraw
  have hkR := residual_meetsContract (w := w) hR J flow
  have hkL := scratchCapacityRoutingLabels_meetsContract (w := w) hproc hScratch hdet hL R C U
    (J.residual_polynomialCosts flow hc)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,fp,heap,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hf,hinput,hC,hu,hn2,hbudget,hz,hs⟩ := hpre
  have hspace : heap+(2+10*J.m+scratchCapacityRoutingLabelsSpace c d R C U)<2^w := hs
  have h8 : 8<2^w := by
    dsimp only [scratchCapacityExtractDualSpace,scratchCapacityRoutingLabelsSpace,scratchCapacityRoutingOptimizeSpace,
      scratchCapacityRoutingSolveSpace,scratchCapacityPositiveSpace,scratchCapacityScalingSpace] at hs
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
  change ret≤residualHeap+scratchCapacityRoutingLabelsSpace c d R C U at hhiL
  change (∀ x<residualHeap,memL x=memR x) at hframeL
  change ZeroFrom memL ret at hzL
  change residualHeap<ptr at hptrLower
  change memL residualHeap=ptr at hptrMem
  have hheapPtr : heap<ptr := by omega
  have hanswer : SignedTableAt memL ptr
      (J.extractDualMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) flow).value := by
    rw [scratchExtractDualMeasured_value_eq_capacityRoutingPotentials]
    exact htable
  have htableF := hanswer.store_before (dst := heap) (value := ptr) hheapPtr
  refine runs_seq_assign_le (v := ptr) (dual_pointer_eval (by rfl) hptrMem) ?_
  refine runs_seq_store_le (x := heap) (v := ptr) (Expr.eval_reg_of_eq (by rfl)) (Expr.eval_reg_of_eq (by rfl)) ?_
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+scratchCapacityExtractDualSpace c d J flow C U ∧
      (∀ x<heap,Function.update memL heap ptr x=mem x) ∧ ZeroFrom (Function.update memL heap ptr) ret ∧
      ∃ ptr',heap<ptr' ∧ ptr'<2^w ∧ ptr'+2*J.n≤ret ∧ Function.update memL heap ptr heap=ptr' ∧
        SignedTableAt (Function.update memL heap ptr) ptr'
          (J.extractDualMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) flow).value
    refine ⟨by omega,by change ret≤heap+(2+10*J.m+scratchCapacityRoutingLabelsSpace c d R C U); omega,
      ?_,?_,ptr,hheapPtr,hptrWord,hptrEnd,Function.update_self _ _ _,htableF⟩
    · intro x hx
      rw [Function.update_of_ne (by omega : x≠heap)]
      exact (hframeL x (by omega)).trans (hframeR x hx)
    · intro x hx
      rw [Function.update_of_ne (by omega : x≠heap)]
      exact hzL x hx
  · simp only [scratchCapacityExtractDualContract,residualContract,scratchCapacityRoutingLabelsContract,
      heapContract,argsSize_cons,argsSize_nil,Expr.size_load,Expr.size_reg,R]
    omega

end MinCostFlow.Final
