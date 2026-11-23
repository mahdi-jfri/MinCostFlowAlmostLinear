module

public import MinCostFlow.Final.ScratchCapacityRoutingOptimize
public import MinCostFlow.Scaling.CapacityRoutingLabelsContract
import Mathlib.Tactic.ClearExclamation
import MinCostFlow.Scaling.CapacityRoutingOptimizeProgram
import MinCostFlow.Scaling.CapacityRoutingPotentials
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Labeling the capacity-backed routing

The optimized routing determines an integer label table for the original
vertices. The program exposes its address to the caller.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Old-vertex labels of the actual capacity-backed optimized routing. -/
noncomputable def scratchCapacityRoutingPotentials (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) (U : ℕ) :
    Fin J.n → ℤ :=
  let labels := J.shortestRoutingGraph.propagateLabels
    (scratchCapacitySolvedRouting solver entry T S c d hproc J U) (Fin.last J.n)
  fun v => labels.1.labels v.castSucc

/-- The named labels equal the exact measured dual-extraction value with
the capacity model as its inner procedure. -/
theorem scratchExtractDualMeasured_value_eq_capacityRoutingPotentials (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (flow : Fin J.m → ℤ) (U : ℕ) :
    (J.extractDualMeasured (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U) flow).value=
      scratchCapacityRoutingPotentials solver entry T S c d hproc (J.residual flow) U := rfl

/-- Capacity-backed routing optimization followed by exact label traversal. -/
def scratchCapacityRoutingLabelsModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let labels := b+1+(scratchCapacityRoutingOptimizeModule solver entry (b+1) c d).length
  capacityRoutingLabelsBody (b+1) labels ::
    (scratchCapacityRoutingOptimizeModule solver entry (b+1) c d ++ propagateLabelsModule labels)

/-- Optimization storage and a full traversal reserve, including a two-cell margin. -/
def scratchCapacityRoutingLabelsSpace (c d : ℕ) (J : Circulation) (C U : ℕ) : ℕ :=
  scratchCapacityRoutingOptimizeSpace c d J C U+5+5*(J.n+1)+6*(J.m+J.n)+2

/-- The old heap holds a fitting pointer to exactly the model's old-vertex
signed label table. All original source memory is preserved. -/
noncomputable def scratchCapacityRoutingLabelsContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ (J.m+J.n+1)*C<2^w ∧ ZeroFrom mem heap ∧
      heap+scratchCapacityRoutingLabelsSpace c d J C U<2^w
    post := fun args mem ret mem' => heapArg args≤ret ∧ ret≤heapArg args+scratchCapacityRoutingLabelsSpace c d J C U ∧
      (∀ x<heapArg args,mem' x=mem x) ∧ ZeroFrom mem' ret ∧
      ∃ ptr,heapArg args<ptr ∧ ptr<2^w ∧ ptr+2*J.n≤ret ∧ mem' (heapArg args)=ptr ∧
        SignedTableAt mem' ptr (scratchCapacityRoutingPotentials solver entry T S c d hproc J U)
    cost := fun _ _ => (scratchCapacityRoutingOptimizeContract w solver entry T S c d hproc J C U).cost [] (fun _ => 0)+
      3000*(J.m+J.n)+1100 }

/-- The entire label-producing module is deterministic. -/
theorem scratchCapacityRoutingLabelsModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityRoutingLabelsModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoutingLabelsBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with ho | hl
    · exact scratchCapacityRoutingOptimizeModule_noRand solver entry _ c d hdet body ho
    · exact propagateLabelsModule_noRand _ body hl

private theorem labels_optimize_args {w a U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=U) (h2 : st.regs 2=heap) :
    evalArgs w st [.reg 0,.reg 1,.reg 2]=some [a,U,heap] := by eval_expr

private theorem labels_flow_eval {w heap count : ℕ} {st : State}
    (h6 : st.regs 6=heap) (h5 : st.regs 5=count) (hh : heap<2^w) :
    Expr.eval w st (.bin .sub (.reg 6) (.reg 5))=some (heap-count) := by eval_expr

private theorem labels_traversal_args {w graph flow root heap : ℕ} {st : State}
    (h2 : st.regs 2=graph) (h7 : st.regs 7=flow) (h3 : st.regs 3=root) (h6 : st.regs 6=heap) :
    evalArgs w st [.reg 2,.reg 7,.reg 3,.reg 6]=some [graph,flow,root,heap] := by eval_expr

private theorem labels_pointer_eval {w base : ℕ} {st : State}
    (h6 : st.regs 6=base) (hh : base+2<2^w) :
    Expr.eval w st (.bin .add (.reg 6) (.const 2))=some (base+2) := by eval_expr

/-- Capacity-backed routing optimization followed by label propagation
returns exactly the measured model's potentials in the signed-table
layout, with linear additional cost and a fitting output pointer. -/
theorem scratchCapacityRoutingLabels_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityRoutingLabelsModule solver entry b c d))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityRoutingLabelsContract w solver entry T S c d hproc J C U) := by
  let M := J.m+J.n
  let routingGraph := J.shortestRoutingGraph
  let routing := scratchCapacitySolvedRouting solver entry T S c d hproc J U
  let root : Fin routingGraph.n := Fin.last J.n
  have ht := hasAt_tail hp
  have hO := hasAt_append_left ht
  have hL := hasAt_append_right ht
  have hkO := scratchCapacityRoutingOptimize_meetsContract (w := w) hproc hScratch hdet hO J C U hc
  have hkL := propagateLabels_meetsContract (w := w) hL C routingGraph routing root
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hbudget,hz,hs⟩ := hpre
  have hspace : heap+(scratchCapacityRoutingOptimizeSpace c d J C U+5+5*(J.n+1)+6*M+2)<2^w := hs
  have hoptSpace : heap+scratchCapacityRoutingOptimizeSpace c d J C U<2^w := by omega
  have hbaseSpace : heap+(4+17*M)<2^w := by
    change heap+(4+16*M+scratchCapacityPositiveSpace c d _ C U+M+5+5*(J.n+1)+6*M+2)<2^w at hspace
    omega
  have h8 : 8<2^w := by omega
  have hh : heap<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by dsimp only [M] at hbaseSpace; omega
  have hMword : M<2^w := by omega
  have hsum : J.n+J.m=M := by dsimp only [M]; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hrouting := scratchCapacitySolvedRouting_bounds solver entry T S c d hproc J U hc hu
  have hvalues : ∀ e,0≤routing e ∧ (routing e).toNat<2^w := by
    intro e
    have hcap : (routing e).toNat≤routingGraph.capacity e := by
      simpa only [Int.toNat_natCast] using Int.toNat_le_toNat (hrouting e).2
    exact ⟨(hrouting e).1,hcap.trans_lt ((J.shortestRoutingGraph_capacities e).trans_lt (by omega))⟩
  have hcostS := J.shortestRoutingGraph_costsBounded C hC
  apply runs_start_le
  unfold capacityRoutingLabelsBody
  refine runs_seq_assign_le (v := J.n) (by clear! solver T routing hinput hc; eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by clear! solver T routing hinput hc; eval_expr) ?_
  refine runs_seq_assign_le (v := M) ?_ ?_
  · rw [←hsum]
    clear! solver T routing hinput hc
    eval_expr
  · refine runs_seq_call_le hkO (vs := [a,U,heap]) (labels_optimize_args (by rfl) (by rfl) (by rfl)) hwords
      ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hz,hoptSpace⟩ ?_
    intro stateBase memO posO hpostO
    obtain ⟨hloO,hhiO,hgraphO,hflowO,hzO,hframeO⟩ := hpostO
    change heap+4+17*M≤stateBase at hloO
    change stateBase≤heap+scratchCapacityRoutingOptimizeSpace c d J C U at hhiO
    change ListAt memO heap routingGraph.solverWords at hgraphO
    change ListAt memO (stateBase-M) (List.ofFn (fun e => (routing e).toNat)) at hflowO
    change ZeroFrom memO stateBase at hzO
    change (∀ x<heap,memO x=mem x) at hframeO
    have hstateWord : stateBase<2^w := by omega
    have hflowWord : stateBase-M<2^w := by omega
    have hptrWord : stateBase+2<2^w := by omega
    have hflowEnd : stateBase-M+M≤stateBase := by omega
    refine runs_seq_assign_le (v := stateBase-M) (labels_flow_eval (by rfl) (by rfl) hstateWord) ?_
    refine runs_seq_call_le hkL (vs := [heap,stateBase-M,J.n,stateBase])
      (labels_traversal_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
      ⟨heap,stateBase-M,stateBase,rfl,hgraphO,hflowO,
        by rw [routingGraph.solverWords_length]; change heap+(2+5*M)≤stateBase; omega,
        hflowEnd,hvalues,hcostS,hbudget,hzO,
        by change stateBase+5+5*(J.n+1)+6*M<2^w; omega,h8⟩ ?_
    intro ret memL posL hpostL
    obtain ⟨hloL,hhiL,hstateL,hzL,hframeL⟩ := hpostL
    change labelNodes routingGraph.n stateBase≤ret at hloL
    change ret≤labelNodes routingGraph.n stateBase+6*M at hhiL
    change LabelStateAt memL stateBase ret (routingGraph.propagateLabels routing root).1 at hstateL
    change ZeroFrom memL ret at hzL
    change (∀ x<stateBase,memL x=memO x) at hframeL
    have hnodes : labelNodes routingGraph.n stateBase=stateBase+3+5*(J.n+1) := rfl
    rw [hnodes] at hloL hhiL
    have hheapPtr : heap<stateBase+2 := by omega
    have htable : SignedTableAt memL (stateBase+2) (scratchCapacityRoutingPotentials solver entry T S c d hproc J U) :=
      hstateL.labels.castSucc
    have htableF := htable.store_before (dst := heap) (value := stateBase+2) hheapPtr
    refine runs_seq_store_le (x := heap) (v := stateBase+2) (Expr.eval_reg_of_eq (by rfl))
      (labels_pointer_eval (by rfl) hptrWord) ?_
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+scratchCapacityRoutingLabelsSpace c d J C U ∧
        (∀ x<heap,Function.update memL heap (stateBase+2) x=mem x) ∧
        ZeroFrom (Function.update memL heap (stateBase+2)) ret ∧
        ∃ ptr,heap<ptr ∧ ptr<2^w ∧ ptr+2*J.n≤ret ∧ Function.update memL heap (stateBase+2) heap=ptr ∧
          SignedTableAt (Function.update memL heap (stateBase+2)) ptr
            (scratchCapacityRoutingPotentials solver entry T S c d hproc J U)
      refine ⟨by omega,by change ret≤heap+(scratchCapacityRoutingOptimizeSpace c d J C U+5+5*(J.n+1)+6*M+2); omega,
        ?_,?_,stateBase+2,hheapPtr,hptrWord,by omega,Function.update_self _ _ _,htableF⟩
      · intro x hx
        rw [Function.update_of_ne (by omega : x≠heap)]
        exact (hframeL x (by omega)).trans (hframeO x hx)
      · intro x hx
        rw [Function.update_of_ne (by omega : x≠heap)]
        exact hzL x hx
    · simp only [scratchCapacityRoutingLabelsContract,scratchCapacityRoutingOptimizeContract,propagateLabelsContract,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,M]
      dsimp only [routingGraph]
      omega

end MinCostFlow.Final
