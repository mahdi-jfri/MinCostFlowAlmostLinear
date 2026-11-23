module

public import MinCostFlow.Scaling.CapacityRoutingLabelsContract
import MinCostFlow.Scaling.CapacityRoutingOptimizeProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# Executing capacity-backed routing-label propagation

The optimized routing is the measured model's exact integer vector.
Propagating its labels therefore produces the same traversal state.
Restrict the stored table to the old vertices and expose its fitting
address by one pointer before the table.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

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
theorem capacityRoutingLabels_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityRoutingLabelsModule solver entry b))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityRoutingLabelsContract w solver entry T hproc J C U) := by
  let M := J.m+J.n
  let S := J.shortestRoutingGraph
  let routing := capacitySolvedRouting solver entry T hproc J U
  let root : Fin S.n := Fin.last J.n
  have ht := hasAt_tail hp
  have hO := hasAt_append_left ht
  have hL := hasAt_append_right ht
  have hkO := capacityRoutingOptimize_meetsContract (w := w) hproc hdet hO J C U hc
  have hkL := propagateLabels_meetsContract (w := w) hL C S routing root
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hbudget,hz,hs⟩ := hpre
  have hspace : heap+(capacityRoutingOptimizeSpace J C U+5+5*(J.n+1)+6*M+2)<2^w := hs
  have hoptSpace : heap+capacityRoutingOptimizeSpace J C U<2^w := by omega
  have hbaseSpace : heap+(4+17*M)<2^w := by
    change heap+(4+16*M+capacityPositiveSpace _ C U+M+5+5*(J.n+1)+6*M+2)<2^w at hspace
    omega
  have h8 : 8<2^w := by omega
  have hh : heap<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by dsimp only [M] at hbaseSpace; omega
  have hMword : M<2^w := by omega
  have hsum : J.n+J.m=M := by dsimp only [M]; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hrouting := capacitySolvedRouting_bounds solver entry T hproc J U hc hu
  have hvalues : ∀ e,0≤routing e ∧ (routing e).toNat<2^w := by
    intro e
    have hcap : (routing e).toNat≤S.capacity e := by
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
    change stateBase≤heap+capacityRoutingOptimizeSpace J C U at hhiO
    change ListAt memO heap S.solverWords at hgraphO
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
        by rw [S.solverWords_length]; change heap+(2+5*M)≤stateBase; omega,
        hflowEnd,hvalues,hcostS,hbudget,hzO,
        by change stateBase+5+5*(J.n+1)+6*M<2^w; omega,h8⟩ ?_
    intro ret memL posL hpostL
    obtain ⟨hloL,hhiL,hstateL,hzL,hframeL⟩ := hpostL
    change labelNodes S.n stateBase≤ret at hloL
    change ret≤labelNodes S.n stateBase+6*M at hhiL
    change LabelStateAt memL stateBase ret (S.propagateLabels routing root).1 at hstateL
    change ZeroFrom memL ret at hzL
    change (∀ x<stateBase,memL x=memO x) at hframeL
    have hnodes : labelNodes S.n stateBase=stateBase+3+5*(J.n+1) := rfl
    rw [hnodes] at hloL hhiL
    have hheapPtr : heap<stateBase+2 := by omega
    have htable : SignedTableAt memL (stateBase+2) (capacityRoutingPotentials solver entry T hproc J U) :=
      hstateL.labels.castSucc
    have htableF := htable.store_before (dst := heap) (value := stateBase+2) hheapPtr
    refine runs_seq_store_le (x := heap) (v := stateBase+2) (Expr.eval_reg_of_eq (by rfl))
      (labels_pointer_eval (by rfl) hptrWord) ?_
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+capacityRoutingLabelsSpace J C U ∧
        (∀ x<heap,Function.update memL heap (stateBase+2) x=mem x) ∧
        ZeroFrom (Function.update memL heap (stateBase+2)) ret ∧
        ∃ ptr,heap<ptr ∧ ptr<2^w ∧ ptr+2*J.n≤ret ∧ Function.update memL heap (stateBase+2) heap=ptr ∧
          SignedTableAt (Function.update memL heap (stateBase+2)) ptr
            (capacityRoutingPotentials solver entry T hproc J U)
      refine ⟨by omega,by change ret≤heap+(capacityRoutingOptimizeSpace J C U+5+5*(J.n+1)+6*M+2); omega,
        ?_,?_,stateBase+2,hheapPtr,hptrWord,by omega,Function.update_self _ _ _,htableF⟩
      · intro x hx
        rw [Function.update_of_ne (by omega : x≠heap)]
        exact (hframeL x (by omega)).trans (hframeO x hx)
      · intro x hx
        rw [Function.update_of_ne (by omega : x≠heap)]
        exact hzL x hx
    · simp only [capacityRoutingLabelsContract,capacityRoutingOptimizeContract,propagateLabelsContract,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,M]
      dsimp only [S]
      omega

end MinCostFlow.Scaling.Machine
