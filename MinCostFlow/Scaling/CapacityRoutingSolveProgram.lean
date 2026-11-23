module

public import MinCostFlow.Scaling.CapacityRoutingSolveContract
import MinCostFlow.Scaling.CapacityPositiveProgram
import MinCostFlow.Scaling.RoutingResidualBounds
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# Executing routing-residual calls to capacity scaling

The prepared residual is exactly the one in the dual-extraction model.
Its capacities are at most the number of old vertices plus one. Thus the
given capacity bound covers the positive adapter, whose exact returned
array supplies the model correction. The retained graph and starting flow
survive that call by its fresh-heap frame.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem routing_prepare_args {w a heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h2 : st.regs 2=heap) :
    evalArgs w st [.reg 0,.reg 2]=some [a,heap] := by eval_expr

private theorem routing_capacity_args {w a U heap : ℕ} {st : State}
    (h7 : st.regs 7=a) (h1 : st.regs 1=U) (h6 : st.regs 6=heap) :
    evalArgs w st [.reg 7,.reg 1,.reg 6]=some [a,U,heap] := by eval_expr

private theorem routing_residual_ptr_eval {w heap count : ℕ} {st : State}
    (h2 : st.regs 2=heap) (h5 : st.regs 5=count) (hconst : 6<2^w)
    (hprod : 6*count<2^w) (hadd : heap+2<2^w) (hptr : heap+2+6*count<2^w) :
    Expr.eval w st (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 6) (.reg 5)))=
      some (heap+2+6*count) := by eval_expr

/-- Preparing the routing residual and calling the full capacity-model
adapter returns its exact correction, retaining both arrays needed for
augmentation and charging only linear work beyond the inner procedure. -/
theorem capacityRoutingSolve_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityRoutingSolveModule solver entry b))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityRoutingSolveContract w solver entry T hproc J C U) := by
  let M := J.m+J.n
  let S := J.shortestRoutingGraph
  let Q := S.residual J.shortestRoutingStart
  have ht := hasAt_tail hp
  have hP := hasAt_append_left ht
  have hS : p.HasAt (b+16) (capacityPositiveModule solver entry (b+16)) := by
    have hraw := hasAt_append_right ht
    have hlen : (routingResidualModule (b+1)).length=15 := rfl
    simpa only [hlen,Nat.add_assoc,Nat.reduceAdd] using hraw
  have hkP := routingResidual_meetsContract (w := w) hP J
  have hkS := capacityPositive_meetsContract (w := w) hproc hdet hS Q C U (routingResidual_cost_bound J hc)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hz,hs⟩ := hpre
  have hspace : heap+(4+16*M+capacityPositiveSpace Q C U)<2^w := hs
  have h8 : 8<2^w := by
    dsimp only [capacityRoutingSolveSpace,capacityPositiveSpace,capacityScalingSpace] at hs
    omega
  have hh : heap<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by dsimp only [M] at hspace; omega
  have hMword : M<2^w := by omega
  have hsum : J.n+J.m=M := by dsimp only [M]; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hQinput := routingResidual_words_fit J w hinput (by omega) (by change M+M<2^w; omega) (by omega)
  have hQcost : Q.CostsBounded C := S.residual_costsBounded J.shortestRoutingStart C
    (J.shortestRoutingGraph_costsBounded C hC)
  have hQcap : ∀ e,Q.capacity e≤U := by
    have h := S.residual_capacities_le J.shortestRoutingStart J.shortestRoutingStart_bounds
      (J.n+1) J.shortestRoutingGraph_capacities
    exact fun e => (h e).trans hu
  have hUword : U<2^w := hwords U (by simp)
  apply runs_start_le
  unfold capacityRoutingSolveBody
  refine runs_seq_assign_le (v := J.n) (by clear! solver T Q hinput hc; eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by clear! solver T Q hinput hc; eval_expr) ?_
  refine runs_seq_assign_le (v := M) ?_ ?_
  · rw [←hsum]
    clear! solver T Q hinput hc
    eval_expr
  · refine runs_seq_call_le hkP (vs := [a,heap]) (routing_prepare_args (by rfl) (by rfl)) (by wram_words)
      ⟨⟨a,heap,rfl,hgraph,hgraphEnd,hinput,by omega,hMword,h8⟩,hz,
        by change heap+(4+16*M)<2^w; omega⟩ ?_
    intro preparedHeap memP posP hpostP
    obtain ⟨⟨_,_,hframeP,hzP,hgraphP,hstartP,hresidualP⟩,hretP⟩ := hpostP
    change preparedHeap=heap+4+16*M at hretP
    change (∀ x<heap,memP x=mem x) at hframeP
    change ZeroFrom memP preparedHeap at hzP
    change ListAt memP heap S.solverWords at hgraphP
    change ListAt memP (heap+2+5*M) (List.ofFn (fun e => (J.shortestRoutingStart e).toNat)) at hstartP
    change ListAt memP (heap+2+6*M) Q.solverWords at hresidualP
    have hpWord : preparedHeap<2^w := by omega
    have hptrWord : heap+2+6*M<2^w := by omega
    refine runs_seq_assign_le (v := heap+2+6*M)
      (routing_residual_ptr_eval (by rfl) (by rfl) (by omega) (by omega) (by omega) hptrWord) ?_
    refine runs_seq_call_le hkS (vs := [heap+2+6*M,U,preparedHeap])
      (routing_capacity_args (by rfl) (by rfl) (by rfl)) (by wram_words)
      ⟨heap+2+6*M,preparedHeap,rfl,hresidualP,
        by rw [Q.solverWords_length]; change heap+2+6*M+(2+5*(M+M))≤preparedHeap; omega,
        hQinput,hn2,h8,hQcost,hQcap,by omega,hzP,
        by omega⟩ ?_
    intro ret memS posS hpostS
    obtain ⟨hloS,hhiS,houtput,hzS,hframeS⟩ := hpostS
    change preparedHeap≤ret at hloS
    change ret≤preparedHeap+capacityPositiveSpace Q C U at hhiS
    change (∀ x<preparedHeap,memS x=memP x) at hframeS
    have hgraphS : ListAt memS heap S.solverWords := hgraphP.of_agree_below (h₀ := preparedHeap)
      (by rw [S.solverWords_length]; change heap+(2+5*M)≤preparedHeap; omega) hframeS
    have hstartS := hstartP.of_agree_below (h₀ := preparedHeap)
      (by rw [List.length_ofFn]; change heap+2+5*M+M≤preparedHeap; omega) hframeS
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap+4+16*M≤ret ∧ ret≤heap+capacityRoutingSolveSpace J C U ∧
        ListAt memS heap S.solverWords ∧
        ListAt memS (heap+2+5*M) (List.ofFn (fun e => (J.shortestRoutingStart e).toNat)) ∧
        _ ∧ ZeroFrom memS ret ∧ ∀ x<heap,memS x=mem x
      refine ⟨by omega,by change ret≤heap+(4+16*M+capacityPositiveSpace Q C U); omega,
        hgraphS,hstartS,houtput,hzS,?_⟩
      intro x hx
      exact (hframeS x (by omega)).trans (hframeP x hx)
    · simp only [capacityRoutingSolveContract,routingResidualContract,capacityPositiveContract,
        heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,Q,S,M]
      omega

end MinCostFlow.Scaling.Machine
