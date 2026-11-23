module

public import MinCostFlow.Scaling.CapacityRoutingOptimizeContract
import MinCostFlow.Scaling.CapacityRoutingSolveProgram
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# Executing capacity-backed source-routing augmentation

The full capacity model returns the exact residual correction. Its proved
feasibility gives nonnegative augmented coordinates and bounds every scan
addition by `n+2`. The existing unsigned residual augmentation scan then
returns exactly the integer routing expression used by the cost model.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem optimize_solve_args {w a U heap : ℕ} {st : State}
    (h0 : st.regs 0=a) (h1 : st.regs 1=U) (h2 : st.regs 2=heap) :
    evalArgs w st [.reg 0,.reg 1,.reg 2]=some [a,U,heap] := by eval_expr

private theorem optimize_start_ptr {w heap M : ℕ} {st : State}
    (h2 : st.regs 2=heap) (h5 : st.regs 5=M) (hconst : 5<2^w)
    (hprod : 5*M<2^w) (hadd : heap+2<2^w) (hptr : heap+2+5*M<2^w) :
    Expr.eval w st (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .mul (.const 5) (.reg 5)))=
      some (heap+2+5*M) := by eval_expr

private theorem optimize_twice_eval {w M : ℕ} {st : State} (h5 : st.regs 5=M) (hM : M+M<2^w) :
    Expr.eval w st (.bin .add (.reg 5) (.reg 5))=some (M+M) := by eval_expr

private theorem optimize_delta_ptr {w heap count : ℕ} {st : State}
    (h6 : st.regs 6=heap) (h8 : st.regs 8=count) (hh : heap<2^w) :
    Expr.eval w st (.bin .sub (.reg 6) (.reg 8))=some (heap-count) := by eval_expr

private theorem optimize_augment_args {w start delta M heap : ℕ} {st : State}
    (h7 : st.regs 7=start) (h9 : st.regs 9=delta) (h5 : st.regs 5=M) (h6 : st.regs 6=heap) :
    evalArgs w st [.reg 7,.reg 9,.reg 5,.reg 6]=some [start,delta,M,heap] := by eval_expr

/-- The complete capacity-backed routing solve and unsigned augmentation
return exactly the measured model's routing, with linear extra work and
preservation of the routing graph and original source memory. -/
theorem capacityRoutingOptimize_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (capacityRoutingOptimizeModule solver entry b))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (capacityRoutingOptimizeContract w solver entry T hproc J C U) := by
  let M := J.m+J.n
  let start := J.shortestRoutingStart
  let delta := capacityRoutingCorrection solver entry T hproc J U
  have ht := hasAt_tail hp
  have hS := hasAt_append_left ht
  have hA := hasAt_append_right ht
  have hkS := capacityRoutingSolve_meetsContract (w := w) hproc hdet hS J C U hc
  have hkA := residualAugment_meetsContract (w := w) hA start delta
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hz,hs⟩ := hpre
  have hspace : heap+(capacityRoutingSolveSpace J C U+M)<2^w := hs
  have hsolveSpace : heap+capacityRoutingSolveSpace J C U<2^w := by omega
  have hbaseSpace : heap+(4+16*M)<2^w := by
    change heap+(4+16*M+capacityPositiveSpace _ C U+M)<2^w at hspace
    omega
  have h8 : 8<2^w := by
    dsimp only [capacityRoutingOptimizeSpace,capacityRoutingSolveSpace,capacityPositiveSpace,capacityScalingSpace] at hs
    omega
  have hh : heap<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by dsimp only [M] at hbaseSpace; omega
  have hMword : M<2^w := by omega
  have hsum : J.n+J.m=M := by dsimp only [M]; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hdeltaOpt := capacityRoutingCorrection_optimal solver entry T hproc J U hc hu
  have hdelta : ∀ e,0≤delta e := fun e => Int.cast_nonneg_iff.mp (hdeltaOpt.1.2 e).1
  have hstart : ∀ e,0≤start e := fun e => Int.cast_nonneg_iff.mp (J.shortestRoutingStart_bounds e).1
  have hupdate : ∀ e,0≤start e+delta (Fin.castAdd M e)-delta (Fin.natAdd M e) :=
    fun e => (capacitySolvedRouting_bounds solver entry T hproc J U hc hu e).1
  have hscan := capacitySolvedRouting_scan_bounds solver entry T hproc J U w hc hu hn2
  apply runs_start_le
  unfold capacityRoutingOptimizeBody
  refine runs_seq_assign_le (v := J.n) (by clear! solver T delta hinput hc; eval_expr) ?_
  refine runs_seq_assign_le (v := J.m) (by clear! solver T delta hinput hc; eval_expr) ?_
  refine runs_seq_assign_le (v := M) ?_ ?_
  · rw [←hsum]
    clear! solver T delta hinput hc
    eval_expr
  · refine runs_seq_call_le hkS (vs := [a,U,heap]) (optimize_solve_args (by rfl) (by rfl) (by rfl)) hwords
      ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hz,hsolveSpace⟩ ?_
    intro solveHeap memS posS hpostS
    obtain ⟨hloS,hhiS,hgraphS,hstartS,hdeltaS,hzS,hframeS⟩ := hpostS
    change heap+4+16*M≤solveHeap at hloS
    change solveHeap≤heap+capacityRoutingSolveSpace J C U at hhiS
    change ListAt memS heap J.shortestRoutingGraph.solverWords at hgraphS
    change ListAt memS (heap+2+5*M) (List.ofFn (fun e => (start e).toNat)) at hstartS
    change ListAt memS (solveHeap-(M+M)) (List.ofFn (fun e => (delta e).toNat)) at hdeltaS
    change ZeroFrom memS solveHeap at hzS
    change (∀ x<heap,memS x=mem x) at hframeS
    have hsolveWord : solveHeap<2^w := by omega
    have hstartWord : heap+2+5*M<2^w := by omega
    have hdeltaWord : solveHeap-(M+M)<2^w := by omega
    have htwiceWord : M+M<2^w := by omega
    have hdeltaEnd : solveHeap-(M+M)+(M+M)≤solveHeap := by omega
    refine runs_seq_assign_le (v := heap+2+5*M)
      (optimize_start_ptr (by rfl) (by rfl) (by omega) (by omega) (by omega) hstartWord) ?_
    refine runs_seq_assign_le (v := M+M) (optimize_twice_eval (by rfl) htwiceWord) ?_
    refine runs_seq_assign_le (v := solveHeap-(M+M)) (optimize_delta_ptr (by rfl) (by rfl) hsolveWord) ?_
    refine runs_seq_call_le hkA (vs := [heap+2+5*M,solveHeap-(M+M),M,solveHeap])
      (optimize_augment_args (by rfl) (by rfl) (by rfl) (by rfl)) (by wram_words)
      ⟨⟨heap+2+5*M,solveHeap-(M+M),solveHeap,rfl,hstartS,hdeltaS,by omega,hdeltaEnd,
        hstart,hdelta,hupdate,hscan,by omega⟩,hzS,by change solveHeap+M<2^w; omega⟩ ?_
    intro ret memA posA hpostA
    obtain ⟨⟨_,_,hframeA,hzA,hflowA⟩,hretA⟩ := hpostA
    change ret=solveHeap+M at hretA
    change (∀ x<solveHeap,memA x=memS x) at hframeA
    change ZeroFrom memA ret at hzA
    change ListAt memA solveHeap (List.ofFn (fun e => (capacitySolvedRouting solver entry T hproc J U e).toNat)) at hflowA
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap+4+17*M≤ret ∧ ret≤heap+capacityRoutingOptimizeSpace J C U ∧
        ListAt memA heap J.shortestRoutingGraph.solverWords ∧
        ListAt memA (ret-M) (List.ofFn (fun e => (capacitySolvedRouting solver entry T hproc J U e).toNat)) ∧
        ZeroFrom memA ret ∧ ∀ x<heap,memA x=mem x
      refine ⟨by omega,by change ret≤heap+(capacityRoutingSolveSpace J C U+M); omega,?_,?_,hzA,?_⟩
      · exact hgraphS.of_agree_below (h₀ := solveHeap)
          (by rw [J.shortestRoutingGraph.solverWords_length]; change heap+(2+5*M)≤solveHeap; omega) hframeA
      · simpa only [hretA,Nat.add_sub_cancel_right] using hflowA
      · intro x hx
        exact (hframeA x (by omega)).trans (hframeS x hx)
    · simp only [capacityRoutingOptimizeContract,capacityRoutingSolveContract,residualAugmentContract,
        heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,M]
      omega

end MinCostFlow.Scaling.Machine
