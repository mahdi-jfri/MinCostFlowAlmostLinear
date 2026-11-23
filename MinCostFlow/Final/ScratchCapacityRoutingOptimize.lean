module

public import MinCostFlow.Final.ScratchCapacityRoutingSolve
public import MinCostFlow.Scaling.CapacityRoutingOptimizeContract
import Mathlib.Tactic.ClearExclamation
import MinCostFlow.Scaling.CapacityRoutingSolveProgram
import MinCostFlow.Scaling.CapacityScalingCorrectness
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import MinCostFlow.Scaling.RoutingCorrectionBounds
import MinCostFlow.Scaling.RoutingResidualBounds
import WordRAM.Tactic

/-!
# Augmenting the capacity-backed routing

The exact correction returned by the widened capacity solver gives
the signed forward and reverse amounts for the augmentation.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- The correction in the measured dual model's actual inner capacity call. -/
noncomputable def scratchCapacityRoutingCorrection (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) (U : ℕ) :
    Fin ((J.m+J.n)+(J.m+J.n)) → ℤ :=
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  (Q.invokePositive (fun K => capacityScalingModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)) K U)).value

/-- The measured model augments its direct routing by forward minus reverse correction. -/
noncomputable def scratchCapacitySolvedRouting (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) (U : ℕ) :
    Fin (J.m+J.n) → ℤ :=
  let delta := scratchCapacityRoutingCorrection solver entry T S c d hproc J U
  fun e => J.shortestRoutingStart e+delta (Fin.castAdd (J.m+J.n) e)-delta (Fin.natAdd (J.m+J.n) e)

/-- The actual routing correction is optimal under the routing input's
polynomial cost bound and its supplied capacity bound. -/
theorem scratchCapacityRoutingCorrection_optimal (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) (U : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hu : J.n+1≤U) :
    (J.shortestRoutingGraph.residual J.shortestRoutingStart).Optimal
      (fun e => (scratchCapacityRoutingCorrection solver entry T S c d hproc J U e : ℝ)) := by
  let solve := (fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver entry T S (hproc K) K)
  let Q := J.shortestRoutingGraph.residual J.shortestRoutingStart
  have hsolve := fun K (_ : K.CostsBounded (K.m^10))
    (_ : ∀ e,1≤K.capacity e ∧ K.capacity e≤K.m^40) => compressedCanonicalSolverAt_optimal _ solver entry T S (hproc K) K
  have hcap : ∀ e,Q.capacity e≤U := by
    have h := J.shortestRoutingGraph.residual_capacities_le J.shortestRoutingStart
      J.shortestRoutingStart_bounds (J.n+1) J.shortestRoutingGraph_capacities
    exact fun e => (h e).trans hu
  have hposCap := Q.positiveInstance_capacitiesBounded U (by omega) hcap
  have hposCost := Q.positiveInstance_costsBounded _ (routingResidual_cost_bound J hc)
  have hopt := lemma_C_9 solve hsolve Q.positiveInstance U hposCost (fun e => (hposCap e).2)
  exact Circulation.solveWithZeroCapacities_of_optimal (fun K => (capacityScalingModel solve K U).value) Q hopt

/-- The model's actual augmented routing lies within its graph's capacities. -/
theorem scratchCapacitySolvedRouting_bounds (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) (U : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hu : J.n+1≤U) :
    ∀ e,0≤scratchCapacitySolvedRouting solver entry T S c d hproc J U e ∧
      scratchCapacitySolvedRouting solver entry T S c d hproc J U e≤(J.shortestRoutingGraph.capacity e : ℤ) :=
  (routingCorrection_bounds J _ (scratchCapacityRoutingCorrection_optimal solver entry T S c d hproc J U hc hu).1).2

/-- A fitting `n+2` budget covers every intermediate unsigned augmentation
sum for the actual capacity-model correction. -/
theorem scratchCapacitySolvedRouting_scan_bounds (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S)) (J : Circulation) (U w : ℕ)
    (hc : J.CostsBounded (J.m^10)) (hu : J.n+1≤U) (hw : J.n+2<2^w) :
    let delta := scratchCapacityRoutingCorrection solver entry T S c d hproc J U
    ∀ e,(J.shortestRoutingStart e).toNat+(delta (Fin.castAdd (J.m+J.n) e)).toNat<2^w ∧
      (delta (Fin.natAdd (J.m+J.n) e)).toNat<2^w :=
  routingCorrection_scan_bounds J w _ (scratchCapacityRoutingCorrection_optimal solver entry T S c d hproc J U hc hu).1 hw

/-- The complete capacity-backed residual solve followed by augmentation. -/
def scratchCapacityRoutingOptimizeModule (solver : Program) (entry b c d : ℕ) : List Stmt :=
  let aug := b+1+(scratchCapacityRoutingSolveModule solver entry (b+1) c d).length
  capacityRoutingOptimizeBody (b+1) aug ::
    (scratchCapacityRoutingSolveModule solver entry (b+1) c d ++ residualAugmentModule aug)

/-- The capacity-backed solve reserve followed by one routing coordinate per edge. -/
def scratchCapacityRoutingOptimizeSpace (c d : ℕ) (J : Circulation) (C U : ℕ) : ℕ :=
  scratchCapacityRoutingSolveSpace c d J C U+(J.m+J.n)

/-- Retain the source-routing graph at the original heap and return its
exact model routing in the final `m+n` words. -/
noncomputable def scratchCapacityRoutingOptimizeContract (w : ℕ) (solver : Program) (entry : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (C U : ℕ) : Contract :=
  let M := J.m+J.n
  { pre := fun args mem => ∃ a heap,args=[a,U,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length≤heap ∧ (∀ x∈J.solverWords,x<2^w) ∧ J.CostsBounded C ∧
      J.n+1≤U ∧ J.n+2<2^w ∧ ZeroFrom mem heap ∧ heap+scratchCapacityRoutingOptimizeSpace c d J C U<2^w
    post := fun args mem ret mem' => heapArg args+4+17*M≤ret ∧
      ret≤heapArg args+scratchCapacityRoutingOptimizeSpace c d J C U ∧
      ListAt mem' (heapArg args) J.shortestRoutingGraph.solverWords ∧
      ListAt mem' (ret-M) (List.ofFn (fun e => (scratchCapacitySolvedRouting solver entry T S c d hproc J U e).toNat)) ∧
      ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
    cost := fun _ _ => (scratchCapacityRoutingSolveContract w solver entry T S c d hproc J C U).cost [] (fun _ => 0)+
      100*M+300 }

/-- Solving and augmenting the routing uses no random instruction. -/
theorem scratchCapacityRoutingOptimizeModule_noRand (solver : Program) (entry b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityRoutingOptimizeModule solver entry b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoutingOptimizeBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hs | ha
    · exact scratchCapacityRoutingSolveModule_noRand solver entry _ c d hdet body hs
    · exact residualAugmentModule_noRand _ body ha

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
theorem scratchCapacityRoutingOptimize_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver entry (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hScratch : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityRoutingOptimizeModule solver entry b c d))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityRoutingOptimizeContract w solver entry T S c d hproc J C U) := by
  let M := J.m+J.n
  let start := J.shortestRoutingStart
  let delta := scratchCapacityRoutingCorrection solver entry T S c d hproc J U
  have ht := hasAt_tail hp
  have hS := hasAt_append_left ht
  have hA := hasAt_append_right ht
  have hkS := scratchCapacityRoutingSolve_meetsContract (w := w) hproc hScratch hdet hS J C U hc
  have hkA := residualAugment_meetsContract (w := w) hA start delta
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hgraph,hgraphEnd,hinput,hC,hu,hn2,hz,hs⟩ := hpre
  have hspace : heap+(scratchCapacityRoutingSolveSpace c d J C U+M)<2^w := hs
  have hsolveSpace : heap+scratchCapacityRoutingSolveSpace c d J C U<2^w := by omega
  have hbaseSpace : heap+(4+16*M)<2^w := by
    change heap+(4+16*M+scratchCapacityPositiveSpace c d _ C U+M)<2^w at hspace
    omega
  have h8 : 8<2^w := by
    dsimp only [scratchCapacityRoutingOptimizeSpace,scratchCapacityRoutingSolveSpace,scratchCapacityPositiveSpace,scratchCapacityScalingSpace] at hs
    omega
  have hh : heap<2^w := by omega
  have hn : J.n<2^w := by omega
  have hm : J.m<2^w := by dsimp only [M] at hbaseSpace; omega
  have hMword : M<2^w := by omega
  have hsum : J.n+J.m=M := by dsimp only [M]; omega
  have ha1 : a+1<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  obtain ⟨hN,hM⟩ := solver_header_at J hgraph
  have hdeltaOpt := scratchCapacityRoutingCorrection_optimal solver entry T S c d hproc J U hc hu
  have hdelta : ∀ e,0≤delta e := fun e => Int.cast_nonneg_iff.mp (hdeltaOpt.1.2 e).1
  have hstart : ∀ e,0≤start e := fun e => Int.cast_nonneg_iff.mp (J.shortestRoutingStart_bounds e).1
  have hupdate : ∀ e,0≤start e+delta (Fin.castAdd M e)-delta (Fin.natAdd M e) :=
    fun e => (scratchCapacitySolvedRouting_bounds solver entry T S c d hproc J U hc hu e).1
  have hscan := scratchCapacitySolvedRouting_scan_bounds solver entry T S c d hproc J U w hc hu hn2
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
    change solveHeap≤heap+scratchCapacityRoutingSolveSpace c d J C U at hhiS
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
    change ListAt memA solveHeap (List.ofFn (fun e => (scratchCapacitySolvedRouting solver entry T S c d hproc J U e).toNat)) at hflowA
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap+4+17*M≤ret ∧ ret≤heap+scratchCapacityRoutingOptimizeSpace c d J C U ∧
        ListAt memA heap J.shortestRoutingGraph.solverWords ∧
        ListAt memA (ret-M) (List.ofFn (fun e => (scratchCapacitySolvedRouting solver entry T S c d hproc J U e).toNat)) ∧
        ZeroFrom memA ret ∧ ∀ x<heap,memA x=mem x
      refine ⟨by omega,by change ret≤heap+(scratchCapacityRoutingSolveSpace c d J C U+M); omega,?_,?_,hzA,?_⟩
      · exact hgraphS.of_agree_below (h₀ := solveHeap)
          (by rw [J.shortestRoutingGraph.solverWords_length]; change heap+(2+5*M)≤solveHeap; omega) hframeA
      · simpa only [hretA,Nat.add_sub_cancel_right] using hflowA
      · intro x hx
        exact (hframeA x (by omega)).trans (hframeS x hx)
    · simp only [scratchCapacityRoutingOptimizeContract,scratchCapacityRoutingSolveContract,residualAugmentContract,
        heapContract,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,M]
      omega

end MinCostFlow.Final
