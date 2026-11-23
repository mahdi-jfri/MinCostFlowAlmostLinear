module

public import MinCostFlow.Scaling.ApproximationFinishContract
import MinCostFlow.Scaling.BottleneckSelection
import MinCostFlow.Scaling.ExtractCycleProgram
import MinCostFlow.Scaling.CycleCandidateProgram
import MinCostFlow.Scaling.CycleCandidateResult
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Finishing the bottleneck approximation for a given solver

The finish routine extracts and scatters a cycle from the retained
unit flow. Its correctness uses the solver's mathematical optimality,
so it does not depend on the policy for guest memory.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- A retained result has bounded threshold and nonnegative unit flow,
using only the actual canonical solver's established optimality. -/
theorem withSolverBottleneckSearch_best_bounds (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ K : Circulation, K.CostsBounded (K.m^10) →
      (∀ e, 1 ≤ K.capacity e ∧ K.capacity e ≤ K.m^40) →
      K.Optimal (fun e => (solve K e : ℝ)))
    (J : Circulation) (U : ℕ) (hc : J.CostsBounded (J.m^10))
    (hu : ∀ e,J.capacity e≤U) (u : ℕ) (flow : Fin J.m → ℤ)
    (hbest : (bottleneckSearch solve J).value.best=some (u,flow)) :
    u≤U ∧ ∀ e,0≤flow e ∧ (flow e).toNat≤1 := by
  let candidates := (sortCapacities (List.ofFn J.capacity)).1
  let s := (bottleneckSearch solve J).value
  have hselection := bottleneckSearch_selection solve hsolve J hc
  have hb := hselection.2.2.2
  change (match s.best with | none => _ | some (u,flow) => _) at hb
  rw [hbest] at hb
  have hindex : s.lower-1<candidates.length := by
    have hsame : s.lower=s.upper := hselection.1
    have hend : s.upper≤candidates.length := hselection.2.1
    have hpos : 0<s.lower := hb.1
    omega
  have hmem : u∈candidates := by
    rw [hb.2.1]
    change candidates.getD (s.lower-1) 0∈candidates
    simpa only [List.getD,List.getElem?_eq_getElem hindex,Option.getD_some] using List.getElem_mem hindex
  have hcapacity : ∃ e : Fin J.m,J.capacity e=u :=
    List.mem_ofFn.mp ((sortCapacities_perm _).mem_iff.mp hmem)
  refine ⟨?_,?_⟩
  · obtain ⟨e,he⟩ := hcapacity
    rw [←he]
    exact hu e
  · have hopt := J.bottleneckTest_optimal solve hsolve hc u
    rw [←hb.2.2.1] at hopt
    intro e
    have hlo : 0≤flow e := Int.cast_le.mp (by simpa only [Int.cast_zero] using (hopt.1.2 e).1)
    have hhi : flow e≤((J.bottleneckGraph u).capacity e : ℤ) :=
      Int.cast_le.mp (by simpa only [Int.cast_natCast] using (hopt.1.2 e).2)
    refine ⟨hlo,?_⟩
    have hnat := Int.toNat_le_toNat hhi
    simp only [Int.toNat_natCast] at hnat
    exact hnat.trans (J.bottleneckGraph_capacities u e)

/-- The retained search header is the actual model header. All other
premises describe represented data and numerical reserves. -/
noncomputable def withSolverApproximationFinishContract (w : ℕ) (solve : (J : Circulation) → Fin J.m → ℤ)
    (J : Circulation) (C U : ℕ) : Contract where
  pre args mem := ∃ a state heap,args=[a,state,heap] ∧ ListAt mem a J.solverWords ∧
    a+J.solverWords.length≤heap ∧ state+5≤heap ∧
    BottleneckStateAt mem state (bottleneckSearch solve J).value ∧
    (∀ i<5,mem (state+i)<2^w) ∧
    (∀ u flow,(bottleneckSearch solve J).value.best=some (u,flow) →
      mem (state+4)+J.m≤heap) ∧
    (∀ x ∈ J.solverWords,x<2^w) ∧ J.CostsBounded C ∧ (∀ e,J.capacity e≤U) ∧
    ZeroFrom mem heap ∧ heap+10+3*J.n+33*J.m+12<2^w ∧
    (6*J.m+2)*C<2^w ∧ J.m*(C*U)<2^w ∧ 9<2^w
  post args mem ret mem' := heapArg args≤ret ∧
    ret≤heapArg args+10+3*J.n+33*J.m+8 ∧
    ApproximationResultAt mem' (ret-2) ret
      (polyApproxModel solve J).value ∧
    ZeroFrom mem' ret ∧ ∀ x<heapArg args,mem' x=mem x
  cost _ _ := 9000*(J.m+1)

/-- An unsuccessful search returns the exact zero approximation, preserving
the old heap prefix and using only linear candidate-construction work. -/
theorem withSolverApproximationFinish_none_meetsContract {w b : ℕ} {p : Program}
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hp : p.HasAt b (approximationFinishModule b)) (J : Circulation) (C U : ℕ)
    (hbest : (bottleneckSearch solve J).value.best=none) :
    MeetsContract w p b (withSolverApproximationFinishContract w solve J C U) := by
  have hkC := cycleCandidate_meetsContract (w := w) (lo := 0)
    (hasAt_append_right (hasAt_tail hp)) J [] 0 C
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hheader,hbestEnd,hinput,hcosts,
    hcapacities,hz,hspace,hbudget,hproduct,hw⟩ := hpre
  obtain ⟨_,_,hflag⟩ := hstate
  rw [hbest] at hflag
  have hs2 : state+2<2^w := by omega
  have hh : heap<2^w := by omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  apply runs_start_le
  unfold approximationFinishBody
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  wram_step
  unfold approximationZeroCall
  refine runs_seq_call_le hkC (vs := [a,0,0,heap]) (by eval_expr) (by wram_words)
    ⟨a,0,heap,rfl,hgraph,hgraphEnd,.nil,hinput,hcosts,by omega,hz,by omega,by omega⟩ ?_
  intro ret memC posC hpostC
  obtain ⟨hret,hresult,hzero,hframe⟩ := cycleCandidate_post_result hpostC
  have hmodel : (polyApproxModel solve J).value=
      (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
    simp only [polyApproxModel,hbest]
  have hresultZero : ApproximationResultAt memC (ret-2) ret (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
    simpa only [List.map_nil,Scatter.withWork,Circulation.integerObjective,mul_zero,
      Finset.sum_const_zero,neg_zero,Int.toNat_zero] using hresult
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+10+3*J.n+33*J.m+8 ∧
      ApproximationResultAt memC (ret-2) ret (polyApproxModel solve J).value ∧
      ZeroFrom memC ret ∧ ∀ x<heap,memC x=mem x
    rw [hmodel]
    exact ⟨by omega,by omega,hresultZero,hzero,hframe⟩
  · simp only [withSolverApproximationFinishContract,cycleCandidateContract,List.length_nil,
      Nat.mul_zero,Nat.add_zero,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    omega

/-- A retained threshold flow is scanned and assembled into exactly the
model's approximation result with a linear finishing cost. -/
theorem withSolverApproximationFinish_some_meetsContract {w b : ℕ} {p : Program}
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ K : Circulation, K.CostsBounded (K.m^10) →
      (∀ e, 1 ≤ K.capacity e ∧ K.capacity e ≤ K.m^40) →
      K.Optimal (fun e => (solve K e : ℝ)))
    (hp : p.HasAt b (approximationFinishModule b)) (J : Circulation) (C U : ℕ)
    (hc : J.CostsBounded (J.m^10)) (u : ℕ) (flow : Fin J.m → ℤ)
    (hbest : (bottleneckSearch solve J).value.best=some (u,flow)) :
    MeetsContract w p b (withSolverApproximationFinishContract w solve J C U) := by
  have ht := hasAt_tail hp
  have hExtract := hasAt_append_left ht
  have hCandidate := hasAt_append_right ht
  have hkE := extractCycle_meetsContract (w := w) hExtract J flow C
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,state,heap,rfl,hgraph,hgraphEnd,hstateEnd,hstate,hheader,hbestEnd,hinput,hcosts,
    hcapacities,hz,hspace,hbudget,hproduct,hw⟩ := hpre
  obtain ⟨hflag,hthreshold,hflow⟩ := hstate.best_table hbest
  have hflowEnd := hbestEnd u flow hbest
  obtain ⟨huBound,hunit⟩ := withSolverBottleneckSearch_best_bounds solve hsolve J U hc hcapacities u flow hbest
  have hs2 : state+2<2^w := by omega
  have hs3 : state+3<2^w := by omega
  have hs4 : state+4<2^w := by omega
  have hh : heap<2^w := by omega
  have hh7 : heap+7<2^w := by omega
  have hh8 : heap+8<2^w := by omega
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hu : u<2^w := by rw [←hthreshold]; exact hheader 3 (by decide)
  have hflowPtr : mem (state+4)<2^w := hheader 4 (by decide)
  have hvalues : ∀ e,0≤flow e ∧ (flow e).toNat<2^w := fun e =>
    ⟨(hunit e).1,(hunit e).2.trans_lt (by omega)⟩
  apply runs_start_le
  unfold approximationFinishBody
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
  wram_step
  refine runs_seq_assign_le (v := u) (by eval_expr) ?_
  refine runs_seq_assign_le (v := mem (state+4)) (by eval_expr) ?_
  refine runs_seq_call_le hkE (vs := [a,mem (state+4),heap]) (by eval_expr) (by wram_words)
    ⟨a,mem (state+4),heap,rfl,hgraph,hflow,hgraphEnd,hflowEnd,hvalues,hcosts,hz,by omega,hbudget,hw⟩ ?_
  intro cycleEnd memE posE hpostE
  obtain ⟨hlo,hhi,hstateE,hzE,hframeE,hheaderE⟩ := hpostE
  change cycleNodes J.n heap≤cycleEnd at hlo
  change cycleEnd≤cycleNodes J.n heap+28*J.m+4 at hhi
  change CycleStateAt memE heap cycleEnd (J.extractCycleModel flow).1 at hstateE
  change ZeroFrom memE cycleEnd at hzE
  change (∀ x<heap,memE x=mem x) at hframeE
  have hloNum : heap+10+3*J.n≤cycleEnd := hlo
  have hhiNum : cycleEnd≤heap+10+3*J.n+28*J.m+4 := hhi
  have hcycleEndWord : cycleEnd<2^w := by omega
  have hgraphE : ListAt memE a J.solverWords := hgraph.of_agree_below (h₀ := heap) hgraphEnd hframeE
  obtain ⟨candidates,stack,edges,flag,result,hstored,hcandidates,hstack,hedges,hresult,hseen,hout⟩ := hstateE
  have hflagE : memE (heap+7)=flag := hstored 7 (by change 7<9; decide)
  have hresultE : memE (heap+8)=result := hstored 8 (by change 8<9; decide)
  cases hcycle : (J.extractCycleModel flow).1.result with
  | none =>
    simp only [CycleResultAt,hcycle] at hresult
    subst flag
    have hkC := cycleCandidate_meetsContract (w := w) (lo := 0) hCandidate J [] 0 C
    refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
    wram_step
    unfold approximationZeroCall
    refine runs_seq_call_le hkC (vs := [a,0,0,cycleEnd]) (by eval_expr) (by wram_words)
      ⟨a,0,cycleEnd,rfl,hgraphE,by omega,.nil,hinput,hcosts,by omega,hzE,by omega,by omega⟩ ?_
    intro ret memC posC hpostC
    obtain ⟨hret,hresultC,hzeroC,hframeC⟩ := cycleCandidate_post_result hpostC
    have hmodel : (polyApproxModel solve J).value=
        (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
      simp only [polyApproxModel,hbest,hcycle]
    have hresultZero : ApproximationResultAt memC (ret-2) ret (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
      simpa only [List.map_nil,Scatter.withWork,Circulation.integerObjective,mul_zero,
        Finset.sum_const_zero,neg_zero,Int.toNat_zero] using hresultC
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+10+3*J.n+33*J.m+8 ∧
        ApproximationResultAt memC (ret-2) ret (polyApproxModel solve J).value ∧
        ZeroFrom memC ret ∧ ∀ x<heap,memC x=mem x
      rw [hmodel]
      refine ⟨by omega,by omega,hresultZero,hzeroC,?_⟩
      intro x hx
      exact (hframeC x (by omega)).trans (hframeE x hx)
    · simp only [withSolverApproximationFinishContract,extractCycleContract,cycleCandidateContract,List.length_nil,
        Nat.mul_zero,Nat.add_zero,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega
  | some es =>
    simp only [CycleResultAt,hcycle] at hresult
    obtain ⟨rfl,hlist⟩ := hresult
    have hresultWord : result<2^w := hlist.pointer_le.trans_lt hcycleEndWord
    have hlength := J.extractCycleModel_result_length flow es hcycle
    have hbudgetCandidate : J.m*(C*u)<2^w :=
      (Nat.mul_le_mul_left J.m (Nat.mul_le_mul_left C huBound)).trans_lt hproduct
    have hkC := cycleCandidate_meetsContract (w := w) (lo := cycleNodes J.n heap) hCandidate J es u C
    refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
    wram_step
    refine runs_seq_call_le hkC (vs := [a,result,u,cycleEnd]) (by eval_expr) (by wram_words)
      ⟨a,result,cycleEnd,rfl,hgraphE,by omega,hlist,hinput,hcosts,hbudgetCandidate,hzE,by omega,by omega⟩ ?_
    intro ret memC posC hpostC
    obtain ⟨hret,hresultC,hzeroC,hframeC⟩ := cycleCandidate_post_result hpostC
    have hmodel : (polyApproxModel solve J).value=
        (⟨(Scatter.withWork (fun _ : Fin J.m => (0 : ℤ)) (es.map (fun e => (e,(u : ℤ))))).1,
          (-J.integerObjective (Scatter.withWork (fun _ : Fin J.m => (0 : ℤ)) (es.map (fun e => (e,(u : ℤ))))).1).toNat⟩ :
          ApproximationResult J) := by
      simp only [polyApproxModel,hbest,hcycle]
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+10+3*J.n+33*J.m+8 ∧
        ApproximationResultAt memC (ret-2) ret (polyApproxModel solve J).value ∧
        ZeroFrom memC ret ∧ ∀ x<heap,memC x=mem x
      rw [hmodel]
      refine ⟨by omega,by omega,hresultC,hzeroC,?_⟩
      intro x hx
      exact (hframeC x (by omega)).trans (hframeE x hx)
    · simp only [withSolverApproximationFinishContract,extractCycleContract,cycleCandidateContract,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

/-- Every represented exact search result is completed into the exact
approximation model value at cost at most `9000*(m+1)`. -/
theorem withSolverApproximationFinish_meetsContract {w b : ℕ} {p : Program}
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ K : Circulation, K.CostsBounded (K.m^10) →
      (∀ e, 1 ≤ K.capacity e ∧ K.capacity e ≤ K.m^40) →
      K.Optimal (fun e => (solve K e : ℝ)))
    (hp : p.HasAt b (approximationFinishModule b)) (J : Circulation) (C U : ℕ)
    (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (withSolverApproximationFinishContract w solve J C U) := by
  cases hbest : (bottleneckSearch solve J).value.best with
  | none => exact withSolverApproximationFinish_none_meetsContract solve hp J C U hbest
  | some best =>
    obtain ⟨u,flow⟩ := best
    exact withSolverApproximationFinish_some_meetsContract solve hsolve hp J C U hc u flow hbest

end MinCostFlow.Final
