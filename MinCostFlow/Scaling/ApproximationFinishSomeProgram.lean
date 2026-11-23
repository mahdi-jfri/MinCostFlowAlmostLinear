module

public import MinCostFlow.Scaling.ApproximationFinishContract
import MinCostFlow.Scaling.BottleneckBestBounds
import MinCostFlow.Scaling.ExtractCycleProgram
import MinCostFlow.Scaling.CycleCandidateProgram
import MinCostFlow.Scaling.CycleCandidateResult
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Finishing a retained bottleneck flow

The retained result is the exact unit optimum from the search. Its
nonnegative unit coordinates supply the extraction input bounds. Read
the extraction result flag, then construct either the scattered cycle
candidate or the zero candidate, as in the two remaining model branches.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A retained threshold flow is scanned and assembled into exactly the
model's approximation result with a linear finishing cost. -/
theorem approximationFinish_some_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hp : p.HasAt b (approximationFinishModule b)) (J : Circulation) (C U : ℕ)
    (hc : J.CostsBounded (J.m^10)) (u : ℕ) (flow : Fin J.m → ℤ)
    (hbest : (bottleneckSearch (canonicalSolver solver entry T hproc) J).value.best=some (u,flow)) :
    MeetsContract w p b (approximationFinishContract w solver entry T hproc J C U) := by
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
  obtain ⟨huBound,hunit⟩ := bottleneckSearch_best_bounds solver entry T hproc J U hc hcapacities u flow hbest
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
    have hmodel : (polyApproxModel (canonicalSolver solver entry T hproc) J).value=
        (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
      simp only [polyApproxModel,hbest,hcycle]
    have hresultZero : ApproximationResultAt memC (ret-2) ret (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
      simpa only [List.map_nil,Scatter.withWork,Circulation.integerObjective,mul_zero,
        Finset.sum_const_zero,neg_zero,Int.toNat_zero] using hresultC
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+10+3*J.n+33*J.m+8 ∧
        ApproximationResultAt memC (ret-2) ret (polyApproxModel (canonicalSolver solver entry T hproc) J).value ∧
        ZeroFrom memC ret ∧ ∀ x<heap,memC x=mem x
      rw [hmodel]
      refine ⟨by omega,by omega,hresultZero,hzeroC,?_⟩
      intro x hx
      exact (hframeC x (by omega)).trans (hframeE x hx)
    · simp only [approximationFinishContract,extractCycleContract,cycleCandidateContract,List.length_nil,
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
    have hmodel : (polyApproxModel (canonicalSolver solver entry T hproc) J).value=
        (⟨(Scatter.withWork (fun _ : Fin J.m => (0 : ℤ)) (es.map (fun e => (e,(u : ℤ))))).1,
          (-J.integerObjective (Scatter.withWork (fun _ : Fin J.m => (0 : ℤ)) (es.map (fun e => (e,(u : ℤ))))).1).toNat⟩ :
          ApproximationResult J) := by
      simp only [polyApproxModel,hbest,hcycle]
    refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
    · change heap≤ret ∧ ret≤heap+10+3*J.n+33*J.m+8 ∧
        ApproximationResultAt memC (ret-2) ret (polyApproxModel (canonicalSolver solver entry T hproc) J).value ∧
        ZeroFrom memC ret ∧ ∀ x<heap,memC x=mem x
      rw [hmodel]
      refine ⟨by omega,by omega,hresultC,hzeroC,?_⟩
      intro x hx
      exact (hframeC x (by omega)).trans (hframeE x hx)
    · simp only [approximationFinishContract,extractCycleContract,cycleCandidateContract,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
      omega

end MinCostFlow.Scaling.Machine
