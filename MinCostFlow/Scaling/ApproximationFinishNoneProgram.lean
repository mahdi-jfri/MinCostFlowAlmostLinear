module

public import MinCostFlow.Scaling.ApproximationFinishContract
import MinCostFlow.Scaling.CycleCandidateProgram
import MinCostFlow.Scaling.CycleCandidateResult
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Finishing an unsuccessful bottleneck search

When the exact search header has no retained flow, invoke the candidate
constructor on an empty index list and zero amount. Its flow and objective
are zero, exactly as in the approximation model's first branch.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- An unsuccessful search returns the exact zero approximation, preserving
the old heap prefix and using only linear candidate-construction work. -/
theorem approximationFinish_none_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ}
    {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hp : p.HasAt b (approximationFinishModule b)) (J : Circulation) (C U : ℕ)
    (hbest : (bottleneckSearch (canonicalSolver solver entry T hproc) J).value.best=none) :
    MeetsContract w p b (approximationFinishContract w solver entry T hproc J C U) := by
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
  have hmodel : (polyApproxModel (canonicalSolver solver entry T hproc) J).value=
      (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
    simp only [polyApproxModel,hbest]
  have hresultZero : ApproximationResultAt memC (ret-2) ret (⟨fun _ => 0,0⟩ : ApproximationResult J) := by
    simpa only [List.map_nil,Scatter.withWork,Circulation.integerObjective,mul_zero,
      Finset.sum_const_zero,neg_zero,Int.toNat_zero] using hresult
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+10+3*J.n+33*J.m+8 ∧
      ApproximationResultAt memC (ret-2) ret (polyApproxModel (canonicalSolver solver entry T hproc) J).value ∧
      ZeroFrom memC ret ∧ ∀ x<heap,memC x=mem x
    rw [hmodel]
    exact ⟨by omega,by omega,hresultZero,hzero,hframe⟩
  · simp only [approximationFinishContract,cycleCandidateContract,List.length_nil,
      Nat.mul_zero,Nat.add_zero,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.Scaling.Machine
