module

public import MinCostFlow.Scaling.PolyApproxContract
import MinCostFlow.Scaling.BottleneckSearchProgram
import MinCostFlow.Scaling.ApproximationFinishProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Executing the complete bottleneck approximation

The search produces its exact model state in the final five words of its
heap. The finishing entry consumes that header and its retained flow.
The combined reserve covers both allocations, and both entries preserve
the original graph prefix. Their costs add with constant call overhead.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The complete machine approximation computes precisely `polyApproxModel`
with the actual canonical solver, charging search and linear finishing. -/
theorem polyApprox_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (polyApproxModule solver entry b))
    (J : Circulation) (C U : ℕ) (hc : J.CostsBounded (J.m^10)) (hC : J.CostsBounded C) :
    MeetsContract w p b (polyApproxContract w solver entry T hproc J C U) := by
  have ht := hasAt_tail hp
  have hkS := bottleneckSearch_meetsContract (w := w) hproc hdet J C hc hC (hasAt_append_left ht)
  have hkF := approximationFinish_meetsContract (w := w) hproc (hasAt_append_right ht) J C U hc
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hsearch,hcapacities,hspace,hbudget,hproduct,hw⟩ := hpre
  have hsearchCopy := hsearch
  obtain ⟨⟨a',heap',hargs,hgraph,hgraphEnd,hinput,hsmall,hmass,hguest,hwSearch⟩,hz,hs⟩ := hsearchCopy
  have heq : a=a' ∧ heap=heap' := by simpa only [List.cons.injEq,and_true] using hargs
  obtain ⟨rfl,rfl⟩ := heq
  have ha : a<2^w := by rw [J.solverWords_length] at hgraphEnd; omega
  have hh : heap<2^w := by omega
  apply runs_start_le
  unfold polyApproxBody
  refine runs_seq_call_le hkS (vs := [a,heap]) (by eval_expr) hwords hsearch ?_
  intro searchEnd memS posS hpostS
  obtain ⟨⟨_,hhi,hframeS,hzS,_⟩,hlo,hstateS,hheaderS,hbestS⟩ := hpostS
  change searchEnd≤heap+bottleneckSearchSpace J at hhi
  change heap+5≤searchEnd at hlo
  change (∀ x<heap,memS x=mem x) at hframeS
  change ZeroFrom memS searchEnd at hzS
  change BottleneckStateAt memS (searchEnd-5)
    (bottleneckSearch (canonicalSolver solver entry T hproc) J).value at hstateS
  change (∀ i<5,memS (searchEnd-5+i)<2^w) at hheaderS
  change (∀ u flow,(bottleneckSearch (canonicalSolver solver entry T hproc) J).value.best=some (u,flow) →
    memS (searchEnd-5+4)+J.m≤searchEnd) at hbestS
  have hsearchEndWord : searchEnd<2^w := by omega
  have hstateWord : searchEnd-5<2^w := by omega
  have hgraphS : ListAt memS a J.solverWords := hgraph.of_agree_below (h₀ := heap) hgraphEnd hframeS
  refine runs_seq_assign_le (v := searchEnd-5) (by eval_expr) ?_
  refine runs_seq_call_le hkF (vs := [a,searchEnd-5,searchEnd]) (by eval_expr) (by wram_words)
    ⟨a,searchEnd-5,searchEnd,rfl,hgraphS,by omega,by omega,hstateS,hheaderS,hbestS,
      hinput,hC,hcapacities,hzS,by omega,hbudget,hproduct,hw⟩ ?_
  intro ret memF posF hpostF
  obtain ⟨hloF,hhiF,hresultF,hzF,hframeF⟩ := hpostF
  change searchEnd≤ret at hloF
  change ret≤searchEnd+10+3*J.n+33*J.m+8 at hhiF
  change (∀ x<searchEnd,memF x=memS x) at hframeF
  refine runs_ret_le (v := ret) (Expr.eval_reg_of_eq (by rfl)) ?_ ?_
  · change heap≤ret ∧ ret≤heap+bottleneckSearchSpace J+10+3*J.n+33*J.m+8 ∧
      ApproximationResultAt memF (ret-2) ret (polyApproxModel (canonicalSolver solver entry T hproc) J).value ∧
      ZeroFrom memF ret ∧ ∀ x<heap,memF x=mem x
    refine ⟨by omega,by omega,hresultF,hzF,?_⟩
    intro x hx
    exact (hframeF x (by omega)).trans (hframeS x hx)
  · simp only [polyApproxContract,approximationFinishContract,startState,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.Scaling.Machine
