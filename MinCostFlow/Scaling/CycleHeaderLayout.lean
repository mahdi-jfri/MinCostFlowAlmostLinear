module

public import MinCostFlow.Scaling.CycleStateLayout

/-!
# Replacing a cycle state's header

A transition first updates its vertex tables and list nodes, then writes
the nine header words. The header writer leaves every table and immutable
node unchanged. This lemma assembles the exact new model state from those
separately established representations.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A new header and preserved table/node suffix represent the supplied
cycle state exactly. All arguments are data representations. -/
theorem cycleStateAt_of_header {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound candidates stack edges flag result : ℕ} (s : Circulation.CycleState J)
    (hheader : ListAt mem' base [cycleModeTag s.mode,cycleModeVertex s.mode,candidates,stack,edges,
      if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result])
    (hcandidates : IndexListAt mem (cycleNodes J.n base) bound candidates s.candidates)
    (hstack : IndexListAt mem (cycleNodes J.n base) bound stack s.stack)
    (hedges : IndexListAt mem (cycleNodes J.n base) bound edges s.cycleEdges)
    (hresult : CycleResultAt mem (cycleNodes J.n base) bound flag result s.result)
    (hseen : BoolTableAt mem (cycleSeen base) s.onPath)
    (hout : AdjacencyAt mem (cycleHeads J.n base) (cycleNodes J.n base) bound s.outgoing)
    (hnodes : cycleNodes J.n base≤bound)
    (hframe : ∀ x,base+9≤x → x<bound → mem' x=mem x) : CycleStateAt mem' base bound s := by
  have hnodeFrame : ∀ x,cycleNodes J.n base≤x → x<bound → mem' x=mem x := by
    intro x hx hxend
    exact hframe x (by dsimp only [cycleNodes] at hx; omega) hxend
  refine ⟨candidates,stack,edges,flag,result,hheader,hcandidates.of_agree hnodeFrame,
    hstack.of_agree hnodeFrame,hedges.of_agree hnodeFrame,?_,?_,?_⟩
  · cases hr : s.result with
    | none => simpa only [CycleResultAt,hr] using hresult
    | some es =>
      simp only [CycleResultAt,hr] at hresult
      exact ⟨hresult.1,hresult.2.of_agree hnodeFrame⟩
  · apply hseen.of_agree
    intro x hx hxend
    exact hframe x (by dsimp only [cycleSeen] at hx; omega)
      (by dsimp only [cycleSeen,cycleNodes] at hxend hnodes; omega)
  · apply hout.of_agree le_rfl ?_ hnodeFrame
    intro x hx hxend
    exact hframe x (by dsimp only [cycleHeads] at hx; omega)
      (by dsimp only [cycleHeads,cycleNodes] at hxend hnodes; omega)

end MinCostFlow.Scaling.Machine
