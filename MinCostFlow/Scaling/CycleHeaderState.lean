module

public import MinCostFlow.Scaling.CycleHeaderLayout
public import MinCostFlow.Scaling.CycleHeaderProgram

/-!
# Logical state after a cycle-header procedure call

Apply the header writer's exact frame to the already prepared immutable
lists and vertex tables. The fresh tail stays zero, and every output
header word fits. This is used after each cycle-mode transition.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Prepared state data and the concrete header procedure's postcondition
supply the complete stored state, zero tail, frame, and fitting words. -/
theorem cycleHeader_post_state (w : ℕ) {J : Circulation} (s : Circulation.CycleState J)
    {mem mem' : ℕ → ℕ} {base heap candidates stack edges flag result ret : ℕ}
    (hcandidates : IndexListAt mem (cycleNodes J.n base) heap candidates s.candidates)
    (hstack : IndexListAt mem (cycleNodes J.n base) heap stack s.stack)
    (hedges : IndexListAt mem (cycleNodes J.n base) heap edges s.cycleEdges)
    (hresult : CycleResultAt mem (cycleNodes J.n base) heap flag result s.result)
    (hseen : BoolTableAt mem (cycleSeen base) s.onPath)
    (hout : AdjacencyAt mem (cycleHeads J.n base) (cycleNodes J.n base) heap s.outgoing)
    (hnodes : cycleNodes J.n base≤heap) (hz : ZeroFrom mem heap)
    (hpost : (cycleHeaderContract w).post
      [cycleModeTag s.mode,cycleModeVertex s.mode,candidates,stack,edges,
        if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result,base] mem ret mem') :
    CycleStateAt mem' base heap s ∧ ZeroFrom mem' heap ∧
      (∀ x,x<base ∨ base+9≤x → mem' x=mem x) ∧ (∀ i<9,mem' (base+i)<2^w) := by
  obtain ⟨_,hheader,hframe,hwords⟩ := hpost
  change ListAt mem' base [cycleModeTag s.mode,cycleModeVertex s.mode,candidates,stack,edges,
    if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,flag,result] at hheader
  change (∀ x,x<base ∨ base+9≤x → mem' x=mem x) at hframe
  change (∀ i<9,mem' (base+i)<2^w) at hwords
  refine ⟨cycleStateAt_of_header s hheader hcandidates hstack hedges hresult hseen hout hnodes
    (fun x hx _ => hframe x (Or.inr hx)),?_,hframe,hwords⟩
  intro x hx
  rw [hframe x (Or.inr (by dsimp only [cycleNodes] at hnodes; omega))]
  exact hz x hx

end MinCostFlow.Scaling.Machine
