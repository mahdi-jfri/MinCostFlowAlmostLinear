module

public import MinCostFlow.Scaling.CycleStateLayout
import WordRAM.Memory

/-!
# Assembling the initial cycle-state representation

Adjacency construction supplies outgoing lists and range construction
supplies all candidate edge indices. The unused header and path flags
remain zero. One header store installs the candidate pointer, yielding
exactly `cycleInitial` while preserving every immutable node.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The initialized adjacency, ordered candidate nodes, and zero prefix
combine into the model's complete initial cycle state after one store. -/
theorem cycleStateAt_initial_of_parts (J : Circulation) (flow : Fin J.m → ℤ)
    {mem : ℕ → ℕ} {base bound ptr : ℕ}
    (hzero : ∀ x,base≤x → x<cycleHeads J.n base → mem x=0)
    (hout : AdjacencyAt mem (cycleHeads J.n base) (cycleNodes J.n base) bound (J.buildAdjacency flow))
    (hcandidates : IndexListAt mem (cycleNodes J.n base) bound ptr (List.finRange J.m)) :
    CycleStateAt (Function.update mem (base+2) ptr) base bound (J.cycleInitial flow) := by
  have hheader : ListAt mem base (List.replicate 9 (0 : ℕ)) := by
    intro i hi
    have hi' : i<9 := by simpa only [List.length_replicate] using hi
    rw [hzero (base+i) (by omega) (by dsimp only [cycleHeads]; omega)]
    exact (List.getElem_replicate hi).symm
  have hnew := hheader.set (i := 2) (v := ptr) (by decide)
  have hnodesFrame : ∀ x,cycleNodes J.n base≤x → x<bound →
      Function.update mem (base+2) ptr x=mem x := by
    intro x hx _
    exact Function.update_of_ne (by dsimp only [cycleNodes] at hx; omega) _ _
  refine ⟨ptr,0,0,0,0,hnew,hcandidates.of_agree hnodesFrame,.nil,.nil,rfl,?_,?_⟩
  · intro v
    change Function.update mem (base+2) ptr (cycleSeen base+v.val)=0
    rw [Function.update_of_ne (by dsimp only [cycleSeen]; omega)]
    exact hzero _ (by dsimp only [cycleSeen]; omega)
      (by have hv := v.isLt; dsimp only [cycleSeen,cycleHeads]; omega)
  · apply hout.of_agree le_rfl ?_ hnodesFrame
    intro x hx _
    exact Function.update_of_ne (by dsimp only [cycleHeads] at hx; omega) _ _

end MinCostFlow.Scaling.Machine
