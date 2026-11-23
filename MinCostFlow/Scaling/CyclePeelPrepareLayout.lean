module

public import MinCostFlow.Scaling.CycleStateLayout
public import MinCostFlow.Scaling.SignedAddProgram
public import MinCostFlow.Scaling.IndexListConsProgram
import MinCostFlow.Scaling.CycleStateFrames

/-!
# Preserving the traversal while preparing a peeled edge

Signed addition allocates two cells, and prepending the peeled edge
allocates two more. Both operations preserve the old state and stack
tail. Their postconditions also give the exact extended cycle list and
canonical signed sum needed by the finishing procedure.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The two fresh allocations preserve the old traversal and expose both
prepared values, with an exact four-cell heap increment. -/
theorem cyclePeel_prepared_layout {w : ℕ} {J : Circulation}
    {s : Circulation.CycleState J} {e : Fin J.m} {rest : List (Fin J.m)}
    {mem memA memC : ℕ → ℕ} {base heap tail edges addEnd consEnd : ℕ}
    (hstate : CycleStateAt mem base heap s)
    (htail : IndexListAt mem (cycleNodes J.n base) heap tail rest)
    (hnodes : cycleNodes J.n base≤heap)
    (hadd : (signedAddContract w s.cycleCost (J.cost e)).post
      [if s.cycleCost<0 then 1 else 0,s.cycleCost.natAbs,
       if J.cost e<0 then 1 else 0,(J.cost e).natAbs,heap] mem addEnd memA)
    (hcons : (indexListConsContract w (cycleNodes J.n base) e s.cycleEdges).post
      [e.val,edges,addEnd] memA consEnd memC) :
    consEnd=heap+4 ∧ CycleStateAt memC base (heap+4) s ∧
    IndexListAt memC (cycleNodes J.n base) (heap+4) tail rest ∧
    IndexListAt memC (cycleNodes J.n base) (heap+4) (heap+2) (e::s.cycleEdges) ∧
    ListAt memC heap (encodeInt (s.cycleCost+J.cost e)) ∧
    ZeroFrom memC (heap+4) ∧ (∀ x<heap,memC x=mem x) := by
  obtain ⟨⟨_,_,hframeA,hzeroA,hsum⟩,haddEnd⟩ := hadd
  change addEnd=heap+2 at haddEnd
  subst addEnd
  change ∀ x<heap,memA x=mem x at hframeA
  change ListAt memA heap (encodeInt (s.cycleCost+J.cost e)) at hsum
  obtain ⟨⟨_,_,hframeC,hzeroC,hcycle⟩,hconsEnd⟩ := hcons
  change consEnd=heap+2+2 at hconsEnd
  have hend : consEnd=heap+4 := by omega
  subst consEnd
  change ∀ x<heap+2,memC x=memA x at hframeC
  change ZeroFrom memC (heap+4) at hzeroC
  change IndexListAt memC (cycleNodes J.n base) (heap+2+2) (heap+2) (e::s.cycleEdges) at hcycle
  have hframe : ∀ x<heap,memC x=mem x := fun x hx =>
    (hframeC x (by omega)).trans (hframeA x hx)
  refine ⟨rfl,?_,(htail.of_agree (fun x _ hx => hframe x hx)).mono le_rfl (by omega),
    by simpa only [Nat.add_assoc,Nat.reduceAdd] using hcycle,?_,hzeroC,hframe⟩
  · exact hstate.of_agree_below hnodes (by omega) hframe
  · intro i hi
    have hi' : i<2 := by simpa only [encodeInt,List.length_cons,List.length_nil] using hi
    exact (hframeC _ (by omega)).trans (hsum i hi)

end MinCostFlow.Scaling.Machine
