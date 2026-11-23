module

public import MinCostFlow.Scaling.CycleStateLayout

/-!
# Updating cycle-state vertex tables

Walking removes one outgoing entry and may mark a new path vertex.
Those table stores preserve the header and immutable list nodes. Fresh
cons allocation can enlarge the node range. The lemmas below transfer the
unchanged state fields through these operations.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Preserving old node cells preserves an optional cycle result while
fresh allocation may enlarge the allowed node range. -/
theorem CycleResultAt.of_agree {m : ℕ} {mem mem' : ℕ → ℕ} {lo bound bound' flag ptr : ℕ}
    {result : Option (List (Fin m))} (hat : CycleResultAt mem lo bound flag ptr result)
    (hbound : bound≤bound') (hframe : ∀ x,lo≤x → x<bound → mem' x=mem x) :
    CycleResultAt mem' lo bound' flag ptr result := by
  cases result with
  | none => exact hat
  | some es => exact ⟨hat.1,(hat.2.of_agree hframe).mono le_rfl hbound⟩

/-- Replacing the represented path flags and outgoing table preserves all
other state fields when the header and immutable nodes are unchanged. -/
theorem CycleStateAt.with_tables {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : Circulation.CycleState J}
    (hat : CycleStateAt mem base bound s) (seen : Fin J.n → Bool) (out : Fin J.n → List (Fin J.m))
    (hbound : bound≤bound') (hseen : BoolTableAt mem' (cycleSeen base) seen)
    (hout : AdjacencyAt mem' (cycleHeads J.n base) (cycleNodes J.n base) bound' out)
    (hheader : ∀ x,base≤x → x<base+9 → mem' x=mem x)
    (hnodes : ∀ x,cycleNodes J.n base≤x → x<bound → mem' x=mem x) :
    CycleStateAt mem' base bound' {s with onPath:=seen,outgoing:=out} := by
  obtain ⟨candidates,stack,edges,flag,result,hstored,hcandidates,hstack,hedges,hresult,_,_⟩ := hat
  refine ⟨candidates,stack,edges,flag,result,?_,
    (hcandidates.of_agree hnodes).mono le_rfl hbound,
    (hstack.of_agree hnodes).mono le_rfl hbound,
    (hedges.of_agree hnodes).mono le_rfl hbound,
    hresult.of_agree hbound hnodes,hseen,hout⟩
  intro i hi
  have hi' : i<9 := hi
  exact (hheader _ (by omega) (by omega)).trans (hstored i hi)

end MinCostFlow.Scaling.Machine
