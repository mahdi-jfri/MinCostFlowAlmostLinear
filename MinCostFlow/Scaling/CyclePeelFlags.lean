module

public import MinCostFlow.Scaling.CycleExtractionModel
import Mathlib.Logic.Function.Basic

/-!
# The peeling step's path-flag update

Peeling clears the edge head's path flag unless it is the target vertex.
Clearing an already false flag changes nothing. Thus performing this
store before the final header update gives exactly the original model
step, including all closed-part and sign cases.
-/

public section
namespace MinCostFlow.Scaling.Circulation.CycleState

/-- A prepared false flag makes the model's conditional path update the
identity, while the target's flag is always left unchanged. -/
theorem peel_seen_eq {J : Circulation} (s : CycleState J) (target : Fin J.n) (e : Fin J.m)
    (hseen : J.head e=target ∨ s.onPath (J.head e)=false) :
    (if J.head e=target then s.onPath else Function.update s.onPath (J.head e) false)=s.onPath := by
  by_cases heq : J.head e=target
  · simp only [heq,↓reduceIte]
  · have hf := hseen.resolve_left heq
    simp only [heq,↓reduceIte]
    rw [←hf]
    exact Function.update_eq_self _ _

/-- Clearing the nontarget head before the rest of peeling leaves the
model's final step unchanged, since its repeated clear is idempotent. -/
theorem peel_step_after_clear {J : Circulation} (s : CycleState J) (target : Fin J.n)
    (e : Fin J.m) (rest : List (Fin J.m)) (hmode : s.mode=.peel target)
    (hstack : s.stack=e::rest) (hhead : J.head e≠target) :
    ({s with onPath:=Function.update s.onPath (J.head e) false} : CycleState J).step=s.step := by
  simp only [step,hmode,hstack,hhead,↓reduceIte,Function.update_idem]

/-- The exact nonempty peeling step after its path flag has been prepared.
Only the closed-part test and the new integer sum's sign remain. -/
theorem peel_step_of_prepared_flag {J : Circulation} (s : CycleState J) (target : Fin J.n)
    (e : Fin J.m) (rest : List (Fin J.m)) (hmode : s.mode=.peel target)
    (hstack : s.stack=e::rest) (hseen : J.head e=target ∨ s.onPath (J.head e)=false) :
    s.step = if J.tail e=target then
      if s.cycleCost+J.cost e<0 then
        {s with mode:=.done,stack:=rest,cycleEdges:=e::s.cycleEdges,cycleCost:=s.cycleCost+J.cost e,result:=some (e::s.cycleEdges)}
      else {s with mode:=.walk target,stack:=rest,cycleEdges:=[],cycleCost:=0}
    else {s with stack:=rest,cycleEdges:=e::s.cycleEdges,cycleCost:=s.cycleCost+J.cost e} := by
  simp only [step,hmode,hstack]
  have h := peel_seen_eq s target e hseen
  rw [h]

end MinCostFlow.Scaling.Circulation.CycleState
