module

public import MinCostFlow.Scaling.CycleCandidateContract
public import MinCostFlow.Scaling.ApproximationLayout
import MinCostFlow.Scaling.CycleCandidateFacts

/-!
# Reading the integer candidate result

The candidate constructor writes an unsigned table. Its proved cast
identity identifies that table with the model's integer scatter. Hence
the stored header and referenced table give exactly the model's integer
flow and its objective magnitude.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The candidate constructor's memory postcondition is the exact integer
scatter result, represented by the common approximation layout. -/
theorem cycleCandidate_post_result {w lo : ℕ} {J : Circulation} {es : List (Fin J.m)} {u C : ℕ}
    {a ptr heap ret : ℕ} {mem mem' : ℕ → ℕ}
    (hpost : (cycleCandidateContract w lo J es u C).post [a,ptr,u,heap] mem ret mem') :
    let F := (Scatter.withWork (fun _ : Fin J.m => (0 : ℤ)) (es.map (fun e => (e,(u : ℤ))))).1
    ret=heap+5*J.m+4 ∧
    ApproximationResultAt mem' (ret-2) ret (⟨F,(-J.integerObjective F).toNat⟩ : ApproximationResult J) ∧
    ZeroFrom mem' ret ∧ ∀ x<heap,mem' x=mem x := by
  obtain ⟨hret,hflow,hheader,hzero,hframe⟩ := hpost
  change ret=heap+5*J.m+4 at hret
  let f := Scatter.write (fun _ : Fin J.m => (0 : ℕ)) (es.map (fun e => (e,u)))
  have hcast := scatter_constant_cast es u
  refine ⟨hret,?_,hzero,hframe⟩
  rw [←hcast]
  exact approximationResultAt_of_unsigned hheader (by change heap+J.m≤ret; omega) hflow

end MinCostFlow.Scaling.Machine
