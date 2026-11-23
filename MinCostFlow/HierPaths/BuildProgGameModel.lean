module

public import MinCostFlow.HierPaths.BuildProgGameStep
public import MinCostFlow.HierPaths.BuildChildLoad

/-!
# The active scan and the child-game model

A core call is made only for a child without a saved set. The dense cut list
then selects exactly the requests in the model, in their original order.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Original child numbers, in the order of the active tables. -/
def activeChildren (k : ℕ) (sts : ℕ → ChildState) : List ℕ :=
  (List.range k).filter fun c => (sts c).saved.isNone

/-- The core scan's job list for the current model state. -/
def modelGameJobs (s k : ℕ) (off addr : ℕ → ℕ) (sts : ℕ → ChildState) : BuildGameJobs :=
  let active := activeChildren k sts
  ⟨active.length, fun i => gameGraph s (sts (active.getD i 0)),
    fun i => addr (active.getD i 0), fun i => off (active.getD i 0), none, none⟩

private theorem tabList_getD_eq (l : List ℕ) : tabList l.length (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [tabList, List.getElem?_eq_getElem h₂]

private theorem mem_activeChildren {k c : ℕ} {sts : ℕ → ChildState} :
    c ∈ activeChildren k sts ↔ c < k ∧ (sts c).saved = none := by
  simp [activeChildren]

/-- The cut indices of a dense active table translate to the original requesting children. -/
theorem modelGameJobs_indices (core : ℕ → Graph → CoreResult) (M r s k : ℕ)
    (off addr : ℕ → ℕ) (sts : ℕ → ChildState) :
    (batchJobIndices (modelGameJobs s k off addr sts) core (coreLevel M r s)).map
        (fun i => (activeChildren k sts).getD i 0) = requesting core M r s k off sts := by
  let active := activeChildren k sts
  let ans := fun c => coreAnswer core M r s (sts c)
  let cut := fun c => decide (coreTag (ans c) = 0)
  change ((List.range active.length).filter (fun i => cut (active.getD i 0))).map
    (fun i => active.getD i 0) = _
  have hWords : (List.range active.length).map (fun i => active.getD i 0) = active := tabList_getD_eq _
  change ((List.range active.length).filter (cut ∘ (fun i => active.getD i 0))).map
    (fun i => active.getD i 0) = _
  rw [← List.filter_map (p := cut),hWords]
  unfold active activeChildren requesting
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  cases hs : (sts c).saved <;>
    cases hAns : ans c <;>
    simp [hs,hAns,cut,coreTag,request,ans] at *

/-- A saved child stays saved, so the next active list consists of the requesters. -/
theorem activeChildren_gameRound (route : RouterFn) (G : Graph) (X : Finset ℕ) (Δ L : ℕ)
    (core : ℕ → Graph → CoreResult) (M r s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) :
    activeChildren k (gameRound route G X Δ L core M r s k off sts) =
      requesting core M r s k off sts := by
  unfold activeChildren requesting
  apply List.filter_congr
  intro c _
  cases hs : (sts c).saved <;>
    cases ha : coreAnswer core M r s (sts c) <;> simp [gameRound,request,hs,ha]

/-- The prepared pair family is the exact family passed to the router by the model. -/
theorem modelGameJobs_pairs (core : ℕ → Graph → CoreResult) (M r s k : ℕ)
    (off addr : ℕ → ℕ) (sts : ℕ → ChildState) :
    batchJobPairs (modelGameJobs s k off addr sts) core (coreLevel M r s) s =
      roundPairs core M r s k off sts := by
  rw [roundPairs,← modelGameJobs_indices core M r s k off addr sts, List.map_map]
  apply List.map_congr_left
  intro i hi
  obtain ⟨hi,U,hCut⟩ := mem_batchJobIndices.mp hi
  let c := (activeChildren k sts).getD i 0
  have hi' : i < (activeChildren k sts).length := hi
  have hMem : c ∈ activeChildren k sts := by
    dsimp [c]
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem _
  have hSaved := (mem_activeChildren.mp hMem).2
  have ha : coreAnswer core M r s (sts c) = .cut U := hCut
  rw [batchJobPair,hCut]
  change (shiftSet (off c) (bisectOf s U), shiftSet (off c) (Finset.range s \ bisectOf s U)) =
    (match (sts c).saved with
      | some _ => none
      | none => match coreAnswer core M r s (sts c) with
        | .expander _ => none
        | .cut V => some (shiftSet (off c) (bisectOf s V),
            shiftSet (off c) (Finset.range s \ bisectOf s V))).getD (∅,∅)
  rw [hSaved,ha]
  rfl

end MinCostFlow.HierPaths
