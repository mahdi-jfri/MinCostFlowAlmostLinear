module

public import MinCostFlow.HierPaths.BuildChildChoiceInv
public import MinCostFlow.HierPaths.BuildProgGameModel

/-!
# Relating reply indices to original children

The scan gives answers in active order. The model gives answers by original
child number. The two arrays define the same router batch and the same
next active order.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Interpret the reply to an active index as the reply of its original child. -/
def answerByChild (k : ℕ) (sts : ℕ → ChildState) (answer : ℕ → CoreResult) (c : ℕ) : CoreResult :=
  answer ((activeChildren k sts).idxOf c)

/-- Keep the answers the core scan returned, indexed by active position. -/
def choiceGameJobs (s k : ℕ) (off addr : ℕ → ℕ) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) : BuildGameJobs :=
  { modelGameJobs s k off addr sts with choice := some answer }

/-- Every active position has the same answer in original numbering. -/
theorem answerByChild_getD {k i : ℕ} {sts : ℕ → ChildState} (answer : ℕ → CoreResult)
    (hi : i < (activeChildren k sts).length) :
    answerByChild k sts answer ((activeChildren k sts).getD i 0) = answer i := by
  have hN : (activeChildren k sts).Nodup := List.nodup_range.filter _
  rw [answerByChild,List.getD_eq_getElem _ _ hi,hN.idxOf_getElem]

/-- Mapping the cut indices back to the original children gives the
requesting children in increasing order. -/
theorem choiceGameJobs_indices (s k : ℕ) (off addr : ℕ → ℕ) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) (core : ℕ → Graph → CoreResult) (q : ℕ) :
    (batchJobIndices (choiceGameJobs s k off addr sts answer) core q).map
      (fun i => (activeChildren k sts).getD i 0) =
      choiceRequesting s k off sts (answerByChild k sts answer) := by
  let l := activeChildren k sts
  let f := fun i => l.getD i 0
  let test := fun c => decide (coreTag (answerByChild k sts answer c) = 0)
  have hList : (List.range l.length).map f = l := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp [f,List.getElem?_eq_getElem hi]
  have he : (List.range l.length).filter (fun i => decide (coreTag (answer i) = 0)) =
      (List.range l.length).filter (test ∘ f) := by
    apply List.filter_congr
    intro i hi
    change decide (coreTag (answer i) = 0) = decide (coreTag (answerByChild k sts answer (f i)) = 0)
    rw [answerByChild_getD answer (List.mem_range.mp hi)]
  change ((List.range l.length).filter (fun i => decide (coreTag (answer i) = 0))).map f = _
  rw [he,← List.filter_map,hList]
  unfold l activeChildren choiceRequesting
  rw [List.filter_filter]
  apply List.filter_congr
  intro c _
  cases hs : (sts c).saved <;> cases ha : answerByChild k sts answer c <;>
    simp [choiceRequest,test,hs,ha,coreTag]

/-- The scratch batch is exactly the list of requests of the certified model
round. -/
theorem choiceGameJobs_pairs (s k : ℕ) (off addr : ℕ → ℕ) (sts : ℕ → ChildState)
    (answer : ℕ → CoreResult) (core : ℕ → Graph → CoreResult) (q : ℕ) :
    batchJobPairs (choiceGameJobs s k off addr sts answer) core q s =
      choiceRoundPairs s k off sts (answerByChild k sts answer) := by
  let J := choiceGameJobs s k off addr sts answer
  let l := activeChildren k sts
  rw [choiceRoundPairs,← choiceGameJobs_indices s k off addr sts answer core q,List.map_map]
  apply List.map_congr_left
  intro i hi
  obtain ⟨hi,U,hU⟩ := mem_batchJobIndices.mp hi
  have hi' : i < l.length := hi
  have hU' : answer i = .cut U := hU
  let c := l.getD i 0
  have hMem : c ∈ l := by
    dsimp [c]
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hActive : (sts c).saved = none := by
    have h := List.mem_filter.mp hMem
    exact Option.isNone_iff_eq_none.mp h.2
  have hL : answerByChild k sts answer c = .cut U :=
    (answerByChild_getD answer hi').trans hU'
  change batchJobPair J core q s i = (choiceRequest s (off c) (sts c)
    (answerByChild k sts answer c)).getD (∅,∅)
  rw [batchJobPair,show J.answer core q i = .cut U from hU]
  simp only [choiceRequest,hActive,hL,Option.getD_some]
  rfl

/-- The children that remain active are exactly those that asked for a matching. -/
theorem activeChildren_choiceRound (route : RouterFn) (G : Graph) (X : Finset ℕ)
    (Δ L s k : ℕ) (off : ℕ → ℕ) (sts : ℕ → ChildState) (answer : ℕ → CoreResult) :
    activeChildren k (choiceGameRound route G X Δ L s k off sts answer) =
      choiceRequesting s k off sts answer := by
  unfold activeChildren choiceRequesting
  apply List.filter_congr
  intro c hc
  have hk := List.mem_range.mp hc
  cases hs : (sts c).saved <;> cases ha : answer c <;>
    simp [choiceGameRound,childStepAnswer,choiceRequest,hs,ha,hk]

end MinCostFlow.HierPaths
