module

public import MinCostFlow.HierPaths.BuildProgScanChoice
public import MinCostFlow.HierPaths.BuildProgBatchInputs

/-!
# Using the recorded replies to prepare the router batch

The core result for a job is read from the ordered scan. Its address is
the end of the preceding prepared block, so later passes can use the
same address and pair formulas with the recorded choices.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- A scan recorded these exact values and bump sizes. The model cursor gives the address
of every block including the end of the last one. -/
theorem ChoiceRepliesAt.chosenPrefixes {J : BuildGameJobs} {M q h replies n top : ℕ}
    {mem : ℕ → ℕ} {sC : ℕ → ℕ} {reply : ℕ → CoreResult} {bump addr : ℕ → ℕ}
    (hr : ChoiceRepliesAt J M q h replies n top mem sC reply bump addr)
    (core : ℕ → Graph → CoreResult) :
    ∀ i ≤ n, addr i = ({ J with choice := some reply, bump := some bump } : BuildGameJobs).prepPrefix core q h i := by
  intro i hi
  induction i with
  | zero => exact hr.first
  | succ i ih =>
    have hPrev := ih (by omega)
    have he := (hr.rows i (by omega)).2.2.2.1
    rw [he,hPrev]
    rfl

/-- The chosen replies and their block bounds meet the input view of the
batch routing pass. -/
theorem ChoiceRepliesAt.gameRepliesAt {J : BuildGameJobs} {M q h replies top : ℕ}
    {mem : ℕ → ℕ} {sC : ℕ → ℕ} {reply : ℕ → CoreResult} {bump addr : ℕ → ℕ}
    (hr : ChoiceRepliesAt J M q h replies J.count top mem sC reply bump addr)
    (hEnd : mem (replies + J.count) = top)
    (core : ℕ → Graph → CoreResult) :
    GameRepliesAt { J with choice := some reply, bump := some bump } core q h replies mem := by
  refine ⟨hEnd.trans (hr.last.symm.trans (hr.chosenPrefixes core J.count le_rfl)), ?_⟩
  intro i hi
  obtain ⟨hp,_,hb,_,_⟩ := hr.rows i hi
  have h₀ := hr.chosenPrefixes core i hi.le
  have h₁ := hr.chosenPrefixes core (i+1) (Nat.succ_le_of_lt hi)
  exact ⟨hp.trans h₀,h₀ ▸ h₁ ▸ hb⟩

end MinCostFlow.HierPaths
