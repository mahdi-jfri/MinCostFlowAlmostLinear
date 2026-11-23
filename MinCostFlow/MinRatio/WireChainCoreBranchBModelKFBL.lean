module

public import MinCostFlow.Chain.Ordered.Algorithm1
public import MinCostFlow.Chain.Ordered.Compact
public import MinCostFlow.MinRatio.WireChainCorePreAux

/-!
# The model after the exits of Branch B (`WireChainCoreBranchBModelKFBL`)

The loop of Branch B stops at a level `i₀` with the chain `chE`, and the rest of the update loop
of the model from there is the step at `i₀` (`BranchBLoopExitKFBL`). The exits compute the chain
that this step gives. When the test fires at a level `0 < i₀ < d`, the step is the rebuild from
`i₀` (`branchBUpdateLoop_int`), which is the chain `next` of the interior exit. When the loop
reaches `d`, no step is left, and the chain is that of the last level (`branchBUpdateLoop_term`),
which is the chain `X` of the terminal exits.

`branchBSplit` also needs two facts on the new root graph `G.applyBatch U`: an edge of `G` that
the batch does not delete stays (`mem_applyBatch_E_of_not_delete`), and a deleted edge that no
update of the batch inserts again is gone (`notMem_applyBatch_of_delete`).
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain

/-- The rest of the update loop from a level `0 < i₀ < d` where the test fires is the rebuild
from `i₀`, on the lengths and gradients `ℓ'`, `g'`. -/
theorem branchBUpdateLoop_int {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ} {ℓ' g' : ℕ → ℝ} {i₀ : ℕ}
    {ch : ChainState T P} {curG : MGraph} {curU : List Update} {curEnc : ℕ}
    (hi : i₀ < P.d) (hpos : 0 < i₀)
    (hT : intRebuildThreshold P N₀ i₀ < ch.updCount i₀ + curU.length) :
    (Ordered.updateLoop T L TP P N₀ ℓ' g' (P.d - i₀) i₀ ch curG curU curEnc).1 =
      (Ordered.algorithm1_rebuild T L P { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1 := by
  obtain ⟨r, hr⟩ : ∃ r, P.d - i₀ = r + 1 := ⟨P.d - i₀ - 1, by omega⟩
  have h0 : i₀ ≠ 0 := by omega
  rw [hr]
  simp only [Ordered.updateLoop, if_pos hT, Ordered.rebuildStartFn, Ordered.rebuildStartGraph, h0, ↓reduceIte]

/-- The rest of the update loop from level `d` is the loop at `rem = 0`. -/
theorem branchBUpdateLoop_term {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {P : ChainParams} {N₀ : ℕ} {ℓ' g' : ℕ → ℝ}
    {ch : ChainState T P} {curG : MGraph} {curU : List Update} {curEnc : ℕ} :
    (Ordered.updateLoop T L TP P N₀ ℓ' g' (P.d - P.d) P.d ch curG curU curEnc).1 =
      (Ordered.updateLoop T L TP P N₀ ℓ' g' 0 P.d ch curG curU curEnc).1 := by
  rw [Nat.sub_self]

/-- An edge that the batch deletes and no update of the batch inserts is not in the graph after
the batch. After the deletion, the later updates do not insert it (`mem_applyBatch_of_no_insert`).
-/
theorem notMem_applyBatch_of_delete {e : ℕ} :
    ∀ (U : List Update) (G : MGraph), Update.delete e ∈ U → (∀ u ∈ U, ¬ u.Inserts e) →
      e ∉ (G.applyBatch U).E
  | [], _, h, _ => by simp at h
  | v :: vs, G, h, hNo => by
    have hNo' : ∀ u ∈ vs, ¬ u.Inserts e := fun u hu => hNo u (List.mem_cons_of_mem _ hu)
    change e ∉ ((G.applyUpdate v).applyBatch vs).E
    by_cases hvs : Update.delete e ∈ vs
    · exact notMem_applyBatch_of_delete vs (G.applyUpdate v) hvs hNo'
    · have hv : v = Update.delete e := by
        rcases List.mem_cons.mp h with h' | h'
        · exact h'.symm
        · exact absurd h' hvs
      subst hv
      intro he
      have h1 := mem_applyBatch_of_no_insert vs (G.applyUpdate (Update.delete e)) e he
        (fun ⟨u, hu, hi⟩ => hNo' u hu hi)
      simp [MGraph.applyUpdate] at h1

end MinCostFlow.MinRatio
