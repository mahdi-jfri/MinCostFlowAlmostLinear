module

public import MinCostFlow.MinRatio.OrdSolverReached
public import MinCostFlow.MinRatio.UpdateCycleLoopBase
public import MinCostFlow.Chain.Ordered.ShiftLoopLevels
public import MinCostFlow.MinRatio.ShiftLoopLevelFacts

/-!
# The shift loop of the solver keeps `n ≤ m + 1` at every level

The sparse-core program builds a level from a graph `G` only when `G.n ≤ G.m + 1`
(`AsmBranchAt.init_runs`): it charges its work on the vertices to the edges. The shift loop of
`Update` rebuilds levels from the graphs of its chain, so each chain it visits must have this
bound at every level.

`Chain.Ordered.ShiftLoopChainInv` (`Chain/Ordered/ShiftLoopLevels.lean`) holds this and the
facts that make it last. This file puts it on the solver's states:
* `OrdSolverReached.preLoop_shiftLoopChainInv`: on a reached state whose graph is connected, the
  chain that the shift loop starts from (`alg2PreLoopState`) meets it;
* `alg2LoopShiftStep_shiftLoopChainInv`: each step of the shift loop keeps it;
* `ShiftLoopLevelFacts` and `shiftLoopLevelFacts_of_inv` (in `ShiftLoopLevelFacts.lean`, so that
  the loop and the select files can import them): the facts that the machine needs at a chain of
  the loop, namely `n ≤ m + 1` at every level, the level sizes `levelM` and the vertex bound `N₀`
  of the configuration.
-/

public section

namespace MinCostFlow.MinRatio

open Chain IPM IPM.Machine

/-- **The chain before the shift loop meets `ShiftLoopChainInv`.** On a reached state of a
connected graph `G`, with the hypotheses of `ordSolverReached_update`, the chain that the shift
loop starts from meets `Chain.Ordered.ShiftLoopChainInv`. It is the chain at the last stage of
the longer history (`histSnoc`) before its shift loop, so
`Chain.Ordered.alg2_preLoop_shiftLoopChainInv_with` applies. -/
theorem OrdSolverReached.preLoop_shiftLoopChainInv {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) {U : List Update} {g l : ℕ → ℝ}
    (hU : RefreshBatch G U) (hl : ∀ e ∈ G.E, 0 < l e)
    (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e) :
    Ordered.ShiftLoopChainInv cfg (alg2PreLoopState cfg model U g l).chain := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  obtain ⟨hgx, hlx⟩ := OrdSolverReached.ext hHist hm
  have hEdgeU : ∀ u ∈ U, Bundle.IsEdgeUpdate u := by
    intro u hu
    have := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd this id
  have hV' := histSnoc_valid (b := true) hHist (hG T le_rfl) hU.1 hU.2.1 hl
    (fun h => absurd h (by decide)) (fun e he hnot => by rw [← hgx, ← hlx]; exact hagree e he hnot)
  have hG' : ∀ t ≤ T + 1, (histSnoc D T G U g l).G t = G := by
    intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT
      simp only [histSnoc, seqSnoc_succ]
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]
      exact hG t hle
  have hInv := Ordered.alg2_preLoop_shiftLoopChainInv_with (η := seqSnoc η T 0) κ hV hV'
    (histSnoc_edgeOnly hE hEdgeU) (histSnoc_lengths hL hlR)
    (fun t ht => by rw [hG' t ht]; exact hmG) (fun t ht => by rw [hG' t ht]; exact hnG) T le_rfl
    (by rw [hG' (T + 1) le_rfl]; exact hConn)
  dsimp only at hInv
  rw [minRatioFailState_snoc_of_le _ D η op T G U g l 0 true T le_rfl, ← hm] at hInv
  simp only [histSnoc, seqSnoc_succ] at hInv
  exact hInv

/-- **One step of the shift loop keeps `ShiftLoopChainInv`**: the chain of
`alg2LoopShiftStep cfg model i` is `algorithm1_shift` of the chain of `model` at level `i`. -/
theorem alg2LoopShiftStep_shiftLoopChainInv {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} (h : Ordered.ShiftLoopChainInv cfg model.chain)
    (i : Fin (cfg.P.d + 1)) :
    Ordered.ShiftLoopChainInv cfg (alg2LoopShiftStep cfg model i).chain :=
  h.shift hV i.val (Nat.lt_succ_iff.mp i.isLt)

end MinCostFlow.MinRatio

end
