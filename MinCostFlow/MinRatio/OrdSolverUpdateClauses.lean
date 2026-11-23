module

public import MinCostFlow.MinRatio.UpdateAssemblyPrep
public import MinCostFlow.MinRatio.ShiftLoopSpaceBound
public import MinCostFlow.Chain.Ordered.NextFreshBound
import Mathlib.Tactic

/-!
# The space and cost clauses of Update

The envelope `OrdSolverContractEnvelope` asks, for op `0` (Update), that the space bound
`updateSpaceBound … model.nextFresh |U| (loopStepBound cfg model1) …` fit the allocation, and
that the budget fit the rate. Both bounds grow with the next fresh name `nextFresh`, the batch
length `|U|`, and (for the space) the loop step bound. Here we bound each of them on the states
that Algorithm 2 reaches.

* `updateSpaceBound_mono`: the space bound is monotone in these three quantities and in the
  refresh space.
* `alg2_update_space_le_reached`: on a reached state, with `|U| ≤ 2 m`, the space bound is at
  most its value at `nextFresh = alg2NameBase + intRebuildThreshold 0` (the bound of
  `alg2_nextFresh_le_with`), at batch length `2 m`, and at any bound `S` on
  `loopStepBound` (such as the `a (m + 2)^3` of `loopStepBound_poly`).
* `updateBudgetBound_eq`: the budget is a part without the loop, `updateBudgetNoLoop`, plus the
  loop term `(N + 1) B`. The loop term is the one that `update_fwd_amortized` replaces by
  `B + B W_0 |U|`. `updateBudgetNoLoop_le` bounds the part without the loop by
  `r₀ + r₁ |U|`, the form that `update_charge_le_rate` asks for.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- `updateSpaceBound` is monotone in the next fresh name, the batch length, the loop step
bound and the refresh space. -/
theorem updateSpaceBound_mono {L m d nf nf' u u' N N' fs ss me mp rs rs' : ℕ} (hnf : nf ≤ nf')
    (hu : u ≤ u') (hN : N ≤ N') (hrs : rs ≤ rs') :
    updateSpaceBound L m d nf u N fs ss me mp rs ≤
      updateSpaceBound L m d nf' u' N' fs ss me mp rs' := by
  unfold updateSpaceBound
  have h := Nat.mul_le_mul_right (cycleLoopIterSpace L fs ss) (Nat.add_le_add_right hN 1)
  omega

/-- **The Update space on reached states.** Take the hypotheses of `alg2_nextFresh_le_with`.
At step `t ≤ T`, if the next batch has at most `2 m` updates and the loop step
bound of the pre-loop state is at most `S`, then the space bound of the call is at most its value
at `nextFresh = alg2NameBase cfg (D.G 0) + intRebuildThreshold cfg.P cfg.N₀ 0`, batch length
`2 m` and loop step bound `S`. The refresh space must be monotone in the batch length. -/
theorem alg2_update_space_le_reached {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : Ordered.HistoryEdgeOnly D T)
    (hLen : Ordered.HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) {m t : ℕ} (ht : t ≤ T)
    (hU : (D.U (t + 1)).length ≤ 2 * m) (L fs ss me mp S : ℕ) (refreshSpace : ℕ → ℕ)
    (hrs : Monotone refreshSpace) (gVec lVec : ℕ → ℝ)
    (hS : loopStepBound cfg (alg2PreLoopState cfg
      (minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η isUpdate t) (D.U (t + 1)) gVec lVec)
        ≤ S) :
    updateSpaceBound L m cfg.P.d
        (minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η isUpdate t).nextFresh
        (D.U (t + 1)).length
        (loopStepBound cfg (alg2PreLoopState cfg
          (minRatioFailState (Ordered.algorithm2_dsWith cfg κ) D η isUpdate t) (D.U (t + 1))
            gVec lVec)) fs ss me mp (refreshSpace (D.U (t + 1)).length) ≤
      updateSpaceBound L m cfg.P.d
        (Ordered.alg2NameBase cfg (D.G 0) + intRebuildThreshold cfg.P cfg.N₀ 0) (2 * m) S
        fs ss me mp (refreshSpace (2 * m)) :=
  updateSpaceBound_mono
    (Ordered.alg2_nextFresh_le_with (η := η) κ hV hHist hEdge hLen hmBound hnBound t ht) hU hS
    (hrs hU)

/-- The part of `updateBudgetBound` without the shift loop. -/
@[expose] def updateBudgetNoLoop (L n intCap nextFresh batchLen maxEdges maxPaths drainUnit
    refreshBudget : ℕ) : ℕ :=
  (if intCap < nextFresh + batchLen then 102 * intCap + 34 * (nextFresh + batchLen) + 270 else 50) +
    20 * L + 300 * batchLen + refreshBudget + (batchLen * (34 * L + 100) + 50) +
    updateGoodBranchBudget L n maxEdges maxPaths drainUnit + 500

/-- `updateBudgetBound` is the part without the loop plus the loop term `(N + 1) B`. -/
theorem updateBudgetBound_eq (L d n intCap nextFresh batchLen N findBudget shiftBudget
    maxEdges maxPaths drainUnit refreshBudget : ℕ) :
    updateBudgetBound L d n intCap nextFresh batchLen N findBudget shiftBudget maxEdges maxPaths
        drainUnit refreshBudget =
      updateBudgetNoLoop L n intCap nextFresh batchLen maxEdges maxPaths drainUnit refreshBudget +
        (N + 1) * cycleLoopIterBudget L d findBudget shiftBudget := by
  unfold updateBudgetBound updateBudgetNoLoop
  omega

/-- The part of the Update budget without the loop is at most `r₀ + r₁ |U|`, when the name
capacity is at most `c`, the next fresh name at most `nf`, and the refresh budget at most
`ρ₀ + ρ₁ |U|`. -/
theorem updateBudgetNoLoop_le {L n intCap nextFresh u maxEdges maxPaths drainUnit rb c nf ρ₀ ρ₁ : ℕ}
    (hc : intCap ≤ c) (hnf : nextFresh ≤ nf) (hrb : rb ≤ ρ₀ + ρ₁ * u) :
    updateBudgetNoLoop L n intCap nextFresh u maxEdges maxPaths drainUnit rb ≤
      (102 * c + 34 * nf + 370 + 20 * L + ρ₀ + updateGoodBranchBudget L n maxEdges maxPaths drainUnit
        + 500) + (434 + 34 * L + ρ₁) * u := by
  unfold updateBudgetNoLoop
  have h1 : (if intCap < nextFresh + u then 102 * intCap + 34 * (nextFresh + u) + 270 else 50) ≤
      102 * c + 34 * nf + 34 * u + 320 := by
    split_ifs <;> omega
  have h2 : (434 + 34 * L + ρ₁) * u = 334 * u + u * (34 * L + 100) + ρ₁ * u := by ring
  omega

/-- When `nextFresh + u ≤ intCap`, the dynamic table-growth branch of `Update` does not run,
so `updateBudgetNoLoop` charges only `50` for the check (no `intCap` or `nextFresh` term). -/
theorem updateBudgetNoLoop_le_noGrow {L n intCap nextFresh u maxEdges maxPaths drainUnit rb ρ₀ ρ₁ : ℕ}
    (hcap : nextFresh + u ≤ intCap) (hrb : rb ≤ ρ₀ + ρ₁ * u) :
    updateBudgetNoLoop L n intCap nextFresh u maxEdges maxPaths drainUnit rb ≤
      (600 + 20 * L + ρ₀ + updateGoodBranchBudget L n maxEdges maxPaths drainUnit) +
        (400 + 34 * L + ρ₁) * u := by
  unfold updateBudgetNoLoop
  have hng : ¬ intCap < nextFresh + u := Nat.not_lt.mpr hcap
  rw [ite_eq_right hng]
  have h2 : (400 + 34 * L + ρ₁) * u = 300 * u + u * (34 * L + 100) + ρ₁ * u := by ring
  omega

end MinCostFlow.MinRatio
