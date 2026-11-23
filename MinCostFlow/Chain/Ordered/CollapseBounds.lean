module

public import MinCostFlow.Chain.Ordered.Budget
public import MinCostFlow.Chain.CollapseBounds
import MinCostFlow.Chain.Ordered.BudgetHelpersCost
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collapsing Runtime and Tree-Update Bounds for Ordered Algorithm 1 (Lemma 5.11 Helpers)

Ordered-chain counterpart of `MinCostFlow.Chain.CollapseBounds`: proves `opRuntimeBudget_collapse`
using `lemma511TimeFactor` (carrying the extra factor `k + 1 ≤ 3 M₀^{1/d}` into `M₀^{2/d}`), and
proves the collapsing runtime and `T^𝒢` edge-update bounds (`totalRuntime_collapse*`,
`totalTreeUpdates_collapse*`).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section CollapsingBounds

/-- Per-operation runtime budget collapse for ordered Algorithm 1: multiplies
`Chain.opRuntimeBudget_collapse` by `k + 1 ≤ 3 M₀^{1/d}` to yield `lemma511TimeFactor`. -/
lemma opRuntimeBudget_collapse (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) {n i₀ : ℕ} (hi₀ : i₀ ≤ P.d) :
    opRuntimeBudget TP LP P n i₀ ≤ lemma511TimeFactor TP LP P n * powTerm P i₀ := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hM_pos : (0 : ℝ) < (P.M₀ : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hM1d1 : (1 : ℝ) ≤ (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) :=
    Real.one_le_rpow hM1 (by positivity)
  have hk1_le : (P.k : ℝ) + 1 ≤ 3 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) := by
    linarith [P.hk_upper, hM1d1]
  have hOld := Chain.opRuntimeBudget_collapse TP LP P hTP hLP hγM₀ hi₀ (n := n)
  have hOld_rhs_nn :
      0 ≤ ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
        (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
        (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
        (2 * logFactor P n) ^ (max TP.p_T LP.p_last + 1) *
        powTerm P i₀ := by
    have := hTP.2.2.2.2.2.2.2.2.2
    have := hLP.2.2.2.2
    have := one_le_logFactor P n
    have := hTP.2.2.1 (P.M₀ ^ 2)
    have := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
    have := one_le_powTerm P hi₀
    positivity
  have hRpow : (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) =
      (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) := by
    rw [← Real.rpow_add hM_pos]
    congr 1
    ring
  unfold opRuntimeBudget lemma511TimeFactor
  calc
    ((P.k : ℝ) + 1) * Chain.opRuntimeBudget TP LP P n i₀
        ≤ ((P.k : ℝ) + 1) *
            (((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
              (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
              (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
              (2 * logFactor P n) ^ (max TP.p_T LP.p_last + 1) *
              powTerm P i₀) :=
      mul_le_mul_of_nonneg_left hOld (by positivity)
    _ ≤ (3 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) *
          (((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
            (P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) *
            (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
            (2 * logFactor P n) ^ (max TP.p_T LP.p_last + 1) *
            powTerm P i₀) :=
      mul_le_mul_of_nonneg_right hk1_le hOld_rhs_nn
    _ = 3 * ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
          ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ)) * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) *
          (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
          (2 * logFactor P n) ^ (max TP.p_T LP.p_last + 1) *
          powTerm P i₀ := by ring
    _ = 3 * ((P.d : ℝ) + 1) * (8 * TP.c_T + 81 * LP.c_last + 430) *
          (P.M₀ : ℝ) ^ (2 / (P.d : ℝ)) *
          (TP.γ_r (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2)) ^ (3 * P.d + 2)) *
          (2 * logFactor P n) ^ (max TP.p_T LP.p_last + 1) *
          powTerm P i₀ := by rw [hRpow]

/-- Total runtime bound (Lemma 5.11, pages 20 & 23–24) in explicit
non-asymptotic form from ordered `ChainInv` and `ChainBudgetInvWith`. -/
theorem totalRuntime_collapse_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {overflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow) :
    (st.totalRuntime : ℝ) ≤
      lemma511TimeFactor TP LP P N₀ *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) + overflow := by
  have hCost := ChainInv.level_cost_bounds_noHidden hTP hLP hγM₀ hγk hInv
  have hActive : ((∑ i ∈ Finset.range P.d, (T.cost (st.scState i) + st.curEnc i) : ℕ) : ℝ) +
      (st.curLastCost : ℝ) ≤
        opRuntimeBudget TP LP P N₀ 0 + activeRestartCap TP P N₀ st.curRestarts := by
    have hsum : ((∑ i ∈ Finset.range P.d, (T.cost (st.scState i) + st.curEnc i) : ℕ) : ℝ) ≤
        ((P.k : ℝ) + 1) * (Finset.Ico 0 P.d).sum (levelToolCap TP P N₀) +
          activeRestartCap TP P N₀ st.curRestarts := by
      rw [Nat.cast_sum]
      calc
        ∑ i ∈ Finset.range P.d, ((T.cost (st.scState i) + st.curEnc i : ℕ) : ℝ)
            ≤ ∑ i ∈ Finset.range P.d,
                (((P.k : ℝ) + 1) *
                  (levelToolCap TP P N₀ i + (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i)) :=
              Finset.sum_le_sum fun i hi => by
                rw [Nat.cast_add]; exact hCost.1 i (Finset.mem_range.mp hi)
        _ = ((P.k : ℝ) + 1) *
              ∑ i ∈ Finset.range P.d,
                (levelToolCap TP P N₀ i + (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) := by
              rw [Finset.mul_sum]
        _ = ((P.k : ℝ) + 1) *
              ((Finset.Ico 0 P.d).sum (levelToolCap TP P N₀) +
                Chain.activeRestartCap TP P N₀ st.curRestarts) := by
              rw [Finset.sum_add_distrib, Nat.Ico_zero_eq_range]
              rfl
        _ = ((P.k : ℝ) + 1) * (Finset.Ico 0 P.d).sum (levelToolCap TP P N₀) +
              activeRestartCap TP P N₀ st.curRestarts := by
              unfold activeRestartCap; ring
    have hlast_nn : 0 ≤ lastCostCap TP LP P N₀ := by
      unfold lastCostCap
      have := hTP.2.2.1 (P.M₀ ^ 2)
      have := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
      have := hLP.2.2.2.2
      have := one_le_logFactor P N₀
      positivity
    have hlast : (st.curLastCost : ℝ) ≤ ((P.k : ℝ) + 1) * lastCostCap TP LP P N₀ := by
      have hk1 : (1 : ℝ) ≤ (P.k : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ P.k from Nat.cast_nonneg _]
      exact le_trans (hCost.2.2.1 P.hd) (le_mul_of_one_le_left hlast_nn hk1)
    have hex_nn : 0 ≤ ((P.k : ℝ) + 1) * extraEncCap P := by
      unfold extraEncCap
      have hlog : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
      positivity
    unfold opRuntimeBudget Chain.opRuntimeBudget
    simp only [P.hd, ↓reduceIte]
    linarith
  have hTot : (st.totalRuntime : ℝ) ≤
      opRuntimeBudget TP LP P N₀ 0 +
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P N₀ i + overflow := by
    unfold ChainState.totalRuntime
    rw [Nat.cast_add, Nat.cast_add]
    have hBud1 : (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤
        ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opRuntimeBudget TP LP P N₀ i +
            overflow :=
      hBudget.1
    linarith [hBud1, hActive]
  set Cfac := lemma511TimeFactor TP LP P N₀
  have h0 : opRuntimeBudget TP LP P N₀ 0 ≤ Cfac * (P.M₀ : ℝ) := by
    simpa [Cfac, powTerm_zero P] using opRuntimeBudget_collapse TP LP P hTP hLP hγM₀ (Nat.zero_le P.d)
  have hSum : (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) *
          opRuntimeBudget TP LP P N₀ i) ≤
      Cfac * (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hci := opRuntimeBudget_collapse TP LP P hTP hLP hγM₀ hi_le (n := N₀)
    calc
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opRuntimeBudget TP LP P N₀ i
          ≤ ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * (Cfac * powTerm P i) :=
        mul_le_mul_of_nonneg_left hci (Nat.cast_nonneg _)
      _ = Cfac * (((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by ring
  calc
    (st.totalRuntime : ℝ)
        ≤ Cfac * (P.M₀ : ℝ) + Cfac * (∑ i ∈ Finset.range (P.d + 1),
            ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) + overflow := by
      linarith
    _ = Cfac * ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) + overflow := by ring

theorem totalRuntime_collapse_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st) :
    (st.totalRuntime : ℝ) ≤
      lemma511TimeFactor TP LP P N₀ *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
  simpa using totalRuntime_collapse_with_noHidden T L TP LP P hTP hLP
    hγM₀ hγk hInv hBudget.toWith

/-- Total `T^𝒢` edge-update bound (Lemma 5.11, pages 20 & 23–24) in explicit non-asymptotic form
from ordered `ChainInv` and `ChainBudgetInvWith`. -/
theorem totalTreeUpdates_collapse_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {overflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow) :
    (st.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
  have hCost := ChainInv.level_cost_bounds_noHidden hTP hLP hγM₀ hγk hInv
  have hActivePlusDiff : ((∑ i ∈ Finset.range P.d, st.curDecUpdates i : ℕ) : ℝ) +
      (st.curLastTreeUpdates : ℝ) + diffTreeCap TP P 0 ≤ opTreeBudget TP P 0 := by
    have hsum : ((∑ i ∈ Finset.range P.d, st.curDecUpdates i : ℕ) : ℝ) ≤
        (Finset.Ico 0 P.d).sum (levelDecCap TP P) := by
      rw [Nat.cast_sum, Nat.Ico_zero_eq_range]
      exact Finset.sum_le_sum fun i hi => hCost.2.1 i (Finset.mem_range.mp hi)
    unfold opTreeBudget
    simp only [P.hd, ↓reduceIte]
    linarith [hCost.2.2.2.1]
  have hTot : (st.totalTreeUpdates : ℝ) ≤
      opTreeBudget TP P 0 +
      ∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i := by
    unfold ChainState.totalTreeUpdates
    rw [Nat.cast_add, Nat.cast_add]
    have hBud2 : (st.closedTreeUpdates : ℝ) ≤ diffTreeCap TP P 0 +
        ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i :=
      hBudget.2
    linarith [hBud2, hActivePlusDiff]
  set Tfac := (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1)
  have h0 : opTreeBudget TP P 0 ≤ Tfac * (P.M₀ : ℝ) := by
    simpa [Tfac, powTerm_zero P] using opTreeBudget_collapse TP P hTP (Nat.zero_le P.d)
  have hSum : (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i) ≤
      Tfac * (∑ i ∈ Finset.range (P.d + 1),
        ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi_le : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hti := opTreeBudget_collapse TP P hTP hi_le
    calc
      ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * opTreeBudget TP P i
          ≤ ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * (Tfac * powTerm P i) :=
        mul_le_mul_of_nonneg_left hti (Nat.cast_nonneg _)
      _ = Tfac * (((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by ring
  calc
    (st.totalTreeUpdates : ℝ)
        ≤ Tfac * (P.M₀ : ℝ) + Tfac * (∑ i ∈ Finset.range (P.d + 1),
            ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by linarith
    _ = Tfac * ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) := by ring

theorem totalTreeUpdates_collapse_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st) :
    (st.totalTreeUpdates : ℝ) ≤
      (14 * (P.d : ℝ) + 36) * (TP.γ_ℓ (P.M₀ ^ 2) * TP.γ_r (P.M₀ ^ 2)) ^ (2 * P.d + 1) *
        ((P.M₀ : ℝ) + ∑ i ∈ Finset.range (P.d + 1),
          ((st.shiftCount i + st.rebuildCount i : ℕ) : ℝ) * powTerm P i) :=
  totalTreeUpdates_collapse_with_noHidden T L TP LP P hTP hLP
    hγM₀ hγk hInv hBudget.toWith

end CollapsingBounds

end MinCostFlow.Chain.Ordered
