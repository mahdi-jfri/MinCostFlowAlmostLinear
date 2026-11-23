module

public import MinCostFlow.MinRatio.ShiftForwardPotential
import Mathlib.Tactic

/-!
# The potentials at Init

The amortized cost of Update (`update_fwd_amortized`) is measured against three potentials: the
unused shift quota, the deposit, and the forward potential. Init must pay for their first value.
Here we compute it. Algorithm 1's `Initialize` starts every count at `0`, so the deposit, the
deeper deposit and the forward potential are `0`. The unused quota is
`Σ_{j ≤ d} ⌊(10 Ψ k)^{j+1}⌋`, at most `(d + 1) ⌊(10 Ψ k)^{d+1}⌋`
(`algorithm1_initialize_potentials`). This is the quota of the game with no rebuilds
(`gameShiftBound` with all rebuild counts `0`).
-/

public section

namespace MinCostFlow.MinRatio

open Chain

/-- Algorithm 1's `Initialize` starts all counts at `0`. -/
theorem algorithm1_initialize_counts (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    let ch := (Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
    ch.shiftCount = (fun _ => 0) ∧ ch.rebuildCount = (fun _ => 0) ∧
      ch.recUpdates = (fun _ => 0) ∧ (∀ j, ch.updCount j = 0) ∧ ∀ j, ch.curFwd j = 0 := by
  dsimp only [Ordered.algorithm1_initialize]
  refine ⟨rfl, rfl, rfl, fun j => ?_, fun j => ?_⟩
  · rw [rebuildSuffix_updCount]; split_ifs <;> rfl
  · rw [rebuildSuffix_curFwd]; split_ifs <;> rfl

/-- **The potentials at Init.** After Algorithm 1's `Initialize`, the deposit, the deeper
deposit and the forward potential are `0`, and the unused shift quota is at most
`(d + 1) ⌊(10 Ψ k)^{d+1}⌋` when `10 Ψ k ≥ 1`. -/
theorem algorithm1_initialize_potentials (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) (psi : ℝ) (Γ : ℕ)
    (hbase : 1 ≤ 10 * psi * (P.k : ℝ)) :
    let ch := (Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
    shiftRemainingBudget P psi ch ≤ (P.d + 1) * ⌊(10 * psi * (P.k : ℝ)) ^ (P.d + 1)⌋₊ ∧
      chainShiftDeposit P N₀ psi ch = 0 ∧ deeperDeposit P N₀ psi 0 ch = 0 ∧
      fwdPotential P N₀ psi Γ ch = 0 := by
  intro ch
  obtain ⟨hs, hr, hrec, hu, hf⟩ := algorithm1_initialize_counts T L P lvlM N₀ G₀ ℓ₀ g₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold shiftRemainingBudget
    have hterm : ∀ j : Fin (P.d + 1),
        ⌊gameShiftBound P psi ch.rebuildCount j.val⌋₊ - ch.shiftCount j.val ≤
          ⌊(10 * psi * (P.k : ℝ)) ^ (P.d + 1)⌋₊ := by
      intro j
      rw [hs, hr, Nat.sub_zero]
      apply Nat.floor_le_floor
      have hgame : gameShiftBound P psi (fun _ => 0) j.val = (10 * psi * (P.k : ℝ)) ^ (j.val + 1) := by
        unfold gameShiftBound; simp
      rw [hgame]
      exact pow_le_pow_right₀ hbase (by omega)
    calc ∑ j : Fin (P.d + 1), (⌊gameShiftBound P psi ch.rebuildCount j.val⌋₊ - ch.shiftCount j.val)
        ≤ ∑ _j : Fin (P.d + 1), ⌊(10 * psi * (P.k : ℝ)) ^ (P.d + 1)⌋₊ :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = (P.d + 1) * ⌊(10 * psi * (P.k : ℝ)) ^ (P.d + 1)⌋₊ := by simp
  · unfold chainShiftDeposit
    exact Finset.sum_eq_zero fun i _ => by rw [hu i, Nat.mul_zero]
  · unfold deeperDeposit
    exact Finset.sum_eq_zero fun i _ => by rw [hrec, Nat.mul_zero]
  · unfold fwdPotential
    exact Finset.sum_eq_zero fun j _ => by rw [hu j, hf j]; simp

/-- The potentials at the initial state of Algorithm 2, whose chain is that of Algorithm 1's
`Initialize`. -/
theorem algorithm2_init_potentials (cfg : Alg2Config) (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) (Γ : ℕ)
    (hbase : 1 ≤ 10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) :
    let ψ := alg2PsiGame cfg.Ψ cfg.P.M₀
    let ch := (Ordered.algorithm2_init cfg G₀ g₀ ℓ₀).chain
    shiftRemainingBudget cfg.P ψ ch ≤ (cfg.P.d + 1) * ⌊(10 * ψ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊ ∧
      chainShiftDeposit cfg.P cfg.N₀ ψ ch = 0 ∧ deeperDeposit cfg.P cfg.N₀ ψ 0 ch = 0 ∧
      fwdPotential cfg.P cfg.N₀ ψ Γ ch = 0 :=
  algorithm1_initialize_potentials cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀ g₀ _ Γ
    hbase

end MinCostFlow.MinRatio
