module

public import MinCostFlow.Chain.Ordered.BudgetHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Order Helpers and Per-Level Cost Bounds for Algorithm 1 with Orders

This file proves the small rotation-witness helpers for `Bundle.OrderedUpTo`
(`orderedUpTo_zero_of_rotation`, `rotation_of_orderedUpTo`, `exists_rotation_of_eq`) and the
per-level cost bounds implied by `Ordered.LevelHistory` and `Ordered.ChainInv`
(`LevelHistory.cost_le_cap_add_restart`, `ChainInv.level_cost_bounds_noHidden`), carrying the `(k + 1)` factor of
`SparseCoreRestartTool.IsSpecOrdRestartNoHidden`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section OrderHelpers

/-- Any valid rotation of `D.G 0` matching `ord 0` yields `OrderedUpTo D 0 β ord`. -/
lemma orderedUpTo_zero_of_rotation {D : DynamicInstance} {β : ℕ} {ord : ℕ → ℕ → List End}
    (h : ∃ ρ : Rotation (D.G 0), ρ.order = ord 0) :
    OrderedUpTo D 0 β ord := by
  obtain ⟨ρ₀, hρ₀⟩ := h
  refine ⟨fun t => if ht : t = 0 then ht ▸ ρ₀ else sortedRotation (D.G t), ?_,
    fun t ht => by omega⟩
  intro t ht
  have ht0 : t = 0 := Nat.le_zero.mp ht
  subst ht0
  simpa using hρ₀

/-- Extract a valid rotation witness at stage `t ≤ τ` from `OrderedUpTo D τ β ord`. -/
lemma rotation_of_orderedUpTo {D : DynamicInstance} {τ β : ℕ} {ord : ℕ → ℕ → List End}
    (h : OrderedUpTo D τ β ord) {t : ℕ} (ht : t ≤ τ) :
    ∃ ρ : Rotation (D.G t), ρ.order = ord t := by
  obtain ⟨ρ, hρ, _⟩ := h
  exact ⟨ρ t, hρ t ht⟩

/-- Transport a rotation existence witness across graph and order equalities. -/
lemma exists_rotation_of_eq {G₁ G₂ : MGraph} {ord₁ ord₂ : ℕ → List End}
    (hG : G₁ = G₂) (hord : ord₁ = ord₂)
    (h : ∃ ρ : Rotation G₁, ρ.order = ord₁) :
    ∃ ρ : Rotation G₂, ρ.order = ord₂ := by
  subst hG; subst hord; exact h

end OrderHelpers

section CostBounds

/-- Cumulative runtime bound for a single level `i < P.d` from its `LevelHistory`, carrying the
`(k + 1)` factor of `IsSpecOrdRestartNoHidden`. -/
lemma LevelHistory.cost_le_cap_add_restart {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} {i : ℕ} (_hi : i < P.d) (H : LevelHistory T TP P N₀ st i) :
    (T.cost (st.scState i) : ℝ) ≤ ((P.k : ℝ) + 1) * (
      2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
        (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
      (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) := by
  have hTPValid : TP.Valid := hTP
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, hγr_m, _, hcT⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hγℓ_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hm0_le : levelM TP P i ≤ P.M₀ ^ 2 := levelM_le_sq hTPValid hγM₀ hγk i
  have hm0_lt := levelM_lt_add_one hTPValid P i
  have hγr_le : TP.γ_r (levelM TP P i) ≤ TP.γ_r (P.M₀ ^ 2) := hγr_m _ _ hm0_le
  have hSpec := H.hOK.noHidden P.k H.len (levelM TP P i) N₀ H.D H.ord H.restarts
    P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
    (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hCost := hSpec.2.2.2.2.2
  dsimp only at hCost
  rw [← H.hRun, H.hRestartsCount] at hCost
  have hlog_pos0 : 0 ≤ Real.log ((levelM TP P i : ℝ) + (N₀ : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ levelM TP P i from Nat.cast_nonneg _,
      show (0 : ℝ) ≤ N₀ from Nat.cast_nonneg _])
  have hlog_le : Real.log ((levelM TP P i : ℝ) + (N₀ : ℝ) + 2) ≤ 2 * logFactor P N₀ := by
    unfold logFactor
    have hM0_nn : (0 : ℝ) ≤ P.M₀ := Nat.cast_nonneg _
    have hN0_nn : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg _
    have hm_sq : (levelM TP P i : ℝ) ≤ (P.M₀ : ℝ) ^ 2 := by exact_mod_cast hm0_le
    have h1 : (levelM TP P i : ℝ) + (N₀ : ℝ) + 2 ≤ ((P.M₀ : ℝ) + (N₀ : ℝ) + 2) ^ 2 := by
      have hexp : ((P.M₀ : ℝ) + (N₀ : ℝ) + 2) ^ 2 =
          (P.M₀ : ℝ) ^ 2 + 2 * (P.M₀ : ℝ) * (N₀ : ℝ) + (N₀ : ℝ) ^ 2 +
            4 * (P.M₀ : ℝ) + 4 * (N₀ : ℝ) + 4 := by ring
      nlinarith
    calc
      Real.log ((levelM TP P i : ℝ) + (N₀ : ℝ) + 2)
          ≤ Real.log (((P.M₀ : ℝ) + (N₀ : ℝ) + 2) ^ 2) :=
        Real.log_le_log (by linarith [show (0 : ℝ) ≤ levelM TP P i from Nat.cast_nonneg _, hN0_nn]) h1
      _ = 2 * Real.log ((P.M₀ : ℝ) + (N₀ : ℝ) + 2) := by
        rw [Real.log_pow]; simp
  have hpow_log :
      (Real.log ((levelM TP P i : ℝ) + (N₀ : ℝ) + 2)) ^ TP.p_T ≤
        (2 * logFactor P N₀) ^ TP.p_T :=
    pow_le_pow_left₀ hlog_pos0 hlog_le _
  have hm_double : (levelM TP P i : ℝ) + 1 ≤
      2 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) := by
    have hnn : 0 ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i := by positivity
    linarith
  have hpow_nn : 0 ≤ (2 * logFactor P N₀) ^ TP.p_T :=
    pow_nonneg (by linarith [(logFactor_pos P N₀).le]) _
  have hγr0 : 0 ≤ TP.γ_r (levelM TP P i) := le_trans zero_le_one (hγr_ge _)
  have hMain :
      TP.c_T * ((levelM TP P i : ℝ) + 1) * ((P.k : ℝ) + (st.curRestarts i : ℝ)) *
          ((P.k : ℝ) + 1) * TP.γ_r (levelM TP P i) *
          (Real.log ((levelM TP P i : ℝ) + (N₀ : ℝ) + 2)) ^ TP.p_T ≤
        TP.c_T * (2 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1)) *
          ((P.k : ℝ) + (st.curRestarts i : ℝ)) * ((P.k : ℝ) + 1) * TP.γ_r (P.M₀ ^ 2) *
            (2 * logFactor P N₀) ^ TP.p_T := by
    gcongr
  have hEq :
      TP.c_T * (2 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1)) *
          ((P.k : ℝ) + (st.curRestarts i : ℝ)) * ((P.k : ℝ) + 1) * TP.γ_r (P.M₀ ^ 2) *
            (2 * logFactor P N₀) ^ TP.p_T =
        ((P.k : ℝ) + 1) * (
          2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
            (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
          (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) := by
    unfold restartCostCap; ring
  exact le_trans hCost (hEq ▸ hMain)

/-- Per-level runtime, decremental tree-update, last-level, and active-forest size bounds implied
by `ChainInv`. -/
lemma ChainInv.level_cost_bounds_noHidden {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    (∀ i < P.d, (T.cost (st.scState i) + st.curEnc i : ℝ) ≤
      ((P.k : ℝ) + 1) *
        (levelToolCap TP P N₀ i + (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i)) ∧
    (∀ i < P.d, (st.curDecUpdates i : ℝ) ≤ levelDecCap TP P i) ∧
    (0 < P.d → (st.curLastCost : ℝ) ≤ lastCostCap TP LP P N₀) ∧
    ((st.curLastTreeUpdates : ℝ) ≤ lastTreeCap TP P) ∧
    (∀ i ≤ P.d, ((st.toTreeChain.activeLSF i).F.F.E.card : ℝ) ≤
      (levelM TP P i : ℝ)) := by
  have hB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  have hTPValid : TP.Valid := hTP
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, hγr_m, _, hcT⟩
  rcases hLP with ⟨_, _, _, _, hcLast⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hk_one : (1 : ℝ) ≤ P.k := by exact_mod_cast P.hk
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγr_nonneg : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hγ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / P.k := div_nonneg hγℓ_nonneg hk_pos.le
  have hγ_le_one : TP.γ_ℓ (P.M₀ ^ 2) / P.k ≤ 1 := (div_le_one hk_pos).mpr hγk
  have hhist_spec : ∀ i (hi : i < P.d) (H : LevelHistory T TP P N₀ st i),
      levelM TP P i ≤ P.M₀ ^ 2 ∧
      TP.γ_r (levelM TP P i) ≤ TP.γ_r (P.M₀ ^ 2) ∧
      ((st.updCount i : ℕ) : ℝ) ≤ 4 * (levelM TP P i : ℝ) / (P.k : ℝ) ∧
      ((T.cost (st.scState i) : ℝ) ≤ ((P.k : ℝ) + 1) * (
        2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
          (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
        (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i)) := by
    intro i hi H
    have hm0_le : levelM TP P i ≤ P.M₀ ^ 2 := levelM_le_sq hTPValid hγM₀ hγk i
    have hγr_le : TP.γ_r (levelM TP P i) ≤ TP.γ_r (P.M₀ ^ 2) := hγr_m _ _ hm0_le
    have hupd_le : ((st.updCount i : ℕ) : ℝ) ≤ 4 * (levelM TP P i : ℝ) / (P.k : ℝ) :=
      le_trans H.hThresh (updateThreshold_le_four_div P.k _ _ P.hk)
    exact ⟨hm0_le, hγr_le, hupd_le, H.cost_le_cap_add_restart hTPValid hγM₀ hγk hi⟩
  have hRebReal : (st.curLastRebuilds : ℝ) ≤
      4 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
          (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ)) +
        4 * TP.γ_r (P.M₀ ^ 2) := by
    obtain ⟨⟨H, hReb⟩, _, _⟩ := hInv.hLastCap P.hd
    have hdi : P.d - 1 < P.d := Nat.sub_lt P.hd zero_lt_one
    obtain ⟨_, hγr_le, hupd_le, _⟩ := hhist_spec (P.d - 1) hdi H
    have hSpec := H.hOK.noHidden P.k H.len (levelM TP P (P.d - 1)) N₀ H.D H.ord H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hRec := (hSpec.2.2.2.1 H.s₀ H.len H.hs₀ (le_refl _) (st.bran (P.d - 1))
      (hInv.hBran (P.d - 1) hdi) H.hS0Fresh
      (fun r hr1 hr2 => H.hNoRestartAfterS0 r hr1 (Nat.le_of_lt hr2))).1
    have hsub : Finset.Icc (H.s₀ + 1) H.len ⊆ Finset.Icc 1 H.len := by
      intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
    have hU_sum :
        (((Finset.Icc (H.s₀ + 1) H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) ≤
          (st.updCount (P.d - 1) : ℝ) := by
      rw [← H.hUpd]
      exact_mod_cast Finset.sum_le_sum_of_subset hsub
    have hm_lt : (levelM TP P (P.d - 1) : ℝ) ≤
        (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) + 1 :=
      (levelM_lt_add_one hTPValid P (P.d - 1)).le
    have hdiv_one : 4 * TP.γ_r (P.M₀ ^ 2) / (P.k : ℝ) ≤ 4 * TP.γ_r (P.M₀ ^ 2) := by
      calc
        4 * TP.γ_r (P.M₀ ^ 2) / (P.k : ℝ) ≤ 4 * TP.γ_r (P.M₀ ^ 2) / 1 := by gcongr
        _ = 4 * TP.γ_r (P.M₀ ^ 2) := div_one _
    calc
      (st.curLastRebuilds : ℝ)
          ≤ (((Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.ord H.restarts s).2
                (st.bran (P.d - 1))).length : ℕ) : ℝ) := by
        exact_mod_cast hReb
      _ ≤ TP.γ_r (levelM TP P (P.d - 1)) *
            (((Finset.Icc (H.s₀ + 1) H.len).sum fun s => (H.D.U s).length : ℕ) : ℝ) := hRec
      _ ≤ TP.γ_r (levelM TP P (P.d - 1)) * (st.updCount (P.d - 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hU_sum (le_trans zero_le_one (hγr_ge _))
      _ ≤ TP.γ_r (P.M₀ ^ 2) * (4 * (levelM TP P (P.d - 1) : ℝ) / (P.k : ℝ)) := by gcongr
      _ ≤ TP.γ_r (P.M₀ ^ 2) *
            (4 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
              (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) + 1) / (P.k : ℝ)) := by
        gcongr
      _ = 4 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
            (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ)) +
            4 * TP.γ_r (P.M₀ ^ 2) / (P.k : ℝ) := by ring
      _ ≤ 4 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
            (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ)) +
            4 * TP.γ_r (P.M₀ ^ 2) := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨H⟩ := hInv.hHist i hi
    obtain ⟨hm0, hγr_le, hupd_le, hCost⟩ := hhist_spec i hi H
    have hEncBound : (st.curEnc i : ℝ) ≤
        if i = 0 then
          200 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2)
        else
          5 * TP.γ_r (P.M₀ ^ 2) *
            ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) + 1) := by
      cases i with
      | zero =>
        simp only [↓reduceIte]
        have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
        have hγ1 : 1 ≤ TP.γ_ℓ (P.M₀ ^ 2) := hγℓ_ge (P.M₀ ^ 2)
        have hMγ1 : 1 ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := one_le_mul_of_one_le_of_one_le hM1 hγ1
        have hlt0 : (levelM TP P 0 : ℝ) < (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 1 := by
          simpa using levelM_lt_add_one hTPValid P 0
        have hm0' : (levelM TP P 0 : ℝ) ≤ 2 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := by linarith
        have hupd0 : (st.updCount 0 : ℝ) ≤ 8 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := by
          calc
            (st.updCount 0 : ℝ) ≤ 4 * (levelM TP P 0 : ℝ) / (P.k : ℝ) := hupd_le
            _ ≤ 4 * (2 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2)) / 1 := by gcongr
            _ = 8 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := by ring
        have hsum : (levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) ≤ 10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := by
          linarith
        have hlog : Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2) ≤
            Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) :=
          Real.log_le_log (by positivity) (by linarith)
        have hlog0 : 0 ≤ Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2) :=
          Real.log_nonneg (by linarith [show (0 : ℝ) ≤ levelM TP P 0 from Nat.cast_nonneg _,
            show (0 : ℝ) ≤ st.updCount 0 from Nat.cast_nonneg _])
        calc
          (st.curEnc 0 : ℝ) ≤ 20 * ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ)) *
              Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2) := hInv.hEnc0
          _ ≤ 20 * (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2)) *
                Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) := by
            gcongr
          _ = 200 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
                Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) := by ring
      | succ i' =>
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        have hi'_lt : i' < P.d := Nat.lt_of_succ_lt hi
        obtain ⟨H'⟩ := hInv.hHist i' hi'_lt
        obtain ⟨hm0', hγr_le', hupd_le', _⟩ := hhist_spec i' hi'_lt H'
        have hSpec' := H'.hOK.noHidden P.k H'.len (levelM TP P i') N₀ H'.D H'.ord H'.restarts
          P.hk H'.hG0 H'.hD H'.hLen H'.hℓPos H'.hOrd H'.hInitMBound H'.hInitNBound H'.hRestartsLt
          (by rw [H'.hUpd]; exact H'.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hEncSpec := (hSpec'.2.2.2.1 H'.s₀ H'.len H'.hs₀ (le_refl _) (st.bran i')
          (hInv.hBran i' hi'_lt) H'.hS0Fresh
          (fun r hr1 hr2 => H'.hNoRestartAfterS0 r hr1 (Nat.le_of_lt hr2))).2
        have hsub : Finset.Icc (H'.s₀ + 1) H'.len ⊆ Finset.Icc 1 H'.len := by
          intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
        have hU_sum :
            (((Finset.Icc (H'.s₀ + 1) H'.len).sum fun s => (H'.D.U s).length : ℕ) : ℝ) ≤
              (st.updCount i' : ℝ) := by
          rw [← H'.hUpd]
          exact_mod_cast Finset.sum_le_sum_of_subset hsub
        have hEnc1 : (st.curEnc (i' + 1) : ℝ) ≤
            (((Finset.Icc (H'.s₀ + 1) H'.len).sum fun s =>
              (T.S (T.runOrdAfterRestarts P.k (levelM TP P i') N₀ H'.D H'.ord H'.restarts (s - 1))
                (st.bran i')).batchEnc
                ((T.runOrdAfterUpdate P.k (levelM TP P i') N₀ H'.D H'.ord H'.restarts s).2
                  (st.bran i')) : ℕ) : ℝ) := by
          exact_mod_cast H'.hEncLe hi
        have hm'_lt : (levelM TP P i' : ℝ) ≤
            (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i' + 1 :=
          (levelM_lt_add_one hTPValid P i').le
        have hdivk : (1 : ℝ) / (P.k : ℝ) ≤ 1 := by
          calc
            (1 : ℝ) / (P.k : ℝ) ≤ 1 / 1 := by gcongr
            _ = 1 := div_one 1
        have hγr'_nn : 0 ≤ TP.γ_r (levelM TP P i') := le_trans zero_le_one (hγr_ge _)
        calc
          (st.curEnc (i' + 1) : ℝ)
              ≤ TP.γ_r (levelM TP P i') * ((levelM TP P i' : ℝ) / (P.k : ℝ) +
                  (((Finset.Icc (H'.s₀ + 1) H'.len).sum fun s => (H'.D.U s).length : ℕ) : ℝ)) :=
            le_trans hEnc1 hEncSpec
          _ ≤ TP.γ_r (levelM TP P i') * ((levelM TP P i' : ℝ) / (P.k : ℝ) + (st.updCount i' : ℝ)) := by
            exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hU_sum) hγr'_nn
          _ ≤ TP.γ_r (P.M₀ ^ 2) * ((levelM TP P i' : ℝ) / (P.k : ℝ) + 4 * (levelM TP P i' : ℝ) / (P.k : ℝ)) := by
            gcongr
          _ = 5 * TP.γ_r (P.M₀ ^ 2) * ((levelM TP P i' : ℝ) / (P.k : ℝ)) := by ring
          _ ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                (((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i' + 1) / (P.k : ℝ)) := by
            gcongr
          _ = 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i' / (P.k : ℝ) +
                  1 / (P.k : ℝ)) := by
            ring
          _ ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i' / (P.k : ℝ) + 1) := by
            gcongr
    have hEncNonneg : 0 ≤
        (if i = 0 then
          200 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2)
        else
          5 * TP.γ_r (P.M₀ ^ 2) *
            ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) + 1)) := by
      split_ifs
      · have hlog10 : 0 ≤ Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2) :=
          Real.log_nonneg (by
            have := mul_nonneg (Nat.cast_nonneg (α := ℝ) P.M₀) hγℓ_nonneg
            linarith)
        positivity
      · positivity
    have hEncScaled : (st.curEnc i : ℝ) ≤ ((P.k : ℝ) + 1) *
        (if i = 0 then
          200 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * Real.log (10 * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) + 2)
        else
          5 * TP.γ_r (P.M₀ ^ 2) *
            ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (i - 1) / (P.k : ℝ) + 1)) := by
      nlinarith
    unfold levelToolCap
    linarith
  · intro i hi
    obtain ⟨H⟩ := hInv.hHist i hi
    obtain ⟨_, _, hupd_le, _⟩ := hhist_spec i hi H
    have hSpec := H.hOK.noHidden P.k H.len (levelM TP P i) N₀ H.D H.ord H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hs0_spec := hSpec.1 H.s₀ H.hs₀ (st.bran i) (hInv.hBran i hi)
    have hsubE : (T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P i) N₀ H.D H.ord H.restarts H.s₀)
        (st.bran i)).F.F.E ⊆ (H.D.G H.s₀).E :=
      hs0_spec.1.2.1.2.2.2.2.2.1
    have hdec_le : st.curDecUpdates i ≤ (H.D.G H.s₀).m := by
      have hDec := H.hDecEq
      have h1 : st.curDecUpdates i ≤
          (T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P i) N₀ H.D H.ord H.restarts H.s₀)
            (st.bran i)).F.F.E.card := by
        omega
      exact le_trans h1 (Finset.card_le_card hsubE)
    have hm_s0 : (H.D.G H.s₀).m ≤
        (H.D.G 0).m + (Finset.Icc 1 H.s₀).sum (fun s => (H.D.U s).length) :=
      dynamic_m_le H.hD H.s₀ H.hs₀
    have hsum_s0 : (Finset.Icc 1 H.s₀).sum (fun s => (H.D.U s).length) ≤ st.updCount i := by
      rw [← H.hUpd]
      apply Finset.sum_le_sum_of_subset
      intro s hs
      have hs0 := H.hs₀
      simp only [Finset.mem_Icc] at hs ⊢
      omega
    have hm_s0_real : ((H.D.G H.s₀).m : ℝ) ≤ (levelM TP P i : ℝ) + (st.updCount i : ℝ) := by
      have h1 : (H.D.G H.s₀).m ≤ levelM TP P i + st.updCount i :=
        le_trans hm_s0 (Nat.add_le_add H.hInitMBound hsum_s0)
      exact_mod_cast h1
    have hupd_4m : (st.updCount i : ℝ) ≤ 4 * (levelM TP P i : ℝ) := by
      calc
        (st.updCount i : ℝ) ≤ 4 * (levelM TP P i : ℝ) / (P.k : ℝ) := hupd_le
        _ ≤ 4 * (levelM TP P i : ℝ) / 1 := by gcongr
        _ = 4 * (levelM TP P i : ℝ) := div_one _
    have hm_lt : (levelM TP P i : ℝ) ≤
        (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1 :=
      (levelM_lt_add_one hTPValid P i).le
    unfold levelDecCap
    calc
      (st.curDecUpdates i : ℝ) ≤ ((H.D.G H.s₀).m : ℝ) := by exact_mod_cast hdec_le
      _ ≤ (levelM TP P i : ℝ) + (st.updCount i : ℝ) := hm_s0_real
      _ ≤ 5 * (levelM TP P i : ℝ) := by linarith
      _ ≤ 5 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) := by gcongr
  · intro hd
    obtain ⟨_, hCost, _⟩ := hInv.hLastCap hd
    have hlog_arg_pos : 0 < (levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2 := by
      positivity
    have hlog_pos : 0 ≤ Real.log ((levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2) := by
      apply Real.log_nonneg
      linarith [show (0 : ℝ) ≤ (levelM TP P P.d : ℝ) from Nat.cast_nonneg _,
        show (0 : ℝ) ≤ (st.G 0).n from Nat.cast_nonneg _]
    have hld_sq : (levelM TP P P.d : ℝ) ≤ (P.M₀ : ℝ) ^ 2 := by
      have := levelM_le_sq hTPValid hγM₀ hγk P.d
      exact_mod_cast this
    have hG0n_real : ((st.G 0).n : ℝ) ≤ N₀ := by exact_mod_cast hInv.hG0n
    have hlog_le : Real.log ((levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2) ≤
        2 * logFactor P N₀ := by
      unfold logFactor
      have harg_le : (levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2 ≤
          ((P.M₀ : ℝ) + (N₀ : ℝ) + 2) ^ 2 := by
        have hM0 : (0 : ℝ) ≤ P.M₀ := Nat.cast_nonneg P.M₀
        have hN0 : (0 : ℝ) ≤ N₀ := Nat.cast_nonneg N₀
        nlinarith
      calc Real.log ((levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2)
          ≤ Real.log (((P.M₀ : ℝ) + (N₀ : ℝ) + 2) ^ 2) := Real.log_le_log hlog_arg_pos harg_le
        _ = 2 * Real.log ((P.M₀ : ℝ) + (N₀ : ℝ) + 2) := by rw [Real.log_pow]; norm_num
    have hlog_pow :
        (Real.log ((levelM TP P P.d : ℝ) + ((st.G 0).n : ℝ) + 2)) ^ LP.p_last ≤
          (2 * logFactor P N₀) ^ LP.p_last :=
      pow_le_pow_left₀ hlog_pos hlog_le _
    unfold lastCostCap
    have hReb1 : ((st.curLastRebuilds + 1 : ℕ) : ℝ) ≤
        4 * TP.γ_r (P.M₀ ^ 2) * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
            (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ) +
          4 * TP.γ_r (P.M₀ ^ 2) + 1 := by
      push_cast
      calc
        (st.curLastRebuilds : ℝ) + 1
            ≤ 4 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
                  (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ)) +
                4 * TP.γ_r (P.M₀ ^ 2) + 1 := by linarith
        _ = 4 * TP.γ_r (P.M₀ ^ 2) * (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
                (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ) +
              4 * TP.γ_r (P.M₀ ^ 2) + 1 := by ring
    refine le_trans hCost ?_
    exact mul_le_mul hReb1 (mul_le_mul_of_nonneg_left hlog_pow (by positivity))
      (by positivity) (by positivity)
  · obtain ⟨_, _, hTree⟩ := hInv.hLastCap P.hd
    unfold lastTreeCap
    refine le_trans hTree ?_
    have hnonneg : 0 ≤ (levelM TP P P.d : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (by linarith) hnonneg
  · intro i hi
    have hmi := (hB i hi).2.2.1
    have hsubE : (st.toTreeChain.activeLSF i).F.F.E ⊆ (st.G i).E := by
      by_cases hlt : i < P.d
      · simp only [TreeChain.activeLSF, ChainState.toTreeChain, hlt, ↓reduceIte]
        exact ((hB i hi).2.2.2.2 hlt (st.bran i) (hInv.hBran i hlt)).1.2.1.2.2.2.2.2.1
      · have hieq : i = P.d := by omega
        subst hieq
        simp only [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl, ↓reduceIte]
        exact (hInv.hLastHolds st.lastBran hInv.hLastBran).2.1.2.2.2.2.2.1
    exact le_trans (by exact_mod_cast Finset.card_le_card hsubE) hmi

end CostBounds

end MinCostFlow.Chain.Ordered
