module

public import MinCostFlow.Chain.Algorithm1BudgetHelpers
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cost Bounds and `rebuildSuffix` Specification (Algorithm 1 Proofs Helpers)

Split from `MinCostFlow.Chain.Algorithm1Proofs`: `CostBounds` (`LevelHistory.cost_le_cap_add_restart`, `level_cost_bounds*`) and `RebuildSuffixSpec` (`rebuildSuffix_spec*`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section CostBounds

lemma LevelHistory.cost_le_cap_add_restart {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} {i : ℕ} (_hi : i < P.d) (H : LevelHistory T TP P N₀ st i) :
    (T.cost (st.scState i) : ℝ) ≤
      2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
        (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
      (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i := by
  have hTPValid : TP.Valid := hTP
  rcases hTP with ⟨_, _, hγℓ_ge, _, _, _, hγr_ge, hγr_m, _, hcT⟩
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hγr_ge (P.M₀ ^ 2))
  have hγℓ_nn : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hm0_le : levelM TP P i ≤ P.M₀ ^ 2 := levelM_le_sq hTPValid hγM₀ hγk i
  have hm0_lt := levelM_lt_add_one hTPValid P i
  have hγr_le : TP.γ_r (levelM TP P i) ≤ TP.γ_r (P.M₀ ^ 2) := hγr_m _ _ hm0_le
  have hSpec := hT P.k H.len (levelM TP P i) N₀ H.D H.restarts
    P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
    (by rw [H.hUpd]; exact H.hThresh)
  have hCost := hSpec.2.2.2.2
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
          TP.γ_r (levelM TP P i) * (Real.log ((levelM TP P i : ℝ) + (N₀ : ℝ) + 2)) ^ TP.p_T ≤
        TP.c_T * (2 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1)) *
          ((P.k : ℝ) + (st.curRestarts i : ℝ)) * TP.γ_r (P.M₀ ^ 2) *
            (2 * logFactor P N₀) ^ TP.p_T := by
    gcongr
  have hEq :
      TP.c_T * (2 * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1)) *
          ((P.k : ℝ) + (st.curRestarts i : ℝ)) * TP.γ_r (P.M₀ ^ 2) *
            (2 * logFactor P N₀) ^ TP.p_T =
        2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
          (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
        (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i := by
    unfold restartCostCap; ring
  exact le_trans hCost (hEq ▸ hMain)

lemma ChainInv.level_cost_bounds_noHidden {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    (∀ i < P.d, (T.cost (st.scState i) + st.curEnc i : ℝ) ≤
      levelToolCap TP P N₀ i + (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) ∧
    (∀ i < P.d, (st.curDecUpdates i : ℝ) ≤ levelDecCap TP P i) ∧
    (0 < P.d → (st.curLastCost : ℝ) ≤ lastCostCap TP LP P N₀) ∧
    ((st.curLastTreeUpdates : ℝ) ≤ lastTreeCap TP P) ∧
    (∀ i ≤ P.d, ((st.toTreeChain.activeLSF i).F.F.E.card : ℝ) ≤
      (levelM TP P i : ℝ)) := by
  have hB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
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
      ((T.cost (st.scState i) : ℝ) ≤
        2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ i + 1) *
          (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
        (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) := by
    intro i hi H
    have hm0_le : levelM TP P i ≤ P.M₀ ^ 2 := levelM_le_sq hTPValid hγM₀ hγk i
    have hγr_le : TP.γ_r (levelM TP P i) ≤ TP.γ_r (P.M₀ ^ 2) := hγr_m _ _ hm0_le
    have hupd_le : ((st.updCount i : ℕ) : ℝ) ≤ 4 * (levelM TP P i : ℝ) / (P.k : ℝ) :=
      le_trans H.hThresh (updateThreshold_le_four_div P.k _ _ P.hk)
    exact ⟨hm0_le, hγr_le, hupd_le, H.cost_le_cap_add_restart hTPValid hT hγM₀ hγk hi⟩
  have hRebReal : (st.curLastRebuilds : ℝ) ≤
      4 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) *
          (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (P.d - 1) / (P.k : ℝ)) +
        4 * TP.γ_r (P.M₀ ^ 2) := by
    obtain ⟨⟨H, hReb⟩, _, _⟩ := hInv.hLastCap P.hd
    have hdi : P.d - 1 < P.d := Nat.sub_lt P.hd zero_lt_one
    obtain ⟨_, hγr_le, hupd_le, _⟩ := hhist_spec (P.d - 1) hdi H
    have hSpec := hT P.k H.len (levelM TP P (P.d - 1)) N₀ H.D H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh)
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
              ((T.runAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.restarts s).2
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
        have hSpec' := hT P.k H'.len (levelM TP P i') N₀ H'.D H'.restarts
          P.hk H'.hG0 H'.hD H'.hLen H'.hℓPos H'.hInitMBound H'.hInitNBound H'.hRestartsLt
          (by rw [H'.hUpd]; exact H'.hThresh)
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
              (T.S (T.runAfterRestarts P.k (levelM TP P i') N₀ H'.D H'.restarts (s - 1)) (st.bran i')).batchEnc
                ((T.runAfterUpdate P.k (levelM TP P i') N₀ H'.D H'.restarts s).2 (st.bran i')) : ℕ) : ℝ) := by
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
    unfold levelToolCap
    linarith
  · intro i hi
    obtain ⟨H⟩ := hInv.hHist i hi
    obtain ⟨_, _, hupd_le, _⟩ := hhist_spec i hi H
    have hSpec := hT P.k H.len (levelM TP P i) N₀ H.D H.restarts
      P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
      (by rw [H.hUpd]; exact H.hThresh)
    have hs0_spec := hSpec.1 H.s₀ H.hs₀ (st.bran i) (hInv.hBran i hi)
    have hsubE : (T.lsfs (T.runAfterRestarts P.k (levelM TP P i) N₀ H.D H.restarts H.s₀) (st.bran i)).F.F.E ⊆
        (H.D.G H.s₀).E :=
      hs0_spec.1.2.1.2.2.2.2.2.1
    have hdec_le : st.curDecUpdates i ≤ (H.D.G H.s₀).m := by
      have hDec := H.hDecEq
      have h1 : st.curDecUpdates i ≤
          (T.lsfs (T.runAfterRestarts P.k (levelM TP P i) N₀ H.D H.restarts H.s₀) (st.bran i)).F.F.E.card := by
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

lemma ChainInv.level_cost_bounds {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    (∀ i < P.d, (T.cost (st.scState i) + st.curEnc i : ℝ) ≤
      levelToolCap TP P N₀ i + (st.curRestarts i : ℝ) * restartCostCap TP P N₀ i) ∧
    (∀ i < P.d, (st.curDecUpdates i : ℝ) ≤ levelDecCap TP P i) ∧
    (0 < P.d → (st.curLastCost : ℝ) ≤ lastCostCap TP LP P N₀) ∧
    ((st.curLastTreeUpdates : ℝ) ≤ lastTreeCap TP P) ∧
    (∀ i ≤ P.d, ((st.toTreeChain.activeLSF i).F.F.E.card : ℝ) ≤
      (levelM TP P i : ℝ)) :=
  hInv.level_cost_bounds_noHidden hTP hLP hT.toNoHidden hγM₀ hγk

end CostBounds

section RebuildSuffixSpec

/-- Partial `TreeChain` formed from `(G, sc, bran)` for reading `chainLen` and `chainGrad`
up to `idx`. -/
noncomputable def mkPartialChain (T : SparseCoreRestartTool) (P : ChainParams)
    (G : ℕ → MGraph) (sc : ℕ → T.State) (bran : ℕ → ℕ) (Gdummy : MGraph) : TreeChain where
  d := P.d
  k := P.k
  G := G
  lsfs := fun j => T.lsfs (sc j)
  bran := bran
  S := fun j => T.S (sc j)
  emb := fun j => T.emb (sc j)
  lastK := 1
  lastLSFs := fun _ => ⟨Gdummy, ⟨Gdummy, ∅⟩, fun _ => 1⟩
  lastBran := 0

lemma chainLen_congr_params {T : SparseCoreRestartTool} {P : ChainParams}
    {C : TreeChain} (hCd : C.d = P.d)
    {G : ℕ → MGraph} {sc : ℕ → T.State} {bran : ℕ → ℕ} {Gd : MGraph}
    (ℓ₀ : ℕ → ℝ) {idx : ℕ} (hidx : idx ≤ P.d)
    (hG : ∀ j < idx, C.G j = G j)
    (hL : ∀ j < idx, C.lsfs j (C.bran j) = T.lsfs (sc j) (bran j)) :
    C.chainLen ℓ₀ idx = (mkPartialChain T P G sc bran Gd).chainLen ℓ₀ idx := by
  apply chainLen_congr_lt ℓ₀ idx hG
  intro j hj
  have hjC : j < C.d := by omega
  have hjP : j < P.d := by omega
  have h1 : C.activeLSF j = C.lsfs j (C.bran j) := by
    unfold TreeChain.activeLSF; exact ite_eq_left_iff.mpr fun h => absurd hjC h
  have h2 : (mkPartialChain T P G sc bran Gd).activeLSF j = T.lsfs (sc j) (bran j) := by
    unfold TreeChain.activeLSF
    exact ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hjP) h
  rw [h1, h2]
  exact hL j hj

lemma chainGrad_congr_params {T : SparseCoreRestartTool} {P : ChainParams}
    {C : TreeChain} (hCd : C.d = P.d)
    {G : ℕ → MGraph} {sc : ℕ → T.State} {bran : ℕ → ℕ} {Gd : MGraph}
    (g₀ : ℕ → ℝ) {idx : ℕ} (hidx : idx ≤ P.d)
    (hG : ∀ j < idx, C.G j = G j)
    (hL : ∀ j < idx, C.lsfs j (C.bran j) = T.lsfs (sc j) (bran j)) :
    C.chainGrad g₀ idx = (mkPartialChain T P G sc bran Gd).chainGrad g₀ idx := by
  apply chainGrad_congr_lt g₀ idx hG
  intro j hj
  have hjC : j < C.d := by omega
  have hjP : j < P.d := by omega
  have h1 : C.activeLSF j = C.lsfs j (C.bran j) := by
    unfold TreeChain.activeLSF; exact ite_eq_left_iff.mpr fun h => absurd hjC h
  have h2 : (mkPartialChain T P G sc bran Gd).activeLSF j = T.lsfs (sc j) (bran j) := by
    unfold TreeChain.activeLSF
    exact ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hjP) h
  rw [h1, h2]
  exact hL j hj

lemma levelHistory_of_init (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (_hTP : TP.Valid) (N₀ : ℕ) (st : ChainState T P) (i : ℕ) (_hi : i < P.d)
    (hGiValid : (st.G i).IsValid)
    (hGiM : ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ))
    (hGiN : (st.G i).n ≤ N₀)
    (hℓPos : ∀ e ∈ (st.G i).E, 0 < st.toTreeChain.chainLen st.ℓ i e)
    (hInit : st.scState i = T.init P.k (levelM TP P i) N₀ (st.G i) (st.toTreeChain.chainLen st.ℓ i)
      (st.toTreeChain.chainGrad st.g i))
    (hUpd : st.updCount i = 0)
    (hCurFwd : st.curFwd i = 0)
    (hDec : st.curDecUpdates i = 0)
    (hCurRest : st.curRestarts i = 0)
    (hEnc0 : i = 0 → st.curEnc 0 = 0)
    (hEncNext : i + 1 < P.d → st.curEnc (i + 1) = 0) :
    Nonempty (LevelHistory T TP P N₀ st i) := by
  let D : DynamicInstance :=
    { G := fun _ => st.G i
      U := fun _ => []
      ℓ := fun _ => st.toTreeChain.chainLen st.ℓ i
      g := fun _ => st.toTreeChain.chainGrad st.g i }
  refine ⟨{
    D := D
    len := 0
    s₀ := 0
    hs₀ := le_refl 0
    restarts := fun _ => []
    hRestartsLt := fun _ _ _ h => by cases h
    hRestartsCount := by simp [hCurRest]
    hS0Fresh := Or.inl rfl
    hNoRestartAfterS0 := fun _ hr1 hr2 => by omega
    hG0 := hGiValid
    hD := fun _ ht1 ht2 => by omega
    hLen := fun _ ht1 ht2 => by omega
    hℓPos := fun _ _ e he => hℓPos e he
    hEndG := rfl
    hEndℓ := fun _ _ => rfl
    hEndg := rfl
    hUpd := by simp [hUpd]
    hThresh := by rw [hUpd]; simp [updateThreshold_nonneg]
    hInitMBound := by exact_mod_cast hGiM
    hInitNBound := hGiN
    hRun := by
      simp only [SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
        List.foldl_nil]
      exact hInit
    branchSeq := fun _ => 0
    hBranch := fun _ => P.hk
    hBranchTail := fun _ hs1 hs2 => by omega
    hWinFwdBound := by simp
    hCurFwdEq := by simp [hCurFwd]
    hDecEq := by
      rw [hInit]
      simp [hDec, SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate, D]
    hEnc0Le := fun h0 => by simp [hEnc0 h0]
    hEncLe := fun h1 => by simp [hEncNext h1] }⟩

theorem rebuildSuffix_spec_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ)
      (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      idx + rem = P.d →
      (G idx).IsValid →
      (G idx).V ⊆ (G 0).V →
      (G 0).n ≤ N₀ →
      ((G idx).m : ℝ) ≤ (levelM TP P idx : ℝ) →
      (∀ e ∈ (G idx).E, 0 < (mkPartialChain T P G sc bran (G idx)).chainLen ℓ₀ idx e) →
      let res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      let G' := res.1
      let sc' := res.2.1
      let bran' := res.2.2.1
      let upd' := res.2.2.2.1
      let cEnc' := res.2.2.2.2.1
      let cDec' := res.2.2.2.2.2.1
      let cFwd' := res.2.2.2.2.2.2.1
      let lastRes := res.2.2.2.2.2.2.2.1
      let lastCost := res.2.2.2.2.2.2.2.2
      (∀ j ≤ idx, G' j = G j) ∧
      (∀ j < idx,
        sc' j = sc j ∧ bran' j = bran j ∧ upd' j = upd j ∧
        cEnc' j = cEnc j ∧ cDec' j = cDec j ∧ cFwd' j = cFwd j) ∧
      (∀ j, idx ≤ j → j < P.d →
        bran' j = 0 ∧ upd' j = 0 ∧
        cEnc' j = 0 ∧ cDec' j = 0 ∧ cFwd' j = 0 ∧
        (G' j).IsValid ∧ (G' j).V ⊆ (G' 0).V ∧
        ((G' j).m : ℝ) ≤ (levelM TP P j : ℝ) ∧
        (∀ e ∈ (G' j).E, 0 < (mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j e) ∧
        sc' j = T.init P.k (levelM TP P j) N₀ (G' j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainGrad g₀ j) ∧
        G' (j + 1) = T.S (sc' j) 0) ∧
      (G' P.d).IsValid ∧
      (G' P.d).V ⊆ (G' 0).V ∧
      ((G' P.d).m : ℝ) ≤ (levelM TP P P.d : ℝ) ∧
      (∀ e ∈ (G' P.d).E, 0 < (mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ P.d e) ∧
      0 < lastRes.1 ∧
      (∀ j < lastRes.1, (lastRes.2 j).Holds (G' P.d)
        ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ P.d)
        (LP.σ_last (G' P.d).n)) ∧
      (∀ e ∈ (G' P.d).E,
        (∑ j ∈ Finset.range lastRes.1, (lastRes.2 j).wstr e) / (lastRes.1 : ℝ) ≤
          LP.σ_mwu (G' P.d).n) ∧
      (∀ j < lastRes.1, ∀ u ∈ (G' P.d).V, ∀ v ∈ (G' P.d).V,
        (G' P.d).Connected u v → (lastRes.2 j).F.F.Connected u v) ∧
      ((lastCost : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((G' 0).n : ℝ) + 2)) ^
            LP.p_last) := by
  have hcLast := hLP.2.2.2.2
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  intro rem
  induction rem with
  | zero =>
    intro idx G sc bran upd cEnc cDec cFwd hsum hGValid hGV _hG0n hGm hℓ
    have hidx : idx = P.d := by omega
    subst hidx
    dsimp only [rebuildSuffix]
    have hLspec := hL (G P.d) _ hGValid hℓ
    have hGdn : (G P.d).n ≤ (G 0).n := Finset.card_le_card hGV
    have hlog_pos0 : 0 ≤ Real.log (((G P.d).m : ℝ) + ((G P.d).n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (G P.d).m from Nat.cast_nonneg _,
        show (0 : ℝ) ≤ (G P.d).n from Nat.cast_nonneg _])
    have hlog_le : Real.log (((G P.d).m : ℝ) + ((G P.d).n : ℝ) + 2) ≤
        Real.log ((levelM TP P P.d : ℝ) + ((G 0).n : ℝ) + 2) := by
      apply Real.log_le_log (by positivity)
      have hn_real : ((G P.d).n : ℝ) ≤ (G 0).n := by exact_mod_cast hGdn
      linarith
    have hpow_log :
        (Real.log (((G P.d).m : ℝ) + ((G P.d).n : ℝ) + 2)) ^ LP.p_last ≤
          (Real.log ((levelM TP P P.d : ℝ) + ((G 0).n : ℝ) + 2)) ^ LP.p_last :=
      pow_le_pow_left₀ hlog_pos0 hlog_le _
    have hCost' : (L.cost (G P.d) : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((G 0).n : ℝ) + 2)) ^ LP.p_last := by
      refine le_trans hLspec.2.2.2.2 ?_
      apply mul_le_mul _ hpow_log (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ hcLast
      have : ((G P.d).m : ℝ) + 1 ≤ (levelM TP P P.d : ℝ) + 1 := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
      fun j hj1 hj2 => absurd hj2 (by omega),
      hGValid, hGV, hGm, hℓ, hLspec.1, hLspec.2.1, hLspec.2.2.1, hLspec.2.2.2.1, hCost'⟩
  | succ rem' ih =>
    intro idx G sc bran upd cEnc cDec cFwd hsum hGValid hGV hG0n hGm hℓ
    dsimp only [rebuildSuffix]
    set Cpartial : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    set ℓi := Cpartial.chainLen ℓ₀ idx
    set gi := Cpartial.chainGrad g₀ idx
    set Gi := G idx
    set sc_i := T.init P.k (levelM TP P idx) N₀ Gi ℓi gi
    set Gi1 := T.S sc_i 0
    set G1 := fun j => if j = idx + 1 then Gi1 else G j
    set sc1 := fun j => if j = idx then sc_i else sc j
    set bran1 := fun j => if j = idx then 0 else bran j
    set upd1 := fun j => if j = idx then 0 else upd j
    set cEnc1 := fun j => if j = idx then 0 else cEnc j
    set cDec1 := fun j => if j = idx then 0 else cDec j
    set cFwd1 := fun j => if j = idx then 0 else cFwd j
    have hidx_lt : idx < P.d := by omega
    have hℓi_pos : ∀ e ∈ Gi.E, 0 < ℓi e := by
      intro e he
      have heq : ℓi = (mkPartialChain T P G sc bran Gi).chainLen ℓ₀ idx := by
        apply chainLen_congr_params rfl ℓ₀ (Nat.le_of_lt hidx_lt)
        · intro j _; rfl
        · intro j _; rfl
      rw [heq]; exact hℓ e he
    let D0 : DynamicInstance :=
      { G := fun _ => Gi, U := fun _ => [], ℓ := fun _ => ℓi, g := fun _ => gi }
    have hD0ℓ : ∀ s ≤ 0, ∀ e ∈ (D0.G s).E, 0 < D0.ℓ s e := fun _ _ e he => hℓi_pos e he
    have hGin : Gi.n ≤ N₀ := le_trans (Finset.card_le_card hGV) hG0n
    have hSpec0 := hT P.k 0 (levelM TP P idx) N₀ D0 (fun _ => [])
      P.hk hGValid (fun _ ht1 ht2 => by omega) (fun _ ht1 ht2 => by omega)
      hD0ℓ (by exact_mod_cast hGm) hGin (fun _ _ _ h => by cases h) (by simp [updateThreshold_nonneg])
    have hAt0 := hSpec0.1 0 (le_refl 0) 0 P.hk
    dsimp only [D0, SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
      List.foldl_nil] at hAt0
    have hHolds0 : (T.lsfs sc_i 0).Holds Gi ℓi (TP.σ P.k Gi.n) := hAt0.1
    have hSp0 : IsSparsifiedCoreGraphAt Gi (T.lsfs sc_i 0) ℓi (P.k : ℝ)
        (TP.γ_ℓ (levelM TP P idx)) (TP.γ_c (levelM TP P idx)) (levelM TP P idx)
        Gi1 (T.emb sc_i 0) := hAt0.2.1
    have hGi1_Valid : Gi1.IsValid := by
      have hCore := coreGraph_isValid hGValid hHolds0.2.1
      intro e he
      have hEnd := hSp0.1.2.2 e he
      have hc := hCore e (hSp0.1.2.1 he)
      rw [hEnd.1, hEnd.2]
      exact ⟨hSp0.2.1.1 hc.1, hSp0.2.1.1 hc.2⟩
    have hG1_idx1_Valid : (G1 (idx + 1)).IsValid := by
      simp only [G1, ↓reduceIte]; exact hGi1_Valid
    have hG1_0 : G1 0 = G 0 := by simp [G1]
    have hG1_idx1_V : (G1 (idx + 1)).V ⊆ (G1 0).V := by
      rw [hG1_0]; simp only [G1, ↓reduceIte]
      exact Finset.Subset.trans (Finset.Subset.trans hSp0.1.1 hHolds0.2.1.2.2.1) hGV
    have hG1_idx1_m : ((G1 (idx + 1)).m : ℝ) ≤ (levelM TP P (idx + 1) : ℝ) := by
      simp only [G1, ↓reduceIte]
      have hlm_sq : levelM TP P idx ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk idx
      have hγ_le_M0 : TP.γ_ℓ (levelM TP P idx) ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.2.1 _ _ hlm_sq
      have hcard : (Gi1.m : ℝ) ≤ (levelM TP P idx : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / (P.k : ℝ) := by
        unfold MGraph.m
        exact le_trans hSp0.2.2.2.2.2 (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hγ_le_M0 (Nat.cast_nonneg _)) hk_pos.le)
      exact_mod_cast levelM_step_nat hTP hγk hcard
    have hℓ1 : ∀ e ∈ (G1 (idx + 1)).E,
        0 < (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ (idx + 1) e := by
      intro e he
      simp only [G1, ↓reduceIte] at he
      have heGi : e ∈ Gi.E := (Finset.mem_sdiff.mp (hSp0.1.2.1 he)).1
      have hw1 : 1 ≤ (T.lsfs sc_i 0).wstr e := by
        have hnonneg : ∀ f ∈ Gi.E, 0 ≤ ℓi f := fun f hf => (hℓi_pos f hf).le
        exact le_trans (one_le_stretch hHolds0.2.1.2.2.2.2 hnonneg heGi) (hHolds0.2.2.2 e heGi).1
      have hPre : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ idx = ℓi := by
        apply chainLen_congr_lt ℓ₀ idx (fun j hj => by
          change G1 j = G j; simp [G1, show j ≠ idx + 1 by omega])
        · intro j hj
          have hjlt : j < P.d := by omega
          have hL1 : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).activeLSF j =
              T.lsfs (sc1 j) (bran1 j) := by
            unfold TreeChain.activeLSF
            exact ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hjlt) h
          have hL2 : Cpartial.activeLSF j = T.lsfs (sc j) (bran j) := by
            unfold TreeChain.activeLSF
            exact ite_eq_left_iff.mpr fun h => absurd (by simpa [Cpartial] using hjlt) h
          rw [hL1, hL2]
          simp [sc1, bran1, show j ≠ idx by omega]
      have hLidx : (mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).activeLSF idx = T.lsfs sc_i 0 := by
        unfold TreeChain.activeLSF
        rw [ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hidx_lt) h]
        simp [mkPartialChain, sc1, bran1]
      change 0 < coreLen ((mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).activeLSF idx)
          ((mkPartialChain T P G1 sc1 bran1 (G1 (idx + 1))).chainLen ℓ₀ idx) e
      rw [hLidx, hPre]
      unfold coreLen
      exact mul_pos (lt_of_lt_of_le zero_lt_one hw1) (hℓi_pos e heGi)
    have hIH := ih (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1 (by omega)
      hG1_idx1_Valid hG1_idx1_V (hG1_0 ▸ hG0n) hG1_idx1_m hℓ1
    rcases hIH with ⟨hIG, hIPre, hISuf, hGdV, hGdSub, hGdm, hGdℓ, hLk, hLH, hLM, hLS, hLC⟩
    have hG'eq : ∀ j ≤ idx,
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j =
          G j := by
      intro j hj
      rw [hIG j (Nat.le_succ_of_le hj)]
      simp [G1, show j ≠ idx + 1 by omega]
    have hG'idx :
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 idx =
          Gi := hG'eq idx (le_refl idx)
    have hPreEq : ∀ j < idx,
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 j = sc j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.1 j = bran j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.1 j = upd j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.2.1 j = cEnc j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.2.2.1 j = cDec j ∧
        (rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (idx + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.2.2.2.2.1 j = cFwd j := by
      intro j hj
      have hj1 : j < idx + 1 := Nat.lt_succ_of_lt hj
      have hne : j ≠ idx := Nat.ne_of_lt hj
      rcases hIPre j hj1 with ⟨a1, a2, a3, a4, a5, a6⟩
      simp only [sc1, bran1, upd1, cEnc1, cDec1, cFwd1, hne, ↓reduceIte]
        at a1 a2 a3 a4 a5 a6
      exact ⟨a1, a2, a3, a4, a5, a6⟩
    refine ⟨hG'eq, hPreEq, fun j hj1 hj2 => ?_, hGdV, hGdSub, hGdm, hGdℓ, hLk, hLH, hLM, hLS, hLC⟩
    by_cases hjeq : j = idx
    · subst hjeq
      have hlt1 : j < j + 1 := Nat.lt_succ_self j
      rcases hIPre j hlt1 with ⟨a1, a2, a3, a4, a5, a6⟩
      simp only [sc1, bran1, upd1, cEnc1, cDec1, cFwd1, ↓reduceIte] at a1 a2 a3 a4 a5 a6
      set res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem' (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1
      have hG_0 : res.1 0 = G1 0 := hIG 0 (Nat.zero_le _)
      have hG_j1 : res.1 (j + 1) = Gi1 := by
        rw [hIG (j + 1) (le_refl _)]; simp [G1]
      have hCL : (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen ℓ₀ j = ℓi := by
        symm
        apply chainLen_congr_params rfl ℓ₀ (Nat.le_of_lt hj2)
        · intro m hm; rw [hG'eq m (Nat.le_of_lt hm)]
        · intro m hm
          rcases hPreEq m hm with ⟨hm1, hm2, _⟩
          rw [hm1, hm2]
      have hCG : (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad g₀ j = gi := by
        symm
        apply chainGrad_congr_params rfl g₀ (Nat.le_of_lt hj2)
        · intro m hm; rw [hG'eq m (Nat.le_of_lt hm)]
        · intro m hm
          rcases hPreEq m hm with ⟨hm1, hm2, _⟩
          rw [hm1, hm2]
      refine ⟨a2, a3, a4, a5, a6,
        by rw [hG'idx]; exact hGValid,
        by rw [hG'idx, hG_0, hG1_0]; exact hGV,
        by rw [hG'idx]; exact hGm,
        by rw [hCL, hG'idx]; exact hℓi_pos,
        by rw [a1, hG'idx, hCL, hCG],
        by rw [hG_j1, a1]⟩
    · exact hISuf j (by omega) hj2

theorem rebuildSuffix_spec (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) (N₀ : ℕ)
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ)
      (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      idx + rem = P.d →
      (G idx).IsValid →
      (G idx).V ⊆ (G 0).V →
      (G 0).n ≤ N₀ →
      ((G idx).m : ℝ) ≤ (levelM TP P idx : ℝ) →
      (∀ e ∈ (G idx).E, 0 < (mkPartialChain T P G sc bran (G idx)).chainLen ℓ₀ idx e) →
      let res := rebuildSuffix T L P (levelM TP P) N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      let G' := res.1
      let sc' := res.2.1
      let bran' := res.2.2.1
      let upd' := res.2.2.2.1
      let cEnc' := res.2.2.2.2.1
      let cDec' := res.2.2.2.2.2.1
      let cFwd' := res.2.2.2.2.2.2.1
      let lastRes := res.2.2.2.2.2.2.2.1
      let lastCost := res.2.2.2.2.2.2.2.2
      (∀ j ≤ idx, G' j = G j) ∧
      (∀ j < idx,
        sc' j = sc j ∧ bran' j = bran j ∧ upd' j = upd j ∧
        cEnc' j = cEnc j ∧ cDec' j = cDec j ∧ cFwd' j = cFwd j) ∧
      (∀ j, idx ≤ j → j < P.d →
        bran' j = 0 ∧ upd' j = 0 ∧
        cEnc' j = 0 ∧ cDec' j = 0 ∧ cFwd' j = 0 ∧
        (G' j).IsValid ∧ (G' j).V ⊆ (G' 0).V ∧
        ((G' j).m : ℝ) ≤ (levelM TP P j : ℝ) ∧
        (∀ e ∈ (G' j).E, 0 < (mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j e) ∧
        sc' j = T.init P.k (levelM TP P j) N₀ (G' j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ j)
          ((mkPartialChain T P G' sc' bran' (G' P.d)).chainGrad g₀ j) ∧
        G' (j + 1) = T.S (sc' j) 0) ∧
      (G' P.d).IsValid ∧
      (G' P.d).V ⊆ (G' 0).V ∧
      ((G' P.d).m : ℝ) ≤ (levelM TP P P.d : ℝ) ∧
      (∀ e ∈ (G' P.d).E, 0 < (mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ P.d e) ∧
      0 < lastRes.1 ∧
      (∀ j < lastRes.1, (lastRes.2 j).Holds (G' P.d)
        ((mkPartialChain T P G' sc' bran' (G' P.d)).chainLen ℓ₀ P.d)
        (LP.σ_last (G' P.d).n)) ∧
      (∀ e ∈ (G' P.d).E,
        (∑ j ∈ Finset.range lastRes.1, (lastRes.2 j).wstr e) / (lastRes.1 : ℝ) ≤
          LP.σ_mwu (G' P.d).n) ∧
      (∀ j < lastRes.1, ∀ u ∈ (G' P.d).V, ∀ v ∈ (G' P.d).V,
        (G' P.d).Connected u v → (lastRes.2 j).F.F.Connected u v) ∧
      ((lastCost : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((G' 0).n : ℝ) + 2)) ^
            LP.p_last) :=
  rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT.toNoHidden hL hγM₀ hγk ℓ₀ g₀

end RebuildSuffixSpec

end MinCostFlow.Chain
