module

public import MinCostFlow.Chain.Ordered.RebuildPreserves
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `algorithm1_shift` Preservation for Algorithm 1 with Orders

This file proves that `Ordered.algorithm1_shift` preserves `Ordered.ChainInv` and
`Ordered.ChainBudgetInvWith` (`shift_preserves_with_noHidden`, `shift_preserves_noHidden`), extending the level-`i₀` history with a restart of the new branch and using
the output-order clause of `IsSpecOrdRestartNoHidden` to supply the rotation witness at level
`i₀ + 1`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section OpPreservation

/-- `algorithm1_shift` preserves `ChainInv`, `ChainBudgetInvWith`, the top-level graph and edge
functions, exact `T^𝒢` tree changes, and `totalTreeUpdates`. -/
lemma shift_preserves_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hℓR : LenInRange Λ (st.G 0) st.ℓ)
    {overflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow)
    (i₀ : ℕ) (hi₀ : i₀ ≤ P.d) :
    let (st', changes) := algorithm1_shift T L P st i₀
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInvWith TP LP N₀ st' overflow ∧
    st'.G 0 = st.G 0 ∧
    st'.ℓ = st.ℓ ∧
    st'.g = st.g ∧
    st'.shiftCount = (fun j => if j = i₀ then st.shiftCount i₀ + 1 else st.shiftCount j) ∧
    st'.rebuildCount = st.rebuildCount ∧
    applyTreeChanges st.toTreeChain.chainTree.E changes = st'.toTreeChain.chainTree.E ∧
    st'.totalTreeUpdates = st.totalTreeUpdates + changes.length := by
  have hCostB := hInv.level_cost_bounds_noHidden hTP hLP hγM₀ hγk
  have hLevB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInv
  have hγℓ_ge := hTP.2.2.1
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  by_cases hlt : i₀ < P.d
  · dsimp only [algorithm1_shift]
    rw [dite_eq_left_iff.mpr fun h => absurd hlt h]
    set newBran := (st.bran i₀ + 1) % P.k
    set sc_i0 := T.restart (st.scState i₀) newBran
    set Gnext := T.S sc_i0 newBran
    set sc0 := fun j => if j = i₀ then sc_i0 else st.scState j
    set G0 := fun j => if j = i₀ + 1 then Gnext else st.G j
    set bran0 := fun j => if j = i₀ then newBran else st.bran j
    set cDec0 := fun j => if j = i₀ then 0 else st.curDecUpdates j
    set cEnc0 := fun j => if j = i₀ + 1 then 0 else st.curEnc j
    set res := rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
      G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd
    set retiredTool := (Finset.Ico (i₀ + 1) P.d).sum fun j => T.cost (st.scState j) + st.curEnc j
    set retiredDec := (Finset.Ico i₀ P.d).sum fun j => st.curDecUpdates j
    set oldE := st.toTreeChain.chainTree.E
    set stMidCore : ChainState T P :=
      { st with
        G := res.1, scState := res.2.1,
        curRestarts := fun j =>
          if j = i₀ then st.curRestarts i₀ + 1
          else if i₀ + 1 ≤ j ∧ j < P.d then 0
          else st.curRestarts j,
        bran := res.2.2.1, updCount := res.2.2.2.1,
        curFwd := res.2.2.2.2.2.2.1,
        lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
        curLastRebuilds := 0, curLastCost := res.2.2.2.2.2.2.2.2,
        curEnc := res.2.2.2.2.1, curDecUpdates := res.2.2.2.2.2.1,
        curLastTreeUpdates := 0 }
    have hNewBran : newBran < P.k := Nat.mod_lt _ P.hk
    have hLev_i0 := hLevB i₀ (Nat.le_of_lt hlt)
    obtain ⟨H_i0⟩ := hInv.hHist i₀ hlt
    let restarts_i0' : ℕ → List ℕ :=
      fun r => if r = H_i0.len then H_i0.restarts H_i0.len ++ [newBran] else H_i0.restarts r
    have hRestLt_i0' : ∀ r ≤ H_i0.len, ∀ j ∈ restarts_i0' r, j < P.k := by
      intro r hr j hj
      by_cases hr_eq : r = H_i0.len
      · subst hr_eq
        simp only [restarts_i0', ↓reduceIte, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact H_i0.hRestartsLt _ (le_refl _) _ hj
        · exact hNewBran
      · simp only [restarts_i0', hr_eq, ↓reduceIte] at hj
        exact H_i0.hRestartsLt r hr j hj
    have hRunPre_i0 : ∀ s ≤ H_i0.len,
        T.runOrdAfterUpdate P.k (levelM TP P i₀) N₀ H_i0.D H_i0.ord restarts_i0' s =
          T.runOrdAfterUpdate P.k (levelM TP P i₀) N₀ H_i0.D H_i0.ord H_i0.restarts s := by
      intro s hs
      exact T.runOrdAfterUpdate_congr_lt P.k (levelM TP P i₀) N₀ s rfl rfl rfl
        (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl)
        (fun r hr => by simp [restarts_i0', show r ≠ H_i0.len by omega])
    have hRunRestart : sc_i0 =
        T.runOrdAfterRestarts P.k (levelM TP P i₀) N₀ H_i0.D H_i0.ord restarts_i0' H_i0.len := by
      change T.restart (st.scState i₀) newBran =
        (restarts_i0' H_i0.len).foldl T.restart
          (T.runOrdAfterUpdate P.k (levelM TP P i₀) N₀ H_i0.D H_i0.ord restarts_i0' H_i0.len).1
      rw [hRunPre_i0 H_i0.len (le_refl _)]
      simp only [restarts_i0', ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [H_i0.hRun]
      rfl
    have hSpecPost := H_i0.hOK.noHidden P.k H_i0.len (levelM TP P i₀) N₀ H_i0.D H_i0.ord
      restarts_i0'
      P.hk H_i0.hG0 H_i0.hD H_i0.hLen H_i0.hℓPos H_i0.hOrd H_i0.hInitMBound H_i0.hInitNBound
      hRestLt_i0' (by rw [H_i0.hUpd]; exact H_i0.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hAtPost := hSpecPost.1 H_i0.len (le_refl _) newBran hNewBran
    dsimp only at hAtPost
    rw [← hRunRestart, H_i0.hEndG] at hAtPost
    have hOrdNext : ∃ ρ : Rotation (G0 (i₀ + 1)),
        ρ.order = chainLevelOrd T G0 sc0 bran0 (i₀ + 1) := by
      have hOut := hSpecPost.2.2.2.2.1 H_i0.len H_i0.len (le_refl _) (le_refl _) newBran hNewBran
        (Or.inr (by simp [restarts_i0'])) (fun _ h1 h2 => by omega)
      have hRot := rotation_of_orderedUpTo hOut (Nat.zero_le (H_i0.len - H_i0.len))
      refine exists_rotation_of_eq ?_ ?_ hRot
      · simp only [SparseCoreRestartTool.coreInstanceOrdFrom, Nat.add_zero, G0, ↓reduceIte, Gnext]
        rw [← hRunRestart]
      · simp only [Nat.add_zero, chainLevelOrd, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel, sc0, bran0]
        rw [← hRunRestart]
    have hActiveNew :
        (T.lsfs sc_i0 newBran).Holds (st.G i₀) (st.toTreeChain.chainLen st.ℓ i₀)
          (TP.σ P.k (st.G 0).n) ∧
        IsSparsifiedCoreGraphAt (st.G i₀) (T.lsfs sc_i0 newBran)
          (st.toTreeChain.chainLen st.ℓ i₀) (P.k : ℝ) (TP.γ_ℓ (P.M₀ ^ 2)) (TP.γ_c (P.M₀ ^ 2))
          (levelM TP P i₀) (T.S sc_i0 newBran) (T.emb sc_i0 newBran) := by
      have hn_le_i0 : (st.G i₀).n ≤ (st.G 0).n := Finset.card_le_card hLev_i0.2.1
      have hHolds := LSF.Holds.mono_σ
        (LSF.Holds.congr_len hAtPost.1 fun e he => H_i0.hEndℓ e he)
        (hTP.2.1 _ _ _ _ (le_refl _) hn_le_i0)
      have hm_le : levelM TP P i₀ ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk i₀
      have hSp' : IsSparsifiedCoreGraphAt (st.G i₀) (T.lsfs sc_i0 newBran)
          (st.toTreeChain.chainLen st.ℓ i₀) (P.k : ℝ)
          (TP.γ_ℓ (levelM TP P i₀)) (TP.γ_c (levelM TP P i₀)) (levelM TP P i₀)
          (T.S sc_i0 newBran) (T.emb sc_i0 newBran) := by
        rcases hAtPost.2.1 with ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩
        refine ⟨hs1, hs2, fun e he e' he' => ?_, hs4, hs5, hs6⟩
        have he0 : e ∈ (st.G i₀).E := (Finset.mem_sdiff.mp he).1
        have he'0 : e' ∈ (st.G i₀).E := by
          have he'S : e' ∈ (T.S sc_i0 newBran).E := mem_E_of_mem_walkEdges (hs2.2 e he) he'
          exact (Finset.mem_sdiff.mp (hs1.2.1 he'S)).1
        simpa [coreLen, H_i0.hEndℓ e he0, H_i0.hEndℓ e' he'0] using hs3 e he e' he'
      exact ⟨hHolds, isSparsifiedCoreGraphAt_mono hSp' hk_pos
        (le_trans zero_le_one (hγℓ_ge (levelM TP P i₀)))
        (hTP.2.2.2.1 _ _ hm_le) (hTP.2.2.2.2.2.1 _ _ hm_le) (le_refl _)⟩
    have hGnextValid : Gnext.IsValid := by
      have hCore := coreGraph_isValid hLev_i0.1 hActiveNew.1.2.1
      intro e he
      have hEnd := hActiveNew.2.1.2.2 e he
      have hc := hCore e (hActiveNew.2.1.2.1 he)
      rw [hEnd.1, hEnd.2]
      exact ⟨hActiveNew.2.2.1.1 hc.1, hActiveNew.2.2.1.1 hc.2⟩
    have hG0Eq0 : G0 0 = st.G 0 := by simp [G0]
    have hGnextV : Gnext.V ⊆ (G0 0).V := by
      rw [hG0Eq0]
      have hVsub : Gnext.V ⊆ (st.G i₀).V :=
        Finset.Subset.trans hActiveNew.2.1.1 hActiveNew.1.2.1.2.2.1
      exact Finset.Subset.trans hVsub hLev_i0.2.1
    have hGnextM : (Gnext.m : ℝ) ≤ (levelM TP P (i₀ + 1) : ℝ) := by
      have hcard : (Gnext.E.card : ℝ) ≤ (levelM TP P i₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / P.k :=
        hActiveNew.2.2.2.2.2.2
      exact_mod_cast levelM_step_nat hTP hγk hcard
    have hℓ_next : LevelLenRange TP P N₀ Λ (i₀ + 1) (G0 (i₀ + 1))
        ((mkPartialChain T P G0 sc0 bran0 (G0 (i₀ + 1))).chainLen st.ℓ (i₀ + 1)) := by
      intro e he
      simp only [G0, ↓reduceIte] at he
      have heGi0 : e ∈ (st.G i₀).E := (Finset.mem_sdiff.mp (hActiveNew.2.1.2.1 he)).1
      have hw1 : 1 ≤ (T.lsfs sc_i0 newBran).wstr e := by
        have hnonneg : ∀ f ∈ (st.G i₀).E, 0 ≤ st.toTreeChain.chainLen st.ℓ i₀ f :=
          fun f hf => (hLev_i0.2.2.2.1 f hf).le
        exact le_trans (one_le_stretch hActiveNew.1.2.1.2.2.2.2 hnonneg heGi0)
          (hActiveNew.1.2.2.2 e heGi0).1
      have hPre : (mkPartialChain T P G0 sc0 bran0 (G0 (i₀ + 1))).chainLen st.ℓ i₀ =
          st.toTreeChain.chainLen st.ℓ i₀ := by
        apply chainLen_congr_lt st.ℓ i₀ (fun j hj => by
          dsimp only [mkPartialChain, ChainState.toTreeChain]
          simp [G0, show j ≠ i₀ + 1 by omega])
          (fun j hj => by
            have hjlt : j < P.d := by omega
            dsimp only [TreeChain.activeLSF, mkPartialChain, ChainState.toTreeChain]
            rw [ite_eq_left_iff.mpr (fun h => absurd hjlt h), ite_eq_left_iff.mpr (fun h => absurd hjlt h)]
            simp [sc0, bran0, show j ≠ i₀ by omega])
      have hidxP : i₀ < P.d := hlt
      dsimp only [TreeChain.chainLen, coreLen, TreeChain.activeLSF, mkPartialChain]
      rw [ite_eq_left_iff.mpr (fun h => absurd hidxP h)]
      change Real.exp (-Λ) ≤ (T.lsfs (sc0 i₀) (bran0 i₀)).wstr e *
          (mkPartialChain T P G0 sc0 bran0 (G0 (i₀ + 1))).chainLen st.ℓ i₀ e ∧
        (T.lsfs (sc0 i₀) (bran0 i₀)).wstr e *
          (mkPartialChain T P G0 sc0 bran0 (G0 (i₀ + 1))).chainLen st.ℓ i₀ e ≤
          Real.exp Λ * max 2 (TP.σ P.k N₀) ^ (i₀ + 1)
      simp only [sc0, bran0, ↓reduceIte, hPre]
      have hwσ : (T.lsfs sc_i0 newBran).wstr e ≤ max 2 (TP.σ P.k N₀) :=
        le_trans (hActiveNew.1.2.2.2 e heGi0).2
          (le_trans (hTP.2.1 _ _ _ _ le_rfl hInv.hG0n) (le_max_right _ _))
      exact (chainInv_levelLenRange hTP hγM₀ hγk hInv hℓR i₀ (Nat.le_of_lt hlt)).stretch_step
        heGi0 hw1 hwσ
    have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk st.ℓ st.g
      (P.d - (i₀ + 1)) (i₀ + 1) G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd
      (by omega) (by simp only [G0, ↓reduceIte]; exact hGnextValid)
      (by simp only [G0, ↓reduceIte]; exact hGnextV)
      (by rw [hG0Eq0]; exact hInv.hG0n)
      (by simp only [G0, ↓reduceIte]; exact hGnextM) hℓ_next hOrdNext
    have hOrdSuf := rebuildSuffix_levelOrd_rotation T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk
      st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1) G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd
      (by omega) (by simp only [G0, ↓reduceIte]; exact hGnextValid)
      (by simp only [G0, ↓reduceIte]; exact hGnextV)
      (by rw [hG0Eq0]; exact hInv.hG0n)
      (by simp only [G0, ↓reduceIte]; exact hGnextM) hℓ_next hOrdNext
    have hResEq : res = rebuildSuffix T L P (levelM TP P) N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
        G0 sc0 bran0 st.updCount cEnc0 cDec0 st.curFwd := by
      dsimp only [res]; rw [hInv.hLvlM, hInv.hN0]
    rw [← hResEq] at hRS hOrdSuf
    have hPreEq := hRS.2.1
    have hSuf := hRS.2.2.1
    have hLk := hRS.2.2.2.2.2.2.2.1
    have hLH := hRS.2.2.2.2.2.2.2.2.1
    have hLM := hRS.2.2.2.2.2.2.2.2.2.1
    have hLS := hRS.2.2.2.2.2.2.2.2.2.2.1
    have hLC := hRS.2.2.2.2.2.2.2.2.2.2.2
    have hG0Mid : stMidCore.G 0 = st.G 0 := by
      dsimp only [stMidCore, res]
      rw [hRS.1 0 (Nat.zero_le _), hG0Eq0]
    have hOrdMidLe : ∀ j ≤ i₀, stMidCore.levelOrd j = st.levelOrd j := by
      intro j hj
      cases j with
      | zero =>
        simp only [ChainState.levelOrd, chainLevelOrd, ↓reduceIte]
        rw [hG0Mid]
      | succ m =>
        simp only [ChainState.levelOrd, chainLevelOrd, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel]
        have hm_lt : m < i₀ := by omega
        rcases hPreEq m (Nat.lt_succ_of_lt hm_lt) with ⟨hm1, hm2, _⟩
        change T.rot (res.2.1 m) (res.2.2.1 m) = T.rot (st.scState m) (st.bran m)
        rw [hm1, hm2]
        simp [sc0, bran0, Nat.ne_of_lt hm_lt]
    have hChainMidPre : ∀ j ≤ i₀,
        stMidCore.toTreeChain.chainLen stMidCore.ℓ j = st.toTreeChain.chainLen st.ℓ j ∧
        stMidCore.toTreeChain.chainGrad stMidCore.g j = st.toTreeChain.chainGrad st.g j := by
      intro j hj
      refine ⟨chainLen_congr_lt st.ℓ j (fun m hm => ?_) (fun m hm => ?_),
        chainGrad_congr_lt st.g j (fun m hm => ?_) (fun m hm => ?_)⟩
      · dsimp only [stMidCore, res, ChainState.toTreeChain]
        rw [hRS.1 m (by omega)]; simp [G0, show m ≠ i₀ + 1 by omega]
      · have hmlt : m < P.d := by omega
        rcases hPreEq m (by omega) with ⟨a1, a2, _⟩
        dsimp only [TreeChain.activeLSF, ChainState.toTreeChain, stMidCore, res]
        rw [ite_eq_left_iff.mpr (fun h => absurd hmlt h), ite_eq_left_iff.mpr (fun h => absurd hmlt h)]
        rw [a1, a2]; simp [sc0, bran0, show m ≠ i₀ by omega]
      · dsimp only [stMidCore, res, ChainState.toTreeChain]
        rw [hRS.1 m (by omega)]; simp [G0, show m ≠ i₀ + 1 by omega]
      · have hmlt : m < P.d := by omega
        rcases hPreEq m (by omega) with ⟨a1, a2, _⟩
        dsimp only [TreeChain.activeLSF, ChainState.toTreeChain, stMidCore, res]
        rw [ite_eq_left_iff.mpr (fun h => absurd hmlt h), ite_eq_left_iff.mpr (fun h => absurd hmlt h)]
        rw [a1, a2]; simp [sc0, bran0, show m ≠ i₀ by omega]
    have hChainAll : ∀ idx ≤ P.d,
        stMidCore.toTreeChain.chainLen stMidCore.ℓ idx =
          (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen st.ℓ idx ∧
        stMidCore.toTreeChain.chainGrad stMidCore.g idx =
          (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad st.g idx := by
      intro idx hidx
      exact ⟨chainLen_congr_params rfl st.ℓ hidx (fun _ _ => rfl) (fun _ _ => rfl),
        chainGrad_congr_params rfl st.g hidx (fun _ _ => rfl) (fun _ _ => rfl)⟩
    have hHistMid : ∀ j < P.d, Nonempty (LevelHistory T TP P N₀ stMidCore j) := by
      intro j hj
      by_cases hltj : j < i₀
      · obtain ⟨H⟩ := hInv.hHist j (lt_trans hltj hlt)
        rcases hPreEq j (by omega) with ⟨a1, a2, a3, a4, a5, a6⟩
        have hjne : j ≠ i₀ := Nat.ne_of_lt hltj
        have h1ne : j + 1 ≠ i₀ + 1 := by omega
        have hC := hChainMidPre j (Nat.le_of_lt hltj)
        refine ⟨{
          D := H.D, len := H.len, s₀ := H.s₀, hs₀ := H.hs₀,
          restarts := H.restarts, hRestartsLt := H.hRestartsLt,
          hRestartsCount := by
            have hcR : stMidCore.curRestarts j = st.curRestarts j := by
              dsimp only [stMidCore]
              simp [hjne]
              omega
            rw [hcR]; exact H.hRestartsCount,
          hS0Fresh := by dsimp only [stMidCore]; rw [a2]; simp [bran0, hjne]; exact H.hS0Fresh,
          hNoRestartAfterS0 := by
            dsimp only [stMidCore]; rw [a2]; simp [bran0, hjne]; exact H.hNoRestartAfterS0,
          hG0 := H.hG0, hD := H.hD, hLen := H.hLen, hℓPos := H.hℓPos,
          hEndG := by dsimp only [stMidCore, res]; rw [hRS.1 j (by omega)]; simp [G0, show j ≠ i₀ + 1 by omega]; exact H.hEndG,
          hEndℓ := fun e he => by
            have he' : e ∈ (st.G j).E := by
              dsimp only [stMidCore, res] at he
              rwa [hRS.1 j (by omega), show G0 j = st.G j by simp [G0, show j ≠ i₀ + 1 by omega]] at he
            rw [hC.1]; exact H.hEndℓ e he',
          hEndg := by rw [hC.2]; exact H.hEndg,
          hUpd := by dsimp only [stMidCore, res]; rw [a3]; exact H.hUpd,
          hThresh := by dsimp only [stMidCore, res]; rw [a3]; exact H.hThresh,
          hInitMBound := H.hInitMBound,
          hInitNBound := H.hInitNBound,
          ord := H.ord,
          hOrd := H.hOrd,
          hEndOrd := by rw [hOrdMidLe j (Nat.le_of_lt hltj)]; exact H.hEndOrd,
          hRun := by dsimp only [stMidCore, res]; rw [a1]; simp [sc0, hjne]; exact H.hRun,
          hOK := H.hOK,
          branchSeq := H.branchSeq,
          hBranch := H.hBranch,
          hBranchTail := by dsimp only [stMidCore]; rw [a2]; simp [bran0, hjne]; exact H.hBranchTail,
          hWinFwdBound := H.hWinFwdBound,
          hCurFwdEq := by dsimp only [stMidCore, res]; rw [a6]; exact H.hCurFwdEq,
          hDecEq := by dsimp only [stMidCore, res]; rw [a1, a2, a5]; simp [sc0, bran0, cDec0, hjne]; exact H.hDecEq,
          hEnc0Le := fun h0 => by subst h0; dsimp only [stMidCore, res] at a4 ⊢; rw [a4]; simp [cEnc0]; exact H.hEnc0Le rfl,
          hEncLe := fun h1 => by
            dsimp only [stMidCore, res]; rw [a2]; simp only [bran0, ite_eq_right_iff.mpr fun h => absurd h hjne]
            have ha4 := (hPreEq (j + 1) (by omega)).2.2.2.1
            rw [ha4]; simp only [cEnc0, ite_eq_right_iff.mpr fun h => absurd h h1ne]; exact H.hEncLe h1 }⟩
      · by_cases hjeq : j = i₀
        · subst hjeq
          rcases hPreEq j (Nat.lt_succ_self j) with ⟨a1, a2, a3, a4, a5, a6⟩
          have hC := hChainMidPre j (le_refl j)
          have hencNext : j + 1 < P.d → stMidCore.curEnc (j + 1) = 0 := fun h1 =>
            (hSuf (j + 1) (le_refl _) h1).2.2.1
          have hRestCount_j :
              (Finset.range (H_i0.len + 1)).sum (fun r => (restarts_i0' r).length) =
                stMidCore.curRestarts j := by
            rw [Finset.sum_range_succ]
            have hPreSum :
                (Finset.range H_i0.len).sum (fun r => (restarts_i0' r).length) =
                  (Finset.range H_i0.len).sum (fun r => (H_i0.restarts r).length) :=
              Finset.sum_congr rfl fun r hr => by
                simp [restarts_i0', Nat.ne_of_lt (Finset.mem_range.mp hr)]
            rw [hPreSum]
            have hLastLen : (restarts_i0' H_i0.len).length = (H_i0.restarts H_i0.len).length + 1 := by
              simp [restarts_i0']
            rw [hLastLen, ← add_assoc, ← Finset.sum_range_succ, H_i0.hRestartsCount]
            dsimp only [stMidCore]; simp
          have hWinFwd_j :
              (((Finset.Icc 1 H_i0.len).sum fun s =>
                ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord restarts_i0' s).2
                  (H_i0.branchSeq s)).length : ℕ) : ℝ) ≤
                TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc 1 H_i0.len).sum fun s => (H_i0.D.U s).length : ℕ) : ℝ) := by
            have hsub1 : ∀ s ∈ Finset.Icc 1 H_i0.len,
                ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord restarts_i0' s).2
                  (H_i0.branchSeq s)).length =
                  ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord H_i0.restarts s).2
                    (H_i0.branchSeq s)).length := fun s hs => by
              rw [hRunPre_i0 s (Finset.mem_Icc.mp hs).2]
            have hIccSplit : Finset.Icc 1 H_i0.len =
                Finset.Icc 1 H_i0.s₀ ∪ Finset.Icc (H_i0.s₀ + 1) H_i0.len := by
              ext s; simp only [Finset.mem_Icc, Finset.mem_union]; have := H_i0.hs₀; omega
            have hIccDisj : Disjoint (Finset.Icc 1 H_i0.s₀) (Finset.Icc (H_i0.s₀ + 1) H_i0.len) := by
              rw [Finset.disjoint_left]; intro s h1 h2
              simp only [Finset.mem_Icc] at h1 h2; omega
            have hLHS :
                (Finset.Icc 1 H_i0.len).sum (fun s =>
                  ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord restarts_i0' s).2
                    (H_i0.branchSeq s)).length) =
                  (Finset.Icc 1 H_i0.s₀).sum (fun s =>
                    ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord H_i0.restarts s).2
                      (H_i0.branchSeq s)).length) +
                  (Finset.Icc (H_i0.s₀ + 1) H_i0.len).sum (fun s =>
                    ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord H_i0.restarts s).2
                      (st.bran j)).length) := by
              rw [Finset.sum_congr rfl hsub1, hIccSplit, Finset.sum_union hIccDisj]
              congr 1
              refine Finset.sum_congr rfl fun s hs => ?_
              rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
              rw [H_i0.hBranchTail s (by omega) hs2]
            have hRHS :
                (Finset.Icc 1 H_i0.len).sum (fun s => (H_i0.D.U s).length) =
                  (Finset.Icc 1 H_i0.s₀).sum (fun s => (H_i0.D.U s).length) +
                  (Finset.Icc (H_i0.s₀ + 1) H_i0.len).sum (fun s => (H_i0.D.U s).length) := by
              rw [hIccSplit, Finset.sum_union hIccDisj]
            have hSpecH := H_i0.hOK.noHidden P.k H_i0.len (levelM TP P j) N₀ H_i0.D H_i0.ord
              H_i0.restarts
              P.hk H_i0.hG0 H_i0.hD H_i0.hLen H_i0.hℓPos H_i0.hOrd H_i0.hInitMBound H_i0.hInitNBound
              H_i0.hRestartsLt (by rw [H_i0.hUpd]; exact H_i0.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
            have hTail := (hSpecH.2.2.2.1 H_i0.s₀ H_i0.len H_i0.hs₀ (le_refl _) (st.bran j)
              (hInv.hBran j hlt) H_i0.hS0Fresh
              (fun r hr1 hr2 => H_i0.hNoRestartAfterS0 r hr1 (Nat.le_of_lt hr2))).1
            have hm_le : levelM TP P j ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk j
            have hγr_le : TP.γ_r (levelM TP P j) ≤ TP.γ_r (P.M₀ ^ 2) := hTP.2.2.2.2.2.2.2.1 _ _ hm_le
            have hTail' :
                (((Finset.Icc (H_i0.s₀ + 1) H_i0.len).sum fun s =>
                  ((T.runOrdAfterUpdate P.k (levelM TP P j) N₀ H_i0.D H_i0.ord H_i0.restarts s).2
                    (st.bran j)).length : ℕ) : ℝ) ≤
                  TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc (H_i0.s₀ + 1) H_i0.len).sum fun s =>
                    (H_i0.D.U s).length : ℕ) : ℝ) :=
              le_trans hTail (mul_le_mul_of_nonneg_right hγr_le (Nat.cast_nonneg _))
            rw [hLHS, hRHS, Nat.cast_add, Nat.cast_add, mul_add]
            exact add_le_add H_i0.hWinFwdBound hTail'
          refine ⟨{
            D := H_i0.D, len := H_i0.len, s₀ := H_i0.len, hs₀ := le_refl H_i0.len,
            restarts := restarts_i0', hRestartsLt := hRestLt_i0',
            hRestartsCount := hRestCount_j,
            hS0Fresh := Or.inr (by
              dsimp only [stMidCore]; rw [a2]; simp [bran0, restarts_i0']),
            hNoRestartAfterS0 := fun _ hr1 hr2 => by omega,
            hG0 := H_i0.hG0, hD := H_i0.hD, hLen := H_i0.hLen, hℓPos := H_i0.hℓPos,
            hEndG := by dsimp only [stMidCore, res]; rw [hRS.1 j (by omega)]; simp [G0]; exact H_i0.hEndG,
            hEndℓ := fun e he => by
              have he' : e ∈ (st.G j).E := by
                dsimp only [stMidCore, res] at he
                rwa [hRS.1 j (by omega), show G0 j = st.G j by simp [G0]] at he
              rw [hC.1]; exact H_i0.hEndℓ e he',
            hEndg := by rw [hC.2]; exact H_i0.hEndg,
            hUpd := by dsimp only [stMidCore, res]; rw [a3]; exact H_i0.hUpd,
            hThresh := by dsimp only [stMidCore, res]; rw [a3]; exact H_i0.hThresh,
            hInitMBound := H_i0.hInitMBound,
            hInitNBound := H_i0.hInitNBound,
            ord := H_i0.ord,
            hOrd := H_i0.hOrd,
            hEndOrd := by rw [hOrdMidLe j (le_refl j)]; exact H_i0.hEndOrd,
            hRun := by dsimp only [stMidCore, res]; rw [a1]; simp [sc0, hRunRestart],
            hOK := H_i0.hOK,
            branchSeq := H_i0.branchSeq,
            hBranch := H_i0.hBranch,
            hBranchTail := fun _ hs1 hs2 => by omega,
            hWinFwdBound := hWinFwd_j,
            hCurFwdEq := by
              dsimp only [stMidCore, res]
              rw [a6, H_i0.hCurFwdEq]
              refine Finset.sum_congr rfl fun s hs => ?_
              rw [hRunPre_i0 s (Finset.mem_Icc.mp hs).2],
            hDecEq := by
              dsimp only [stMidCore, res]
              rw [a1, a2, a5]; simp [cDec0, sc0, bran0, ← hRunRestart],
            hEnc0Le := fun h0 => by
              subst h0
              dsimp only [stMidCore, res] at a4 ⊢
              rw [a4]; simp only [cEnc0, Nat.zero_ne_add_one, ↓reduceIte]
              exact H_i0.hEnc0Le rfl,
            hEncLe := fun h1 => by
              rw [hencNext h1]
              exact Nat.zero_le _ }⟩
        · have hj1 : i₀ + 1 ≤ j := by omega
          rcases hSuf j hj1 hj with ⟨hb, hu, henc, hdec, hcfwd, hGV, hSubV, hGm, hℓj, hsc, _, hOKj⟩
          have hencNext : j + 1 < P.d → stMidCore.curEnc (j + 1) = 0 := fun h1 =>
            (hSuf (j + 1) (by omega) h1).2.2.1
          have hGjN : (stMidCore.G j).n ≤ N₀ :=
            le_trans (Finset.card_le_card (hG0Eq0 ▸ (hRS.1 0 (Nat.zero_le _)) ▸ hSubV)) hInv.hG0n
          refine levelHistory_of_init T TP P hTP N₀ stMidCore j hj hGV hGm hGjN ?_
            (hOrdSuf j hj1 hj) ?_ hu hcfwd hdec
            (by dsimp only [stMidCore]; simp [show j ≠ i₀ by omega, hj1, hj])
            (fun h0 => by subst h0; exact henc) hencNext ?_
          · rw [(hChainAll j (Nat.le_of_lt hj)).1]; exact hℓj
          · rw [(hChainAll j (Nat.le_of_lt hj)).1, (hChainAll j (Nat.le_of_lt hj)).2]; exact hsc
          · rw [(hChainAll j (Nat.le_of_lt hj)).1]; exact hOKj
    have hRecRebMid : ∀ j < P.d,
        (stMidCore.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
          (stMidCore.updCount j : ℝ) ≤ (stMidCore.recUpdates j : ℝ) := by
      intro j hj
      dsimp only [stMidCore]
      by_cases hlt1 : j < i₀ + 1
      · rw [(hPreEq j hlt1).2.2.1]
        exact hInv.hRecRebuild j hj
      · rw [(hSuf j (by omega) hj).2.1]
        simp only [Nat.cast_zero, add_zero]
        linarith [hInv.hRecRebuild j hj, show (0 : ℝ) ≤ st.updCount j from Nat.cast_nonneg _]
    have hRecFwdMid : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) stMidCore := by
      have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
      exact chainRecBound_of_rebuildSuffix hγr_nn (Nat.succ_le_of_lt hlt)
        hInv.hRecFwd rfl
        (fun j hj => ⟨(hPreEq j hj).2.2.1, (hPreEq j hj).2.2.2.2.2⟩)
        (fun j hj1 hj2 => ⟨(hSuf j hj1 hj2).2.1, (hSuf j hj1 hj2).2.2.2.2.1⟩)
    have hInvMid : ChainInv T L TP LP P N₀ stMidCore := by
      refine ⟨hG0Mid ▸ hInv.hG0Valid, hG0Mid ▸ hInv.hG0m, hG0Mid ▸ hInv.hG0n, hG0Mid ▸ hInv.hℓPos,
        hLk, hLk, fun j hj => ?_, hLM, hLS, ?_, ?_, hHistMid, hRecRebMid, hRecFwdMid, ?_, ?_,
        hInv.hLvlM, hInv.hN0⟩
      · rw [(hChainAll P.d (le_refl P.d)).1]; exact hLH j hj
      · intro j hj
        by_cases hlt1 : j < i₀ + 1
        · dsimp only [stMidCore, res]; rw [(hPreEq j hlt1).2.1]
          by_cases hjeq : j = i₀
          · subst hjeq; simp [bran0, hNewBran]
          · simp [bran0, hjeq, hInv.hBran j hj]
        · dsimp only [stMidCore, res]; rw [(hSuf j (by omega) hj).1]; exact P.hk
      · intro j hj
        by_cases hlt1 : j < i₀
        · rcases hPreEq j (by omega) with ⟨a1, a2, _⟩
          change res.1 (j + 1) = T.S (res.2.1 j) (res.2.2.1 j)
          rw [a1, a2, hRS.1 (j + 1) (by omega)]
          simp [G0, sc0, bran0, show j ≠ i₀ by omega, hInv.hGSucc j hj]
        · by_cases hjeq : j = i₀
          · subst hjeq
            rcases hPreEq j (Nat.lt_succ_self j) with ⟨a1, a2, _⟩
            change res.1 (j + 1) = T.S (res.2.1 j) (res.2.2.1 j)
            rw [a1, a2, hRS.1 (j + 1) (le_refl _)]
            simp [G0, sc0, bran0, Gnext]
          · rcases hSuf j (by omega) hj with ⟨hb, _, _, _, _, _, _, _, _, _, hS, _⟩
            change res.1 (j + 1) = T.S (res.2.1 j) (res.2.2.1 j)
            rw [hb]; exact hS
      · rcases hPreEq 0 (Nat.zero_lt_succ i₀) with ⟨_, _, a3, a4, _⟩
        dsimp only [stMidCore]; rw [a3, a4]
        simp only [cEnc0, Nat.zero_ne_add_one, ↓reduceIte]
        exact hInv.hEnc0
      · intro hd
        obtain ⟨H⟩ := hHistMid (P.d - 1) (Nat.sub_lt hd zero_lt_one)
        refine ⟨⟨H, by simp [stMidCore]⟩, ?_, by simp [stMidCore]⟩
        simpa [stMidCore, hG0Mid] using hLC
    set stMid : ChainState T P :=
      { stMidCore with
        shiftCount := fun j => if j = i₀ then st.shiftCount i₀ + 1 else st.shiftCount j
        closedRuntime := st.closedRuntime + retiredTool + st.curLastCost
        closedTreeUpdates := st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates }
    set changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    set stFinal : ChainState T P := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    have hInvFinal : ChainInv T L TP LP P N₀ stFinal :=
      chainInv_with_bookkeeping hInvMid rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun j hj => hInvMid.hRecRebuild j hj)
    have hPreActive : ∀ j < i₀,
        (st.toTreeChain.activeLSF j).F.F.E = (stMidCore.toTreeChain.activeLSF j).F.F.E := by
      intro j hj
      rcases hPreEq j (by omega) with ⟨a1, a2, _⟩
      have hjlt : j < P.d := lt_trans hj hlt
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjlt, ↓reduceIte]
      change (T.lsfs (st.scState j) (st.bran j)).F.F.E = (T.lsfs (res.2.1 j) (res.2.2.1 j)).F.F.E
      rw [a1, a2]; simp [sc0, bran0, Nat.ne_of_lt hj]
    have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P i₀ :=
      diffTreeChanges_chainTree_le_cap_noHidden hTP hLP hγM₀ hγk hInv hInvMid hi₀ hPreActive
    have hBudget : ChainBudgetInvWith TP LP N₀ stFinal overflow := by
      refine ⟨?_, ?_⟩
      · have hSumEq := sum_range_inc_coeff P.d i₀ hi₀
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid, stMidCore]; split_ifs with h <;> [subst h; rfl]; omega)
          (opRuntimeBudget TP LP P N₀)
        have hRetTool : (retiredTool : ℝ) ≤
            ((P.k : ℝ) + 1) * (Finset.Ico (i₀ + 1) P.d).sum (levelToolCap TP P N₀) +
              ((P.k : ℝ) + 1) * ∑ j ∈ Finset.Ico (i₀ + 1) P.d,
                (st.curRestarts j : ℝ) * restartCostCap TP P N₀ j := by
          push_cast [retiredTool]
          rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_le_sum fun j hj => hCostB.1 j (Finset.mem_Ico.mp hj).2
        have hAR := activeRestartCap_shift TP P N₀ i₀ hlt st.curRestarts
        have hRestartLe : ((P.k : ℝ) + 1) * restartCostCap TP P N₀ i₀ ≤
            ((P.k : ℝ) + 1) * levelToolCap TP P N₀ i₀ :=
          mul_le_mul_of_nonneg_left (restartCostCap_le_levelToolCap hTP P N₀ i₀) (by positivity)
        have hLastC : (st.curLastCost : ℝ) ≤ ((P.k : ℝ) + 1) * lastCostCap TP LP P N₀ := by
          have h1 := hCostB.2.2.1 P.hd
          have h2 := lastCostCap_nonneg hTP hLP P N₀
          have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
          nlinarith
        have hIco : (Finset.Ico i₀ P.d).sum (levelToolCap TP P N₀) =
            levelToolCap TP P N₀ i₀ + (Finset.Ico (i₀ + 1) P.d).sum (levelToolCap TP P N₀) :=
          Finset.sum_eq_sum_Ico_succ_bot hlt (levelToolCap TP P N₀)
        have hCR : (stFinal.closedRuntime : ℝ) =
            (st.closedRuntime : ℝ) + (retiredTool : ℝ) + (st.curLastCost : ℝ) := by
          change ((st.closedRuntime + retiredTool + st.curLastCost : ℕ) : ℝ) = _; push_cast; rfl
        have hCRest : activeRestartCap TP P N₀ stFinal.curRestarts =
            activeRestartCap TP P N₀ stMidCore.curRestarts := rfl
        have hOpR : opRuntimeBudget TP LP P N₀ i₀ =
            ((P.k : ℝ) + 1) * ((Finset.Ico i₀ P.d).sum (levelToolCap TP P N₀) +
              lastCostCap TP LP P N₀ + (if i₀ = 0 then extraEncCap P else 0)) := by
          unfold opRuntimeBudget Chain.opRuntimeBudget
          rw [ite_eq_left_iff.mpr fun h => absurd hlt h]
        rw [hCR, hCRest, hSumEq, hOpR, hIco]
        have h0_le : (0 : ℝ) ≤ ((P.k : ℝ) + 1) * (if i₀ = 0 then extraEncCap P else 0) := by
          apply mul_nonneg (by positivity)
          split_ifs
          · unfold extraEncCap
            have hlog2 : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
              Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
            positivity
          · exact le_rfl
        linarith [hBudget.1]
      · have hSumEq := sum_range_inc_coeff P.d i₀ hi₀
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid, stMidCore]; split_ifs with h <;> [subst h; rfl]; omega)
          (opTreeBudget TP P)
        have hRetDec : (retiredDec : ℝ) ≤ (Finset.Ico i₀ P.d).sum (levelDecCap TP P) := by
          push_cast [retiredDec]
          exact Finset.sum_le_sum fun j hj => hCostB.2.1 j (Finset.mem_Ico.mp hj).2
        have hCL : (stFinal.closedTreeUpdates : ℝ) =
            (st.closedTreeUpdates : ℝ) + (retiredDec : ℝ) + (st.curLastTreeUpdates : ℝ) +
              (changes.length : ℝ) := by
          change ((st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates + changes.length : ℕ) : ℝ) = _
          push_cast; rfl
        have hOpT : opTreeBudget TP P i₀ =
            (Finset.Ico i₀ P.d).sum (levelDecCap TP P) + lastTreeCap TP P + diffTreeCap TP P i₀ := by
          unfold opTreeBudget; rw [ite_eq_left_iff.mpr fun h => absurd hlt h]
        rw [hCL, hSumEq, hOpT]
        linarith [hBudget.2, hCostB.2.2.2.1]
    refine ⟨hInvFinal, hBudget, hG0Mid, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change applyTreeChanges st.toTreeChain.chainTree.E
          (diffTreeChanges st.toTreeChain.chainTree.E stMid.toTreeChain.chainTree.E) =
        stMid.toTreeChain.chainTree.E
      exact applyTreeChanges_diffTreeChanges _ _
    · have hSumDec :
          (Finset.range P.d).sum stFinal.curDecUpdates + retiredDec =
            (Finset.range P.d).sum st.curDecUpdates := by
        have hsplit : Finset.range P.d = Finset.range i₀ ∪ Finset.Ico i₀ P.d := by
          ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        have hdisj : Disjoint (Finset.range i₀) (Finset.Ico i₀ P.d) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
        have hPreD : (Finset.range i₀).sum stFinal.curDecUpdates = (Finset.range i₀).sum st.curDecUpdates := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hmem := Finset.mem_range.mp hj
          have a5 := (hPreEq j (by omega)).2.2.2.2.1
          change res.2.2.2.2.2.1 j = st.curDecUpdates j
          rw [a5]; simp [cDec0, Nat.ne_of_lt hmem]
        have hSufD : (Finset.Ico i₀ P.d).sum stFinal.curDecUpdates = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hmem := Finset.mem_Ico.mp hj
          by_cases hjeq : j = i₀
          · subst hjeq
            have a5 := (hPreEq j (Nat.lt_succ_self j)).2.2.2.2.1
            change res.2.2.2.2.2.1 j = 0
            rw [a5]; simp [cDec0]
          · exact (hSuf j (by omega) hmem.2).2.2.2.1
        change (Finset.range i₀).sum stFinal.curDecUpdates + (Finset.Ico i₀ P.d).sum stFinal.curDecUpdates +
            retiredDec = _
        rw [hPreD, hSufD, add_zero]
      unfold ChainState.totalTreeUpdates
      change st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates + changes.length +
          (Finset.range P.d).sum stFinal.curDecUpdates + 0 =
        st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + st.curLastTreeUpdates + changes.length
      omega
  · have hi0_eq : i₀ = P.d := by omega
    subst hi0_eq
    dsimp only [algorithm1_shift]
    rw [dite_eq_right_iff.mpr fun h => absurd h (lt_irrefl P.d)]
    set newLastBran := (st.lastBran + 1) % st.lastK
    set oldE := st.toTreeChain.chainTree.E
    set stMid : ChainState T P :=
      { st with
        lastBran := newLastBran
        shiftCount := fun j => if j = P.d then st.shiftCount P.d + 1 else st.shiftCount j }
    set changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    set stFinal : ChainState T P := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    have hNewB : newLastBran < st.lastK := Nat.mod_lt _ hInv.hLastK
    have hInvFinal : ChainInv T L TP LP P N₀ stFinal := by
      have hBase := chainInv_with_bookkeeping hInv rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (rfl : st.lastBran = st.lastBran) rfl rfl rfl rfl rfl rfl rfl rfl rfl hInv.hRecRebuild
      have hPreTC : ∀ j < P.d, stFinal.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
        intro j hj; simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stFinal, stMid]
      refine ⟨hBase.hG0Valid, hBase.hG0m, hBase.hG0n, hBase.hℓPos,
        hInv.hLastK, hNewB, fun j hj => ?_, hInv.hLastMWU, hInv.hLastSpans,
        hInv.hBran, hInv.hGSucc, fun i hi => ?_, hInv.hRecRebuild, hInv.hRecFwd, hInv.hEnc0,
        fun hd => ?_, hInv.hLvlM, hInv.hN0⟩
      · have hℓdEq : stFinal.toTreeChain.chainLen stFinal.ℓ P.d = st.toTreeChain.chainLen st.ℓ P.d :=
          chainLen_congr_lt st.ℓ P.d (fun _ _ => rfl) hPreTC
        change (st.lastLSFs j).Holds (st.G P.d) (stFinal.toTreeChain.chainLen stFinal.ℓ P.d) _
        rw [hℓdEq]
        exact hInv.hLastHolds j hj
      · obtain ⟨H⟩ := hInv.hHist i hi
        exact ⟨{ H with
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.ℓ i
              (fun _ _ => rfl) (fun j hj => hPreTC j (lt_trans hj hi))]
            exact H.hEndℓ e he
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.g i
              (fun _ _ => rfl) (fun j hj => hPreTC j (lt_trans hj hi))]
            exact H.hEndg }⟩
      · obtain ⟨⟨H, hReb⟩, hCost, hTree⟩ := hInv.hLastCap hd
        have hSub := Nat.sub_lt hd zero_lt_one
        exact ⟨⟨{ H with
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.ℓ (P.d - 1)
              (fun _ _ => rfl) (fun j hj => hPreTC j (lt_trans hj hSub))]
            exact H.hEndℓ e he
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.g (P.d - 1)
              (fun _ _ => rfl) (fun j hj => hPreTC j (lt_trans hj hSub))]
            exact H.hEndg }, hReb⟩, hCost, hTree⟩
    have hPreActive : ∀ j < P.d,
        (st.toTreeChain.activeLSF j).F.F.E = (stFinal.toTreeChain.activeLSF j).F.F.E := fun j hj => by
      simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stFinal, stMid]
    have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P P.d :=
      diffTreeChanges_chainTree_le_cap_noHidden hTP hLP hγM₀ hγk hInv hInvFinal (le_refl P.d) hPreActive
    have hBudget : ChainBudgetInvWith TP LP N₀ stFinal overflow := by
      refine ⟨?_, ?_⟩
      · have hSumEq := sum_range_inc_coeff P.d P.d (le_refl P.d)
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid]; split_ifs with h <;> [subst h; rfl]; omega)
          (opRuntimeBudget TP LP P N₀)
        change (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts ≤ _
        rw [hSumEq]
        have hOpNN : 0 ≤ opRuntimeBudget TP LP P N₀ P.d := by
          unfold opRuntimeBudget Chain.opRuntimeBudget
          apply mul_nonneg (by positivity)
          rw [ite_eq_right_iff.mpr fun h => absurd h (lt_irrefl P.d)]
          have h2 : 0 ≤ if P.d = 0 then extraEncCap P else 0 := by
            split_ifs
            · unfold extraEncCap
              have : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
                Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
              positivity
            · exact le_rfl
          linarith [lastCostCap_nonneg hTP hLP P N₀]
        linarith [hBudget.1]
      · have hSumEq := sum_range_inc_coeff P.d P.d (le_refl P.d)
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid]; split_ifs with h <;> [subst h; rfl]; omega)
          (opTreeBudget TP P)
        have hCL : ((stFinal.closedTreeUpdates : ℕ) : ℝ) = (st.closedTreeUpdates : ℝ) + (changes.length : ℝ) := by
          change ((st.closedTreeUpdates + changes.length : ℕ) : ℝ) = _; push_cast; rfl
        have hOpT : opTreeBudget TP P P.d = lastTreeCap TP P + diffTreeCap TP P P.d := by
          unfold opTreeBudget
          rw [ite_eq_right_iff.mpr fun h => absurd h (lt_irrefl P.d)]
          ring
        rw [hCL, hSumEq, hOpT]
        have hLastTNN : 0 ≤ lastTreeCap TP P := by
          have := hCostB.2.2.2.1; linarith [show (0 : ℝ) ≤ st.curLastTreeUpdates from Nat.cast_nonneg _]
        linarith [hBudget.2, hDiffCap]
    refine ⟨hInvFinal, hBudget, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change applyTreeChanges st.toTreeChain.chainTree.E
          (diffTreeChanges st.toTreeChain.chainTree.E stMid.toTreeChain.chainTree.E) =
        stMid.toTreeChain.chainTree.E
      exact applyTreeChanges_diffTreeChanges _ _
    · change stFinal.totalTreeUpdates = st.totalTreeUpdates + changes.length
      unfold ChainState.totalTreeUpdates
      change st.closedTreeUpdates + changes.length + (Finset.range P.d).sum st.curDecUpdates +
          st.curLastTreeUpdates =
        st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + st.curLastTreeUpdates +
          changes.length
      omega

lemma shift_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hℓR : LenInRange Λ (st.G 0) st.ℓ)
    (hBudget : ChainBudgetInv TP LP N₀ st)
    (i₀ : ℕ) (hi₀ : i₀ ≤ P.d) :
    let (st', changes) := algorithm1_shift T L P st i₀
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInv TP LP N₀ st' ∧
    st'.G 0 = st.G 0 ∧
    st'.ℓ = st.ℓ ∧
    st'.g = st.g ∧
    st'.shiftCount = (fun j => if j = i₀ then st.shiftCount i₀ + 1 else st.shiftCount j) ∧
    st'.rebuildCount = st.rebuildCount ∧
    applyTreeChanges st.toTreeChain.chainTree.E changes = st'.toTreeChain.chainTree.E ∧
    st'.totalTreeUpdates = st.totalTreeUpdates + changes.length := by
  have h := shift_preserves_with_noHidden T L TP LP P hTP hLP hT hL hγM₀ hγk hInv hℓR
    (overflow := 0) hBudget.toWith i₀ hi₀
  dsimp only at h ⊢
  rcases h with ⟨h1, h2, h3⟩
  exact ⟨h1, h2.toZero, h3⟩

end OpPreservation

end MinCostFlow.Chain.Ordered
