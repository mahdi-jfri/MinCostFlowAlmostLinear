module

public import MinCostFlow.Chain.Ordered.UpdateTraceRebuild

/-!
# Step helpers for ordered `updateLoop_hidden_trace`

Factors out the per-step rotation-batch existence (`U3.updateLoop_step_ord`) and the adjacent-level
core-instance + order coupling extension (`U3.updateLoop_step_coreRel`) for the no-rebuild step of
`updateLoop_hidden_trace`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

namespace U3

/-- One-step `RotationBatch 2` witness at level `idx` for the no-rebuild step of `updateLoop`:
at `idx = 0` from `sortedRotation_batch` under `hEdge0`, and at `idx > 0` from the output-order
clause of `IsSpecOrdRestartNoHidden` on level `idx - 1`. -/
lemma updateLoop_step_ord {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {stOrig st : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    (HOrig : ∀ k < P.d, LevelHistory T TP P N₀ stOrig k)
    {ℓ' g' : ℕ → ℝ} {U₀ : List Update} (hEdge0 : ∀ u ∈ U₀, IsEdgeUpdate u)
    {idx : ℕ} (hidxLt : idx < P.d)
    {curG : MGraph} {curU : List Update}
    (hBr : st.bran = stOrig.bran)
    (hCurU0 : idx = 0 → curU = U₀)
    (hCurGEq : curG = (stOrig.G idx).applyBatch curU)
    (hCurGBatch : (stOrig.G idx).BatchIsValid curU)
    (HPre : ∀ k, k < idx → LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } k)
    (hPreExt : ∀ k (hk : k < idx),
      (HPre k hk).len = (HOrig k (by omega)).len + 1 ∧
      (∀ s ≤ (HOrig k (by omega)).len,
        (HPre k hk).D.G s = (HOrig k (by omega)).D.G s ∧
        (HPre k hk).D.U s = (HOrig k (by omega)).D.U s ∧
        (HPre k hk).D.ℓ s = (HOrig k (by omega)).D.ℓ s ∧
        (HPre k hk).D.g s = (HOrig k (by omega)).D.g s ∧
        (HPre k hk).ord s = (HOrig k (by omega)).ord s) ∧
      (k = 0 → (HPre k hk).D.U ((HOrig k (by omega)).len + 1) = U₀) ∧
      ((HPre k hk).D.ℓ ((HPre k hk).len) =
        ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' k) ∧
      (HPre k hk).s₀ = (HOrig k (by omega)).s₀ ∧
      (∀ s ≤ (HOrig k (by omega)).len,
        (HPre k hk).restarts s = (HOrig k (by omega)).restarts s))
    (hCurFromPrev : ∀ h0 : 0 < idx,
      curU = (T.runOrdAfterUpdate P.k (levelM TP P (idx - 1)) N₀
        (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).D
        (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).ord
        (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).restarts
        ((HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).len)).2 (stOrig.bran (idx - 1)) ∧
      curG = T.S (st.scState (idx - 1)) (stOrig.bran (idx - 1))) :
    let ordIdx := chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
    ∃ (ρPrev : Rotation (stOrig.G idx)) (ρNew : Rotation curG),
      ρPrev.order = stOrig.levelOrd idx ∧ ρNew.order = ordIdx ∧
      RotationBatch 2 curU ρPrev (hCurGEq ▸ ρNew) := by
  intro ordIdx
  by_cases h0 : idx = 0
  · subst h0
    have hEdgeCur : ∀ u ∈ curU, IsEdgeUpdate u := by
      rw [hCurU0 rfl]; exact hEdge0
    refine ⟨sortedRotation (stOrig.G 0), sortedRotation curG, ?_, ?_, ?_⟩
    · simp [sortedRotation, ChainState.levelOrd, chainLevelOrd]
    · simp [sortedRotation, ordIdx, chainLevelOrd]
    · have hRB0 : RotationBatch 0 curU (sortedRotation (stOrig.G 0))
          (hCurGEq ▸ sortedRotation curG) := by
        exact rotationBatch_cast rfl rfl rfl hCurGEq rfl
          (by simp [sortedRotation, hCurGEq]) (sortedRotation_batch hCurGBatch hEdgeCur)
      exact RotationBatch.mono hRB0 (Nat.zero_le 2)
  · have h0lt : 0 < idx := Nat.pos_of_ne_zero h0
    let k := idx - 1
    have hklt : k < idx := Nat.sub_lt h0lt zero_lt_one
    have hkd : k < P.d := lt_trans hklt hidxLt
    have hk1 : k + 1 = idx := Nat.sub_add_cancel h0lt
    let Hk := HPre k hklt
    have hPE := hPreExt k hklt
    have hSpecK := Hk.hOK.noHidden P.k Hk.len (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts P.hk
      Hk.hG0 Hk.hD Hk.hLen Hk.hℓPos Hk.hOrd Hk.hInitMBound Hk.hInitNBound
      Hk.hRestartsLt (by rw [Hk.hUpd]; exact Hk.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hBrK : stOrig.bran k < P.k := hInvOrig.hBran k hkd
    have hS0FreshK : Hk.s₀ = 0 ∨ stOrig.bran k ∈ Hk.restarts Hk.s₀ := by
      have h := Hk.hS0Fresh; simpa [hBr] using h
    have hNoRestK : ∀ r, Hk.s₀ < r → r ≤ Hk.len → stOrig.bran k ∉ Hk.restarts r := by
      intro r hr1 hr2
      have h := Hk.hNoRestartAfterS0 r hr1 hr2; simpa [hBr] using h
    have hOrdOut := hSpecK.2.2.2.2.1 Hk.s₀ Hk.len Hk.hs₀ (le_refl _) (stOrig.bran k) hBrK
      hS0FreshK hNoRestK
    obtain ⟨ρc, hρc_ord, hρc_step⟩ := hOrdOut
    let δ₀ := (HOrig k hkd).len - Hk.s₀
    have hLenK : Hk.len = (HOrig k hkd).len + 1 := hPE.1
    have hS0_le : Hk.s₀ ≤ (HOrig k hkd).len := by rw [hPE.2.2.2.2.1]; exact (HOrig k hkd).hs₀
    have hδ₀_lt : δ₀ < Hk.len - Hk.s₀ := by dsimp only [δ₀]; omega
    obtain ⟨h1, hB1⟩ := hρc_step δ₀ hδ₀_lt
    have hSum0 : Hk.s₀ + δ₀ = (HOrig k hkd).len := Nat.add_sub_of_le hS0_le
    have hSum1 : Hk.s₀ + (δ₀ + 1) = Hk.len := by dsimp only [δ₀]; omega
    have hRun0 : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
        (Hk.s₀ + δ₀) = stOrig.scState k := by
      rw [hSum0]
      have hcongr := T.runOrdAfterRestarts_congr_le P.k (levelM TP P k) N₀ (HOrig k hkd).len
        (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
        (hPE.2.1 0 (Nat.zero_le _)).2.2.2.1
        (fun s _ hs => ⟨(hPE.2.1 s hs).2.1, (hPE.2.1 s hs).2.2.1, (hPE.2.1 s hs).2.2.2.1⟩)
        (fun s hs => (hPE.2.1 s hs).2.2.2.2)
        (fun r hr => hPE.2.2.2.2.2 r hr)
      exact hcongr.trans (HOrig k hkd).hRun.symm
    have hRun1 : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
        (Hk.s₀ + (δ₀ + 1)) = st.scState k := by
      rw [hSum1, ← Hk.hRun]
    have hGprev : (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
        Hk.s₀ (stOrig.bran k)).G δ₀ = stOrig.G idx := by
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hRun0]
      rw [← hk1, hInvOrig.hGSucc k hkd]
    have hGnext : (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
        Hk.s₀ (stOrig.bran k)).G (δ₀ + 1) = curG := by
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hRun1]
      exact (hCurFromPrev h0lt).2.symm
    have hUnext : (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
        Hk.s₀ (stOrig.bran k)).U (δ₀ + 1) = curU := by
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hSum1]
      exact (hCurFromPrev h0lt).1.symm
    refine ⟨hGprev ▸ ρc δ₀, hGnext ▸ ρc (δ₀ + 1), ?_, ?_, ?_⟩
    · rw [rotation_cast_order, hρc_ord δ₀ hδ₀_lt.le]
      dsimp only
      rw [hRun0]
      simp [ChainState.levelOrd, chainLevelOrd, h0, k]
    · rw [rotation_cast_order, hρc_ord (δ₀ + 1) (Nat.succ_le_of_lt hδ₀_lt)]
      dsimp only
      rw [hRun1]
      simp [ordIdx, chainLevelOrd, h0, k, hBr]
    · exact rotationBatch_cast hGprev hUnext h1 hCurGEq
        (rotation_cast_order _ _).symm (rotation_cast_order _ _).symm hB1

/-- Adjacent-level `ChainCoreRel` step when extending level `idx = k + 1` on top of an already
extended level `k`. -/
lemma updateLoop_step_coreRel {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ}
    {stOrig st stNextLG : ChainState T P}
    {HOrig : ∀ k < P.d, LevelHistory T TP P N₀ stOrig k}
    (hOrigCore : ChainCoreRel T TP P stOrig HOrig)
    {ℓ' g' : ℕ → ℝ} {idx k : ℕ} (hidxLt : idx < P.d) (hk1eq : k + 1 = idx)
    (hk_lt_d : k < P.d) (hk1_lt_d : k + 1 < P.d)
    {curG : MGraph} {curU : List Update} {ordIdx : ℕ → List End}
    (_hBr : st.bran = stOrig.bran)
    (hHk : LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } k)
    (hHidx : LevelHistory T TP P N₀ stNextLG idx)
    (hLenIdx : hHidx.len = (HOrig idx hidxLt).len + 1)
    (hIdxOld : ∀ δ ≤ (HOrig idx hidxLt).len,
      hHidx.D.G δ = (HOrig idx hidxLt).D.G δ ∧
      hHidx.D.U δ = (HOrig idx hidxLt).D.U δ ∧
      hHidx.D.ℓ δ = (HOrig idx hidxLt).D.ℓ δ ∧
      hHidx.ord δ = (HOrig idx hidxLt).ord δ)
    (hIdxNew :
      hHidx.D.G ((HOrig idx hidxLt).len + 1) = curG ∧
      hHidx.D.U ((HOrig idx hidxLt).len + 1) = curU ∧
      hHidx.D.ℓ ((HOrig idx hidxLt).len + 1) = stNextLG.toTreeChain.chainLen ℓ' idx ∧
      hHidx.ord ((HOrig idx hidxLt).len + 1) = ordIdx)
    (hOrdIdxEq : ordIdx = T.rot (st.scState k) (stOrig.bran k))
    (hPE : hHk.len = (HOrig k hk_lt_d).len + 1 ∧
      (∀ s ≤ (HOrig k hk_lt_d).len,
        hHk.D.G s = (HOrig k hk_lt_d).D.G s ∧
        hHk.D.U s = (HOrig k hk_lt_d).D.U s ∧
        hHk.D.ℓ s = (HOrig k hk_lt_d).D.ℓ s ∧
        hHk.D.g s = (HOrig k hk_lt_d).D.g s ∧
        hHk.ord s = (HOrig k hk_lt_d).ord s) ∧
      hHk.D.ℓ hHk.len = ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' k ∧
      hHk.s₀ = (HOrig k hk_lt_d).s₀ ∧
      (∀ s ≤ (HOrig k hk_lt_d).len, hHk.restarts s = (HOrig k hk_lt_d).restarts s))
    (hFP1 : curU = (T.runOrdAfterUpdate P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
      hHk.len).2 (stOrig.bran k))
    (hFP2 : curG = T.S (st.scState k) (stOrig.bran k))
    (hAct : stNextLG.toTreeChain.activeLSF k = T.lsfs (st.scState k) (stOrig.bran k))
    (hCLk : stNextLG.toTreeChain.chainLen ℓ' k =
      ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' k) :
    hHidx.len ≤ hHk.len ∧
      let off := hHk.len - hHidx.len
      hHk.s₀ ≤ off ∧
      (∀ δ ≤ hHidx.len, hHidx.D.G δ =
        (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ hHk.D hHk.ord
          hHk.restarts hHk.s₀ (stOrig.bran k)).G ((off - hHk.s₀) + δ)) ∧
      (∀ δ, 1 ≤ δ → δ ≤ hHidx.len → hHidx.D.U δ =
        (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ hHk.D hHk.ord
          hHk.restarts hHk.s₀ (stOrig.bran k)).U ((off - hHk.s₀) + δ)) ∧
      (∀ δ ≤ hHidx.len, ∀ e ∈ (hHidx.D.G δ).E, hHidx.D.ℓ δ e =
        (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ hHk.D hHk.ord
          hHk.restarts hHk.s₀ (stOrig.bran k)).ℓ ((off - hHk.s₀) + δ) e) ∧
      (∀ δ ≤ hHidx.len, hHidx.ord δ =
        T.rot (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
          (hHk.s₀ + ((off - hHk.s₀) + δ))) (stOrig.bran k)) := by
  have hOC := hOrigCore k hk1_lt_d
  have hlen_ok1 : (HOrig (k + 1) hk1_lt_d).len = (HOrig idx hidxLt).len :=
    (show ∀ a (ha : a < P.d) b (hb : b < P.d), a = b → (HOrig a ha).len = (HOrig b hb).len from
      fun _ _ _ _ hab => by cases hab; rfl) (k + 1) hk1_lt_d idx hidxLt hk1eq
  have hlen_le : hHidx.len ≤ hHk.len := by
    rw [hLenIdx, hPE.1, ← hlen_ok1]; exact Nat.add_le_add_right hOC.1 1
  have hoff : hHk.len - hHidx.len = (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len := by
    rw [hLenIdx, hPE.1, ← hlen_ok1]; omega
  have hs0_eq : hHk.s₀ = (HOrig k hk_lt_d).s₀ := hPE.2.2.2.1
  have hs0_le_orig : (HOrig k hk_lt_d).s₀ ≤ (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len :=
    hOC.2.1
  have hs0_le : hHk.s₀ ≤ hHk.len - hHidx.len := by rw [hs0_eq, hoff]; exact hs0_le_orig
  refine ⟨hlen_le, hs0_le, fun δ hδ => ?_, fun δ h1 hδ => ?_, fun δ hδ e he => ?_, fun δ hδ => ?_⟩
  · rw [hoff, hs0_eq]
    by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
    · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
          (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
      have hidx_sum : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by omega
      have hrun_eq := T.runOrdAfterRestarts_congr_le P.k (levelM TP P k) N₀ _
        (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
        (hPE.2.1 0 (Nat.zero_le _)).2.2.2.1
        (fun s _ hs => ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
          (hPE.2.1 s (le_trans hs hsum_le)).2.2.1, (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.1⟩)
        (fun s hs => (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.2)
        (fun r hr => hPE.2.2.2.2 r (le_trans hr hsum_le))
      have hG_o := hOC.2.2.1 δ (by rw [hlen_ok1]; exact hδ_old)
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hidx_sum] at hG_o ⊢
      rw [hrun_eq, ← hG_o, (hIdxOld δ hδ_old).1]
      subst hk1eq; rfl
    · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
      have hsum_eq : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          hHk.len := by rw [hlen_ok1, hδeq, hPE.1]; omega
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hsum_eq, ← hHk.hRun]
      rw [hδeq, hIdxNew.1, hFP2]
  · rw [hoff, hs0_eq]
    by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
    · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
          (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
      have hidx_sum : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by omega
      have hrun_eq := T.runOrdAfterUpdate_congr_lt P.k (levelM TP P k) N₀ _
        (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
        (hPE.2.1 0 (Nat.zero_le _)).2.2.2.1
        (fun s _ hs => ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
          (hPE.2.1 s (le_trans hs hsum_le)).2.2.1, (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.1⟩)
        (fun s hs => (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.2)
        (fun r hr => hPE.2.2.2.2 r (le_trans (Nat.le_of_lt hr) hsum_le))
      have hU_o := hOC.2.2.2.1 δ h1 (by rw [hlen_ok1]; exact hδ_old)
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hidx_sum] at hU_o ⊢
      rw [hrun_eq, ← hU_o, (hIdxOld δ hδ_old).2.1]
      subst hk1eq; rfl
    · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
      have hsum_eq : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          hHk.len := by rw [hlen_ok1, hδeq, hPE.1]; omega
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hsum_eq]
      rw [hδeq, hIdxNew.2.1, hFP1]
  · rw [hoff, hs0_eq]
    by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
    · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
          (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
      have hidx_sum : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by omega
      have hrun_eq := T.runOrdAfterRestarts_congr_le P.k (levelM TP P k) N₀ _
        (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
        (hPE.2.1 0 (Nat.zero_le _)).2.2.2.1
        (fun s _ hs => ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
          (hPE.2.1 s (le_trans hs hsum_le)).2.2.1, (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.1⟩)
        (fun s hs => (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.2)
        (fun r hr => hPE.2.2.2.2 r (le_trans hr hsum_le))
      have hD_oldG : hHidx.D.G δ = (HOrig (k + 1) hk1_lt_d).D.G δ := by
        rw [(hIdxOld δ hδ_old).1]; subst hk1eq; rfl
      have hℓ_o := hOC.2.2.2.2.1 δ (by rw [hlen_ok1]; exact hδ_old) e (hD_oldG ▸ he)
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hidx_sum] at hℓ_o ⊢
      rw [hrun_eq, (hPE.2.1 _ hsum_le).2.2.1, ← hℓ_o, (hIdxOld δ hδ_old).2.2.1]
      subst hk1eq; rfl
    · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
      have hsum_eq : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          hHk.len := by rw [hlen_ok1, hδeq, hPE.1]; omega
      simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hsum_eq, ← hHk.hRun, hPE.2.2.1]
      have hCLk1 : hHidx.D.ℓ δ e =
          coreLen (stNextLG.toTreeChain.activeLSF k) (stNextLG.toTreeChain.chainLen ℓ' k) e := by
        rw [hδeq, hIdxNew.2.2.1, ← hk1eq]; rfl
      rw [hCLk1, hAct, hCLk]
  · rw [hoff, hs0_eq]
    by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
    · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
          (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
      have hidx_sum : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by omega
      have hrun_eq := T.runOrdAfterRestarts_congr_le P.k (levelM TP P k) N₀ _
        (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
        (hPE.2.1 0 (Nat.zero_le _)).2.2.2.1
        (fun s _ hs => ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
          (hPE.2.1 s (le_trans hs hsum_le)).2.2.1, (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.1⟩)
        (fun s hs => (hPE.2.1 s (le_trans hs hsum_le)).2.2.2.2)
        (fun r hr => hPE.2.2.2.2 r (le_trans hr hsum_le))
      have hO_o := hOC.2.2.2.2.2 δ (by rw [hlen_ok1]; exact hδ_old)
      simp only [hidx_sum] at hO_o ⊢
      rw [hrun_eq, ← hO_o, (hIdxOld δ hδ_old).2.2.2]
      subst hk1eq; rfl
    · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
      have hsum_eq : (HOrig k hk_lt_d).s₀ +
            (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
          hHk.len := by rw [hlen_ok1, hδeq, hPE.1]; omega
      simp only [hsum_eq, ← hHk.hRun]
      rw [hδeq, hIdxNew.2.2.2, hOrdIdxEq]

end U3

end MinCostFlow.Chain.Ordered
