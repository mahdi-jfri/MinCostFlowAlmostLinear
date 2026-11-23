module

public import MinCostFlow.Chain.Ordered.UpdateTraceHelpers

/-!
# Rebuild branch of ordered `updateLoop_hidden_trace`

Proves `U3.updateLoop_hidden_trace_rebuild`: when `updateLoop` triggers `algorithm1_rebuild`
at level `idx < P.d`, constructs the updated per-level ordered `LevelHistory` family (keeping
extended histories below `idx` and fresh `0`-step histories at `≥ idx` using `zeroLevelHistory`)
and establishes `ChainCoreRel` with the output-order clause.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

namespace U3

lemma updateLoop_hidden_trace_rebuild (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    (HOrig : ∀ k < P.d, LevelHistory T TP P N₀ stOrig k)
    (ℓ' g' : ℕ → ℝ) (U₀ : List Update)
    {idx : ℕ} (hidxLt : idx < P.d)
    (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hBr : st.bran = stOrig.bran)
    (hReb : st.rebuildCount = stOrig.rebuildCount)
    (hRest : st.curRestarts = stOrig.curRestarts)
    (hLvlM : st.lvlM = stOrig.lvlM)
    (hN0 : st.N₀ = stOrig.N₀)
    (hG0Inv : 0 < idx → (st.G 0).IsValid ∧ (st.G 0).m ≤ P.M₀ ∧ (st.G 0).n ≤ N₀ ∧
      (stOrig.G 0).V ⊆ (st.G 0).V ∧ (∀ e ∈ (st.G 0).E, 0 < ℓ' e))
    (hCurGValid : curG.IsValid)
    (hCurGM : (curG.m : ℝ) ≤ (levelM TP P idx : ℝ))
    (hCurGV0 : idx = 0 → curG.m ≤ P.M₀ ∧ curG.n ≤ N₀ ∧ (stOrig.G 0).V ⊆ curG.V ∧
      (∀ e ∈ curG.E, 0 < ℓ' e))
    (hCurGVPos : 0 < idx → curG.V ⊆ (st.G 0).V)
    (hCurLenR : LevelLenRange TP P N₀ Λ idx curG
      (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx))
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
      curG = T.S (st.scState (idx - 1)) (stOrig.bran (idx - 1)))
    (hPreCore : ∀ k (hk1 : k + 1 < idx),
      let Hk := HPre k (Nat.lt_of_succ_lt hk1)
      let Hk1 := HPre (k + 1) hk1
      Hk1.len ≤ Hk.len ∧
      let off := Hk.len - Hk1.len
      Hk.s₀ ≤ off ∧
      (∀ δ ≤ Hk1.len,
        Hk1.D.G δ = (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
          Hk.s₀ (stOrig.bran k)).G ((off - Hk.s₀) + δ)) ∧
      (∀ δ, 1 ≤ δ → δ ≤ Hk1.len →
        Hk1.D.U δ = (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
          Hk.s₀ (stOrig.bran k)).U ((off - Hk.s₀) + δ)) ∧
      (∀ δ ≤ Hk1.len, ∀ e ∈ (Hk1.D.G δ).E,
        Hk1.D.ℓ δ e = (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts
          Hk.s₀ (stOrig.bran k)).ℓ ((off - Hk.s₀) + δ) e) ∧
      (∀ δ ≤ Hk1.len,
        Hk1.ord δ = T.rot (T.runOrdAfterRestarts P.k (levelM TP P k) N₀
          Hk.D Hk.ord Hk.restarts (Hk.s₀ + ((off - Hk.s₀) + δ))) (stOrig.bran k))) :
    let stEnd := (algorithm1_rebuild T L P { st with ℓ := ℓ', g := g' } idx curG curEncAcc).1
    Nonempty (Σ' (H' : ∀ k < P.d, LevelHistory T TP P N₀ stEnd k),
      ChainCoreRel T TP P stEnd H' ∧
      (∀ iStar, firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some iStar →
        iStar < P.d ∧
        (∀ k (hk : k < P.d), k < iStar →
          (H' k hk).len = (HOrig k hk).len + 1 ∧
          (∀ s ≤ (HOrig k hk).len,
            (H' k hk).D.G s = (HOrig k hk).D.G s ∧ (H' k hk).D.U s = (HOrig k hk).D.U s ∧
            (H' k hk).D.ℓ s = (HOrig k hk).D.ℓ s ∧ (H' k hk).D.g s = (HOrig k hk).D.g s ∧
            (H' k hk).ord s = (HOrig k hk).ord s) ∧
          (k = 0 → (H' k hk).D.U ((HOrig k hk).len + 1) = U₀) ∧
          stEnd.bran k = stOrig.bran k ∧
          (H' k hk).s₀ = (HOrig k hk).s₀ ∧
          (∀ s ≤ (HOrig k hk).len, (H' k hk).restarts s = (HOrig k hk).restarts s)) ∧
        (∀ k (hk : k < P.d), iStar ≤ k → (H' k hk).len = 0 ∧ stEnd.bran k = 0)) ∧
      (firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = none →
        (∀ k (hk : k < P.d),
          (H' k hk).len = (HOrig k hk).len + 1 ∧
          (∀ s ≤ (HOrig k hk).len,
            (H' k hk).D.G s = (HOrig k hk).D.G s ∧ (H' k hk).D.U s = (HOrig k hk).D.U s ∧
            (H' k hk).D.ℓ s = (HOrig k hk).D.ℓ s ∧ (H' k hk).D.g s = (HOrig k hk).D.g s ∧
            (H' k hk).ord s = (HOrig k hk).ord s) ∧
          (k = 0 → (H' k hk).D.U ((HOrig k hk).len + 1) = U₀) ∧
          stEnd.bran k = stOrig.bran k ∧
          (H' k hk).s₀ = (HOrig k hk).s₀ ∧
          (∀ s ≤ (HOrig k hk).len, (H' k hk).restarts s = (HOrig k hk).restarts s)))) := by
  let stWithLG : ChainState T P := { st with ℓ := ℓ', g := g' }
  let G0 := fun j => if j = idx then curG else st.G j
  have hG0_valid : (G0 idx).IsValid := by simpa [G0] using hCurGValid
  have hG0_V : (G0 idx).V ⊆ (G0 0).V := by
    dsimp only [G0]
    by_cases h0 : idx = 0
    · simp [h0]
    · have h0' : 0 ≠ idx := Ne.symm h0
      simp only [↓reduceIte, h0']
      exact hCurGVPos (Nat.pos_of_ne_zero h0)
  have hG0_m : ((G0 idx).m : ℝ) ≤ (levelM TP P idx : ℝ) := by
    simpa [G0] using hCurGM
  have hℓ_pos_idx : LevelLenRange TP P N₀ Λ idx (G0 idx)
      ((mkPartialChain T P G0 st.scState st.bran (G0 idx)).chainLen ℓ' idx) := by
    intro e he
    have heC : e ∈ curG.E := by simpa [G0] using he
    have hCL := congrFun (chainLen_congr_lt
      (C₁ := mkPartialChain T P G0 st.scState st.bran (G0 idx))
      (C₂ := { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }) ℓ' idx
      (fun j _ => by simp [mkPartialChain, G0])
      (fun j hj => by
        have hjd := lt_trans hj hidxLt
        simp [TreeChain.activeLSF, mkPartialChain, ChainState.toTreeChain, hjd])) e
    rw [hCL]
    exact hCurLenR e heC
  have hG0_n : (G0 0).n ≤ N₀ := by
    dsimp only [G0]
    by_cases h0 : idx = 0
    · subst h0; simp only [↓reduceIte]; exact (hCurGV0 rfl).2.1
    · simp only [show (0 : ℕ) ≠ idx by omega, ↓reduceIte]
      exact (hG0Inv (Nat.pos_of_ne_zero h0)).2.2.1
  have hRot_idx : ∃ ρ : Rotation (G0 idx), ρ.order = chainLevelOrd T G0 st.scState st.bran idx := by
    by_cases h0 : idx = 0
    · subst h0
      exact ⟨sortedRotation (G0 0), by simp [sortedRotation, chainLevelOrd]⟩
    · have h0lt : 0 < idx := Nat.pos_of_ne_zero h0
      let k := idx - 1
      have hklt : k < idx := Nat.sub_lt h0lt zero_lt_one
      have hkd : k < P.d := lt_trans hklt hidxLt
      let hHk := HPre k hklt
      have hSpecK := hHk.hOK.noHidden P.k hHk.len (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts P.hk
        hHk.hG0 hHk.hD hHk.hLen hHk.hℓPos hHk.hOrd hHk.hInitMBound hHk.hInitNBound
        hHk.hRestartsLt (by rw [hHk.hUpd]; exact hHk.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hBrK : st.bran k < P.k := by rw [hBr]; exact hInvOrig.hBran k hkd
      have hOrdOut := hSpecK.2.2.2.2.1 hHk.s₀ hHk.len hHk.hs₀ (le_refl _) (st.bran k) hBrK
        hHk.hS0Fresh hHk.hNoRestartAfterS0
      obtain ⟨ρc, hρc_ord, _⟩ := hOrdOut
      let δ := hHk.len - hHk.s₀
      have hsum : hHk.s₀ + δ = hHk.len := Nat.add_sub_of_le hHk.hs₀
      have hRunEnd : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
          (hHk.s₀ + δ) = st.scState k := by
        rw [hsum, ← hHk.hRun]
      have hBrK_eq : st.bran k = stOrig.bran k := congrFun hBr k
      have hGeq : (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
          hHk.s₀ (st.bran k)).G δ = G0 idx := by
        simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hRunEnd, G0, ↓reduceIte]
        rw [hBrK_eq]
        exact (hCurFromPrev h0lt).2.symm
      refine ⟨hGeq ▸ ρc δ, ?_⟩
      rw [rotation_cast_order, hρc_ord δ (le_refl _)]
      dsimp only
      rw [hRunEnd]
      simp [chainLevelOrd, h0, k]
  have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk ℓ' g'
    (P.d - idx) idx G0 st.scState st.bran st.updCount st.curEnc
    st.curDecUpdates st.curFwd (by omega) hG0_valid hG0_V hG0_n hG0_m hℓ_pos_idx hRot_idx
  set res := rebuildSuffix T L P st.lvlM st.N₀ ℓ' g' (P.d - idx) idx G0 st.scState st.bran st.updCount
    st.curEnc st.curDecUpdates st.curFwd
  have hResEq : res = rebuildSuffix T L P (levelM TP P) N₀ ℓ' g' (P.d - idx) idx G0 st.scState st.bran st.updCount
      st.curEnc st.curDecUpdates st.curFwd := by
    dsimp only [res]; rw [hLvlM, hInvOrig.hLvlM, hN0, hInvOrig.hN0]
  rw [← hResEq] at hRS
  set stEnd := (algorithm1_rebuild T L P stWithLG idx curG curEncAcc).1
  have hFields : stEnd.G = res.1 ∧ stEnd.scState = res.2.1 ∧ stEnd.bran = res.2.2.1 ∧
      stEnd.updCount = res.2.2.2.1 ∧ stEnd.curEnc = res.2.2.2.2.1 ∧
      stEnd.curDecUpdates = res.2.2.2.2.2.1 ∧ stEnd.curFwd = res.2.2.2.2.2.2.1 ∧
      stEnd.curRestarts = (fun j => if idx ≤ j ∧ j < P.d then 0 else stOrig.curRestarts j) ∧
      stEnd.ℓ = ℓ' ∧ stEnd.g = g' ∧
      stEnd.rebuildCount = (fun j => if j = idx then stOrig.rebuildCount idx + 1
        else stOrig.rebuildCount j) := by
    simp [stEnd, algorithm1_rebuild, hidxLt, stWithLG, res, G0, hReb, hRest]
  rcases hFields with ⟨hF_G, hF_sc, hF_br, hF_upd, hF_enc, hF_dec, hF_fwd, hF_rest, hF_ℓ, hF_g, hF_reb⟩
  have hFirstSome : firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some idx := by
    rw [hF_reb]; exact firstRebuiltLevel_eq_of_inc hidxLt _
  have hChCon : ∀ k ≤ P.d,
      stEnd.toTreeChain.chainLen stEnd.ℓ k =
        (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainLen ℓ' k ∧
      stEnd.toTreeChain.chainGrad stEnd.g k =
        (mkPartialChain T P res.1 res.2.1 res.2.2.1 (res.1 P.d)).chainGrad g' k := by
    intro k hk
    refine ⟨?_, ?_⟩
    · rw [hF_ℓ]
      exact chainLen_congr_params (T := T) (C := stEnd.toTreeChain) rfl ℓ' hk
        (fun j _ => congrFun hF_G j)
        (fun j hj => by
          have hjd := lt_of_lt_of_le hj hk
          simp [ChainState.toTreeChain, hF_sc, hF_br])
    · rw [hF_g]
      exact chainGrad_congr_params (T := T) (C := stEnd.toTreeChain) rfl g' hk
        (fun j _ => congrFun hF_G j)
        (fun j hj => by
          have hjd := lt_of_lt_of_le hj hk
          simp [ChainState.toTreeChain, hF_sc, hF_br])
  have hEndG0n : (stEnd.G 0).n ≤ N₀ := by
    rw [hF_G, hRS.1 0 (Nat.zero_le _)]
    by_cases hidx0 : idx = 0
    · subst hidx0
      simp only [G0, ↓reduceIte]
      exact (hCurGV0 rfl).2.1
    · simp only [G0, show (0 : ℕ) ≠ idx by omega, ↓reduceIte]
      exact (hG0Inv (Nat.pos_of_ne_zero hidx0)).2.2.1
  have hOrdSuf : ∀ j, idx ≤ j → j < P.d →
      chainLevelOrd T res.1 res.2.1 res.2.2.1 j = stEnd.levelOrd j := by
    intro j _ _
    simp only [ChainState.levelOrd, chainLevelOrd, hF_G, hF_sc, hF_br]
  have hRotAll : ∀ k < P.d, ∃ ρ : Rotation (stEnd.G k), ρ.order = stEnd.levelOrd k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨sortedRotation (stEnd.G 0), by simp [sortedRotation, ChainState.levelOrd, chainLevelOrd]⟩
    | succ k ih =>
      intro hk1
      have hk : k < P.d := Nat.lt_of_succ_lt hk1
      by_cases hki : k < idx
      · let hHk := HPre k hki
        have hSpecK := hHk.hOK.noHidden P.k hHk.len (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts P.hk
          hHk.hG0 hHk.hD hHk.hLen hHk.hℓPos hHk.hOrd hHk.hInitMBound hHk.hInitNBound
          hHk.hRestartsLt (by rw [hHk.hUpd]; exact hHk.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hBrK : st.bran k < P.k := by rw [hBr]; exact hInvOrig.hBran k hk
        have hOrdOut := hSpecK.2.2.2.2.1 hHk.s₀ hHk.len hHk.hs₀ (le_refl _) (st.bran k) hBrK
          hHk.hS0Fresh hHk.hNoRestartAfterS0
        obtain ⟨ρc, hρc_ord, _⟩ := hOrdOut
        let δ := hHk.len - hHk.s₀
        have hsum : hHk.s₀ + δ = hHk.len := Nat.add_sub_of_le hHk.hs₀
        have hRunEnd : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
            (hHk.s₀ + δ) = stEnd.scState k := by
          rw [hsum, ← hHk.hRun]
          exact ((congrFun hF_sc k).trans (hRS.2.1 k hki).1).symm
        have hBrEnd : stEnd.bran k = st.bran k := (congrFun hF_br k).trans (hRS.2.1 k hki).2.1
        have hBrK_eq : st.bran k = stOrig.bran k := congrFun hBr k
        have hGeq : (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
            hHk.s₀ (st.bran k)).G δ = stEnd.G (k + 1) := by
          simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hRunEnd]
          by_cases hk1i : k + 1 < idx
          · have hGstep : stEnd.G (k + 1) = st.G (k + 1) := by
              rw [congrFun hF_G (k + 1), hRS.1 (k + 1) (by omega)]
              simp [G0, show k + 1 ≠ idx by omega]
            rw [hGstep]
            have hPC := (hPreCore k hk1i).2.2.1 (HPre (k + 1) hk1i).len (le_refl _)
            have hHk_len : (HPre (k + 1) hk1i).len ≤ hHk.len := (hPreCore k hk1i).1
            have hHk_s0 : hHk.s₀ ≤ hHk.len - (HPre (k + 1) hk1i).len := (hPreCore k hk1i).2.1
            have hsum' : hHk.s₀ + ((hHk.len - (HPre (k + 1) hk1i).len - hHk.s₀) +
                (HPre (k + 1) hk1i).len) = hHk.len := by omega
            simp only [SparseCoreRestartTool.coreInstanceOrdFrom] at hPC
            change (HPre (k + 1) hk1i).D.G (HPre (k + 1) hk1i).len =
              T.S (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ hHk.D hHk.ord hHk.restarts
                (hHk.s₀ + ((hHk.len - (HPre (k + 1) hk1i).len - hHk.s₀) +
                  (HPre (k + 1) hk1i).len))) (stOrig.bran k) at hPC
            rw [hsum', ← hHk.hRun] at hPC
            rw [← (HPre (k + 1) hk1i).hEndG, hPC, hBrK_eq,
              ← (congrFun hF_sc k).trans (hRS.2.1 k hki).1]
          · have hk1eq : k + 1 = idx := by omega
            have h0lt : 0 < idx := by omega
            have hIdxEq : idx - 1 = k := by omega
            have hFP2 : curG = T.S (st.scState k) (stOrig.bran k) := by
              have h := (hCurFromPrev h0lt).2
              rw [hIdxEq] at h
              exact h
            rw [hk1eq, congrFun hF_G idx, hRS.1 idx (le_refl _)]
            simp only [G0, ↓reduceIte]
            rw [hFP2, ← hBrK_eq, ← (congrFun hF_sc k).trans (hRS.2.1 k hki).1]
        refine ⟨hGeq ▸ ρc δ, ?_⟩
        rw [rotation_cast_order, hρc_ord δ (le_refl _)]
        dsimp only
        rw [hRunEnd]
        simp only [ChainState.levelOrd, chainLevelOrd, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel, hBrEnd]
      · have hik : idx ≤ k := by omega
        have hsuf := hRS.2.2.1 k hik hk
        have hRotK := ih hk
        let Dk : DynamicInstance :=
          { G := fun _ => stEnd.G k, U := fun _ => [],
            ℓ := fun _ => stEnd.toTreeChain.chainLen stEnd.ℓ k,
            g := fun _ => stEnd.toTreeChain.chainGrad stEnd.g k }
        have hOrdK : OrderedUpTo Dk 0 2 (fun _ => stEnd.levelOrd k) :=
          orderedUpTo_zero_of_rotation (fun _ => rfl) hRotK
        have hOKk : T.ToolOKAt TP P.k (levelM TP P k) N₀ (stEnd.G k)
            (stEnd.toTreeChain.chainLen stEnd.ℓ k) := by
          rw [(hChCon k hk.le).1, hF_G]; exact hsuf.2.2.2.2.2.2.2.2.2.2.2
        have hSpecK := hOKk.noHidden P.k 0 (levelM TP P k) N₀ Dk (fun _ => stEnd.levelOrd k)
          (fun _ => [])
          P.hk (by dsimp only [Dk]; rw [hF_G]; exact hsuf.2.2.2.2.2.1)
          (fun _ h1 h2 => by omega) (fun _ h1 h2 => by omega)
          (fun _ _ e he => by
            dsimp only [Dk] at he ⊢
            rw [(hChCon k hk.le).1]; rw [hF_G] at he; exact hsuf.2.2.2.2.2.2.2.2.1 e he)
          hOrdK
          (by
            dsimp only [Dk]
            exact_mod_cast (show ((stEnd.G k).m : ℝ) ≤ (levelM TP P k : ℝ) by
              rw [hF_G]; exact hsuf.2.2.2.2.2.2.2.1))
          (by
            dsimp only [Dk]
            have hVsub : (stEnd.G k).V ⊆ (stEnd.G 0).V := by
              rw [hF_G]; exact hsuf.2.2.2.2.2.2.1
            exact le_trans (Finset.card_le_card hVsub) hEndG0n)
          (fun _ _ _ h => absurd h List.not_mem_nil)
          (by simp [updateThreshold_nonneg]) ⟨rfl, rfl, rfl, rfl, rfl⟩
        have hOrdOut := hSpecK.2.2.2.2.1 0 0 (le_refl 0) (le_refl 0) 0 P.hk (Or.inl rfl)
          (fun _ _ _ h => absurd h List.not_mem_nil)
        obtain ⟨ρc, hρc_ord, _⟩ := hOrdOut
        have hScK : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ Dk (fun _ => stEnd.levelOrd k)
            (fun _ => []) 0 = stEnd.scState k := by
          simp only [SparseCoreRestartTool.runOrdAfterRestarts,
            SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil, Dk]
          rw [hF_sc, hF_G, (hChCon k hk.le).1, (hChCon k hk.le).2, ← hOrdSuf k hik hk]
          exact hsuf.2.2.2.2.2.2.2.2.2.1.symm
        have hGeq : (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Dk (fun _ => stEnd.levelOrd k)
            (fun _ => []) 0 0).G 0 = stEnd.G (k + 1) := by
          simp only [SparseCoreRestartTool.coreInstanceOrdFrom, Nat.add_zero, hScK]
          rw [hF_G, hF_sc]
          exact hsuf.2.2.2.2.2.2.2.2.2.2.1.symm
        refine ⟨hGeq ▸ ρc 0, ?_⟩
        rw [rotation_cast_order, hρc_ord 0 (le_refl 0)]
        dsimp only
        rw [Nat.add_zero, hScK]
        simp only [ChainState.levelOrd, chainLevelOrd, Nat.add_eq_zero_iff,
          one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel, hF_br, hsuf.1]
  let H' : ∀ k < P.d, LevelHistory T TP P N₀ stEnd k := fun k hk =>
    if hki : k < idx then
      have hpre := hRS.2.1 k hki
      levelHistory_congr_state hk (HPre k hki)
        (fun j hj => by
          rw [congrFun hF_G j, hRS.1 j (by omega)]
          simp [G0, show j ≠ idx by omega])
        (congrFun hF_sc k |>.trans hpre.1)
        (by rw [hF_rest, hRest]; simp [show ¬ idx ≤ k by omega])
        (fun j hj => by
          have hjl := lt_trans hj hk
          have hjp := hRS.2.1 j (lt_trans hj hki)
          simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjl, ↓reduceIte]
          rw [hF_sc, hF_br, hjp.1, hjp.2.1])
        hF_ℓ hF_g
        (congrFun hF_upd k |>.trans hpre.2.2.1)
        (congrFun hF_fwd k |>.trans hpre.2.2.2.2.2)
        (congrFun hF_br k |>.trans hpre.2.1)
        (congrFun hF_dec k |>.trans hpre.2.2.2.2.1)
        (fun h0 => by subst h0; exact congrFun hF_enc 0 |>.trans hpre.2.2.2.1)
        (fun _ => by
          by_cases hlt1 : k + 1 < idx
          · exact le_of_eq (congrFun hF_enc (k + 1) |>.trans
              (hRS.2.1 (k + 1) hlt1).2.2.2.1)
          · have heq : k + 1 = idx := by omega
            rw [heq, congrFun hF_enc idx, (hRS.2.2.1 idx (le_refl _) hidxLt).2.2.1]
            exact Nat.zero_le _)
        (by
          simp only [ChainState.levelOrd, chainLevelOrd]
          by_cases h0 : k = 0
          · subst h0
            simp only [↓reduceIte]
            rw [congrFun hF_G 0, hRS.1 0 (Nat.zero_le _)]
            simp [G0, show (0 : ℕ) ≠ idx by omega]
          · simp only [h0, ↓reduceIte]
            have hpm : k - 1 < idx := by omega
            have hpp := hRS.2.1 (k - 1) hpm
            rw [congrFun hF_sc (k - 1), hpp.1, congrFun hF_br (k - 1), hpp.2.1])
    else
      have hik : idx ≤ k := by omega
      have hsuf := hRS.2.2.1 k hik hk
      zeroLevelHistory T TP P N₀ stEnd k hk hTP
        (by rw [hF_G]; exact hsuf.2.2.2.2.2.1)
        (by rw [hF_G]; exact hsuf.2.2.2.2.2.2.2.1)
        (by
          have hVsub : (stEnd.G k).V ⊆ (stEnd.G 0).V := by
            rw [hF_G]; exact hsuf.2.2.2.2.2.2.1
          exact le_trans (Finset.card_le_card hVsub) hEndG0n)
        (fun e he => by rw [(hChCon k hk.le).1]; rw [hF_G] at he; exact hsuf.2.2.2.2.2.2.2.2.1 e he)
        (hRotAll k hk)
        (by
          rw [hF_sc, hF_G, (hChCon k hk.le).1, (hChCon k hk.le).2, ← hOrdSuf k hik hk]
          exact hsuf.2.2.2.2.2.2.2.2.2.1)
        (by rw [hF_upd]; exact hsuf.2.1)
        (by rw [hF_fwd]; exact hsuf.2.2.2.2.1)
        (by rw [hF_dec]; exact hsuf.2.2.2.1)
        (by rw [hF_rest]; simp [hik, hk])
        (fun h0 => by
          subst h0
          have hidx0 : idx = 0 := by omega
          subst hidx0
          rw [hF_enc]; exact hsuf.2.2.1)
        (fun h1 => by
          rw [hF_enc]
          exact (hRS.2.2.1 (k + 1) (by omega) h1).2.2.1)
        (by rw [(hChCon k hk.le).1, hF_G]; exact hsuf.2.2.2.2.2.2.2.2.2.2.2)
  refine ⟨⟨H', ?_, fun iStar hSome => ?_, fun hNone => ?_⟩⟩
  · intro k hk
    by_cases hk1 : k + 1 < idx
    · have hk0 : k < idx := Nat.lt_of_succ_lt hk1
      have hPC := hPreCore k hk1
      have hBr_eq : stEnd.bran k = stOrig.bran k := by
        rw [hF_br, (hRS.2.1 k hk0).2.1, hBr]
      simp only [H', hk0, ↓reduceDIte, hk1, levelHistory_congr_state, hBr_eq]
      exact hPC
    · by_cases hk_lt : k < idx
      · have hkeq : k + 1 = idx := by omega
        have h0lt : 0 < idx := by omega
        have hIdxEq : idx - 1 = k := by omega
        have hFP2 : curG = T.S (st.scState k) (stOrig.bran k) := by
          have h := (hCurFromPrev h0lt).2
          rw [hIdxEq] at h
          exact h
        have hBr_k : stEnd.bran k = stOrig.bran k := by
          rw [hF_br, (hRS.2.1 k hk_lt).2.1, hBr]
        simp only [H', hk_lt, ↓reduceDIte, hk1, levelHistory_congr_state, zeroLevelHistory]
        have hoff0 : (HPre k hk_lt).s₀ + (((HPre k hk_lt).len - 0 - (HPre k hk_lt).s₀) + 0) =
            (HPre k hk_lt).len := by
          have := (HPre k hk_lt).hs₀; omega
        refine ⟨Nat.zero_le _, (HPre k hk_lt).hs₀, fun δ hδ => ?_, fun δ h1 hδ => by omega,
          fun δ hδ e _ => ?_, fun δ hδ => ?_⟩
        · have hδ0 : δ = 0 := by omega
          subst hδ0
          simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hoff0]
          change stEnd.G (k + 1) =
            T.S (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D (HPre k hk_lt).ord
              (HPre k hk_lt).restarts (HPre k hk_lt).len) (stEnd.bran k)
          rw [hkeq, hF_G, hRS.1 idx (le_refl _), hBr_k, ← (HPre k hk_lt).hRun]
          simpa [G0] using hFP2
        · have hδ0 : δ = 0 := by omega
          subst hδ0
          simp only [SparseCoreRestartTool.coreInstanceOrdFrom, hoff0]
          change stEnd.toTreeChain.chainLen stEnd.ℓ (k + 1) e =
            coreLen (T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D
              (HPre k hk_lt).ord (HPre k hk_lt).restarts (HPre k hk_lt).len) (stEnd.bran k))
              ((HPre k hk_lt).D.ℓ (HPre k hk_lt).len) e
          have hActk : stEnd.toTreeChain.activeLSF k =
              T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D
                (HPre k hk_lt).ord (HPre k hk_lt).restarts (HPre k hk_lt).len) (stEnd.bran k) := by
            have hk_d : k < P.d := Nat.lt_of_succ_lt hk
            simp only [TreeChain.activeLSF, ChainState.toTreeChain, hk_d, ↓reduceIte]
            rw [hF_sc, (hRS.2.1 k hk_lt).1, ← (HPre k hk_lt).hRun, hBr_k, hBr]
          have hCLk : stEnd.toTreeChain.chainLen stEnd.ℓ k e =
              (HPre k hk_lt).D.ℓ (HPre k hk_lt).len e := by
            rw [(hPreExt k hk_lt).2.2.2.1, hF_ℓ]
            exact congrFun (chainLen_congr_lt (C₁ := stEnd.toTreeChain)
              (C₂ := ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain) ℓ' k
              (fun j hj => by
                simp only [ChainState.toTreeChain]
                rw [congrFun hF_G j, hRS.1 j (by omega)]
                simp [G0, show j ≠ idx by omega])
              (fun j hj => by
                have hjd : j < P.d := lt_trans hj (Nat.lt_of_succ_lt hk)
                have hjp := hRS.2.1 j (lt_trans hj hk_lt)
                simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjd, ↓reduceIte]
                rw [hF_sc, hF_br, hjp.1, hjp.2.1])) e
          rw [← hActk]
          change (stEnd.toTreeChain.activeLSF k).wstr e * stEnd.toTreeChain.chainLen stEnd.ℓ k e =
            (stEnd.toTreeChain.activeLSF k).wstr e * (HPre k hk_lt).D.ℓ (HPre k hk_lt).len e
          rw [hCLk]
        · have hδ0 : δ = 0 := by omega
          subst hδ0
          simp only [hoff0]
          change stEnd.levelOrd (k + 1) =
            T.rot (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D
              (HPre k hk_lt).ord (HPre k hk_lt).restarts (HPre k hk_lt).len) (stEnd.bran k)
          simp only [ChainState.levelOrd, chainLevelOrd, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            ↓reduceIte, Nat.add_sub_cancel]
          rw [hF_sc, (hRS.2.1 k hk_lt).1, ← (HPre k hk_lt).hRun]
      · have hik : idx ≤ k := by omega
        have hk_lt_d : k < P.d := Nat.lt_of_succ_lt hk
        have hsuf := hRS.2.2.1 k hik hk_lt_d
        simp only [H', hk_lt, ↓reduceDIte, hk1, zeroLevelHistory]
        have hsc_k : stEnd.scState k =
            T.initOrd P.k (levelM TP P k) N₀ (stEnd.G k) (stEnd.toTreeChain.chainLen stEnd.ℓ k)
              (stEnd.toTreeChain.chainGrad stEnd.g k) (stEnd.levelOrd k) := by
          rw [hF_sc, hF_G, (hChCon k hk_lt_d.le).1, (hChCon k hk_lt_d.le).2, ← hOrdSuf k hik hk_lt_d]
          exact hsuf.2.2.2.2.2.2.2.2.2.1
        refine ⟨le_refl 0, le_refl 0, fun δ hδ => ?_, fun δ h1 hδ => by omega,
          fun δ hδ e _ => ?_, fun δ hδ => ?_⟩
        · have hδ0 : δ = 0 := by omega
          subst hδ0
          simp only [SparseCoreRestartTool.coreInstanceOrdFrom,
            SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
            Nat.sub_zero, add_zero, List.foldl_nil]
          rw [← hsc_k, hF_G, hF_br, hsuf.1, hF_sc]
          exact hsuf.2.2.2.2.2.2.2.2.2.2.1
        · have hδ0 : δ = 0 := by omega
          subst hδ0
          simp only [SparseCoreRestartTool.coreInstanceOrdFrom,
            SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
            Nat.sub_zero, add_zero, List.foldl_nil]
          change stEnd.toTreeChain.chainLen stEnd.ℓ (k + 1) e =
            coreLen (T.lsfs (T.initOrd P.k (levelM TP P k) N₀ (stEnd.G k)
              (stEnd.toTreeChain.chainLen stEnd.ℓ k) (stEnd.toTreeChain.chainGrad stEnd.g k)
              (stEnd.levelOrd k)) (stEnd.bran k))
              (stEnd.toTreeChain.chainLen stEnd.ℓ k) e
          have hActk : stEnd.toTreeChain.activeLSF k = T.lsfs (stEnd.scState k) (stEnd.bran k) := by
            simp only [TreeChain.activeLSF, ChainState.toTreeChain, hk_lt_d, ↓reduceIte]
          rw [← hsc_k, ← hActk]; rfl
        · have hδ0 : δ = 0 := by omega
          subst hδ0
          simp only [SparseCoreRestartTool.runOrdAfterRestarts,
            SparseCoreRestartTool.runOrdAfterUpdate, Nat.sub_zero, add_zero, List.foldl_nil]
          change stEnd.levelOrd (k + 1) =
            T.rot (T.initOrd P.k (levelM TP P k) N₀ (stEnd.G k)
              (stEnd.toTreeChain.chainLen stEnd.ℓ k) (stEnd.toTreeChain.chainGrad stEnd.g k)
              (stEnd.levelOrd k)) (stEnd.bran k)
          rw [← hsc_k]
          simp [ChainState.levelOrd, chainLevelOrd]
  · rw [hFirstSome] at hSome
    obtain rfl := Option.some.inj hSome
    refine ⟨hidxLt, fun k hk hki => ?_, fun k hk hik => ?_⟩
    · have hpre := hRS.2.1 k hki
      simp only [H', hki, ↓reduceDIte, levelHistory_congr_state]
      refine ⟨(hPreExt k hki).1, (hPreExt k hki).2.1, (hPreExt k hki).2.2.1, ?_,
        (hPreExt k hki).2.2.2.2⟩
      rw [hF_br, hpre.2.1, hBr]
    · have hnot : ¬ k < idx := by omega
      have hsuf := hRS.2.2.1 k hik hk
      simp only [H', hnot, ↓reduceDIte, zeroLevelHistory]
      exact ⟨trivial, by rw [hF_br, hsuf.1]⟩
  · rw [hFirstSome] at hNone; cases hNone

end U3

end MinCostFlow.Chain.Ordered
