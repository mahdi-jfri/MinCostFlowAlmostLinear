module

public import MinCostFlow.Chain.UpdateTraceHelpers

/-!
# Per-level dynamic history extension through `updateLoop` (`MinCostFlow/Chain/UpdateTrace`)

Proves `updateLoop_hidden_trace`, tracking explicit `LevelHistory` records and inter-level
`coreInstance` coupling across `updateLoop` / `algorithm1_update`.
-/

@[expose] public section

namespace MinCostFlow.Chain

lemma updateLoop_hidden_trace (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    (HOrig : ∀ k < P.d, LevelHistory T TP P N₀ stOrig k)
    (hOrigCore : ChainCoreRel T TP P stOrig HOrig)
    (ℓ' g' : ℕ → ℝ) (U₀ : List Update) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
      (hidxSum : idx + rem = P.d),
      (∀ j, idx ≤ j → st.G j = stOrig.G j) →
      (∀ j, idx ≤ j → st.scState j = stOrig.scState j) →
      (∀ j, idx ≤ j → st.updCount j = stOrig.updCount j) →
      (∀ j, idx ≤ j → st.curDecUpdates j = stOrig.curDecUpdates j) →
      (∀ j, idx < j → st.curEnc j = stOrig.curEnc j) →
      st.bran = stOrig.bran →
      (∀ j, idx ≤ j → st.curFwd j = stOrig.curFwd j) →
      st.rebuildCount = stOrig.rebuildCount →
      st.curRestarts = stOrig.curRestarts →
      st.lvlM = stOrig.lvlM →
      st.N₀ = stOrig.N₀ →
      (idx = 0 → curEncAcc = (stOrig.G 0).batchEnc curU ∧ st.curEnc 0 = stOrig.curEnc 0) →
      (0 < idx → curEncAcc = 0) →
      (∀ j < idx, (st.G j).V ⊆ (st.G 0).V) →
      (∀ j < idx, ((st.G j).m : ℝ) ≤ (levelM TP P j : ℝ)) →
      (∀ j, j + 1 < idx → st.G (j + 1) = T.S (st.scState j) (st.bran j)) →
      (idx = 0 → curU = U₀) →
      (0 < idx → (st.G 0).IsValid ∧ (st.G 0).m ≤ P.M₀ ∧ (st.G 0).n ≤ N₀ ∧
        (stOrig.G 0).V ⊆ (st.G 0).V ∧ (∀ e ∈ (st.G 0).E, 0 < ℓ' e)) →
      curG = (stOrig.G idx).applyBatch curU →
      (stOrig.G idx).BatchIsValid curU →
      curG.IsValid →
      (curG.m : ℝ) ≤ (levelM TP P idx : ℝ) →
      (idx = 0 → curG.m ≤ P.M₀ ∧ curG.n ≤ N₀ ∧ (stOrig.G 0).V ⊆ curG.V ∧
        (∀ e ∈ curG.E, 0 < ℓ' e)) →
      (0 < idx → curG.V ⊆ (st.G 0).V) →
      (∀ e ∈ curG.E, 0 <
        ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx e) →
      (∀ e ∈ curG.E, e ∈ (stOrig.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
        ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx e =
          stOrig.toTreeChain.chainLen stOrig.ℓ idx e) →
      ∀ (HPre : ∀ k, k < idx → LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } k),
      (∀ k (hk : k < idx),
        (HPre k hk).len = (HOrig k (by omega)).len + 1 ∧
        (∀ s ≤ (HOrig k (by omega)).len,
          (HPre k hk).D.G s = (HOrig k (by omega)).D.G s ∧
          (HPre k hk).D.U s = (HOrig k (by omega)).D.U s ∧
          (HPre k hk).D.ℓ s = (HOrig k (by omega)).D.ℓ s ∧
          (HPre k hk).D.g s = (HOrig k (by omega)).D.g s) ∧
        (k = 0 → (HPre k hk).D.U ((HOrig k (by omega)).len + 1) = U₀) ∧
        ((HPre k hk).D.ℓ ((HPre k hk).len) =
          ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' k) ∧
        (HPre k hk).s₀ = (HOrig k (by omega)).s₀ ∧
        (∀ s ≤ (HOrig k (by omega)).len,
          (HPre k hk).restarts s = (HOrig k (by omega)).restarts s)) →
      (∀ h0 : 0 < idx,
        curU = (T.runAfterUpdate P.k (levelM TP P (idx - 1)) N₀
          (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).D
          (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).restarts
          ((HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).len)).2 (stOrig.bran (idx - 1)) ∧
        curG = T.S (st.scState (idx - 1)) (stOrig.bran (idx - 1))) →
      (∀ k (hk1 : k + 1 < idx),
        let Hk := HPre k (Nat.lt_of_succ_lt hk1)
        let Hk1 := HPre (k + 1) hk1
        Hk1.len ≤ Hk.len ∧
        let off := Hk.len - Hk1.len
        Hk.s₀ ≤ off ∧
        (∀ δ ≤ Hk1.len,
          Hk1.D.G δ = (T.coreInstanceFrom P.k (levelM TP P k) N₀ Hk.D Hk.restarts Hk.s₀ (stOrig.bran k)).G
            ((off - Hk.s₀) + δ)) ∧
        (∀ δ, 1 ≤ δ → δ ≤ Hk1.len →
          Hk1.D.U δ = (T.coreInstanceFrom P.k (levelM TP P k) N₀ Hk.D Hk.restarts Hk.s₀ (stOrig.bran k)).U
            ((off - Hk.s₀) + δ)) ∧
        (∀ δ ≤ Hk1.len, ∀ e ∈ (Hk1.D.G δ).E,
          Hk1.D.ℓ δ e = (T.coreInstanceFrom P.k (levelM TP P k) N₀ Hk.D Hk.restarts Hk.s₀ (stOrig.bran k)).ℓ
            ((off - Hk.s₀) + δ) e)) →
      let stEnd := (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
      Nonempty (Σ' (H' : ∀ k < P.d, LevelHistory T TP P N₀ stEnd k),
        ChainCoreRel T TP P stEnd H' ∧
        (∀ iStar, firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = some iStar →
          iStar < P.d ∧
          (∀ k (hk : k < P.d), k < iStar →
            (H' k hk).len = (HOrig k hk).len + 1 ∧
            (∀ s ≤ (HOrig k hk).len,
              (H' k hk).D.G s = (HOrig k hk).D.G s ∧ (H' k hk).D.U s = (HOrig k hk).D.U s ∧
              (H' k hk).D.ℓ s = (HOrig k hk).D.ℓ s ∧ (H' k hk).D.g s = (HOrig k hk).D.g s) ∧
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
              (H' k hk).D.ℓ s = (HOrig k hk).D.ℓ s ∧ (H' k hk).D.g s = (HOrig k hk).D.g s) ∧
            (k = 0 → (H' k hk).D.U ((HOrig k hk).len + 1) = U₀) ∧
            stEnd.bran k = stOrig.bran k ∧
            (H' k hk).s₀ = (HOrig k hk).s₀ ∧
            (∀ s ≤ (HOrig k hk).len, (H' k hk).restarts s = (HOrig k hk).restarts s)))) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hidxSum _ _ _ _ _
      hBr _ hReb hRest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPre hPreExt _ hPreCore
    have hidxEq : idx = P.d := by omega
    subst hidxEq
    set stEnd := (updateLoop T L TP P N₀ ℓ' g' 0 P.d st curG curU curEncAcc).1
    have hFields : stEnd.scState = st.scState ∧ stEnd.bran = st.bran ∧
        stEnd.updCount = st.updCount ∧ stEnd.curFwd = st.curFwd ∧
        stEnd.curDecUpdates = st.curDecUpdates ∧ stEnd.curEnc = st.curEnc ∧
        stEnd.rebuildCount = stOrig.rebuildCount ∧ stEnd.curRestarts = stOrig.curRestarts ∧
        stEnd.ℓ = ℓ' ∧ stEnd.g = g' ∧ ∀ j < P.d, stEnd.G j = st.G j := by
      dsimp only [stEnd, updateLoop]
      by_cases hU : curU = []
      · simp [hU, hReb, hRest]; exact fun j hj => by simp [Nat.ne_of_lt hj]
      · simp [hU, hReb, hRest]; exact fun j hj => by simp [Nat.ne_of_lt hj]
    rcases hFields with ⟨hF_sc, hF_br, hF_upd, hF_fwd, hF_dec, hF_enc, hF_reb, hF_rest, hF_ℓ, hF_g, hF_G⟩
    have hFirstNone : firstRebuiltLevel P.d stOrig.rebuildCount stEnd.rebuildCount = none := by
      rw [hF_reb]; exact firstRebuiltLevel_eq_of_eq _
    let H' : ∀ k < P.d, LevelHistory T TP P N₀ stEnd k := fun k hk =>
      levelHistory_congr_state hk (HPre k hk)
        (fun j hj => hF_G j (lt_of_le_of_lt hj hk))
        (congrFun hF_sc k)
        (congrFun hF_rest k |>.trans (congrFun hRest.symm k))
        (fun j hj => by
          have hjd : j < P.d := lt_trans hj hk
          simp [TreeChain.activeLSF, ChainState.toTreeChain, hjd, hF_sc, hF_br])
        hF_ℓ hF_g
        (congrFun hF_upd k) (congrFun hF_fwd k)
        (congrFun hF_br k) (congrFun hF_dec k)
        (fun _ => congrFun hF_enc 0)
        (fun _ => le_of_eq (congrFun hF_enc (k + 1)))
    refine ⟨⟨H', ?_, fun iStar hSome => ?_, fun _ k hk => ?_⟩⟩
    · intro k hk
      simpa only [H', levelHistory_congr_state, hF_br, hBr] using hPreCore k hk
    · rw [hFirstNone] at hSome; cases hSome
    · refine ⟨(hPreExt k hk).1, (hPreExt k hk).2.1, (hPreExt k hk).2.2.1, ?_,
        (hPreExt k hk).2.2.2.2⟩
      rw [hF_br, hBr]
  | succ rem ih =>
    intro idx st curG curU curEncAcc hidxSum hGGe hScGe hUpdGe hDecGe hEncGt
      hBr hCFwd hReb hRest hLvlM hN0 hEncAcc0 hEncAccPos hPreV hPreM hPreGSucc hCurU0 hG0Inv hCurGEq
      hCurGBatch hCurGValid hCurGM hCurGV0 hCurGVPos hCurLenPos hCurLenStable
      HPre hPreExt hCurFromPrev hPreCore
    have hidxLt : idx < P.d := by omega
    have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInvOrig
    dsimp only [updateLoop]
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · rw [ite_eq_left_iff.mpr fun h => absurd hOver h]
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
      have hℓ_pos_idx : ∀ e ∈ (G0 idx).E,
          0 < (mkPartialChain T P G0 st.scState st.bran (G0 idx)).chainLen ℓ' idx e := by
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
        exact hCurLenPos e heC
      have hG0_n : (G0 0).n ≤ N₀ := by
        dsimp only [G0]
        by_cases h0 : idx = 0
        · subst h0; simp only [↓reduceIte]; exact (hCurGV0 rfl).2.1
        · simp only [show (0 : ℕ) ≠ idx by omega, ↓reduceIte]
          exact (hG0Inv (Nat.pos_of_ne_zero h0)).2.2.1
      have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk ℓ' g'
        (P.d - idx) idx G0 st.scState st.bran st.updCount st.curEnc
        st.curDecUpdates st.curFwd (by omega) hG0_valid hG0_V hG0_n hG0_m hℓ_pos_idx
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
        else
          have hik : idx ≤ k := by omega
          have hsuf := hRS.2.2.1 k hik hk
          zeroLevelHistory T TP P N₀ stEnd k hk hTP
            (by rw [hF_G]; exact hsuf.2.2.2.2.2.1)
            (by rw [hF_G]; exact hsuf.2.2.2.2.2.2.2.1)
            (by
              have hVsub : (stEnd.G k).V ⊆ (stEnd.G 0).V := by
                rw [hF_G]; exact hsuf.2.2.2.2.2.2.1
              have hG0n : (stEnd.G 0).n ≤ N₀ := by
                rw [hF_G, hRS.1 0 (Nat.zero_le _)]
                by_cases hidx0 : idx = 0
                · subst hidx0
                  simp only [G0, ↓reduceIte]
                  exact (hCurGV0 rfl).2.1
                · simp only [G0, show (0 : ℕ) ≠ idx by omega, ↓reduceIte]
                  exact (hG0Inv (Nat.pos_of_ne_zero hidx0)).2.2.1
              exact le_trans (Finset.card_le_card hVsub) hG0n)
            (fun e he => by rw [(hChCon k hk.le).1]; rw [hF_G] at he; exact hsuf.2.2.2.2.2.2.2.2.1 e he)
            (by rw [hF_sc, hF_G, (hChCon k hk.le).1, (hChCon k hk.le).2]; exact hsuf.2.2.2.2.2.2.2.2.2.1)
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
              fun δ hδ e _ => ?_⟩
            · have hδ0 : δ = 0 := by omega
              subst hδ0
              simp only [SparseCoreRestartTool.coreInstanceFrom, hoff0]
              change stEnd.G (k + 1) =
                T.S (T.runAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D (HPre k hk_lt).restarts
                  (HPre k hk_lt).len) (stEnd.bran k)
              rw [hkeq, hF_G, hRS.1 idx (le_refl _), hBr_k, ← (HPre k hk_lt).hRun]
              simpa [G0] using hFP2
            · have hδ0 : δ = 0 := by omega
              subst hδ0
              simp only [SparseCoreRestartTool.coreInstanceFrom, hoff0]
              change stEnd.toTreeChain.chainLen stEnd.ℓ (k + 1) e =
                coreLen (T.lsfs (T.runAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D (HPre k hk_lt).restarts
                  (HPre k hk_lt).len) (stEnd.bran k))
                  ((HPre k hk_lt).D.ℓ (HPre k hk_lt).len) e
              have hActk : stEnd.toTreeChain.activeLSF k =
                  T.lsfs (T.runAfterRestarts P.k (levelM TP P k) N₀ (HPre k hk_lt).D (HPre k hk_lt).restarts
                    (HPre k hk_lt).len) (stEnd.bran k) := by
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
          · have hik : idx ≤ k := by omega
            have hk_lt_d : k < P.d := Nat.lt_of_succ_lt hk
            have hsuf := hRS.2.2.1 k hik hk_lt_d
            simp only [H', hk_lt, ↓reduceDIte, hk1, zeroLevelHistory]
            refine ⟨le_refl 0, le_refl 0, fun δ hδ => ?_, fun δ h1 hδ => by omega,
              fun δ hδ e _ => ?_⟩
            · have hδ0 : δ = 0 := by omega
              subst hδ0
              simp only [SparseCoreRestartTool.coreInstanceFrom,
                SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
                Nat.sub_zero, add_zero, List.foldl_nil]
              rw [hF_G, hF_br, hsuf.1, hsuf.2.2.2.2.2.2.2.2.2.2,
                (hChCon k hk_lt_d.le).1, (hChCon k hk_lt_d.le).2, ← hsuf.2.2.2.2.2.2.2.2.2.1]
            · have hδ0 : δ = 0 := by omega
              subst hδ0
              simp only [SparseCoreRestartTool.coreInstanceFrom,
                SparseCoreRestartTool.runAfterRestarts, SparseCoreRestartTool.runAfterUpdate,
                Nat.sub_zero, add_zero, List.foldl_nil]
              change stEnd.toTreeChain.chainLen stEnd.ℓ (k + 1) e =
                coreLen (T.lsfs (T.init P.k (levelM TP P k) N₀ (stEnd.G k) (stEnd.toTreeChain.chainLen stEnd.ℓ k)
                  (stEnd.toTreeChain.chainGrad stEnd.g k)) (stEnd.bran k))
                  (stEnd.toTreeChain.chainLen stEnd.ℓ k) e
              have hsc_k : stEnd.scState k =
                  T.init P.k (levelM TP P k) N₀ (stEnd.G k) (stEnd.toTreeChain.chainLen stEnd.ℓ k)
                    (stEnd.toTreeChain.chainGrad stEnd.g k) := by
                rw [hF_sc, hF_G, (hChCon k hk_lt_d.le).1, (hChCon k hk_lt_d.le).2]
                exact hsuf.2.2.2.2.2.2.2.2.2.1
              have hActk : stEnd.toTreeChain.activeLSF k = T.lsfs (stEnd.scState k) (stEnd.bran k) := by
                simp only [TreeChain.activeLSF, ChainState.toTreeChain, hk_lt_d, ↓reduceIte]
              rw [← hsc_k, ← hActk]; rfl
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
    · rw [ite_eq_right_iff.mpr fun h => absurd h hOver]
      have hLeThresh : ((st.updCount idx + curU.length : ℕ) : ℝ) ≤
          SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ :=
        (Nat.cast_le.mpr (Nat.le_of_not_lt hOver)).trans (intRebuildThreshold_le_updateThreshold hTP N₀ idx)
      set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      set ℓi := Cpartial.chainLen ℓ' idx
      set gi := Cpartial.chainGrad g' idx
      set updRes := T.update (st.scState idx) curU ℓi gi
      set sc' := updRes.1
      set U_S := updRes.2
      set oldFiE := (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
      set newFiE := (T.lsfs sc' (st.bran idx)).F.F.E
      set fiChanges := diffTreeChanges oldFiE newFiE
      set nextG := T.S sc' (st.bran idx)
      set nextU := U_S (st.bran idx)
      set nextEnc := (st.G (idx + 1)).batchEnc nextU
      let stNext : ChainState T P :=
        { st with
          G := fun j => if j = idx then curG else st.G j
          scState := fun j => if j = idx then sc' else st.scState j
          updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
          recUpdates := fun j =>
            if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
          curFwd := fun j =>
            if j = idx then st.curFwd idx + nextU.length else st.curFwd j
          curEnc := fun j =>
            if j = idx then st.curEnc idx + curEncAcc
            else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
            else st.curEnc j
          curDecUpdates := fun j => if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
      let stNextLG : ChainState T P := { stNext with ℓ := ℓ', g := g' }
      have hG_eq : stNextLG.G idx = curG := by simp [stNextLG, stNext]
      have hBrLt : stOrig.bran idx < P.k := hInvOrig.hBran idx hidxLt
      have hToTC : ∀ j < idx, stNextLG.toTreeChain.activeLSF j = Cpartial.activeLSF j := fun j hj => by
        have hjd : j < P.d := lt_trans hj hidxLt
        simp [TreeChain.activeLSF, ChainState.toTreeChain, stNextLG, stNext, Cpartial, hjd, Nat.ne_of_lt hj]
      have hCL_eq : ℓi = stNextLG.toTreeChain.chainLen ℓ' idx :=
        (chainLen_congr_lt (C₁ := stNextLG.toTreeChain) (C₂ := Cpartial) ℓ' idx
          (fun j hj => by simp [stNextLG, stNext, Cpartial, ChainState.toTreeChain, Nat.ne_of_lt hj])
          hToTC).symm
      have hCG_eq : gi = stNextLG.toTreeChain.chainGrad g' idx :=
        (chainGrad_congr_lt (C₁ := stNextLG.toTreeChain) (C₂ := Cpartial) g' idx
          (fun j hj => by simp [stNextLG, stNext, Cpartial, ChainState.toTreeChain, Nat.ne_of_lt hj])
          hToTC).symm
      have hThresh1 : ((stNextLG.updCount idx : ℕ) : ℝ) ≤
          SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ := by
        dsimp only [stNextLG, stNext]
        simp only [↓reduceIte]
        exact hLeThresh
      have hCurLenStable' : ∀ e ∈ curG.E, e ∈ (stOrig.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
          ℓi e = stOrig.toTreeChain.chainLen stOrig.ℓ idx e :=
        fun e he1 he2 hno => hCurLenStable e he1 he2 hno
      let hHidx : LevelHistory T TP P N₀ stNextLG idx :=
        extendLevelHistory hTP hT hγk hidxLt (HOrig idx hidxLt) curU curG ℓi gi hCurGEq hCurGBatch
          hCurGValid hG_eq hCL_eq hCG_eq
          (fun e he => hCurLenPos e he) hCurLenStable'
          (by simp [stNextLG, stNext, hUpdGe idx (le_refl _)]) hThresh1
          (by simp [stNextLG, stNext, nextU, U_S, updRes, hScGe idx (le_refl _),
            hCFwd idx (le_refl _), hBr])
          (by simp [stNextLG, stNext, updRes, sc', hScGe idx (le_refl _)])
          (by simp [stNextLG, stNext, congrFun hRest idx])
          (by simp [stNextLG, stNext, hBr]) hBrLt
          (by
            dsimp only [stNextLG, stNext, fiChanges, oldFiE, newFiE, sc', updRes]
            simp only [↓reduceIte]
            rw [hDecGe idx (le_refl _), hScGe idx (le_refl _), hBr])
          (fun h0 => by
            subst h0
            simp only [stNextLG, stNext, ↓reduceIte]
            rw [(hEncAcc0 rfl).2, (hEncAcc0 rfl).1])
          (fun _ => by
            simp only [stNextLG, stNext, show idx + 1 ≠ idx by omega, ↓reduceIte,
              nextEnc, nextU, U_S, updRes]
            rw [hEncGt (idx + 1) (Nat.lt_succ_self _), hGGe (idx + 1) (Nat.le_succ _),
              hInvOrig.hGSucc idx hidxLt, hScGe idx (le_refl _), hBr])
      let HPreNext : ∀ k (hk : k < idx + 1), LevelHistory T TP P N₀ stNextLG k := fun k hk =>
        if hklt : k < idx then
          levelHistory_congr_state (by omega) (HPre k hklt)
            (fun j hj => by simp [stNextLG, stNext, show j ≠ idx by omega])
            (by simp [stNextLG, stNext, show k ≠ idx by omega])
            (by simp [stNextLG, stNext])
            (fun j hj => by
              have hjd : j < P.d := by omega
              simp [TreeChain.activeLSF, ChainState.toTreeChain, hjd, stNextLG, stNext,
                show j ≠ idx by omega])
            rfl rfl
            (by simp [stNextLG, stNext, show k ≠ idx by omega])
            (by simp [stNextLG, stNext, show k ≠ idx by omega])
            rfl
            (by simp [stNextLG, stNext, show k ≠ idx by omega])
            (fun h0 => by
              subst h0
              simp [stNextLG, stNext, show (0 : ℕ) ≠ idx by omega])
            (fun _ => by
              by_cases hkeq : k + 1 = idx
              · simp [stNextLG, stNext, hkeq, hEncAccPos (by omega)]
              · simp [stNextLG, stNext, show k + 1 ≠ idx by omega, show k ≠ idx by omega])
        else
          by cases (show k = idx by omega); exact hHidx
      have hHPreNext_k : ∀ k (hk : k < idx),
          (HPreNext k (Nat.lt_succ_of_lt hk)).D = (HPre k hk).D ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).len = (HPre k hk).len ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).s₀ = (HPre k hk).s₀ ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).restarts = (HPre k hk).restarts := fun k hk => by
        simp [HPreNext, hk, levelHistory_congr_state]
      have hHPreNext_idx : ∀ k' (hk' : k' < idx + 1) (heq : k' = idx),
          (HPreNext k' hk').D = hHidx.D ∧ (HPreNext k' hk').len = hHidx.len ∧
          (HPreNext k' hk').s₀ = hHidx.s₀ ∧ (HPreNext k' hk').restarts = hHidx.restarts := by
        intro k' hk' heq; subst heq; simp [HPreNext]
      have hSpecIdx := hT P.k hHidx.len (levelM TP P idx) N₀ hHidx.D hHidx.restarts
        P.hk hHidx.hG0 hHidx.hD hHidx.hLen hHidx.hℓPos hHidx.hInitMBound hHidx.hInitNBound
        hHidx.hRestartsLt (by rw [hHidx.hUpd]; exact hHidx.hThresh)
      have hRunD'Len : T.runAfterUpdate P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len = updRes := by
        dsimp only [hHidx, extendLevelHistory]
        rw [T.runAfterUpdate_succ P.k (levelM TP P idx) N₀ _ _ (HOrig idx hidxLt).len,
          runAfterRestarts_extendDyn_prefix T P.k (levelM TP P idx) N₀ (HOrig idx hidxLt).D (HOrig idx hidxLt).restarts
            (HOrig idx hidxLt).len curU curG _ _ (HOrig idx hidxLt).len (le_refl _),
          ← (HOrig idx hidxLt).hRun, ← hScGe idx (le_refl _)]
        simp [extendDyn, stNextLG, hCL_eq, hCG_eq, updRes]
      have hRunPostD'Len : T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len = sc' := by
        have h := hHidx.hRun.symm
        simpa [stNextLG, stNext] using h
      have hSpIdx := hSpecIdx.1 hHidx.len (le_refl _) (stOrig.bran idx) hBrLt
      have hSpIdx2 := hSpecIdx.2.1 hHidx.len (Nat.succ_pos _) (le_refl _) (stOrig.bran idx) hBrLt
      have hRunPrevIdx :
          T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts (HOrig idx hidxLt).len = st.scState idx := by
        dsimp only [hHidx, extendLevelHistory]
        rw [runAfterRestarts_extendDyn_prefix T P.k (levelM TP P idx) N₀ _ _ _ _ _ _ _ (HOrig idx hidxLt).len (le_refl _),
          ← (HOrig idx hidxLt).hRun, hScGe idx (le_refl _)]
      have hSubLen : hHidx.len - 1 = (HOrig idx hidxLt).len := Nat.add_sub_cancel _ 1
      have hNextU_batch : (stOrig.G (idx + 1)).BatchIsValid nextU := by
        rw [hInvOrig.hGSucc idx hidxLt, ← hScGe idx (le_refl _), ← hRunPrevIdx, ← hBr]
        simpa [nextU, U_S, hRunD'Len, hSubLen, hBr] using hSpIdx2.2.2.2.1
      have hNextG_eq : nextG = (stOrig.G (idx + 1)).applyBatch nextU := by
        rw [hInvOrig.hGSucc idx hidxLt, ← hScGe idx (le_refl _), ← hRunPrevIdx, ← hBr]
        simpa [nextG, nextU, sc', U_S, hRunD'Len, hSubLen, hBr] using hSpIdx2.2.2.2.2
      have hNextG_valid : nextG.IsValid := by
        have hSp := hSpIdx.2.1
        have hCore := coreGraph_isValid (by simpa [hHidx.hEndG, hG_eq] using hCurGValid) hSpIdx.1.2.1
        intro e he
        have he' : e ∈ (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len) (stOrig.bran idx)).E := by
          simpa [nextG, sc', hBr, hRunPostD'Len] using he
        have hE := hSp.1.2.2 e he'
        have hc := hCore e (hSp.1.2.1 he')
        have hEnd : nextG.tail e =
              (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len) (stOrig.bran idx)).tail e ∧
            nextG.head e =
              (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len) (stOrig.bran idx)).head e := by
          simp [nextG, sc', hBr, hRunPostD'Len]
        rw [hEnd.1, hEnd.2, hE.1, hE.2]
        simpa [nextG, sc', hBr, hRunPostD'Len] using And.intro (hSp.2.1.1 hc.1) (hSp.2.1.1 hc.2)
      have hNextG_V : nextG.V ⊆ (stNext.G 0).V := by
        have hV1 : nextG.V ⊆ curG.V := by
          refine Finset.Subset.trans
            (by simpa [nextG, sc', hBr, hRunPostD'Len, coreGraph] using hSpIdx.2.1.1.1)
            (Finset.Subset.trans hSpIdx.1.2.1.2.2.1 ?_)
          simp [hHidx.hEndG, hG_eq]
        by_cases h0 : idx = 0
        · subst h0; simpa [stNext] using hV1
        · have h0' : 0 ≠ idx := by omega
          have hV2 : curG.V ⊆ (st.G 0).V := hCurGVPos (Nat.pos_of_ne_zero h0)
          simpa [stNext, h0'] using Finset.Subset.trans hV1 hV2
      have hNextG_m : (nextG.m : ℝ) ≤ (levelM TP P (idx + 1) : ℝ) := by
        have hmM0 : levelM TP P idx ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk idx
        have hγle : TP.γ_ℓ (levelM TP P idx) ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.2.1 _ _ hmM0
        have hcard : (nextG.E.card : ℝ) ≤ (levelM TP P idx : ℝ) * TP.γ_ℓ (levelM TP P idx) / P.k := by
          simpa [nextG, nextU, sc', hRunPostD'Len, hHidx.hEndG, hG_eq, hBr] using
            hSpIdx.2.1.2.2.2.2.2
        have hcard' : (nextG.E.card : ℝ) ≤ (levelM TP P idx : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / P.k :=
          le_trans hcard (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hγle (Nat.cast_nonneg _)) (Nat.cast_pos.mpr P.hk).le)
        exact_mod_cast levelM_step_nat hTP hγk hcard'
      let Cnext' : TreeChain :=
        { stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j }
      have hCnext_idx : Cnext'.chainLen ℓ' idx = ℓi := by
        rw [hCL_eq]
        exact chainLen_congr_lt (C₁ := Cnext') (C₂ := stNextLG.toTreeChain) ℓ' idx
          (fun j hj => by simp [Cnext', ChainState.toTreeChain, stNextLG, show j ≠ idx + 1 by omega])
          (fun j hj => by
            have hjd := lt_trans hj hidxLt
            simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, stNextLG, hjd])
      have hCurLenNextPos : ∀ e ∈ nextG.E, 0 < Cnext'.chainLen ℓ' (idx + 1) e := by
        intro e he
        have heC : e ∈ curG.E := by
          simpa [hHidx.hEndG, hG_eq] using
            (Finset.mem_sdiff.mp (hSpIdx.2.1.1.2.1 (by simpa [nextG, sc', hBr, hRunPostD'Len] using he))).1
        have h1w : 1 ≤ (Cnext'.activeLSF idx).wstr e := by
          have hAct : Cnext'.activeLSF idx =
              T.lsfs (T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len) (stOrig.bran idx) := by
            simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext, hBr, hRunPostD'Len, sc']
          rw [hAct]
          have hHold := hSpIdx.1
          have hLnonneg : ∀ f ∈ (hHidx.D.G hHidx.len).E, 0 ≤ hHidx.D.ℓ hHidx.len f := fun f hf => by
            have hf' : f ∈ curG.E := by simpa [hHidx.hEndG, hG_eq] using hf
            rw [hHidx.hEndℓ f (by simpa [hG_eq] using hf'), ← hCL_eq]; exact (hCurLenPos f hf').le
          exact le_trans (one_le_stretch hHold.2.1.2.2.2.2 hLnonneg (by simpa [hHidx.hEndG, hG_eq] using heC))
            (hHold.2.2.2 e (by simpa [hHidx.hEndG, hG_eq] using heC)).1
        change 0 < coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e
        unfold coreLen
        exact mul_pos (lt_of_lt_of_le zero_lt_one h1w) (by rw [hCnext_idx]; exact hCurLenPos e heC)
      have hCurLenNextStable : ∀ e ∈ nextG.E, e ∈ (stOrig.G (idx + 1)).E →
          (∀ u ∈ nextU, ¬ u.Inserts e) →
          Cnext'.chainLen ℓ' (idx + 1) e = stOrig.toTreeChain.chainLen stOrig.ℓ (idx + 1) e := by
        intro e he heOrig hno
        have heC : e ∈ curG.E := by
          simpa [hHidx.hEndG, hG_eq] using
            (Finset.mem_sdiff.mp (hSpIdx.2.1.1.2.1 (by simpa [nextG, sc', hBr, hRunPostD'Len] using he))).1
        have heOrigIdx : e ∈ (stOrig.G idx).E := by
          have hSpOrig := (hOrigLev idx hidxLt.le).2.2.2.2 hidxLt (stOrig.bran idx) hBrLt
          have heS : e ∈ (T.S (stOrig.scState idx) (stOrig.bran idx)).E := by
            rw [← hInvOrig.hGSucc idx hidxLt]; exact heOrig
          exact (Finset.mem_sdiff.mp (hSpOrig.2.1.2.1 heS)).1
        have hNoInsCur : ∀ u ∈ curU, ¬ u.Inserts e := by
          have hNR := hNoReinsTool P.k hHidx.len (levelM TP P idx) N₀ hHidx.D hHidx.restarts
            P.hk hHidx.hG0 hHidx.hD hHidx.hLen hHidx.hℓPos hHidx.hInitMBound hHidx.hInitNBound
            hHidx.hRestartsLt (by rw [hHidx.hUpd]; exact hHidx.hThresh)
            hHidx.len (Nat.succ_pos _) (le_refl _) (stOrig.bran idx) hBrLt
            e (by
              rw [hSubLen, hRunPrevIdx, hScGe idx (le_refl _), ← hInvOrig.hGSucc idx hidxLt]
              exact heOrig)
            (by
              rw [hRunPostD'Len]
              simpa [nextG, hBr] using he)
            (fun u hu => by
              rw [hRunD'Len] at hu
              exact hno u (by simpa [nextU, U_S, hBr] using hu))
          intro u hu
          exact hNR u (by simpa [hHidx, extendLevelHistory, extendDyn] using hu)
        have hWstrEq : (Cnext'.activeLSF idx).wstr e = (stOrig.toTreeChain.activeLSF idx).wstr e := by
          have h1 : Cnext'.activeLSF idx =
              T.lsfs (T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts hHidx.len) (stOrig.bran idx) := by
            simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext, hBr, hRunPostD'Len, sc']
          have h2 : stOrig.toTreeChain.activeLSF idx =
              T.lsfs (T.runAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.restarts (HOrig idx hidxLt).len)
                (stOrig.bran idx) := by
            simp [TreeChain.activeLSF, ChainState.toTreeChain, hidxLt, hRunPrevIdx, hScGe idx (le_refl _)]
          rw [h1, h2]
          simpa [hSubLen] using hSpIdx2.2.1 e (by simpa [hHidx.hEndG, hG_eq] using heC)
            (by simpa [hHidx, extendLevelHistory, extendDyn, hSubLen, (HOrig idx hidxLt).hEndG] using heOrigIdx)
            (fun u hu => hNoInsCur u (by simpa [hHidx, extendLevelHistory, extendDyn] using hu))
        have hCLpre : Cnext'.chainLen ℓ' idx e = stOrig.toTreeChain.chainLen stOrig.ℓ idx e := by
          rw [hCnext_idx]; exact hCurLenStable e heC heOrigIdx hNoInsCur
        change coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e =
          coreLen (stOrig.toTreeChain.activeLSF idx) (stOrig.toTreeChain.chainLen stOrig.ℓ idx) e
        unfold coreLen
        rw [hWstrEq, hCLpre]
      refine ih (idx + 1) stNext nextG nextU 0 (by omega)
        (fun j hj => by simp [stNext, show j ≠ idx by omega, hGGe j (Nat.le_of_succ_le hj)])
        (fun j hj => by simp [stNext, show j ≠ idx by omega, hScGe j (Nat.le_of_succ_le hj)])
        (fun j hj => by simp [stNext, show j ≠ idx by omega, hUpdGe j (Nat.le_of_succ_le hj)])
        (fun j hj => by simp [stNext, show j ≠ idx by omega, hDecGe j (Nat.le_of_succ_le hj)])
        (fun j hj => by
          simp [stNext, show j ≠ idx by omega, show j ≠ idx + 1 by omega, hEncGt j (by omega)])
        (by simp [stNext, hBr])
        (fun j hj => by simp [stNext, show j ≠ idx by omega, hCFwd j (Nat.le_of_succ_le hj)])
        (by simp [stNext, hReb])
        (by simp [stNext, hRest])
        hLvlM hN0
        (fun h => by omega) (fun _ => rfl)
        (fun j hj => by
          by_cases hjeq : j = idx
          · rw [hjeq]
            by_cases h0 : idx = 0
            · simp [stNext, h0]
            · have h0' : 0 ≠ idx := by omega
              simpa [stNext, h0'] using hCurGVPos (Nat.pos_of_ne_zero h0)
          · by_cases h0 : idx = 0
            · omega
            · have h0' : 0 ≠ idx := by omega
              simpa [stNext, hjeq, h0'] using hPreV j (by omega))
        (fun j hj => by
          by_cases hjeq : j = idx
          · rw [hjeq]; simpa [stNext] using hCurGM
          · simpa [stNext, hjeq] using hPreM j (by omega))
        (fun j hj => by
          by_cases hjeq : j + 1 = idx
          · have h0lt : 0 < idx := by omega
            have hIdxEq : idx - 1 = j := by omega
            have hFP2 : curG = T.S (st.scState j) (stOrig.bran j) := by
              have h := (hCurFromPrev h0lt).2
              rw [hIdxEq] at h
              exact h
            simp [stNext, hjeq, show j ≠ idx by omega, hFP2, hBr]
          · simp [stNext, hjeq, show j ≠ idx by omega, hPreGSucc j (by omega)])
        (fun h0 => by omega)
        (fun _ => by
          by_cases h0 : idx = 0
          · have h0' : 0 = idx := h0.symm
            refine ⟨by simpa [stNext, h0'] using hCurGValid, by simpa [stNext, h0'] using (hCurGV0 h0).1,
              by simpa [stNext, h0'] using (hCurGV0 h0).2.1,
              by simpa [stNext, h0'] using (hCurGV0 h0).2.2.1,
              fun e he => (hCurGV0 h0).2.2.2 e (by simpa [stNext, h0'] using he)⟩
          · have h0' : 0 ≠ idx := by omega
            simpa [stNext, h0'] using hG0Inv (Nat.pos_of_ne_zero h0))
        hNextG_eq hNextU_batch hNextG_valid hNextG_m
        (fun h0 => by omega) (fun _ => hNextG_V)
        hCurLenNextPos hCurLenNextStable
        HPreNext
        (fun k hk => by
          by_cases hklt : k < idx
          · obtain ⟨hD_k, hlen_k, hS_k, hR_k⟩ := hHPreNext_k k hklt
            have hPE := hPreExt k hklt
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hlen_k]; exact hPE.1
            · intro s hs; rw [hD_k]; exact hPE.2.1 s hs
            · intro h0; rw [hD_k]; exact hPE.2.2.1 h0
            · rw [hD_k, hlen_k, hPE.2.2.2.1]
              exact chainLen_congr_lt (C₁ := ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain)
                (C₂ := stNextLG.toTreeChain) ℓ' k
                (fun j hj => by simp [stNextLG, stNext, ChainState.toTreeChain, show j ≠ idx by omega])
                (fun j hj => by
                  have hjd : j < P.d := lt_trans hj (lt_trans hklt hidxLt)
                  simp [TreeChain.activeLSF, stNextLG, stNext, ChainState.toTreeChain, hjd,
                    show j ≠ idx by omega])
            · rw [hS_k]; exact hPE.2.2.2.2.1
            · intro s hs; rw [hR_k]; exact hPE.2.2.2.2.2 s hs
          · have hkeq : k = idx := by omega
            subst k
            obtain ⟨hD_i, hlen_i, hS_i, hR_i⟩ := hHPreNext_idx idx (Nat.lt_succ_self idx) rfl
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hlen_i]; rfl
            · intro s hs; rw [hD_i]; simp [hHidx, extendLevelHistory, extendDyn, hs]
            · intro h0; rw [hD_i]; simp [hHidx, extendLevelHistory, extendDyn, hCurU0 h0]
            · rw [hD_i, hlen_i]; simp [hHidx, extendLevelHistory, extendDyn, stNextLG]
            · rw [hS_i]; rfl
            · intro s hs; rw [hR_i]; simp [hHidx, extendLevelHistory, hs])
        (fun _ => by
          obtain ⟨hD_i, hlen_i, _, hR_i⟩ :=
            hHPreNext_idx (idx + 1 - 1) (by omega) (Nat.add_sub_cancel idx 1)
          refine ⟨?_, ?_⟩
          · rw [hD_i, hlen_i, hR_i, Nat.add_sub_cancel idx 1]; simp [nextU, U_S, hRunD'Len, hBr]
          · rw [Nat.add_sub_cancel idx 1]; simp [stNext, hBr, nextG, sc', updRes])
        (fun k hk1 => by
          by_cases hk1lt : k + 1 < idx
          · have hklt : k < idx := Nat.lt_of_succ_lt hk1lt
            obtain ⟨hDk, hlenk, hSk, hRk⟩ := hHPreNext_k k hklt
            obtain ⟨hDk1, hlenk1, hSk1, hRk1⟩ := hHPreNext_k (k + 1) hk1lt
            have hPC := hPreCore k hk1lt
            dsimp only
            rw [hlenk, hlenk1, hDk, hDk1, hSk, hRk]; exact hPC
          · have hk1eq : k + 1 = idx := by omega
            have hklt : k < idx := by omega
            have h0lt : 0 < idx := by omega
            have hIdxEq : idx - 1 = k := by omega
            have hFP1 : curU =
                (T.runAfterUpdate P.k (levelM TP P k) N₀ (HPre k hklt).D (HPre k hklt).restarts (HPre k hklt).len).2
                  (stOrig.bran k) :=
              (fun k0 (hk0 : k0 < idx) (heq : k0 = k)
                  (hu : curU =
                    (T.runAfterUpdate P.k (levelM TP P k0) N₀ (HPre k0 hk0).D (HPre k0 hk0).restarts (HPre k0 hk0).len).2
                      (stOrig.bran k0)) => by
                subst heq; exact hu) (idx - 1) (Nat.sub_lt h0lt zero_lt_one) hIdxEq (hCurFromPrev h0lt).1
            have hFP2 : curG = T.S (st.scState k) (stOrig.bran k) := by
              have h := (hCurFromPrev h0lt).2
              rw [hIdxEq] at h
              exact h
            have hFP := And.intro hFP1 hFP2
            obtain ⟨hDk, hlenk, hSk, hRk⟩ := hHPreNext_k k hklt
            obtain ⟨hDk1, hlenk1, _, _⟩ := hHPreNext_idx (k + 1) hk1 hk1eq
            have hk_lt_d : k < P.d := by omega
            have hk1_lt_d : k + 1 < P.d := by omega
            have hOC := hOrigCore k hk1_lt_d
            have hPE := hPreExt k hklt
            dsimp only
            rw [hlenk, hlenk1, hDk, hDk1, hSk, hRk]
            change hHidx.len ≤ (HPre k hklt).len ∧
              let off := (HPre k hklt).len - hHidx.len
              (HPre k hklt).s₀ ≤ off ∧
              (∀ δ ≤ hHidx.len, hHidx.D.G δ =
                (T.coreInstanceFrom P.k (levelM TP P k) N₀ (HPre k hklt).D (HPre k hklt).restarts
                  (HPre k hklt).s₀ (stOrig.bran k)).G ((off - (HPre k hklt).s₀) + δ)) ∧
              (∀ δ, 1 ≤ δ → δ ≤ hHidx.len → hHidx.D.U δ =
                (T.coreInstanceFrom P.k (levelM TP P k) N₀ (HPre k hklt).D (HPre k hklt).restarts
                  (HPre k hklt).s₀ (stOrig.bran k)).U ((off - (HPre k hklt).s₀) + δ)) ∧
              (∀ δ ≤ hHidx.len, ∀ e ∈ (hHidx.D.G δ).E, hHidx.D.ℓ δ e =
                (T.coreInstanceFrom P.k (levelM TP P k) N₀ (HPre k hklt).D (HPre k hklt).restarts
                  (HPre k hklt).s₀ (stOrig.bran k)).ℓ ((off - (HPre k hklt).s₀) + δ) e)
            have hlen_hi : hHidx.len = (HOrig idx hidxLt).len + 1 := rfl
            have hlen_hk : (HPre k hklt).len = (HOrig k hk_lt_d).len + 1 := hPE.1
            have hlen_ok1 : (HOrig (k + 1) hk1_lt_d).len = (HOrig idx hidxLt).len :=
              (show ∀ a (ha : a < P.d) b (hb : b < P.d), a = b → (HOrig a ha).len = (HOrig b hb).len from
                fun _ _ _ _ hab => by cases hab; rfl) (k + 1) hk1_lt_d idx hidxLt hk1eq
            have hlen_le : hHidx.len ≤ (HPre k hklt).len := by
              rw [hlen_hi, hlen_hk, ← hlen_ok1]; exact Nat.add_le_add_right hOC.1 1
            have hoff : (HPre k hklt).len - hHidx.len =
                (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len := by
              rw [hlen_hi, hlen_hk, ← hlen_ok1]; omega
            have hs0_eq : (HPre k hklt).s₀ = (HOrig k hk_lt_d).s₀ := hPE.2.2.2.2.1
            have hs0_le : (HPre k hklt).s₀ ≤ (HPre k hklt).len - hHidx.len := by
              rw [hs0_eq, hoff]; exact hOC.2.1
            have hs0_le_orig : (HOrig k hk_lt_d).s₀ ≤
                (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len := hOC.2.1
            refine ⟨hlen_le, hs0_le, fun δ hδ => ?_, fun δ h1 hδ => ?_, fun δ hδ e he => ?_⟩
            · rw [hoff, hs0_eq]
              by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
              · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
                    (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
                have hidx_sum : (HOrig k hk_lt_d).s₀ +
                      (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
                    (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by
                  have := hs0_le_orig; omega
                have hrun_eq := T.runAfterRestarts_congr_le P.k (levelM TP P k) N₀ _
                  (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
                  (hPE.2.1 0 (Nat.zero_le _)).2.2.2
                  (fun s _ hs =>
                    ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
                      (hPE.2.1 s (le_trans hs hsum_le)).2.2.1,
                      (hPE.2.1 s (le_trans hs hsum_le)).2.2.2⟩)
                  (fun r hr => hPE.2.2.2.2.2 r (le_trans hr hsum_le))
                have hG_o := hOC.2.2.1 δ (by rw [hlen_ok1]; exact hδ_old)
                simp only [SparseCoreRestartTool.coreInstanceFrom, hidx_sum] at hG_o ⊢
                rw [hrun_eq, ← hG_o]
                have hD_old : hHidx.D.G δ = (HOrig (k + 1) hk1_lt_d).D.G δ := by
                  have : hHidx.D.G δ = (HOrig idx hidxLt).D.G δ := by
                    simp [hHidx, extendLevelHistory, extendDyn, hδ_old]
                  rw [this]; subst hk1eq; rfl
                exact hD_old
              · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
                have hsum_eq : (HOrig k hk_lt_d).s₀ +
                      (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
                    (HPre k hklt).len := by have := hs0_le_orig; rw [hlen_ok1, hδeq, hlen_hk]; omega
                simp only [SparseCoreRestartTool.coreInstanceFrom, hsum_eq, ← (HPre k hklt).hRun]
                have hD_new : hHidx.D.G δ = curG := by
                  simp [hHidx, extendLevelHistory, extendDyn, hδeq]
                rw [hD_new, hFP.2]
            · rw [hoff, hs0_eq]
              by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
              · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
                    (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
                have hidx_sum : (HOrig k hk_lt_d).s₀ +
                      (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
                    (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by
                  have := hs0_le_orig; omega
                have hrun_eq := T.runAfterUpdate_congr_lt P.k (levelM TP P k) N₀ _
                  (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
                  (hPE.2.1 0 (Nat.zero_le _)).2.2.2
                  (fun s _ hs =>
                    ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
                      (hPE.2.1 s (le_trans hs hsum_le)).2.2.1,
                      (hPE.2.1 s (le_trans hs hsum_le)).2.2.2⟩)
                  (fun r hr => hPE.2.2.2.2.2 r (le_trans (Nat.le_of_lt hr) hsum_le))
                have hU_o := hOC.2.2.2.1 δ h1 (by rw [hlen_ok1]; exact hδ_old)
                simp only [SparseCoreRestartTool.coreInstanceFrom, hidx_sum] at hU_o ⊢
                rw [hrun_eq, ← hU_o]
                have hD_old : hHidx.D.U δ = (HOrig (k + 1) hk1_lt_d).D.U δ := by
                  have : hHidx.D.U δ = (HOrig idx hidxLt).D.U δ := by
                    simp [hHidx, extendLevelHistory, extendDyn, hδ_old]
                  rw [this]; subst hk1eq; rfl
                exact hD_old
              · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
                have hsum_eq : (HOrig k hk_lt_d).s₀ +
                      (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
                    (HPre k hklt).len := by have := hs0_le_orig; rw [hlen_ok1, hδeq, hlen_hk]; omega
                simp only [SparseCoreRestartTool.coreInstanceFrom, hsum_eq]
                have hD_new : hHidx.D.U δ = curU := by
                  simp [hHidx, extendLevelHistory, extendDyn, hδeq]
                rw [hD_new, hFP.1]
            · rw [hoff, hs0_eq]
              by_cases hδ_old : δ ≤ (HOrig idx hidxLt).len
              · have hsum_le : (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ ≤
                    (HOrig k hk_lt_d).len := by rw [hlen_ok1]; omega
                have hidx_sum : (HOrig k hk_lt_d).s₀ +
                      (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
                    (HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len + δ := by
                  have := hs0_le_orig; omega
                have hrun_eq := T.runAfterRestarts_congr_le P.k (levelM TP P k) N₀ _
                  (hPE.2.1 0 (Nat.zero_le _)).1 (hPE.2.1 0 (Nat.zero_le _)).2.2.1
                  (hPE.2.1 0 (Nat.zero_le _)).2.2.2
                  (fun s _ hs =>
                    ⟨(hPE.2.1 s (le_trans hs hsum_le)).2.1,
                      (hPE.2.1 s (le_trans hs hsum_le)).2.2.1,
                      (hPE.2.1 s (le_trans hs hsum_le)).2.2.2⟩)
                  (fun r hr => hPE.2.2.2.2.2 r (le_trans hr hsum_le))
                have hD_oldG : hHidx.D.G δ = (HOrig (k + 1) hk1_lt_d).D.G δ := by
                  have : hHidx.D.G δ = (HOrig idx hidxLt).D.G δ := by
                    simp [hHidx, extendLevelHistory, extendDyn, hδ_old]
                  rw [this]; subst hk1eq; rfl
                have hℓ_o := hOC.2.2.2.2 δ (by rw [hlen_ok1]; exact hδ_old) e (hD_oldG ▸ he)
                simp only [SparseCoreRestartTool.coreInstanceFrom, hidx_sum] at hℓ_o ⊢
                rw [hrun_eq, (hPE.2.1 _ hsum_le).2.2.1, ← hℓ_o]
                have hD_old : hHidx.D.ℓ δ e = (HOrig (k + 1) hk1_lt_d).D.ℓ δ e := by
                  have : hHidx.D.ℓ δ e = (HOrig idx hidxLt).D.ℓ δ e := by
                    simp [hHidx, extendLevelHistory, extendDyn, hδ_old]
                  rw [this]; subst hk1eq; rfl
                exact hD_old
              · have hδeq : δ = (HOrig idx hidxLt).len + 1 := by omega
                have hsum_eq : (HOrig k hk_lt_d).s₀ +
                      (((HOrig k hk_lt_d).len - (HOrig (k + 1) hk1_lt_d).len - (HOrig k hk_lt_d).s₀) + δ) =
                    (HPre k hklt).len := by have := hs0_le_orig; rw [hlen_ok1, hδeq, hlen_hk]; omega
                simp only [SparseCoreRestartTool.coreInstanceFrom, hsum_eq, ← (HPre k hklt).hRun, hPE.2.2.2.1]
                have hAct : stNextLG.toTreeChain.activeLSF k = T.lsfs (st.scState k) (stOrig.bran k) := by
                  simp [TreeChain.activeLSF, stNextLG, stNext, ChainState.toTreeChain, hk_lt_d, hBr,
                    show k ≠ idx by omega]
                have hCLk : stNextLG.toTreeChain.chainLen ℓ' k =
                    ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' k :=
                  chainLen_congr_lt (C₁ := stNextLG.toTreeChain)
                    (C₂ := ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain) ℓ' k
                    (fun j hj => by simp [stNextLG, stNext, ChainState.toTreeChain, show j ≠ idx by omega])
                    (fun j hj => by
                      have hjd := lt_trans hj hk_lt_d
                      simp [TreeChain.activeLSF, stNextLG, stNext, ChainState.toTreeChain, hjd,
                        show j ≠ idx by omega])
                have hCLk1 : hHidx.D.ℓ δ e =
                    coreLen (stNextLG.toTreeChain.activeLSF k) (stNextLG.toTreeChain.chainLen ℓ' k) e := by
                  have hDℓ : hHidx.D.ℓ δ e = stNextLG.toTreeChain.chainLen ℓ' idx e := by
                    simp [hHidx, extendLevelHistory, extendDyn, hδeq, stNextLG]
                  rw [hDℓ, ← hk1eq]
                  rfl
                rw [hCLk1, hAct, hCLk])

end MinCostFlow.Chain
