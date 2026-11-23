module

public import MinCostFlow.Chain.Ordered.UpdateTraceStep

/-!
# Per-level dynamic history extension through ordered `updateLoop` (`MinCostFlow/Chain/Ordered/UpdateTrace`)

Proves `updateLoop_hidden_trace`, tracking explicit ordered `LevelHistory` records and inter-level
`coreInstanceOrdFrom` + output-order (`rot`) coupling across `updateLoop` / `algorithm1_update`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

lemma updateLoop_hidden_trace (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hT : ChainToolSupply T TP P N₀ Λ)
    (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    (HOrig : ∀ k < P.d, LevelHistory T TP P N₀ stOrig k)
    (hOrigCore : ChainCoreRel T TP P stOrig HOrig)
    (ℓ' g' : ℕ → ℝ) (U₀ : List Update) (hEdge0 : ∀ u ∈ U₀, IsEdgeUpdate u) :
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
      LevelLenRange TP P N₀ Λ idx curG
        (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen
          ℓ' idx) →
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
          (HPre k hk).D.g s = (HOrig k (by omega)).D.g s ∧
          (HPre k hk).ord s = (HOrig k (by omega)).ord s) ∧
        (k = 0 → (HPre k hk).D.U ((HOrig k (by omega)).len + 1) = U₀) ∧
        ((HPre k hk).D.ℓ ((HPre k hk).len) =
          ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' k) ∧
        (HPre k hk).s₀ = (HOrig k (by omega)).s₀ ∧
        (∀ s ≤ (HOrig k (by omega)).len,
          (HPre k hk).restarts s = (HOrig k (by omega)).restarts s)) →
      (∀ h0 : 0 < idx,
        curU = (T.runOrdAfterUpdate P.k (levelM TP P (idx - 1)) N₀
          (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).D
          (HPre (idx - 1) (Nat.sub_lt h0 zero_lt_one)).ord
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
            Hk.D Hk.ord Hk.restarts (Hk.s₀ + ((off - Hk.s₀) + δ))) (stOrig.bran k))) →
      let stEnd := (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1
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
        (by
          simp only [ChainState.levelOrd, chainLevelOrd]
          by_cases h0 : k = 0
          · subst h0; simp [hF_G 0 P.hd]
          · simp [h0, hF_sc, hF_br])
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
      hCurGBatch hCurGValid hCurGM hCurGV0 hCurGVPos hCurLenR hCurLenStable
      HPre hPreExt hCurFromPrev hPreCore
    have hCurLenPos := hCurLenR.pos
    have hidxLt : idx < P.d := by omega
    have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInvOrig
    dsimp only [updateLoop]
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · rw [ite_eq_left_iff.mpr fun h => absurd hOver h]
      by_cases h0 : idx = 0
      · subst h0
        have hV0 := hCurGV0 rfl
        exact U3.updateLoop_hidden_trace_rebuild T L TP LP P hTP hLP hT hL hγM₀ hγk
          hInvOrig HOrig _ _ U₀ hidxLt st curG.compact curU curEncAcc
          hBr hReb hRest hLvlM hN0 (fun h => absurd h (lt_irrefl 0)) (compact_isValid hCurGValid)
          (by rw [compact_m]; exact hCurGM)
          (fun _ => ⟨by rw [compact_m]; exact hV0.1, by rw [compact_n]; exact hV0.2.1,
            by rw [compact_V]; exact hV0.2.2.1,
            fun j hj => hV0.2.2.2 _ (compactUnrank_mem_of_mem_compact hj)⟩)
          (fun h => absurd h (lt_irrefl 0))
          (fun j hj => by
            have := hCurLenR _ (compactUnrank_mem_of_mem_compact hj)
            simp only [TreeChain.chainLen] at this ⊢
            exact this)
          (fun _ hk => absurd hk (Nat.not_lt_zero _)) (fun _ hk => absurd hk (Nat.not_lt_zero _))
          (fun h => absurd h (lt_irrefl 0)) (fun _ hk => absurd hk (Nat.not_lt_zero _))
      · rw [rebuildStartFn_pos h0, rebuildStartFn_pos h0, rebuildStartGraph_pos h0]
        exact U3.updateLoop_hidden_trace_rebuild T L TP LP P hTP hLP hT hL hγM₀ hγk
          hInvOrig HOrig ℓ' g' U₀ hidxLt st curG curU curEncAcc
          hBr hReb hRest hLvlM hN0 hG0Inv hCurGValid hCurGM hCurGV0 hCurGVPos hCurLenR
          HPre hPreExt hCurFromPrev hPreCore
    · rw [ite_eq_right_iff.mpr fun h => absurd h hOver]
      have hLeThresh : ((st.updCount idx + curU.length : ℕ) : ℝ) ≤
          SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ :=
        (Nat.cast_le.mpr (Nat.le_of_not_lt hOver)).trans (intRebuildThreshold_le_updateThreshold hTP N₀ idx)
      set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
      set ℓi := Cpartial.chainLen ℓ' idx
      set gi := Cpartial.chainGrad g' idx
      set ordIdx := chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
      set updRes := T.updateOrd (st.scState idx) curU ℓi gi ordIdx
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
      have hOrd_eq : stNextLG.levelOrd idx = ordIdx := by
        dsimp only [ChainState.levelOrd, chainLevelOrd, ordIdx, stNextLG, stNext]
        by_cases h0 : idx = 0
        · simp [h0]
        · simp [h0, show idx - 1 ≠ idx by omega]
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
      have hStepOrd := U3.updateLoop_step_ord hInvOrig HOrig hEdge0 hidxLt hBr hCurU0 hCurGEq
        hCurGBatch HPre hPreExt hCurFromPrev
      have hCurLenStable' : ∀ e ∈ curG.E, e ∈ (stOrig.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
          ℓi e = stOrig.toTreeChain.chainLen stOrig.ℓ idx e :=
        fun e he1 he2 hno => hCurLenStable e he1 he2 hno
      let hHidx : LevelHistory T TP P N₀ stNextLG idx :=
        extendLevelHistory hTP hγk hidxLt (HOrig idx hidxLt) curU curG ℓi gi ordIdx hCurGEq
          hCurGBatch hCurGValid hG_eq hOrd_eq hStepOrd hCL_eq hCG_eq
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
            (by
              simp only [ChainState.levelOrd, chainLevelOrd]
              by_cases h0 : k = 0
              · subst h0; simp [stNextLG, stNext, show (0 : ℕ) ≠ idx by omega]
              · simp [h0, stNextLG, stNext, show k - 1 ≠ idx by omega])
        else
          by cases (show k = idx by omega); exact hHidx
      have hHPreNext_k : ∀ k (hk : k < idx),
          (HPreNext k (Nat.lt_succ_of_lt hk)).D = (HPre k hk).D ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).len = (HPre k hk).len ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).s₀ = (HPre k hk).s₀ ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).restarts = (HPre k hk).restarts ∧
          (HPreNext k (Nat.lt_succ_of_lt hk)).ord = (HPre k hk).ord := fun k hk => by
        simp [HPreNext, hk, levelHistory_congr_state]
      have hHPreNext_idx : ∀ k' (hk' : k' < idx + 1) (heq : k' = idx),
          (HPreNext k' hk').D = hHidx.D ∧ (HPreNext k' hk').len = hHidx.len ∧
          (HPreNext k' hk').s₀ = hHidx.s₀ ∧ (HPreNext k' hk').restarts = hHidx.restarts ∧
          (HPreNext k' hk').ord = hHidx.ord := by
        intro k' hk' heq; subst heq; simp [HPreNext]
      have hSpecIdx := hHidx.hOK.noHidden P.k hHidx.len (levelM TP P idx) N₀ hHidx.D hHidx.ord
        hHidx.restarts
        P.hk hHidx.hG0 hHidx.hD hHidx.hLen hHidx.hℓPos hHidx.hOrd hHidx.hInitMBound hHidx.hInitNBound
        hHidx.hRestartsLt (by rw [hHidx.hUpd]; exact hHidx.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hRunD'Len : T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
          hHidx.restarts hHidx.len = updRes := by
        dsimp only [hHidx, extendLevelHistory]
        rw [T.runOrdAfterUpdate_succ P.k (levelM TP P idx) N₀ _ _ _ (HOrig idx hidxLt).len,
          runOrdAfterRestarts_extendDyn_prefix T P.k (levelM TP P idx) N₀ (HOrig idx hidxLt).D
            (HOrig idx hidxLt).ord (HOrig idx hidxLt).restarts (HOrig idx hidxLt).len curU curG
            _ _ ordIdx (HOrig idx hidxLt).len (le_refl _),
          ← (HOrig idx hidxLt).hRun, ← hScGe idx (le_refl _)]
        simp [extendDyn, U3.extendOrd, stNextLG, hCL_eq, hCG_eq, updRes]
      have hRunPostD'Len : T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
          hHidx.restarts hHidx.len = sc' := by
        have h := hHidx.hRun.symm
        simpa [stNextLG, stNext] using h
      have hSpIdx := hSpecIdx.1 hHidx.len (le_refl _) (stOrig.bran idx) hBrLt
      have hSpIdx2 := hSpecIdx.2.1 hHidx.len (Nat.succ_pos _) (le_refl _) (stOrig.bran idx) hBrLt
      have hRunPrevIdx :
          T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord hHidx.restarts
            (HOrig idx hidxLt).len = st.scState idx := by
        dsimp only [hHidx, extendLevelHistory]
        rw [runOrdAfterRestarts_extendDyn_prefix T P.k (levelM TP P idx) N₀ _ _ _ _ _ _ _ _ _
            (HOrig idx hidxLt).len (le_refl _),
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
        have he' : e ∈ (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
            hHidx.restarts hHidx.len) (stOrig.bran idx)).E := by
          simpa [nextG, sc', hBr, hRunPostD'Len] using he
        have hE := hSp.1.2.2 e he'
        have hc := hCore e (hSp.1.2.1 he')
        have hEnd : nextG.tail e =
              (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
                hHidx.restarts hHidx.len) (stOrig.bran idx)).tail e ∧
            nextG.head e =
              (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
                hHidx.restarts hHidx.len) (stOrig.bran idx)).head e := by
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
      have hCurGn : curG.n ≤ N₀ := by
        by_cases h0 : idx = 0
        · subst h0; exact (hCurGV0 rfl).2.1
        · have hpos := Nat.pos_of_ne_zero h0
          exact le_trans (Finset.card_le_card (hCurGVPos hpos)) (hG0Inv hpos).2.2.1
      have hCurLenNextPos : LevelLenRange TP P N₀ Λ (idx + 1) nextG (Cnext'.chainLen ℓ' (idx + 1)) := by
        intro e he
        have heC : e ∈ curG.E := by
          simpa [hHidx.hEndG, hG_eq] using
            (Finset.mem_sdiff.mp (hSpIdx.2.1.1.2.1 (by simpa [nextG, sc', hBr, hRunPostD'Len] using he))).1
        have h1w : 1 ≤ (Cnext'.activeLSF idx).wstr e := by
          have hAct : Cnext'.activeLSF idx =
              T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
                hHidx.restarts hHidx.len) (stOrig.bran idx) := by
            simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext, hBr, hRunPostD'Len, sc']
          rw [hAct]
          have hHold := hSpIdx.1
          have hLnonneg : ∀ f ∈ (hHidx.D.G hHidx.len).E, 0 ≤ hHidx.D.ℓ hHidx.len f := fun f hf => by
            have hf' : f ∈ curG.E := by simpa [hHidx.hEndG, hG_eq] using hf
            rw [hHidx.hEndℓ f (by simpa [hG_eq] using hf'), ← hCL_eq]; exact (hCurLenPos f hf').le
          exact le_trans (one_le_stretch hHold.2.1.2.2.2.2 hLnonneg (by simpa [hHidx.hEndG, hG_eq] using heC))
            (hHold.2.2.2 e (by simpa [hHidx.hEndG, hG_eq] using heC)).1
        have hwσ : (Cnext'.activeLSF idx).wstr e ≤ max 2 (TP.σ P.k N₀) := by
          have hAct : Cnext'.activeLSF idx =
              T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
                hHidx.restarts hHidx.len) (stOrig.bran idx) := by
            simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext, hBr, hRunPostD'Len, sc']
          have hnD : (hHidx.D.G hHidx.len).n ≤ N₀ := by
            have hG : hHidx.D.G hHidx.len = curG := by simpa [hG_eq] using hHidx.hEndG
            rw [hG]; exact hCurGn
          rw [hAct]
          exact le_trans (hSpIdx.1.2.2.2 e (by simpa [hHidx.hEndG, hG_eq] using heC)).2
            (le_trans (hTP.2.1 _ _ _ _ le_rfl hnD) (le_max_right _ _))
        change Real.exp (-Λ) ≤ coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e ∧
          coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e ≤
            Real.exp Λ * max 2 (TP.σ P.k N₀) ^ (idx + 1)
        unfold coreLen
        rw [hCnext_idx]
        exact hCurLenR.stretch_step heC h1w hwσ
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
          have hNR := hNoReinsTool P.k hHidx.len (levelM TP P idx) N₀ hHidx.D hHidx.ord
            hHidx.restarts P.hk hHidx.hG0 hHidx.hD hHidx.hLen hHidx.hℓPos hHidx.hOrd
            hHidx.hInitMBound hHidx.hInitNBound hHidx.hRestartsLt (by rw [hHidx.hUpd]; exact hHidx.hThresh)
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
              T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
                hHidx.restarts hHidx.len) (stOrig.bran idx) := by
            simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext, hBr, hRunPostD'Len, sc']
          have h2 : stOrig.toTreeChain.activeLSF idx =
              T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ hHidx.D hHidx.ord
                hHidx.restarts (HOrig idx hidxLt).len) (stOrig.bran idx) := by
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
          · obtain ⟨hD_k, hlen_k, hS_k, hR_k, hO_k⟩ := hHPreNext_k k hklt
            have hPE := hPreExt k hklt
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hlen_k]; exact hPE.1
            · intro s hs; rw [hD_k, hO_k]; exact hPE.2.1 s hs
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
            obtain ⟨hD_i, hlen_i, hS_i, hR_i, hO_i⟩ := hHPreNext_idx idx (Nat.lt_succ_self idx) rfl
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hlen_i]; rfl
            · intro s hs; rw [hD_i, hO_i]; simp [hHidx, extendLevelHistory, extendDyn, U3.extendOrd, hs]
            · intro h0; rw [hD_i]; simp [hHidx, extendLevelHistory, extendDyn, hCurU0 h0]
            · rw [hD_i, hlen_i]; simp [hHidx, extendLevelHistory, extendDyn, stNextLG]
            · rw [hS_i]; rfl
            · intro s hs; rw [hR_i]; simp [hHidx, extendLevelHistory, hs])
        (fun _ => by
          obtain ⟨hD_i, hlen_i, _, hR_i, hO_i⟩ :=
            hHPreNext_idx (idx + 1 - 1) (by omega) (Nat.add_sub_cancel idx 1)
          refine ⟨?_, ?_⟩
          · rw [hD_i, hlen_i, hR_i, hO_i, Nat.add_sub_cancel idx 1]; simp [nextU, U_S, hRunD'Len, hBr]
          · rw [Nat.add_sub_cancel idx 1]; simp [stNext, hBr, nextG, sc', updRes])
        (fun k hk1 => by
          by_cases hk1lt : k + 1 < idx
          · have hklt : k < idx := Nat.lt_of_succ_lt hk1lt
            obtain ⟨hDk, hlenk, hSk, hRk, hOk⟩ := hHPreNext_k k hklt
            obtain ⟨hDk1, hlenk1, hSk1, hRk1, hOk1⟩ := hHPreNext_k (k + 1) hk1lt
            have hPC := hPreCore k hk1lt
            dsimp only
            rw [hlenk, hlenk1, hDk, hDk1, hSk, hRk, hOk, hOk1]; exact hPC
          · have hk1eq : k + 1 = idx := by omega
            have hklt : k < idx := by omega
            have h0lt : 0 < idx := by omega
            have hIdxEq : idx - 1 = k := by omega
            have hFP1 : curU =
                (T.runOrdAfterUpdate P.k (levelM TP P k) N₀ (HPre k hklt).D (HPre k hklt).ord
                  (HPre k hklt).restarts (HPre k hklt).len).2 (stOrig.bran k) :=
              (fun k0 (hk0 : k0 < idx) (heq : k0 = k)
                  (hu : curU =
                    (T.runOrdAfterUpdate P.k (levelM TP P k0) N₀ (HPre k0 hk0).D (HPre k0 hk0).ord
                      (HPre k0 hk0).restarts (HPre k0 hk0).len).2 (stOrig.bran k0)) => by
                subst heq; exact hu) (idx - 1) (Nat.sub_lt h0lt zero_lt_one) hIdxEq (hCurFromPrev h0lt).1
            have hFP2 : curG = T.S (st.scState k) (stOrig.bran k) := by
              have h := (hCurFromPrev h0lt).2
              rw [hIdxEq] at h
              exact h
            obtain ⟨hDk, hlenk, hSk, hRk, hOk⟩ := hHPreNext_k k hklt
            obtain ⟨hDk1, hlenk1, _, _, hOk1⟩ := hHPreNext_idx (k + 1) hk1 hk1eq
            have hk_lt_d : k < P.d := by omega
            have hk1_lt_d : k + 1 < P.d := by omega
            have hPE := hPreExt k hklt
            dsimp only
            rw [hlenk, hlenk1, hDk, hDk1, hSk, hRk, hOk, hOk1]
            exact U3.updateLoop_step_coreRel (ordIdx := ordIdx) hOrigCore hidxLt hk1eq hk_lt_d hk1_lt_d hBr
              (HPre k hklt) hHidx rfl
              (fun δ hδ => ⟨by simp [hHidx, extendLevelHistory, extendDyn, hδ],
                by simp [hHidx, extendLevelHistory, extendDyn, hδ],
                by simp [hHidx, extendLevelHistory, extendDyn, hδ],
                by simp [hHidx, extendLevelHistory, U3.extendOrd, hδ]⟩)
              ⟨by simp [hHidx, extendLevelHistory, extendDyn],
                by simp [hHidx, extendLevelHistory, extendDyn],
                by simp [hHidx, extendLevelHistory, extendDyn]; rfl,
                by simp [hHidx, extendLevelHistory, U3.extendOrd]⟩
              (by simp [ordIdx, chainLevelOrd, show idx ≠ 0 by omega, hIdxEq, hBr])
              ⟨hPE.1, hPE.2.1, hPE.2.2.2.1, hPE.2.2.2.2.1, hPE.2.2.2.2.2⟩
              hFP1 hFP2
              (by simp [TreeChain.activeLSF, stNextLG, stNext, ChainState.toTreeChain, hk_lt_d, hBr,
                show k ≠ idx by omega])
              (chainLen_congr_lt (C₁ := stNextLG.toTreeChain)
                (C₂ := ({ st with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain) ℓ' k
                (fun j hj => by simp [stNextLG, stNext, ChainState.toTreeChain, show j ≠ idx by omega])
                (fun j hj => by
                  have hjd := lt_trans hj hk_lt_d
                  simp [TreeChain.activeLSF, stNextLG, stNext, ChainState.toTreeChain, hjd,
                    show j ≠ idx by omega])))

end MinCostFlow.Chain.Ordered
