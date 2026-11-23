module

public import MinCostFlow.Chain.Algorithm1UpdateSteps
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algorithm 1 Update Loop Non-Overflow Step (Helpers)

Split from `MinCostFlow.Chain.Algorithm1UpdateProofs`: proves `UpdateLoopInv`
preservation in the non-overflowing (`¬ hOver`) step of `updateLoop`.
-/

@[expose] public section

namespace MinCostFlow.Chain

lemma updateLoop_succ_notOver_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (_hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (_hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (_hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (rem' idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ extraOverflow stOrig st ℓ' g' (rem' + 1) idx curG curU curEncAcc)
    (hOver : ¬ intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    ∃ stNext nextG nextU,
      (updateLoop T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc).1 =
        (updateLoop T L TP P N₀ ℓ' g' rem' (idx + 1) stNext nextG nextU 0).1 ∧
      UpdateLoopInv TP N₀ extraOverflow stOrig stNext ℓ' g' rem' (idx + 1) nextG nextU 0 := by
  have hOrigCost := hInvOrig.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInvOrig
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_ge := hTP.2.2.1
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / P.k := div_nonneg hγℓ_nonneg hk_pos.le
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
  have hidxLt : idx < P.d := by have := hLoop.hidxSum; omega
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
  set stNext : ChainState T P :=
    { st with
      G := fun j => if j = idx then curG else st.G j
      scState := fun j => if j = idx then sc' else st.scState j
      updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
      curEnc := fun j =>
        if j = idx then st.curEnc idx + curEncAcc
        else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
        else st.curEnc j
      curDecUpdates := fun j =>
        if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j
      curFwd := fun j => if j = idx then st.curFwd idx + nextU.length else st.curFwd j
      recUpdates := fun j =>
        if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j }
  obtain ⟨Horig, hRebOrig⟩ : ∃ H : LevelHistory T TP P N₀ stOrig idx,
      idx + 1 = P.d → stOrig.curLastRebuilds ≤
        (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ H.D H.restarts s).2
            (stOrig.bran idx)).length := by
    by_cases hlast : idx + 1 = P.d
    · obtain ⟨H, hR⟩ := (hInvOrig.hLastCap (by omega)).1
      have hieq : idx = P.d - 1 := by omega
      subst hieq
      exact ⟨H, fun _ => hR⟩
    · obtain ⟨H⟩ := hInvOrig.hHist idx hidxLt
      exact ⟨H, fun h => absurd h hlast⟩
  set D' : DynamicInstance :=
    { G := fun s => if s ≤ Horig.len then Horig.D.G s else curG
      U := fun s => if s ≤ Horig.len then Horig.D.U s else curU
      ℓ := fun s => if s ≤ Horig.len then Horig.D.ℓ s else ℓi
      g := fun s => if s ≤ Horig.len then Horig.D.g s else gi }
  set restarts' : ℕ → List ℕ := fun r => if r ≤ Horig.len then Horig.restarts r else []
  have hRestLt' : ∀ r ≤ Horig.len + 1, ∀ j ∈ restarts' r, j < P.k := by
    intro r _ j hj
    by_cases hr : r ≤ Horig.len
    · simp only [restarts', hr, ↓reduceIte] at hj
      exact Horig.hRestartsLt r hr j hj
    · simp [restarts', hr] at hj
  have hD'G0 : D'.G 0 = Horig.D.G 0 := by simp [D']
  have hD'Gend : D'.G Horig.len = stOrig.G idx := by simp [D', Horig.hEndG]
  have hD'Gnext : D'.G (Horig.len + 1) = curG := by simp [D']
  have hD'Unext : D'.U (Horig.len + 1) = curU := by simp [D']
  have hD'ℓnext : D'.ℓ (Horig.len + 1) = ℓi := by simp [D']
  have hD'gnext : D'.g (Horig.len + 1) = gi := by simp [D']
  have hD'Valid : D'.IsValid (Horig.len + 1) := by
    intro s hs1 hs2
    by_cases hs : s ≤ Horig.len
    · have hs' : s - 1 ≤ Horig.len := by omega
      simpa [D', hs, hs'] using Horig.hD s hs1 hs
    · have hseq : s = Horig.len + 1 := by omega
      subst hseq
      simp only [D', Nat.add_sub_cancel, le_refl, ↓reduceIte,
        Nat.not_succ_le_self, Horig.hEndG]
      exact ⟨hLoop.hCurGBatch, hLoop.hCurGEq⟩
  have hD'Len : LengthsStable D' (Horig.len + 1) := by
    intro s hs1 hs2 e heS hePrev hNoI
    by_cases hs : s ≤ Horig.len
    · have hs' : s - 1 ≤ Horig.len := by omega
      simpa [D', hs, hs'] using Horig.hLen s hs1 hs e
        (by simpa [D', hs] using heS) (by simpa [D', hs'] using hePrev)
        (fun u hu => hNoI u (by simpa [D', hs] using hu))
    · have hseq : s = Horig.len + 1 := by omega
      subst hseq
      simp only [D', Nat.add_sub_cancel, le_refl, ↓reduceIte,
        Nat.not_succ_le_self, Horig.hEndG] at heS hePrev hNoI ⊢
      rw [Horig.hEndℓ e hePrev]
      exact hLoop.hCurLenStable e heS hePrev hNoI
  have hD'ℓPos : ∀ s ≤ Horig.len + 1, ∀ e ∈ (D'.G s).E, 0 < D'.ℓ s e := by
    intro s hs e he
    by_cases hsl : s ≤ Horig.len
    · simpa [D', hsl] using Horig.hℓPos s hsl e (by simpa [D', hsl] using he)
    · have hseq : s = Horig.len + 1 := by omega
      subst hseq
      simpa [D'] using hLoop.hCurLenPos e (by simpa [D'] using he)
  have hRunPre : ∀ s ≤ Horig.len,
      T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s =
        T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s := by
    intro s hs
    apply T.runAfterUpdate_congr_lt P.k (levelM TP P idx) N₀ s
    · simp [D']
    · simp [D']
    · simp [D']
    · intro t _ hts
      have htl : t ≤ Horig.len := le_trans hts hs
      exact ⟨by simp [D', htl], by simp [D', htl], by simp [D', htl]⟩
    · intro t hts
      have htl : t ≤ Horig.len := le_trans (Nat.le_of_lt hts) hs
      simp [restarts', htl]
  have hRunPostPre : ∀ s ≤ Horig.len,
      T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' s =
        T.runAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s := by
    intro s hs
    apply T.runAfterRestarts_congr_le P.k (levelM TP P idx) N₀ s
    · simp [D']
    · simp [D']
    · simp [D']
    · intro t _ hts
      have htl : t ≤ Horig.len := le_trans hts hs
      exact ⟨by simp [D', htl], by simp [D', htl], by simp [D', htl]⟩
    · intro t hts
      have htl : t ≤ Horig.len := le_trans hts hs
      simp [restarts', htl]
  have hScIdxEq : st.scState idx = stOrig.scState idx := hLoop.hScGe idx (le_refl idx)
  have hRunNextPre : T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1) = updRes := by
    rw [T.runAfterUpdate_succ P.k (levelM TP P idx) N₀ D' restarts' Horig.len,
      hRunPostPre Horig.len (le_refl _), ← Horig.hRun, ← hScIdxEq]
    simp [D', updRes]
  have hRunNextPost : T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1) = sc' := by
    simp only [SparseCoreRestartTool.runAfterRestarts, restarts',
      show ¬ (Horig.len + 1 ≤ Horig.len) by omega, ↓reduceIte, List.foldl_nil, hRunNextPre]
    rfl
  have hUpdSum' : (Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) =
      st.updCount idx + curU.length := by
    rw [Finset.sum_Icc_one_succ]
    have hpreSum : (Finset.Icc 1 Horig.len).sum (fun s => (D'.U s).length) = stOrig.updCount idx := by
      rw [← Horig.hUpd]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl := (Finset.mem_Icc.mp hs).2
      simp [D', hsl]
    rw [hpreSum, hLoop.hUpdGe idx (le_refl idx)]
    simp [D']
  have hThresh' : (((Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ := by
    rw [hUpdSum']
    exact hLeThresh
  have hSpec := hT P.k (Horig.len + 1) (levelM TP P idx) N₀ D' restarts'
    P.hk (hD'G0 ▸ Horig.hG0) hD'Valid hD'Len hD'ℓPos
    (hD'G0 ▸ Horig.hInitMBound) (hD'G0 ▸ Horig.hInitNBound) hRestLt' hThresh'
  have hBranIdx : st.bran idx < P.k := by
    rw [hLoop.hBran]; exact hInvOrig.hBran idx hidxLt
  have hStep2 := hSpec.2.1 (Horig.len + 1) (by omega) (le_refl _) (st.bran idx) hBranIdx
  have hAtEnd := hSpec.1 (Horig.len + 1) (le_refl _) (st.bran idx) hBranIdx
  have hRecEnd := hSpec.2.2.2.1 Horig.s₀ (Horig.len + 1) (Nat.le_succ_of_le Horig.hs₀)
    (le_refl _) (st.bran idx) hBranIdx
    (by
      simpa [restarts', Horig.hs₀, show st.bran idx = stOrig.bran idx from congrFun hLoop.hBran idx] using
        Horig.hS0Fresh)
    (fun r hr1 hr2 => by
      have hrle : r ≤ Horig.len := by omega
      simpa [restarts', hrle, show st.bran idx = stOrig.bran idx from congrFun hLoop.hBran idx] using
        Horig.hNoRestartAfterS0 r hr1 hrle)
  dsimp only at hStep2 hAtEnd hRecEnd
  simp only [Nat.add_sub_cancel] at hStep2
  rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, ← hScIdxEq, hRunNextPre] at hStep2
  rw [hRunNextPost, hD'Gnext, hD'ℓnext] at hAtEnd
  have hFiSub : newFiE ⊆ oldFiE := by
    simpa [newFiE, oldFiE, hRunNextPost] using hStep2.1
  have hFiLen : fiChanges.length = oldFiE.card - newFiE.card :=
    diffTreeChanges_length_of_subset hFiSub
  have hScCardLe : newFiE.card ≤ oldFiE.card := Finset.card_le_card hFiSub
  have hNextGValid : nextG.IsValid := by
    have hSp := hAtEnd.2.1
    have hCore := coreGraph_isValid hLoop.hCurGValid hAtEnd.1.2.1
    intro e he
    have hEnd := hSp.1.2.2 e he
    have hc := hCore e (hSp.1.2.1 he)
    rw [hEnd.1, hEnd.2]
    exact ⟨hSp.2.1.1 hc.1, hSp.2.1.1 hc.2⟩
  have hNextG_eq : nextG = (stOrig.G (idx + 1)).applyBatch nextU := by
    have hGsuccO := hInvOrig.hGSucc idx hidxLt
    have hScO := hLoop.hScGe idx (le_refl idx)
    have hBrO := congrFun hLoop.hBran idx
    rw [hGsuccO, ← hScO, ← hBrO]
    exact hStep2.2.2.2.2
  have hNextGBatch : (stOrig.G (idx + 1)).BatchIsValid nextU := by
    have hGsuccO := hInvOrig.hGSucc idx hidxLt
    have hScO := hLoop.hScGe idx (le_refl idx)
    have hBrO := congrFun hLoop.hBran idx
    rw [hGsuccO, ← hScO, ← hBrO]
    exact hStep2.2.2.2.1
  have hUpdIdx : stNext.updCount idx = st.updCount idx + curU.length := by simp [stNext]
  have hGIdx : stNext.G idx = curG := by simp [stNext]
  have hScIdx : stNext.scState idx = sc' := by simp [stNext]
  have hDecIdx : stNext.curDecUpdates idx = st.curDecUpdates idx + fiChanges.length := by
    simp [stNext]
  have hCurFwdIdx : stNext.curFwd idx = st.curFwd idx + nextU.length := by simp [stNext]
  have hRecNextIdx : stNext.recUpdates (idx + 1) = st.recUpdates (idx + 1) + nextU.length := by
    simp [stNext]
  have hRecIdxEq : stNext.recUpdates idx = st.recUpdates idx := by
    simp [stNext]
  have hBranEq : stNext.bran idx = st.bran idx := by simp [stNext]
  have hToTC : ∀ j < idx,
      ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.activeLSF j =
        Cpartial.activeLSF j := by
    intro j hj
    have hjlt : j < P.d := lt_trans hj hidxLt
    have hjne : j ≠ idx := Nat.ne_of_lt hj
    simp [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, hjlt, stNext, hjne]
  have hCL : ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainLen ℓ' idx = ℓi :=
    chainLen_congr_lt
      (C₁ := ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain)
      (C₂ := Cpartial) ℓ' idx
      (fun j hj => by change stNext.G j = Cpartial.G j; simp [stNext, Cpartial, Nat.ne_of_lt hj])
      hToTC
  have hCG : ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain.chainGrad g' idx = gi :=
    chainGrad_congr_lt
      (C₁ := ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).toTreeChain)
      (C₂ := Cpartial) g' idx
      (fun j hj => by change stNext.G j = Cpartial.G j; simp [stNext, Cpartial, Nat.ne_of_lt hj])
      hToTC
  have hEnc0Le_prf : idx = 0 →
      ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).curEnc 0 ≤
        (Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.G (s - 1)).batchEnc (D'.U s) := fun h0 => by
    subst h0
    have hEnc0Eq : stNext.curEnc 0 = st.curEnc 0 + curEncAcc := by simp [stNext]
    change stNext.curEnc 0 ≤ _
    rw [hEnc0Eq, (hLoop.hCurEnc0 rfl).1]
    rw [Finset.sum_Icc_one_succ]
    have hPreSum : (Finset.Icc 1 Horig.len).sum (fun s => (D'.G (s - 1)).batchEnc (D'.U s)) =
        (Finset.Icc 1 Horig.len).sum (fun s => (Horig.D.G (s - 1)).batchEnc (Horig.D.U s)) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl := (Finset.mem_Icc.mp hs).2
      have hsl' : s - 1 ≤ Horig.len := by omega
      simp [D', hsl, hsl']
    have hLastTerm : (D'.G (Horig.len + 1 - 1)).batchEnc (D'.U (Horig.len + 1)) = curEncAcc := by
      simp [D', Horig.hEndG, (hLoop.hCurEnc0 rfl).2.1]
    rw [hPreSum, hLastTerm]
    exact Nat.add_le_add_right (Horig.hEnc0Le rfl) curEncAcc
  have hEncLe_prf : idx + 1 < P.d →
      ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).curEnc (idx + 1) ≤
        (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
          (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (s - 1))
            (({ stNext with ℓ := ℓ', g := g' } : ChainState T P).bran idx)).batchEnc
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2
              (({ stNext with ℓ := ℓ', g := g' } : ChainState T P).bran idx)) := fun h1 => by
    have hNE : idx + 1 ≠ idx := by omega
    have hEncSucc : stNext.curEnc (idx + 1) = stOrig.curEnc (idx + 1) + nextEnc := by
      change (if idx + 1 = idx then st.curEnc idx + curEncAcc
        else if idx + 1 = idx + 1 then st.curEnc (idx + 1) + nextEnc else st.curEnc (idx + 1)) = _
      simp only [hNE, ↓reduceIte, hLoop.hEncGt (idx + 1) (Nat.lt_succ_self idx)]
    have hIcc : Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) =
        insert (Horig.len + 1) (Finset.Icc (Horig.s₀ + 1) Horig.len) := by
      ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; have := Horig.hs₀; omega
    have hNotMem : Horig.len + 1 ∉ Finset.Icc (Horig.s₀ + 1) Horig.len := by
      simp only [Finset.mem_Icc]; omega
    have hSumPre : (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
          (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (s - 1)) (stNext.bran idx)).batchEnc
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (stNext.bran idx))) =
        (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
          (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.restarts (s - 1)) (stOrig.bran idx)).batchEnc
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (stOrig.bran idx))) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl := (Finset.mem_Icc.mp hs).2
      rw [hRunPostPre (s - 1) (by omega), hRunPre s hsl]
      have hBr := congrFun hLoop.hBran idx
      change (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.restarts (s - 1)) (st.bran idx)).batchEnc
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (st.bran idx)) = _
      rw [hBr]
    have hLastTerm : (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' Horig.len) (stNext.bran idx)).batchEnc
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1)).2 (stNext.bran idx)) = nextEnc := by
      rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, hRunNextPre]
      have hGsuccO := hInvOrig.hGSucc idx hidxLt
      have hBrO := congrFun hLoop.hBran idx
      change (T.S (stOrig.scState idx) (stNext.bran idx)).batchEnc (updRes.2 (stNext.bran idx)) =
        (st.G (idx + 1)).batchEnc nextU
      dsimp only [nextU]
      rw [show stNext.bran idx = st.bran idx from rfl, hLoop.hGGe (idx + 1) (Nat.le_succ idx),
        hGsuccO, hBrO]
    change stNext.curEnc (idx + 1) ≤
      (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
        (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (s - 1)) (stNext.bran idx)).batchEnc
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (stNext.bran idx))
    rw [hEncSucc, hIcc, Finset.sum_insert hNotMem, Nat.add_sub_cancel, hSumPre, hLastTerm, add_comm nextEnc _]
    exact Nat.add_le_add_right (Horig.hEncLe h1) nextEnc
  let branchSeq' : ℕ → ℕ := fun s => if s ≤ Horig.len then Horig.branchSeq s else st.bran idx
  have hBranSeqLt : ∀ s, branchSeq' s < P.k := by
    intro s
    dsimp only [branchSeq']
    split_ifs
    · exact Horig.hBranch s
    · exact hBranIdx
  have hBranTail' : ∀ s, Horig.s₀ < s → s ≤ Horig.len + 1 →
      branchSeq' s = ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).bran idx := by
    intro s hs1 hs2
    change branchSeq' s = stNext.bran idx
    rw [hBranEq]
    dsimp only [branchSeq']
    by_cases hsl : s ≤ Horig.len
    · simp only [hsl, ↓reduceIte]
      rw [Horig.hBranchTail s hs1 hsl]
      exact (congrFun hLoop.hBran idx).symm
    · simp [hsl]
  have hRestCount' :
      (Finset.range (Horig.len + 1 + 1)).sum (fun r => (restarts' r).length) =
        ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).curRestarts idx := by
    rw [Finset.sum_range_succ]
    have hPreSum : (Finset.range (Horig.len + 1)).sum (fun r => (restarts' r).length) =
        (Finset.range (Horig.len + 1)).sum (fun r => (Horig.restarts r).length) :=
      Finset.sum_congr rfl fun r hr => by
        simp [restarts', Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)]
    have hLast0 : (restarts' (Horig.len + 1)).length = 0 := by simp [restarts']
    rw [hPreSum, hLast0, add_zero, Horig.hRestartsCount]
    change stOrig.curRestarts idx = stNext.curRestarts idx
    have hcR : stNext.curRestarts = stOrig.curRestarts := hLoop.hRestarts
    rw [hcR]
  have hWinFwd' :
      (((Finset.Icc 1 Horig.s₀).sum fun s =>
        ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (branchSeq' s)).length : ℕ) : ℝ) ≤
        TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc 1 Horig.s₀).sum fun s => (D'.U s).length : ℕ) : ℝ) := by
    have hL1 : (Finset.Icc 1 Horig.s₀).sum (fun s =>
        ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (branchSeq' s)).length) =
        (Finset.Icc 1 Horig.s₀).sum (fun s =>
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (Horig.branchSeq s)).length) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl : s ≤ Horig.len := le_trans (Finset.mem_Icc.mp hs).2 Horig.hs₀
      rw [hRunPre s hsl]
      simp [branchSeq', hsl]
    have hR1 : (Finset.Icc 1 Horig.s₀).sum (fun s => (D'.U s).length) =
        (Finset.Icc 1 Horig.s₀).sum (fun s => (Horig.D.U s).length) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl : s ≤ Horig.len := le_trans (Finset.mem_Icc.mp hs).2 Horig.hs₀
      simp [D', hsl]
    rw [hL1, hR1]
    exact Horig.hWinFwdBound
  have hCurFwdEq : ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).curFwd idx =
      (Finset.Icc 1 (Horig.len + 1)).sum fun s =>
        ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (branchSeq' s)).length := by
    change stNext.curFwd idx = _
    rw [hCurFwdIdx, Finset.sum_Icc_one_succ]
    have hpre : (Finset.Icc 1 Horig.len).sum (fun s =>
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (branchSeq' s)).length) =
        stOrig.curFwd idx := by
      rw [Horig.hCurFwdEq]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl := (Finset.mem_Icc.mp hs).2
      rw [hRunPre s hsl]
      simp [branchSeq', hsl]
    have hlast : ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1)).2
          (branchSeq' (Horig.len + 1))).length = nextU.length := by
      rw [hRunNextPre]
      simp [branchSeq', nextU, U_S]
    rw [hpre, hlast, hLoop.hCurFwdGe idx (le_refl idx)]
  let hHidxNew : LevelHistory T TP P N₀ { stNext with ℓ := ℓ', g := g' } idx := {
    D := D', len := Horig.len + 1, s₀ := Horig.s₀, hs₀ := Nat.le_succ_of_le Horig.hs₀,
    restarts := restarts', hRestartsLt := hRestLt', hRestartsCount := hRestCount',
    hS0Fresh := by
      simpa [stNext, restarts', Horig.hs₀, show st.bran idx = stOrig.bran idx from congrFun hLoop.hBran idx] using
        Horig.hS0Fresh,
    hNoRestartAfterS0 := fun r hr1 hr2 => by
      by_cases hrle : r ≤ Horig.len
      · simpa [stNext, restarts', hrle, show st.bran idx = stOrig.bran idx from congrFun hLoop.hBran idx] using
          Horig.hNoRestartAfterS0 r hr1 hrle
      · simp [restarts', hrle],
    hG0 := hD'G0 ▸ Horig.hG0, hD := hD'Valid, hLen := hD'Len, hℓPos := hD'ℓPos,
    hEndG := by simp [D', hGIdx],
    hEndℓ := fun e _ => by rw [hCL]; simp [D'],
    hEndg := by rw [hCG]; simp [D'],
    hUpd := by rw [hUpdIdx]; exact hUpdSum',
    hThresh := by rw [hUpdIdx]; exact hLeThresh,
    hInitMBound := by rw [hD'G0]; exact Horig.hInitMBound,
    hInitNBound := by rw [hD'G0]; exact Horig.hInitNBound,
    hRun := by rw [hScIdx, hRunNextPost],
    branchSeq := branchSeq',
    hBranch := hBranSeqLt,
    hBranchTail := hBranTail',
    hWinFwdBound := hWinFwd',
    hCurFwdEq := hCurFwdEq,
    hDecEq := by
      rw [hDecIdx, hScIdx, hBranEq, hRunPostPre Horig.s₀ Horig.hs₀]
      have hOrigDec := Horig.hDecEq
      rw [← hLoop.hDecGe idx (le_refl idx), ← hLoop.hScGe idx (le_refl idx), ← congrFun hLoop.hBran idx] at hOrigDec
      change st.curDecUpdates idx + fiChanges.length + newFiE.card = _
      rw [hFiLen]
      have hSubEq : oldFiE.card - newFiE.card + newFiE.card = oldFiE.card := Nat.sub_add_cancel hScCardLe
      rw [add_assoc, hSubEq]
      exact hOrigDec
    hEnc0Le := hEnc0Le_prf
    hEncLe := hEncLe_prf }
  have hm0le : levelM TP P idx ≤ P.M₀ ^ 2 := levelM_le_sq hTP hγM₀ hγk idx
  have hPreEnc0Next : 0 < idx + 1 → (stNext.curEnc 0 : ℝ) ≤
      20 * ((levelM TP P 0 : ℝ) + (stNext.updCount 0 : ℝ)) *
        Real.log ((levelM TP P 0 : ℝ) + (stNext.updCount 0 : ℝ) + 2) := by
    intro _
    by_cases h0 : idx = 0
    · subst h0
      have h21 := lemma_2_1 hHidxNew.hG0 hHidxNew.hD
      have hEnc0 := hHidxNew.hEnc0Le rfl
      have hm0r : ((D'.G 0).m : ℝ) ≤ (levelM TP P 0 : ℝ) := by
        exact_mod_cast (hD'G0 ▸ Horig.hInitMBound)
      have hlog0 : 0 ≤ Real.log (((D'.G 0).m : ℝ) + (stNext.updCount 0 : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (D'.G 0).m from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ stNext.updCount 0 from Nat.cast_nonneg _])
      have hlogLe : Real.log (((D'.G 0).m : ℝ) + (stNext.updCount 0 : ℝ) + 2) ≤
          Real.log ((levelM TP P 0 : ℝ) + (stNext.updCount 0 : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [hHidxNew.hUpd] at h21
      have hEnc0r : (stNext.curEnc 0 : ℝ) ≤
          20 * (((D'.G 0).m : ℝ) + (stNext.updCount 0 : ℝ)) *
            Real.log (((D'.G 0).m : ℝ) + (stNext.updCount 0 : ℝ) + 2) :=
        le_trans (by exact_mod_cast hEnc0) h21
      refine le_trans hEnc0r ?_
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by norm_num)) hlogLe hlog0 (by positivity)
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      have heqC : stNext.curEnc 0 = st.curEnc 0 := by simp [stNext, hne0]
      have heqU : stNext.updCount 0 = st.updCount 0 := by simp [stNext, hne0]
      rw [heqC, heqU]
      exact hLoop.hPreEnc0 (Nat.pos_of_ne_zero h0)
  have hNextG_V : nextG.V ⊆ curG.V := by
    intro v hv
    have hvR := hAtEnd.2.1.1.1 hv
    exact hAtEnd.1.2.1.2.2.1 hvR
  have hNextG_m : (nextG.m : ℝ) ≤ (levelM TP P (idx + 1) : ℝ) := by
    have hcard : (nextG.E.card : ℝ) ≤ (levelM TP P idx : ℝ) * TP.γ_ℓ (levelM TP P idx) / P.k :=
      hAtEnd.2.1.2.2.2.2.2
    have hγℓ_le : TP.γ_ℓ (levelM TP P idx) ≤ TP.γ_ℓ (P.M₀ ^ 2) := hTP.2.2.2.1 _ _ hm0le
    have hcard' : (nextG.E.card : ℝ) ≤ (levelM TP P idx : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) / P.k :=
      le_trans hcard (by gcongr)
    exact_mod_cast levelM_step_nat hTP hγk hcard'
  have hCurLenNextPos : ∀ e ∈ nextG.E, 0 <
      ({ stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j } : TreeChain).chainLen ℓ' (idx + 1) e := by
    intro e he
    set Cnext' : TreeChain :=
      { stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j }
    have heCur : e ∈ curG.E := (Finset.mem_sdiff.mp (hAtEnd.2.1.1.2.1 he)).1
    have hw1 : 1 ≤ (T.lsfs sc' (st.bran idx)).wstr e := by
      have hnonneg : ∀ f ∈ curG.E, 0 ≤ ℓi f := fun f hf => (hLoop.hCurLenPos f hf).le
      exact le_trans (one_le_stretch hAtEnd.1.2.1.2.2.2.2 hnonneg heCur) (hAtEnd.1.2.2.2 e heCur).1
    have hCLpre : Cnext'.chainLen ℓ' idx = ℓi := by
      apply chainLen_congr_lt (C₁ := Cnext') (C₂ := Cpartial) ℓ' idx
        (fun j hj => by
          dsimp only [Cnext', Cpartial, ChainState.toTreeChain]
          simp [stNext, show j ≠ idx + 1 by omega, show j ≠ idx by omega])
        (fun j hj => by
          have hjlt : j < P.d := lt_trans hj hidxLt
          simp [TreeChain.activeLSF, Cnext', Cpartial, ChainState.toTreeChain, hjlt, stNext,
            show j ≠ idx by omega])
    have hLidx : Cnext'.activeLSF idx = T.lsfs sc' (st.bran idx) := by
      simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext]
    change 0 < coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e
    rw [hLidx, hCLpre]
    unfold coreLen
    exact mul_pos (lt_of_lt_of_le zero_lt_one hw1) (hLoop.hCurLenPos e heCur)
  have hCurLenNextStable : ∀ e ∈ nextG.E, e ∈ (stOrig.G (idx + 1)).E → (∀ u ∈ nextU, ¬ u.Inserts e) →
      ({ stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j } : TreeChain).chainLen ℓ' (idx + 1) e =
        stOrig.toTreeChain.chainLen stOrig.ℓ (idx + 1) e := by
    intro e heNext heOrigNext hNoInsNext
    set Cnext' : TreeChain :=
      { stNext.toTreeChain with G := fun j => if j = idx + 1 then nextG else stNext.G j }
    have heCur : e ∈ curG.E := (Finset.mem_sdiff.mp (hAtEnd.2.1.1.2.1 heNext)).1
    have heOrigIdx : e ∈ (stOrig.G idx).E := by
      have hSpOrig := (hOrigLev idx (Nat.le_of_lt hidxLt)).2.2.2.2 hidxLt (stOrig.bran idx)
        (hInvOrig.hBran idx hidxLt)
      have heS : e ∈ (T.S (stOrig.scState idx) (stOrig.bran idx)).E := by
        rw [← hInvOrig.hGSucc idx hidxLt]; exact heOrigNext
      exact (Finset.mem_sdiff.mp (hSpOrig.2.1.2.1 heS)).1
    have hNoInsCur : ∀ u ∈ curU, ¬ u.Inserts e := by
      have hNR := hNoReinsTool P.k (Horig.len + 1) (levelM TP P idx) N₀ D' restarts'
        P.hk (hD'G0 ▸ Horig.hG0) hD'Valid hD'Len hD'ℓPos
        (hD'G0 ▸ Horig.hInitMBound) (hD'G0 ▸ Horig.hInitNBound) hRestLt' hThresh'
        (Horig.len + 1) (by omega) (le_refl _) (st.bran idx) hBranIdx
        e (by
          simp only [Nat.add_sub_cancel]
          rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, congrFun hLoop.hBran idx,
            ← hInvOrig.hGSucc idx hidxLt]
          exact heOrigNext)
        (by
          rw [hRunNextPost]
          exact heNext)
        (fun u hu => by
          rw [hRunNextPre] at hu
          exact hNoInsNext u hu)
      intro u hu
      exact hNR u (by simpa [D'] using hu)
    have hCLpre : Cnext'.chainLen ℓ' idx e = stOrig.toTreeChain.chainLen stOrig.ℓ idx e := by
      have heq1 : Cnext'.chainLen ℓ' idx = ℓi := by
        apply chainLen_congr_lt (C₁ := Cnext') (C₂ := Cpartial) ℓ' idx
          (fun j hj => by
            dsimp only [Cnext', Cpartial, ChainState.toTreeChain]
            simp [stNext, show j ≠ idx + 1 by omega, show j ≠ idx by omega])
          (fun j hj => by
            have hjlt : j < P.d := lt_trans hj hidxLt
            simp [TreeChain.activeLSF, Cnext', Cpartial, ChainState.toTreeChain, hjlt, stNext,
              show j ≠ idx by omega])
      rw [heq1]
      exact hLoop.hCurLenStable e heCur heOrigIdx hNoInsCur
    have hWstrEq : (Cnext'.activeLSF idx).wstr e = (stOrig.toTreeChain.activeLSF idx).wstr e := by
      have h1 : Cnext'.activeLSF idx = T.lsfs sc' (st.bran idx) := by
        simp [TreeChain.activeLSF, Cnext', ChainState.toTreeChain, hidxLt, stNext]
      have h2 : stOrig.toTreeChain.activeLSF idx = T.lsfs (stOrig.scState idx) (stOrig.bran idx) := by
        simp [TreeChain.activeLSF, ChainState.toTreeChain, hidxLt]
      rw [h1, h2]
      have hW := hStep2.2.1 e (by simp [D']; exact heCur)
        (by simp [D', Horig.hEndG]; exact heOrigIdx)
        (fun u hu => hNoInsCur u (by simpa [D'] using hu))
      rw [hRunNextPost] at hW
      rw [← hLoop.hScGe idx (le_refl idx), ← congrFun hLoop.hBran idx]
      exact hW
    change coreLen (Cnext'.activeLSF idx) (Cnext'.chainLen ℓ' idx) e =
      coreLen (stOrig.toTreeChain.activeLSF idx) (stOrig.toTreeChain.chainLen stOrig.ℓ idx) e
    unfold coreLen
    rw [hWstrEq, hCLpre]
  have hTreeDiffNext : (diffTreeChanges stOrig.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E).length +
      (Finset.range P.d).sum stOrig.curDecUpdates ≤ (Finset.range P.d).sum stNext.curDecUpdates := by
    have hStepDiff : (diffTreeChanges st.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E).length ≤
        fiChanges.length := by
      have hbi := diffTreeChanges_length_biUnion (Finset.range (P.d + 1))
        (fun j => (st.toTreeChain.activeLSF j).F.F.E)
        (fun j => (stNext.toTreeChain.activeLSF j).F.F.E)
      have hsplit : Finset.range (P.d + 1) = insert idx (Finset.range (P.d + 1) \ {idx}) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        by_cases hji : j = idx
        · simp [hji]; omega
        · simp [hji]
      have hnot : idx ∉ Finset.range (P.d + 1) \ {idx} := by simp
      have hzero : (Finset.range (P.d + 1) \ {idx}).sum (fun j =>
          (diffTreeChanges (st.toTreeChain.activeLSF j).F.F.E
            (stNext.toTreeChain.activeLSF j).F.F.E).length) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne : j ≠ idx := by simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj; exact hj.2
        have hActEq : stNext.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
          by_cases hjlt : j < P.d
          · simp [TreeChain.activeLSF, ChainState.toTreeChain, hjlt, stNext, hne]
          · have hjeq : j = P.d := by
              have hlt' := (Finset.mem_sdiff.mp hj).1
              rw [Finset.mem_range] at hlt'; omega
            subst hjeq
            simp [TreeChain.activeLSF, ChainState.toTreeChain, stNext]
        rw [hActEq, diffTreeChanges_length]
        simp
      change (diffTreeChanges st.toTreeChain.chainTreeEdges stNext.toTreeChain.chainTreeEdges).length ≤ _
      unfold TreeChain.chainTreeEdges
      refine le_trans hbi ?_
      rw [hsplit, Finset.sum_insert hnot, hzero, add_zero]
      simp [TreeChain.activeLSF, ChainState.toTreeChain, hidxLt, stNext, fiChanges, oldFiE, newFiE]
    have hSumDec : (Finset.range P.d).sum stNext.curDecUpdates =
        (Finset.range P.d).sum st.curDecUpdates + fiChanges.length := by
      have hsplit : Finset.range P.d = insert idx (Finset.range P.d \ {idx}) := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        by_cases hji : j = idx
        · simp [hji]; omega
        · simp [hji]
      have hnot : idx ∉ Finset.range P.d \ {idx} := by simp
      have hPre : (∑ j ∈ Finset.range P.d \ {idx}, stNext.curDecUpdates j) =
          ∑ j ∈ Finset.range P.d \ {idx}, st.curDecUpdates j := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne : j ≠ idx := by simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj; exact hj.2
        simp [stNext, hne]
      change (∑ j ∈ Finset.range P.d, stNext.curDecUpdates j) =
        (∑ j ∈ Finset.range P.d, st.curDecUpdates j) + fiChanges.length
      rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot, hPre]
      have hAtIdx : stNext.curDecUpdates idx = st.curDecUpdates idx + fiChanges.length := by simp [stNext]
      rw [hAtIdx]
      ring
    have hTri := diffTreeChanges_length_triangle stOrig.toTreeChain.chainTree.E
      st.toTreeChain.chainTree.E stNext.toTreeChain.chainTree.E
    have hTD := hLoop.hTreeDiff
    omega
  have hLoopNext : UpdateLoopInv TP N₀ extraOverflow stOrig stNext ℓ' g'
      rem' (idx + 1) nextG nextU 0 := by
    refine {
      hidxSum := by have := hLoop.hidxSum; omega
      hGGe := fun j hj => by
        have hne : j ≠ idx := by omega
        change (if j = idx then curG else st.G j) = _
        simp only [hne, ↓reduceIte]
        exact hLoop.hGGe j (by omega)
      hScGe := fun j hj => by
        have hne : j ≠ idx := by omega
        change (if j = idx then sc' else st.scState j) = _
        simp only [hne, ↓reduceIte]
        exact hLoop.hScGe j (by omega)
      hRestarts := hLoop.hRestarts
      hUpdGe := fun j hj => by
        have hne : j ≠ idx := by omega
        change (if j = idx then st.updCount idx + curU.length else st.updCount j) = _
        simp only [hne, ↓reduceIte]; exact hLoop.hUpdGe j (by omega)
      hDecGe := fun j hj => by
        have hne : j ≠ idx := by omega
        change (if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j) = _
        simp only [hne, ↓reduceIte]; exact hLoop.hDecGe j (by omega)
      hEncGt := fun j hj => by
        have hne1 : j ≠ idx := by omega
        have hne2 : j ≠ idx + 1 := by omega
        change (if j = idx then st.curEnc idx + curEncAcc
          else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc else st.curEnc j) = _
        simp only [hne1, hne2, ↓reduceIte]
        exact hLoop.hEncGt j (by omega)
      hCurFwdGe := fun j hj => by
        have hne : j ≠ idx := by omega
        change (if j = idx then st.curFwd idx + nextU.length else st.curFwd j) = _
        simp only [hne, ↓reduceIte]
        exact hLoop.hCurFwdGe j (by omega)
      hRecGt := fun j hj => by
        have hne : j ≠ idx + 1 := by omega
        change (if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j) = _
        simp only [hne, ↓reduceIte]
        exact hLoop.hRecGt j (by omega)
      hCurRecAt := by
        rw [hRecNextIdx, hLoop.hRecGt (idx + 1) (Nat.lt_succ_self idx)]
      hBran := hLoop.hBran
      hLast := hLoop.hLast
      hLG := hLoop.hLG
      hCnt := hLoop.hCnt
      hClosed := hLoop.hClosed
      hLastStats := hLoop.hLastStats
      hG0New := fun _ => by
        by_cases h0 : idx = 0
        · subst h0; simp only [stNext, ↓reduceIte]
          exact ⟨hLoop.hCurGValid, hLoop.hCurGV0 rfl⟩
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          simp only [stNext, hne0, ↓reduceIte]
          exact hLoop.hG0New (Nat.pos_of_ne_zero h0)
      hPreHist := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq; exact ⟨hHidxNew⟩
        · have hjlt : j < idx := by omega
          obtain ⟨Hj⟩ := hLoop.hPreHist j hjlt
          have hcurEncSucc : stNext.curEnc (j + 1) = st.curEnc (j + 1) := by
            by_cases h1 : j + 1 = idx
            · have hpos : 0 < idx := by omega
              simp [stNext, h1, (hLoop.hCurEncPos hpos).1]
            · have h1' : j + 1 ≠ idx := h1
              have hne0 : j ≠ idx := hjeq
              simp only [stNext, h1', hne0, Nat.add_right_cancel_iff, ↓reduceIte]
          have hcurEnc0 : j = 0 → stNext.curEnc 0 = st.curEnc 0 := fun hj0 => by
            subst hj0
            have hpos : 0 < idx := by omega
            simp [stNext, (Ne.symm (Nat.ne_of_gt hpos))]
          exact ⟨{ Hj with
            hEndG := by simp [stNext, hjeq]; exact Hj.hEndG
            hEndℓ := fun e he => by
              have hGj : stNext.G j = st.G j := by simp [stNext, hjeq]
              have hCL := chainLen_congr_lt (C₁ := stNext.toTreeChain) (C₂ := st.toTreeChain) ℓ' j
                (fun m hm => by change stNext.G m = st.G m; simp [stNext, show m ≠ idx by omega])
                (fun m hm => by
                  have hmlt : m < P.d := by omega
                  simp [TreeChain.activeLSF, ChainState.toTreeChain, hmlt, stNext, show m ≠ idx by omega])
              change Hj.D.ℓ Hj.len e = stNext.toTreeChain.chainLen ℓ' j e
              rw [hCL]; exact Hj.hEndℓ e (hGj ▸ he)
            hEndg := by
              have hCG := chainGrad_congr_lt (C₁ := stNext.toTreeChain) (C₂ := st.toTreeChain) g' j
                (fun m hm => by change stNext.G m = st.G m; simp [stNext, show m ≠ idx by omega])
                (fun m hm => by
                  have hmlt : m < P.d := by omega
                  simp [TreeChain.activeLSF, ChainState.toTreeChain, hmlt, stNext, show m ≠ idx by omega])
              change Hj.D.g Hj.len = stNext.toTreeChain.chainGrad g' j
              rw [hCG]; exact Hj.hEndg
            hUpd := by simp [stNext, hjeq]; exact Hj.hUpd
            hThresh := by simp [stNext, hjeq]; exact Hj.hThresh
            hRun := by simp [stNext, hjeq]; exact Hj.hRun
            hCurFwdEq := by simp [stNext, hjeq]; exact Hj.hCurFwdEq
            hDecEq := by simp [stNext, hjeq]; exact Hj.hDecEq
            hEnc0Le := fun h0 => by rw [hcurEnc0 h0]; exact Hj.hEnc0Le h0
            hEncLe := fun h1 => by rw [hcurEncSucc]; exact Hj.hEncLe h1 }⟩
      hPreGSucc := fun j hj => by
        by_cases h1 : j + 1 = idx
        · have hpos : 0 < idx := by omega
          have hjne : j ≠ idx := by omega
          have hjeq : idx - 1 = j := by omega
          simp only [stNext, h1, hjne, ↓reduceIte]
          have hprev := hLoop.hCurGFromPrev hpos
          rw [hjeq] at hprev
          exact hprev
        · have hjne : j ≠ idx := by omega
          simp only [stNext, h1, hjne, ↓reduceIte]
          exact hLoop.hPreGSucc j (by omega)
      hPreV := fun j hj => by
        by_cases h0 : idx = 0
        · subst h0
          have hj0 : j = 0 := by omega
          subst hj0; exact Finset.Subset.refl _
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          have hG0 : stNext.G 0 = st.G 0 := by simp [stNext, hne0]
          rw [hG0]
          by_cases hjeq : j = idx
          · subst hjeq; simp only [stNext, ↓reduceIte]; exact hLoop.hCurGVPos (Nat.pos_of_ne_zero h0)
          · simp only [stNext, hjeq, ↓reduceIte]; exact hLoop.hPreV j (by omega)
      hPreM := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq; simp only [stNext, ↓reduceIte]; exact hLoop.hCurGM
        · simp only [stNext, hjeq, ↓reduceIte]; exact hLoop.hPreM j (by omega)
      hPreEnc0 := hPreEnc0Next
      hLoopRecReb := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq
          have hrb : stNext.rebuildCount j = stOrig.rebuildCount j := by
            change st.rebuildCount j = stOrig.rebuildCount j; rw [hLoop.hCnt.2]
          rw [hrb, hUpdIdx, hLoop.hUpdGe j (le_refl j), hRecIdxEq, hLoop.hCurRecAt]
          have hOrigJ := hInvOrig.hRecRebuild j hidxLt
          push_cast at hOrigJ ⊢
          linarith
        · have hjlt : j < idx := by omega
          have hne1 : j ≠ idx + 1 := by omega
          have hrb : stNext.rebuildCount j = st.rebuildCount j := rfl
          have hupd : stNext.updCount j = st.updCount j := by simp [stNext, hjeq]
          have hrec : stNext.recUpdates j = st.recUpdates j := by simp [stNext, hne1]
          rw [hrb, hupd, hrec]
          exact hLoop.hLoopRecReb j hjlt
      hLoopRecFwd := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq
          refine ⟨?_, ?_⟩
          · have hcf : (stNext.curFwd j : ℝ) =
                (((Finset.Icc 1 (Horig.len + 1)).sum fun s =>
                  ((T.runAfterUpdate P.k (levelM TP P j) N₀ D' restarts' s).2 (branchSeq' s)).length : ℕ) : ℝ) := by
              exact_mod_cast hCurFwdEq
            have hIccSplit : Finset.Icc 1 (Horig.len + 1) =
                Finset.Icc 1 Horig.s₀ ∪ Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) := by
              ext s; simp only [Finset.mem_Icc, Finset.mem_union]; have := Horig.hs₀; omega
            have hIccDisj : Disjoint (Finset.Icc 1 Horig.s₀)
                (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)) := by
              rw [Finset.disjoint_left]; intro s h1 h2
              simp only [Finset.mem_Icc] at h1 h2; omega
            have hLHS :
                (Finset.Icc 1 (Horig.len + 1)).sum (fun s =>
                  ((T.runAfterUpdate P.k (levelM TP P j) N₀ D' restarts' s).2 (branchSeq' s)).length) =
                  (Finset.Icc 1 Horig.s₀).sum (fun s =>
                    ((T.runAfterUpdate P.k (levelM TP P j) N₀ D' restarts' s).2 (branchSeq' s)).length) +
                  (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum (fun s =>
                    ((T.runAfterUpdate P.k (levelM TP P j) N₀ D' restarts' s).2 (st.bran j)).length) := by
              rw [hIccSplit, Finset.sum_union hIccDisj]
              congr 1
              refine Finset.sum_congr rfl fun s hs => ?_
              rcases Finset.mem_Icc.mp hs with ⟨hs1, hs2⟩
              have hbt := hBranTail' s hs1 hs2
              change branchSeq' s = stNext.bran j at hbt
              rw [hbt, hBranEq]
            have hRHS :
                (Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) =
                  (Finset.Icc 1 Horig.s₀).sum (fun s => (D'.U s).length) +
                  (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum (fun s => (D'.U s).length) := by
              rw [hIccSplit, Finset.sum_union hIccDisj]
            have hγr_le := hTP.2.2.2.2.2.2.2.1 _ _ hm0le
            have hTail :
                (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
                  ((T.runAfterUpdate P.k (levelM TP P j) N₀ D' restarts' s).2 (st.bran j)).length : ℕ) : ℝ) ≤
                  TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
                    (D'.U s).length : ℕ) : ℝ) :=
              le_trans hRecEnd.1 (mul_le_mul_of_nonneg_right hγr_le (Nat.cast_nonneg _))
            rw [hcf, hLHS, hUpdIdx, ← hUpdSum', hRHS, Nat.cast_add, Nat.cast_add, mul_add]
            exact add_le_add hWinFwd' hTail
          · rw [hRecNextIdx, hLoop.hRecGt (j + 1) (Nat.lt_succ_self j),
              hCurFwdIdx, hLoop.hCurFwdGe j (le_refl j),
              hRecIdxEq, hLoop.hCurRecAt, hUpdIdx, hLoop.hUpdGe j (le_refl j)]
            have hOrig2 := (hInvOrig.hRecFwd j hidxLt).2
            push_cast
            linarith
        · have hjlt : j < idx := by omega
          have hcf : stNext.curFwd j = st.curFwd j := by simp [stNext, hjeq]
          have hup : stNext.updCount j = st.updCount j := by simp [stNext, hjeq]
          have hr1 : stNext.recUpdates (j + 1) = st.recUpdates (j + 1) := by
            change (if j + 1 = idx + 1 then st.recUpdates (idx + 1) + nextU.length
              else st.recUpdates (j + 1)) = st.recUpdates (j + 1)
            simp only [Nat.add_right_cancel_iff, hjeq, ↓reduceIte]
          have hr0 : stNext.recUpdates j = st.recUpdates j := by
            simp [stNext, show j ≠ idx + 1 by omega]
          rw [hcf, hup, hr1, hr0]
          exact hLoop.hLoopRecFwd j hjlt
      hPreLastReb := fun hPd _ => by
        have hlast : idx + 1 = P.d := hPd
        have hieq : P.d - 1 = idx := by omega
        rw [hieq]
        refine ⟨hHidxNew, ?_⟩
        have hIcc : Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) =
            insert (Horig.len + 1) (Finset.Icc (Horig.s₀ + 1) Horig.len) := by
          ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; have := Horig.hs₀; omega
        have hNotMem : Horig.len + 1 ∉ Finset.Icc (Horig.s₀ + 1) Horig.len := by
          simp only [Finset.mem_Icc]; omega
        have hSumPre : (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
              ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (stNext.bran idx)).length) =
            (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
              ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (stOrig.bran idx)).length) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          have hsl := (Finset.mem_Icc.mp hs).2
          rw [hRunPre s hsl]
          simp [stNext, hLoop.hBran]
        have hLastTerm : ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1)).2
              (stNext.bran idx)).length = nextU.length := by
          rw [hRunNextPre]
        have hIfLe : (if nextU = [] then 0 else 1) ≤ nextU.length := by
          cases nextU with
          | nil => simp
          | cons _ _ => simp
        change stNext.curLastRebuilds + (if nextU = [] then 0 else 1) ≤
          (Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (stNext.bran idx)).length
        rw [hIcc, Finset.sum_insert hNotMem, add_comm]
        rw [hSumPre, hLastTerm]
        have hLastEq : stNext.curLastRebuilds = stOrig.curLastRebuilds := by
          change st.curLastRebuilds = stOrig.curLastRebuilds; exact hLoop.hLastStats.1
        rw [hLastEq]
        have hR0 := hRebOrig hlast
        omega
      hCurGEq := hNextG_eq
      hCurGBatch := hNextGBatch
      hCurGValid := hNextGValid
      hCurGM := hNextG_m
      hCurGV0 := fun h0 => by omega
      hCurGVPos := fun _ => by
        by_cases h0 : idx = 0
        · subst h0; simp only [stNext, ↓reduceIte]; exact hNextG_V
        · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
          have hG0 : stNext.G 0 = st.G 0 := by simp [stNext, hne0]
          rw [hG0]
          exact Finset.Subset.trans hNextG_V (hLoop.hCurGVPos (Nat.pos_of_ne_zero h0))
      hCurGFromPrev := fun _ => by simp [stNext, nextG]
      hCurEnc0 := fun h0 => by omega
      hCurEncPos := fun _ => by
        refine ⟨rfl, fun hidx1Lt => ?_⟩
        have hEncSpec := (hRecEnd).2
        have hsub : Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) ⊆ Finset.Icc 1 (Horig.len + 1) := by
          intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
        have hU_sub :
            (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) ≤
              (((Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) := by
          exact_mod_cast Finset.sum_le_sum_of_subset hsub
        have hEnc1 : (stNext.curEnc (idx + 1) : ℝ) ≤
            (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
              (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (s - 1)) (stNext.bran idx)).batchEnc
                ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (stNext.bran idx)) : ℕ) : ℝ) := by
          exact_mod_cast hHidxNew.hEncLe hidx1Lt
        have hBrEq : stNext.bran idx = st.bran idx := rfl
        rw [hBrEq] at hEnc1
        have hγrle := hTP.2.2.2.2.2.2.2.1 _ _ hm0le
        have hupd_le : (((Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) ≤
            4 * (levelM TP P idx : ℝ) / (P.k : ℝ) :=
          le_trans hThresh' (updateThreshold_le_four_div P.k _ _ P.hk)
        have hm0nn : (0 : ℝ) ≤ levelM TP P idx := Nat.cast_nonneg _
        have hγr0 : 0 ≤ TP.γ_r (levelM TP P idx) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 _)
        have hγrM0 : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 _)
        have hm0_lt := levelM_lt_add_one hTP P idx
        have hdiv1 : (1 : ℝ) / (P.k : ℝ) ≤ 1 := by
          rw [div_le_one hk_pos]
          exact_mod_cast P.hk
        calc
          (stNext.curEnc (idx + 1) : ℝ)
              ≤ TP.γ_r (levelM TP P idx) * ((levelM TP P idx : ℝ) / (P.k : ℝ) +
                  (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
                    (D'.U s).length : ℕ) : ℝ)) :=
                le_trans hEnc1 hEncSpec
          _ ≤ TP.γ_r (levelM TP P idx) * ((levelM TP P idx : ℝ) / (P.k : ℝ) +
                  (((Finset.Icc 1 (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (add_le_add le_rfl hU_sub) hγr0
          _ ≤ TP.γ_r (P.M₀ ^ 2) *
                ((levelM TP P idx : ℝ) / (P.k : ℝ) + 4 * (levelM TP P idx : ℝ) / (P.k : ℝ)) :=
                mul_le_mul hγrle (add_le_add (le_refl _) hupd_le) (by positivity) hγrM0
          _ = 5 * TP.γ_r (P.M₀ ^ 2) * ((levelM TP P idx : ℝ) / (P.k : ℝ)) := by ring
          _ ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                (((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ idx + 1) / (P.k : ℝ)) := by
                gcongr
          _ = 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ idx / (P.k : ℝ) +
                  1 / (P.k : ℝ)) := by
                ring
          _ ≤ 5 * TP.γ_r (P.M₀ ^ 2) *
                ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ idx / (P.k : ℝ) + 1) := by
                gcongr
      hCurLenPos := hCurLenNextPos
      hCurLenStable := hCurLenNextStable
      hDecMono := fun j hj => by
        by_cases hjeq : j = idx
        · subst hjeq; simp only [stNext, ↓reduceIte]
          have := hLoop.hDecMono j hj; omega
        · simp only [stNext, hjeq, ↓reduceIte]; exact hLoop.hDecMono j hj
      hTreeDiff := hTreeDiffNext
      hLvlM := hLoop.hLvlM
      hN0 := hLoop.hN0 }
  refine ⟨stNext, nextG, nextU, ?_, hLoopNext⟩
  dsimp only [updateLoop]
  rw [ite_eq_right_iff.mpr fun h => absurd h hOver]

end MinCostFlow.Chain
