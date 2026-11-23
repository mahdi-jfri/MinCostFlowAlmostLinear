module

public import MinCostFlow.Chain.Ordered.UpdateSteps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extended level history and ordered output step for non-overflowing updates

Split from `MinCostFlow.Chain.Ordered.UpdateStepNoRebuild`: in the non-overflowing (`¬ hOver`)
step of `updateLoop` at level `idx`, this file extends `stOrig`'s level-`idx` history by one
ordered batch, applies `IsSpecOrdRestartNoHidden`, builds the new `LevelHistory` at `idx`,
and extracts the ordered rotation transition for level `idx + 1`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section OupdNotOver

/-- Packaged state, extended history, and core tool consequences for one non-overflowing
(`¬ hOver`) step of `updateLoop` at level `idx`. -/
structure OupdNotOverData
    (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (stOrig st : ChainState T P) (ℓ' g' : ℕ → ℝ) (idx : ℕ)
    (curG : MGraph) (curU : List Update) (curEncAcc : ℕ) where
  sc' : T.State
  U_S : ℕ → List Update
  fiChanges : List TreeChange
  nextG : MGraph
  nextU : List Update
  nextEnc : ℕ
  stNext : ChainState T P
  Horig : LevelHistory T TP P N₀ stOrig idx
  D' : DynamicInstance
  ord' : ℕ → ℕ → List End
  restarts' : ℕ → List ℕ
  branchSeq' : ℕ → ℕ
  hHidxNew : LevelHistory T TP P N₀ { stNext with ℓ := ℓ', g := g' } idx
  hHidxFields : hHidxNew.D = D' ∧ hHidxNew.len = Horig.len + 1 ∧ hHidxNew.s₀ = Horig.s₀ ∧
    hHidxNew.ord = ord' ∧ hHidxNew.restarts = restarts'
  hSc'Eq : sc' = (T.updateOrd (st.scState idx) curU
    (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx)
    (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainGrad g' idx)
    (chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)).1
  hUSEq : U_S = (T.updateOrd (st.scState idx) curU
    (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx)
    (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainGrad g' idx)
    (chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx)).2
  hFiEq : fiChanges = diffTreeChanges
    (T.lsfs (st.scState idx) (st.bran idx)).F.F.E (T.lsfs sc' (st.bran idx)).F.F.E
  hNextGEqDef : nextG = T.S sc' (st.bran idx)
  hNextUEqDef : nextU = U_S (st.bran idx)
  hNextEncDef : nextEnc = (st.G (idx + 1)).batchEnc nextU
  hStNextEq : stNext =
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
  hD'G0 : D'.G 0 = Horig.D.G 0
  hD'Gend : D'.G Horig.len = stOrig.G idx
  hD'Gnext : D'.G (Horig.len + 1) = curG
  hD'Unext : D'.U (Horig.len + 1) = curU
  hD'Valid : D'.IsValid (Horig.len + 1)
  hD'Len : LengthsStable D' (Horig.len + 1)
  hD'ℓPos : ∀ s ≤ Horig.len + 1, ∀ e ∈ (D'.G s).E, 0 < D'.ℓ s e
  hD'Ord : OrderedUpTo D' (Horig.len + 1) 2 ord'
  hRestLt' : ∀ r ≤ Horig.len + 1, ∀ j ∈ restarts' r, j < P.k
  hRunPre : ∀ s ≤ Horig.len,
    T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s =
      T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s
  hRunPostPre : ∀ s ≤ Horig.len,
    T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' s =
      T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s
  hRunNextPre :
    T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1) = (sc', U_S)
  hRunNextPost :
    T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1) = sc'
  hUpdSum' : (Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) =
    st.updCount idx + curU.length
  hThresh' : (((Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) : ℕ) : ℝ) ≤
    SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀
  hBranIdx : st.bran idx < P.k
  hBranTail' : ∀ s, Horig.s₀ < s → s ≤ Horig.len + 1 →
    branchSeq' s = ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).bran idx
  hWinFwd' :
    (((Finset.Icc 1 Horig.s₀).sum fun s =>
      ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
        (branchSeq' s)).length : ℕ) : ℝ) ≤
      TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc 1 Horig.s₀).sum fun s => (D'.U s).length : ℕ) : ℝ)
  hCurFwdEq : ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).curFwd idx =
    (Finset.Icc 1 (Horig.len + 1)).sum fun s =>
      ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (branchSeq' s)).length
  hRebOrig : idx + 1 = P.d → stOrig.curLastRebuilds ≤
    (Finset.Icc (Horig.s₀ + 1) Horig.len).sum fun s =>
      ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
        (stOrig.bran idx)).length
  hAtEnd :
    (T.lsfs sc' (st.bran idx)).Holds curG
      (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx)
      (TP.σ P.k curG.n) ∧
    IsSparsifiedCoreGraphAt curG (T.lsfs sc' (st.bran idx))
      (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx)
      (P.k : ℝ) (TP.γ_ℓ (levelM TP P idx)) (TP.γ_c (levelM TP P idx)) (levelM TP P idx)
      (T.S sc' (st.bran idx)) (T.emb sc' (st.bran idx))
  hWstrStep : ∀ e ∈ (D'.G (Horig.len + 1)).E, e ∈ (D'.G Horig.len).E →
    (∀ u ∈ D'.U (Horig.len + 1), ¬ u.Inserts e) →
    (T.lsfs sc' (st.bran idx)).wstr e = (T.lsfs (st.scState idx) (st.bran idx)).wstr e
  hRecEnd :
    (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
      ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
        (st.bran idx)).length : ℕ) : ℝ) ≤
      TP.γ_r (levelM TP P idx) *
        (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ) ∧
    (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s =>
      (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (s - 1))
        (st.bran idx)).batchEnc
        ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
          (st.bran idx)) : ℕ) : ℝ) ≤
      TP.γ_r (levelM TP P idx) * ((levelM TP P idx : ℝ) / (P.k : ℝ) +
        (((Finset.Icc (Horig.s₀ + 1) (Horig.len + 1)).sum fun s => (D'.U s).length : ℕ) : ℝ))
  hNextGValid : nextG.IsValid
  hNextG_eq : nextG = (stOrig.G (idx + 1)).applyBatch nextU
  hNextGBatch : (stOrig.G (idx + 1)).BatchIsValid nextU
  hNextOrd : ∃ (ρBefore : Rotation (stOrig.G (idx + 1))) (ρAfter : Rotation nextG),
    ρBefore.order = stOrig.levelOrd (idx + 1) ∧
    ρAfter.order =
      chainLevelOrd T (fun j => if j = idx + 1 then nextG else stNext.G j)
        stNext.scState stNext.bran (idx + 1) ∧
    RotationBatch 2 nextU ρBefore (hNextG_eq ▸ ρAfter)

/-- Constructs `OupdNotOverData` for a non-overflowing step of `updateLoop` at level `idx`. -/
lemma oupd_notOver_data
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {Λ extraOverflow : ℝ} (ℓ' g' : ℕ → ℝ)
    (rem' idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ Λ extraOverflow stOrig st ℓ' g' (rem' + 1) idx curG curU curEncAcc)
    (hOver : ¬ intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    Nonempty (OupdNotOverData T TP P N₀ stOrig st ℓ' g' idx curG curU curEncAcc) := by
  have hidxLt : idx < P.d := by have := hLoop.hidxSum; omega
  have hLeThresh : ((st.updCount idx + curU.length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀ :=
    (Nat.cast_le.mpr (Nat.le_of_not_lt hOver)).trans (intRebuildThreshold_le_updateThreshold hTP N₀ idx)
  set Cpartial : TreeChain :=
    { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
  set ℓi := Cpartial.chainLen ℓ' idx
  set gi := Cpartial.chainGrad g' idx
  set ordNew := chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx
  set updRes := T.updateOrd (st.scState idx) curU ℓi gi ordNew
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
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ H.D H.ord H.restarts s).2
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
  set ord' : ℕ → ℕ → List End := fun s => if s ≤ Horig.len then Horig.ord s else ordNew
  set restarts' : ℕ → List ℕ := fun r => if r ≤ Horig.len then Horig.restarts r else []
  have hRestLt' : ∀ r ≤ Horig.len + 1, ∀ j ∈ restarts' r, j < P.k := by
    intro r _ j hj
    by_cases hr : r ≤ Horig.len
    · simp only [restarts', hr, ↓reduceIte] at hj
      exact Horig.hRestartsLt r hr j hj
    · simp [restarts', hr] at hj
  have hD'G0 : D'.G 0 = Horig.D.G 0 := by simp [D']
  have hD'ℓ0 : D'.ℓ 0 = Horig.D.ℓ 0 := by simp [D']
  have hD'Gend : D'.G Horig.len = stOrig.G idx := by simp [D', Horig.hEndG]
  have hD'Gnext : D'.G (Horig.len + 1) = curG := by simp [D']
  have hD'Unext : D'.U (Horig.len + 1) = curU := by simp [D']
  have hD'ℓnext : D'.ℓ (Horig.len + 1) = ℓi := by simp [D']
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
  have hD'Ord : OrderedUpTo D' (Horig.len + 1) 2 ord' := by
    obtain ⟨ρBefore, ρAfter, hBefore, hAfter, hBatch⟩ := hLoop.hCurOrd
    exact oupd_orderedUpTo_extend_one Horig.hOrd Horig.hEndG hLoop.hCurGEq
      (fun t ht => by simp [D', ht]) (by simp [D'])
      (fun t _ ht => by simp [D', ht]) (by simp [D'])
      (fun t ht => by simp [ord', ht]) (by simp [ord']; rfl)
      ρBefore ρAfter (hBefore.trans Horig.hEndOrd.symm) hAfter hBatch
  have hRunPre : ∀ s ≤ Horig.len,
      T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s =
        T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s := by
    intro s hs
    apply T.runOrdAfterUpdate_congr_lt P.k (levelM TP P idx) N₀ s
    · simp [D']
    · simp [D']
    · simp [D']
    · intro t _ hts
      have htl : t ≤ Horig.len := le_trans hts hs
      exact ⟨by simp [D', htl], by simp [D', htl], by simp [D', htl]⟩
    · intro t hts
      have htl : t ≤ Horig.len := le_trans hts hs
      simp [ord', htl]
    · intro t hts
      have htl : t ≤ Horig.len := le_trans (Nat.le_of_lt hts) hs
      simp [restarts', htl]
  have hRunPostPre : ∀ s ≤ Horig.len,
      T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' s =
        T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s := by
    intro s hs
    apply T.runOrdAfterRestarts_congr_le P.k (levelM TP P idx) N₀ s
    · simp [D']
    · simp [D']
    · simp [D']
    · intro t _ hts
      have htl : t ≤ Horig.len := le_trans hts hs
      exact ⟨by simp [D', htl], by simp [D', htl], by simp [D', htl]⟩
    · intro t hts
      have htl : t ≤ Horig.len := le_trans hts hs
      simp [ord', htl]
    · intro t hts
      have htl : t ≤ Horig.len := le_trans hts hs
      simp [restarts', htl]
  have hScIdxEq : st.scState idx = stOrig.scState idx := hLoop.hScGe idx (le_refl idx)
  have hRunNextPre :
      T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1) = updRes := by
    rw [T.runOrdAfterUpdate_succ P.k (levelM TP P idx) N₀ D' ord' restarts' Horig.len,
      hRunPostPre Horig.len (le_refl _), ← Horig.hRun, ← hScIdxEq]
    simp [D', ord', updRes]
  have hRunNextPost :
      T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1) = sc' := by
    simp only [SparseCoreRestartTool.runOrdAfterRestarts, restarts',
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
  have hSpec := Horig.hOK.noHidden P.k (Horig.len + 1) (levelM TP P idx) N₀ D' ord' restarts'
    P.hk (hD'G0 ▸ Horig.hG0) hD'Valid hD'Len hD'ℓPos hD'Ord
    (hD'G0 ▸ Horig.hInitMBound) (hD'G0 ▸ Horig.hInitNBound) hRestLt' hThresh'
    ⟨rfl, rfl, rfl, hD'G0, hD'ℓ0⟩
  have hBranIdx : st.bran idx < P.k := by
    rw [hLoop.hBran]; exact hInvOrig.hBran idx hidxLt
  have hS0Fresh' : Horig.s₀ = 0 ∨ st.bran idx ∈ restarts' Horig.s₀ := by
    simpa [restarts', Horig.hs₀, show st.bran idx = stOrig.bran idx from congrFun hLoop.hBran idx] using
      Horig.hS0Fresh
  have hNoRestAfter' : ∀ r, Horig.s₀ < r → r ≤ Horig.len + 1 → st.bran idx ∉ restarts' r := by
    intro r hr1 _
    by_cases hrle : r ≤ Horig.len
    · simpa [restarts', hrle, show st.bran idx = stOrig.bran idx from congrFun hLoop.hBran idx] using
        Horig.hNoRestartAfterS0 r hr1 hrle
    · simp [restarts', hrle]
  have hStep2 := hSpec.2.1 (Horig.len + 1) (by omega) (le_refl _) (st.bran idx) hBranIdx
  have hAtEndFull := hSpec.1 (Horig.len + 1) (le_refl _) (st.bran idx) hBranIdx
  have hRecEnd := hSpec.2.2.2.1 Horig.s₀ (Horig.len + 1) (Nat.le_succ_of_le Horig.hs₀)
    (le_refl _) (st.bran idx) hBranIdx hS0Fresh'
    (fun r hr1 hr2 => hNoRestAfter' r hr1 (Nat.le_of_lt hr2))
  have hOrdOut := hSpec.2.2.2.2.1 Horig.s₀ (Horig.len + 1) (Nat.le_succ_of_le Horig.hs₀)
    (le_refl _) (st.bran idx) hBranIdx hS0Fresh' hNoRestAfter'
  dsimp only at hStep2 hAtEndFull hRecEnd hOrdOut
  simp only [Nat.add_sub_cancel] at hStep2
  rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, ← hScIdxEq, hRunNextPre] at hStep2
  rw [hRunNextPost, hD'Gnext, hD'ℓnext] at hAtEndFull
  have hFiSub : newFiE ⊆ oldFiE := by
    simpa [newFiE, oldFiE, hRunNextPost] using hStep2.1
  have hFiLen : fiChanges.length = oldFiE.card - newFiE.card :=
    diffTreeChanges_length_of_subset hFiSub
  have hScCardLe : newFiE.card ≤ oldFiE.card := Finset.card_le_card hFiSub
  have hNextGValid : nextG.IsValid := by
    have hSp := hAtEndFull.2.1
    have hCore := coreGraph_isValid hLoop.hCurGValid hAtEndFull.1.2.1
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
  have hNextOrd : ∃ (ρBefore : Rotation (stOrig.G (idx + 1))) (ρAfter : Rotation nextG),
      ρBefore.order = stOrig.levelOrd (idx + 1) ∧
      ρAfter.order =
        chainLevelOrd T (fun j => if j = idx + 1 then nextG else stNext.G j)
          stNext.scState stNext.bran (idx + 1) ∧
      RotationBatch 2 nextU ρBefore (hNextG_eq ▸ ρAfter) := by
    let δ := Horig.len - Horig.s₀
    have hδLt : δ < Horig.len + 1 - Horig.s₀ := by have := Horig.hs₀; omega
    have hδ0 : Horig.s₀ + δ = Horig.len := by have := Horig.hs₀; omega
    have hδ1 : Horig.s₀ + (δ + 1) = Horig.len + 1 := by have := Horig.hs₀; omega
    have hG1 : (T.coreInstanceOrdFrom P.k (levelM TP P idx) N₀ D' ord' restarts' Horig.s₀
        (st.bran idx)).G δ = stOrig.G (idx + 1) := by
      dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom]
      rw [hδ0, hRunPostPre Horig.len (le_refl _), ← Horig.hRun,
        congrFun hLoop.hBran idx, ← hInvOrig.hGSucc idx hidxLt]
    have hG2 : (T.coreInstanceOrdFrom P.k (levelM TP P idx) N₀ D' ord' restarts' Horig.s₀
        (st.bran idx)).G (δ + 1) = nextG := by
      dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom]
      rw [hδ1, hRunNextPost]
    have hU1 : (T.coreInstanceOrdFrom P.k (levelM TP P idx) N₀ D' ord' restarts' Horig.s₀
        (st.bran idx)).U (δ + 1) = nextU := by
      dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom]
      rw [hδ1, hRunNextPre]
    obtain ⟨ρ1, ρ2, hρ1, hρ2, hb⟩ :=
      oupd_orderedUpTo_step_extract hOrdOut hδLt hG1 hG2 hU1 hNextG_eq
    refine ⟨ρ1, ρ2, ?_, ?_, hb⟩
    · rw [hρ1, hδ0, hRunPostPre Horig.len (le_refl _), ← Horig.hRun, congrFun hLoop.hBran idx]
      rfl
    · rw [hρ2, hδ1, hRunNextPost]
      simp [chainLevelOrd, stNext]
  have hUpdIdx : stNext.updCount idx = st.updCount idx + curU.length := by simp [stNext]
  have hGIdx : stNext.G idx = curG := by simp [stNext]
  have hScIdx : stNext.scState idx = sc' := by simp [stNext]
  have hDecIdx : stNext.curDecUpdates idx = st.curDecUpdates idx + fiChanges.length := by
    simp [stNext]
  have hCurFwdIdx : stNext.curFwd idx = st.curFwd idx + nextU.length := by simp [stNext]
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
  have hEndOrdEq : ord' (Horig.len + 1) =
      ({ stNext with ℓ := ℓ', g := g' } : ChainState T P).levelOrd idx := by
    simp only [ord', Nat.not_succ_le_self, ↓reduceIte]
    unfold ChainState.levelOrd chainLevelOrd
    by_cases h0 : idx = 0
    · subst h0; simp [ordNew, chainLevelOrd, stNext]
    · have hne : idx - 1 ≠ idx := by omega
      simp [ordNew, chainLevelOrd, h0, stNext, hne]
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
          (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (s - 1))
            (({ stNext with ℓ := ℓ', g := g' } : ChainState T P).bran idx)).batchEnc
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
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
          (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (s - 1))
            (stNext.bran idx)).batchEnc
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (stNext.bran idx))) =
        (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
          (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts (s - 1))
            (stOrig.bran idx)).batchEnc
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
              (stOrig.bran idx))) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl := (Finset.mem_Icc.mp hs).2
      rw [hRunPostPre (s - 1) (by omega), hRunPre s hsl]
      have hBr := congrFun hLoop.hBran idx
      change (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts (s - 1))
            (st.bran idx)).batchEnc
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
            (st.bran idx)) = _
      rw [hBr]
    have hLastTerm : (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' Horig.len)
            (stNext.bran idx)).batchEnc
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1)).2
            (stNext.bran idx)) = nextEnc := by
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
        (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (s - 1))
          (stNext.bran idx)).batchEnc
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (stNext.bran idx))
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
        ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (branchSeq' s)).length : ℕ) : ℝ) ≤
        TP.γ_r (P.M₀ ^ 2) * (((Finset.Icc 1 Horig.s₀).sum fun s => (D'.U s).length : ℕ) : ℝ) := by
    have hL1 : (Finset.Icc 1 Horig.s₀).sum (fun s =>
        ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (branchSeq' s)).length) =
        (Finset.Icc 1 Horig.s₀).sum (fun s =>
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
            (Horig.branchSeq s)).length) := by
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
        ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (branchSeq' s)).length := by
    change stNext.curFwd idx = _
    rw [hCurFwdIdx, Finset.sum_Icc_one_succ]
    have hpre : (Finset.Icc 1 Horig.len).sum (fun s =>
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2 (branchSeq' s)).length) =
        stOrig.curFwd idx := by
      rw [Horig.hCurFwdEq]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl := (Finset.mem_Icc.mp hs).2
      rw [hRunPre s hsl]
      simp [branchSeq', hsl]
    have hlast : ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1)).2
          (branchSeq' (Horig.len + 1))).length = nextU.length := by
      rw [hRunNextPre]
      simp [branchSeq', nextU, U_S]
    rw [hpre, hlast, hLoop.hCurFwdGe idx (le_refl idx)]
  let hHidxNew : LevelHistory T TP P N₀ { stNext with ℓ := ℓ', g := g' } idx := {
    D := D', len := Horig.len + 1, s₀ := Horig.s₀, hs₀ := Nat.le_succ_of_le Horig.hs₀,
    restarts := restarts', hRestartsLt := hRestLt', hRestartsCount := hRestCount',
    hS0Fresh := by simpa [stNext] using hS0Fresh',
    hNoRestartAfterS0 := fun r hr1 hr2 => by simpa [stNext] using hNoRestAfter' r hr1 hr2,
    hG0 := hD'G0 ▸ Horig.hG0, hD := hD'Valid, hLen := hD'Len, hℓPos := hD'ℓPos,
    hEndG := by simp [D', hGIdx],
    hEndℓ := fun e _ => by rw [hCL]; simp [D'],
    hEndg := by rw [hCG]; simp [D'],
    hUpd := by rw [hUpdIdx]; exact hUpdSum',
    hThresh := by rw [hUpdIdx]; exact hLeThresh,
    hInitMBound := by rw [hD'G0]; exact Horig.hInitMBound,
    hInitNBound := by rw [hD'G0]; exact Horig.hInitNBound,
    ord := ord', hOrd := hD'Ord, hEndOrd := hEndOrdEq,
    hRun := by rw [hScIdx, hRunNextPost],
    hOK := by rw [hD'G0, hD'ℓ0]; exact Horig.hOK,
    branchSeq := branchSeq',
    hBranch := hBranSeqLt,
    hBranchTail := hBranTail',
    hWinFwdBound := hWinFwd',
    hCurFwdEq := hCurFwdEq,
    hDecEq := by
      rw [hDecIdx, hScIdx, hBranEq, hRunPostPre Horig.s₀ Horig.hs₀]
      have hOrigDec := Horig.hDecEq
      rw [← hLoop.hDecGe idx (le_refl idx), ← hLoop.hScGe idx (le_refl idx),
        ← congrFun hLoop.hBran idx] at hOrigDec
      change st.curDecUpdates idx + fiChanges.length + newFiE.card = _
      rw [hFiLen]
      have hSubEq : oldFiE.card - newFiE.card + newFiE.card = oldFiE.card := Nat.sub_add_cancel hScCardLe
      rw [add_assoc, hSubEq]
      exact hOrigDec
    hEnc0Le := hEnc0Le_prf
    hEncLe := hEncLe_prf }
  exact ⟨{
    sc' := sc', U_S := U_S, fiChanges := fiChanges, nextG := nextG, nextU := nextU,
    nextEnc := nextEnc, stNext := stNext, Horig := Horig, D' := D', ord' := ord',
    restarts' := restarts', branchSeq' := branchSeq', hHidxNew := hHidxNew,
    hHidxFields := ⟨rfl, rfl, rfl, rfl, rfl⟩,
    hSc'Eq := rfl, hUSEq := rfl, hFiEq := rfl, hNextGEqDef := rfl, hNextUEqDef := rfl,
    hNextEncDef := rfl, hStNextEq := rfl, hD'G0 := hD'G0, hD'Gend := hD'Gend,
    hD'Gnext := hD'Gnext, hD'Unext := hD'Unext, hD'Valid := hD'Valid, hD'Len := hD'Len,
    hD'ℓPos := hD'ℓPos, hD'Ord := hD'Ord, hRestLt' := hRestLt', hRunPre := hRunPre,
    hRunPostPre := hRunPostPre, hRunNextPre := hRunNextPre, hRunNextPost := hRunNextPost,
    hUpdSum' := hUpdSum', hThresh' := hThresh', hBranIdx := hBranIdx,
    hBranTail' := hBranTail', hWinFwd' := hWinFwd', hCurFwdEq := hCurFwdEq,
    hRebOrig := hRebOrig, hAtEnd := ⟨hAtEndFull.1, hAtEndFull.2.1⟩,
    hWstrStep := fun e he1 he2 hno => by
      have hW := hStep2.2.1 e he1 he2 hno
      rwa [hRunNextPost] at hW,
    hRecEnd := hRecEnd, hNextGValid := hNextGValid, hNextG_eq := hNextG_eq,
    hNextGBatch := hNextGBatch, hNextOrd := hNextOrd }⟩

end OupdNotOver

end MinCostFlow.Chain.Ordered
