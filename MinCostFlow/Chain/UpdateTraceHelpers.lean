module

public import MinCostFlow.Chain.HiddenTraceShift

/-!
# Helpers for `updateLoop` history extension (`MinCostFlow/Chain/UpdateTraceHelpers`)

Provides `extendDyn`, `runAfterUpdate_extendDyn_prefix`, `runAfterRestarts_extendDyn_prefix`,
`levelHistory_congr_state`, `extendLevelHistory`, and `ChainCoreRel`, shared by `UpdateTrace`
and `Lemma6_5`.
-/

@[expose] public section

namespace MinCostFlow.Chain

def extendDyn (D : DynamicInstance) (len : ℕ) (Unew : List Update)
    (Gnew : MGraph) (ℓnew gnew : ℕ → ℝ) : DynamicInstance where
  G := fun s => if s ≤ len then D.G s else Gnew
  U := fun s => if s ≤ len then D.U s else if s = len + 1 then Unew else []
  ℓ := fun s => if s ≤ len then D.ℓ s else ℓnew
  g := fun s => if s ≤ len then D.g s else gnew

lemma runAfterUpdate_extendDyn_prefix (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) (len : ℕ) (Unew : List Update) (Gnew : MGraph) (ℓnew gnew : ℕ → ℝ) :
    ∀ s ≤ len, T.runAfterUpdate k M N (extendDyn D len Unew Gnew ℓnew gnew)
      (fun r => if r ≤ len then restarts r else []) s = T.runAfterUpdate k M N D restarts s := by
  intro s hs
  exact T.runAfterUpdate_congr_lt k M N s (by simp [extendDyn]) (by simp [extendDyn]) (by simp [extendDyn])
    (fun s' _ hs' => by
      have hle : s' ≤ len := le_trans hs' hs
      simp [extendDyn, hle])
    (fun r hr => by
      have hle : r ≤ len := le_trans (Nat.le_of_lt hr) hs
      simp [hle])

lemma runAfterRestarts_extendDyn_prefix (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) (len : ℕ) (Unew : List Update) (Gnew : MGraph) (ℓnew gnew : ℕ → ℝ) :
    ∀ s ≤ len, T.runAfterRestarts k M N (extendDyn D len Unew Gnew ℓnew gnew)
      (fun r => if r ≤ len then restarts r else []) s = T.runAfterRestarts k M N D restarts s := by
  intro s hs
  exact T.runAfterRestarts_congr_le k M N s (by simp [extendDyn]) (by simp [extendDyn]) (by simp [extendDyn])
    (fun s' _ hs' => by
      have hle : s' ≤ len := le_trans hs' hs
      simp [extendDyn, hle])
    (fun r hr => by
      have hle : r ≤ len := le_trans hr hs
      simp [hle])

noncomputable def levelHistory_congr_state {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ} {ch₁ ch₂ : ChainState T P} {k : ℕ} (_hk : k < P.d)
    (H : LevelHistory T TP P N₀ ch₁ k)
    (hG : ∀ j ≤ k, ch₂.G j = ch₁.G j)
    (hSc : ch₂.scState k = ch₁.scState k)
    (hRest : ch₂.curRestarts k = ch₁.curRestarts k)
    (hAct : ∀ j < k, ch₂.toTreeChain.activeLSF j = ch₁.toTreeChain.activeLSF j)
    (hℓ : ch₂.ℓ = ch₁.ℓ) (hg : ch₂.g = ch₁.g)
    (hUpd : ch₂.updCount k = ch₁.updCount k)
    (hCurFwd : ch₂.curFwd k = ch₁.curFwd k)
    (hBr : ch₂.bran k = ch₁.bran k)
    (hDec : ch₂.curDecUpdates k = ch₁.curDecUpdates k)
    (hEnc0 : k = 0 → ch₂.curEnc 0 = ch₁.curEnc 0)
    (hEncNext : k + 1 < P.d → ch₂.curEnc (k + 1) ≤ ch₁.curEnc (k + 1)) :
    LevelHistory T TP P N₀ ch₂ k where
  D := H.D
  len := H.len
  s₀ := H.s₀
  hs₀ := H.hs₀
  restarts := H.restarts
  hRestartsLt := H.hRestartsLt
  hRestartsCount := by rw [hRest]; exact H.hRestartsCount
  hS0Fresh := by rw [hBr]; exact H.hS0Fresh
  hNoRestartAfterS0 := by rw [hBr]; exact H.hNoRestartAfterS0
  hG0 := H.hG0
  hD := H.hD
  hLen := H.hLen
  hℓPos := H.hℓPos
  hEndG := by rw [hG k (le_refl k)]; exact H.hEndG
  hEndℓ := fun e he => by
    have he1 : e ∈ (ch₁.G k).E := by rwa [← hG k (le_refl k)]
    rw [hℓ, chainLen_congr_lt (C₁ := ch₂.toTreeChain) (C₂ := ch₁.toTreeChain) ch₁.ℓ k
      (fun j hj => hG j (le_of_lt hj)) hAct]
    exact H.hEndℓ e he1
  hEndg := by
    rw [hg, chainGrad_congr_lt (C₁ := ch₂.toTreeChain) (C₂ := ch₁.toTreeChain) ch₁.g k
      (fun j hj => hG j (le_of_lt hj)) hAct]
    exact H.hEndg
  hUpd := by rw [hUpd]; exact H.hUpd
  hThresh := by rw [hUpd]; exact H.hThresh
  hInitMBound := H.hInitMBound
  hInitNBound := H.hInitNBound
  hRun := by rw [hSc]; exact H.hRun
  branchSeq := H.branchSeq
  hBranch := H.hBranch
  hBranchTail := by rw [hBr]; exact H.hBranchTail
  hWinFwdBound := H.hWinFwdBound
  hCurFwdEq := by rw [hCurFwd]; exact H.hCurFwdEq
  hDecEq := by rw [hDec, hSc, hBr]; exact H.hDecEq
  hEnc0Le := fun h0 => by rw [hEnc0 h0]; exact H.hEnc0Le h0
  hEncLe := fun h1 => by rw [hBr]; exact le_trans (hEncNext h1) (H.hEncLe h1)

noncomputable def extendLevelHistory {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ} (_hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (_hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {ch0 ch1 : ChainState T P} {idx : ℕ} (_hidx : idx < P.d)
    (Horig : LevelHistory T TP P N₀ ch0 idx)
    (curU : List Update) (curG : MGraph) (ℓi gi : ℕ → ℝ)
    (hG0eq : curG = (ch0.G idx).applyBatch curU)
    (hBatch : (ch0.G idx).BatchIsValid curU)
    (_hCurGValid : curG.IsValid)
    (hEndG1 : ch1.G idx = curG)
    (hℓEq : ℓi = ch1.toTreeChain.chainLen ch1.ℓ idx)
    (hgEq : gi = ch1.toTreeChain.chainGrad ch1.g idx)
    (hCurLenPos : ∀ e ∈ curG.E, 0 < ℓi e)
    (hCurLenStable : ∀ e ∈ curG.E, e ∈ (ch0.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
      ℓi e = ch0.toTreeChain.chainLen ch0.ℓ idx e)
    (hUpd1 : ch1.updCount idx = ch0.updCount idx + curU.length)
    (hThresh1 : ((ch1.updCount idx : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀)
    (hCurFwd1 : ch1.curFwd idx = ch0.curFwd idx + ((T.update (ch0.scState idx) curU ℓi gi).2 (ch0.bran idx)).length)
    (hSc1 : ch1.scState idx = (T.update (ch0.scState idx) curU ℓi gi).1)
    (hRest1 : ch1.curRestarts idx = ch0.curRestarts idx)
    (hBr1 : ch1.bran idx = ch0.bran idx)
    (hBrLt : ch0.bran idx < P.k)
    (hDec1 : ch1.curDecUpdates idx = ch0.curDecUpdates idx +
      (diffTreeChanges ((T.lsfs (ch0.scState idx) (ch0.bran idx)).F.F.E)
        ((T.lsfs (T.update (ch0.scState idx) curU ℓi gi).1 (ch0.bran idx)).F.F.E)).length)
    (hEnc0Le1 : idx = 0 → ch1.curEnc 0 ≤ ch0.curEnc 0 + (ch0.G 0).batchEnc curU)
    (hEncLe1 : idx + 1 < P.d → ch1.curEnc (idx + 1) ≤ ch0.curEnc (idx + 1) +
      (T.S (ch0.scState idx) (ch0.bran idx)).batchEnc
        ((T.update (ch0.scState idx) curU ℓi gi).2 (ch0.bran idx))) :
    LevelHistory T TP P N₀ ch1 idx :=
  let D' := extendDyn Horig.D Horig.len curU curG
    (ch1.toTreeChain.chainLen ch1.ℓ idx) (ch1.toTreeChain.chainGrad ch1.g idx)
  let restarts' : ℕ → List ℕ := fun r => if r ≤ Horig.len then Horig.restarts r else []
  have hRestLt' : ∀ r ≤ Horig.len + 1, ∀ j ∈ restarts' r, j < P.k := fun r _ j hj => by
    dsimp only [restarts'] at hj
    split_ifs at hj with hr
    · exact Horig.hRestartsLt r hr j hj
    · contradiction
  have hD'G0 : D'.G 0 = Horig.D.G 0 := by simp [D', extendDyn]
  have hRunPre : ∀ s ≤ Horig.len,
      T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s =
        T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s :=
    runAfterUpdate_extendDyn_prefix T P.k (levelM TP P idx) N₀ Horig.D Horig.restarts Horig.len curU curG _ _
  have hRunPostPre : ∀ s ≤ Horig.len,
      T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' s =
        T.runAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s :=
    runAfterRestarts_extendDyn_prefix T P.k (levelM TP P idx) N₀ Horig.D Horig.restarts Horig.len curU curG _ _
  have hRunNextPre : T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1) =
      T.update (ch0.scState idx) curU ℓi gi := by
    rw [T.runAfterUpdate_succ P.k (levelM TP P idx) N₀ D' restarts' Horig.len,
      hRunPostPre Horig.len (le_refl _), ← Horig.hRun]
    simp [D', extendDyn, hℓEq, hgEq]
  have hRunNextPost : T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1) =
      (T.update (ch0.scState idx) curU ℓi gi).1 := by
    simp only [SparseCoreRestartTool.runAfterRestarts, restarts',
      show ¬ (Horig.len + 1 ≤ Horig.len) by omega, ↓reduceIte, List.foldl_nil, hRunNextPre]
  have hUpdSum' : (Finset.Icc 1 (Horig.len + 1)).sum (fun s => (D'.U s).length) =
      ch0.updCount idx + curU.length := by
    rw [Finset.sum_Icc_succ_top (Nat.succ_pos Horig.len)]
    have hPre : (Finset.Icc 1 Horig.len).sum (fun s => (D'.U s).length) = ch0.updCount idx := by
      rw [← Horig.hUpd]
      refine Finset.sum_congr rfl fun s hs => ?_
      simp [D', extendDyn, (Finset.mem_Icc.mp hs).2]
    rw [hPre]; simp [D', extendDyn]
  have hD'Valid : D'.IsValid (Horig.len + 1) := by
    intro s hs1 _
    by_cases hs : s ≤ Horig.len
    · have hs' : s - 1 ≤ Horig.len := by omega
      have hv := Horig.hD s hs1 hs
      refine ⟨?_, ?_⟩ <;> simp only [D', extendDyn, hs, hs', ↓reduceIte]
      · exact hv.1
      · exact hv.2
    · have hseq : s = Horig.len + 1 := by omega
      subst hseq
      refine ⟨?_, ?_⟩
      · simp only [D', extendDyn, Nat.add_sub_cancel, le_refl, ↓reduceIte, Nat.not_succ_le_self,
          Horig.hEndG]
        exact hBatch
      · simp only [D', extendDyn, Nat.add_sub_cancel, le_refl, ↓reduceIte, Nat.not_succ_le_self,
          Horig.hEndG]
        exact hG0eq
  have hD'Len : LengthsStable D' (Horig.len + 1) := by
    intro s hs1 _ e heS hePrev hNoI
    by_cases hs : s ≤ Horig.len
    · have hs' : s - 1 ≤ Horig.len := by omega
      simpa [D', extendDyn, hs, hs'] using Horig.hLen s hs1 hs e
        (by simpa [D', extendDyn, hs] using heS)
        (by simpa [D', extendDyn, hs'] using hePrev)
        (fun u hu => hNoI u (by simpa [D', extendDyn, hs] using hu))
    · have hseq : s = Horig.len + 1 := by omega
      subst hseq
      simp only [D', extendDyn, Nat.add_sub_cancel, le_refl, ↓reduceIte,
        Nat.not_succ_le_self, Horig.hEndG] at heS hePrev hNoI ⊢
      rw [Horig.hEndℓ e hePrev, ← hℓEq]
      exact hCurLenStable e heS hePrev hNoI
  have hD'ℓPos : ∀ s ≤ Horig.len + 1, ∀ e ∈ (D'.G s).E, 0 < D'.ℓ s e := by
    intro s _ e he
    by_cases hsl : s ≤ Horig.len
    · simp only [D', extendDyn, hsl, ↓reduceIte] at he ⊢; exact Horig.hℓPos s hsl e he
    · simp only [D', extendDyn, hsl, ↓reduceIte, ← hℓEq] at he ⊢; exact hCurLenPos e he
  have hSpec := hT P.k (Horig.len + 1) (levelM TP P idx) N₀ D' restarts' P.hk
    (hD'G0 ▸ Horig.hG0) hD'Valid hD'Len hD'ℓPos
    (hD'G0 ▸ Horig.hInitMBound) (hD'G0 ▸ Horig.hInitNBound) hRestLt'
    (by
      rw [hUpdSum', ← hUpd1]
      exact hThresh1)
  { D := D'
    len := Horig.len + 1
    s₀ := Horig.s₀
    hs₀ := Nat.le_succ_of_le Horig.hs₀
    restarts := restarts'
    hRestartsLt := hRestLt'
    hRestartsCount := by
      rw [Finset.sum_range_succ]
      have hPreSum : (Finset.range (Horig.len + 1)).sum (fun r => (restarts' r).length) =
          (Finset.range (Horig.len + 1)).sum (fun r => (Horig.restarts r).length) :=
        Finset.sum_congr rfl fun r hr => by
          simp [restarts', Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)]
      rw [hPreSum, show (restarts' (Horig.len + 1)).length = 0 by simp [restarts'], add_zero,
        Horig.hRestartsCount, hRest1]
    hS0Fresh := by
      simpa [hBr1, restarts', Horig.hs₀] using Horig.hS0Fresh
    hNoRestartAfterS0 := fun r hr1 hr2 => by
      by_cases hrle : r ≤ Horig.len
      · simpa [hBr1, restarts', hrle] using Horig.hNoRestartAfterS0 r hr1 hrle
      · simp [restarts', hrle]
    hG0 := hD'G0 ▸ Horig.hG0
    hD := hD'Valid
    hLen := hD'Len
    hℓPos := hD'ℓPos
    hEndG := by simp [D', extendDyn, hEndG1]
    hEndℓ := fun _ _ => by simp [D', extendDyn]
    hEndg := by simp [D', extendDyn]
    hUpd := by rw [hUpd1]; exact hUpdSum'
    hThresh := hThresh1
    hInitMBound := Horig.hInitMBound
    hInitNBound := Horig.hInitNBound
    hRun := by rw [hSc1, hRunNextPost]
    branchSeq := fun s => if s ≤ Horig.len then Horig.branchSeq s else ch0.bran idx
    hBranch := fun s => by
      by_cases hs : s ≤ Horig.len
      · simp [hs, Horig.hBranch s]
      · simp [hs, hBrLt]
    hBranchTail := fun s hs1 hs2 => by
      rw [hBr1]
      by_cases hsl : s ≤ Horig.len
      · simp [hsl, Horig.hBranchTail s hs1 hsl]
      · simp [hsl]
    hWinFwdBound := by
      have hIccSplit : Finset.Icc 1 (Horig.len + 1) =
          Finset.Icc 1 Horig.len ∪ Finset.Icc (Horig.len + 1) (Horig.len + 1) := by
        ext s; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hsub1 : (Finset.Icc 1 Horig.s₀).sum (fun s =>
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2
              (if s ≤ Horig.len then Horig.branchSeq s else ch0.bran idx)).length) =
          (Finset.Icc 1 Horig.s₀).sum (fun s =>
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (Horig.branchSeq s)).length) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := le_trans (Finset.mem_Icc.mp hs).2 Horig.hs₀
        simp only [hsl, ↓reduceIte, hRunPre s hsl]
      have hsub2 : (Finset.Icc 1 Horig.s₀).sum (fun s => (D'.U s).length) =
          (Finset.Icc 1 Horig.s₀).sum (fun s => (Horig.D.U s).length) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := le_trans (Finset.mem_Icc.mp hs).2 Horig.hs₀
        simp [D', extendDyn, hsl]
      rw [hsub1, hsub2]
      exact Horig.hWinFwdBound
    hCurFwdEq := by
      rw [hCurFwd1, Horig.hCurFwdEq]
      rw [Finset.sum_Icc_succ_top (Nat.succ_pos Horig.len)]
      have hPreFwd : (Finset.Icc 1 Horig.len).sum (fun s =>
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2
              (if s ≤ Horig.len then Horig.branchSeq s else ch0.bran idx)).length) =
          (Finset.Icc 1 Horig.len).sum (fun s =>
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (Horig.branchSeq s)).length) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := (Finset.mem_Icc.mp hs).2
        simp only [hsl, ↓reduceIte, hRunPre s hsl]
      have hLastFwd :
          ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1)).2
            (if Horig.len + 1 ≤ Horig.len then Horig.branchSeq (Horig.len + 1) else ch0.bran idx)).length =
          ((T.update (ch0.scState idx) curU ℓi gi).2 (ch0.bran idx)).length := by
        simp only [Nat.not_succ_le_self, ↓reduceIte, hRunNextPre]
      rw [hPreFwd, hLastFwd]
    hDecEq := by
      have hSub := (hSpec.2.1 (Horig.len + 1) (Nat.succ_pos _)
        (le_refl _) (ch0.bran idx) hBrLt).1
      simp only [Nat.add_sub_cancel, hRunPostPre Horig.len (le_refl _), ← Horig.hRun,
        hRunNextPost] at hSub
      have hLenEq : (diffTreeChanges ((T.lsfs (ch0.scState idx) (ch0.bran idx)).F.F.E)
          ((T.lsfs (T.update (ch0.scState idx) curU ℓi gi).1 (ch0.bran idx)).F.F.E)).length =
          (T.lsfs (ch0.scState idx) (ch0.bran idx)).F.F.E.card -
          (T.lsfs (T.update (ch0.scState idx) curU ℓi gi).1 (ch0.bran idx)).F.F.E.card :=
        diffTreeChanges_length_of_subset hSub
      rw [hDec1, hLenEq, hSc1, hBr1]
      rw [add_assoc, Nat.sub_add_cancel (Finset.card_le_card hSub), hRunPostPre Horig.s₀ Horig.hs₀]
      exact Horig.hDecEq
    hEnc0Le := fun h0 => by
      subst h0
      refine le_trans (hEnc0Le1 rfl) ?_
      rw [Finset.sum_Icc_succ_top (Nat.succ_pos Horig.len)]
      have hPre : (Finset.Icc 1 Horig.len).sum (fun s => (D'.G (s - 1)).batchEnc (D'.U s)) =
          (Finset.Icc 1 Horig.len).sum (fun s => (Horig.D.G (s - 1)).batchEnc (Horig.D.U s)) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := (Finset.mem_Icc.mp hs).2
        have hsl' : s - 1 ≤ Horig.len := by omega
        simp [D', extendDyn, hsl, hsl']
      have hLast : (D'.G (Horig.len + 1 - 1)).batchEnc (D'.U (Horig.len + 1)) =
          (ch0.G 0).batchEnc curU := by
        simp [D', extendDyn, Horig.hEndG]
      rw [hPre, hLast]
      exact Nat.add_le_add_right (Horig.hEnc0Le rfl) _
    hEncLe := fun h1 => by
      refine le_trans (hEncLe1 h1) ?_
      have hs0 := Horig.hs₀
      have hIcc : Finset.Icc (Horig.s₀ + 1) (Horig.len + 1) =
          insert (Horig.len + 1) (Finset.Icc (Horig.s₀ + 1) Horig.len) := by
        ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hNotMem : Horig.len + 1 ∉ Finset.Icc (Horig.s₀ + 1) Horig.len :=
        fun h => Nat.not_succ_le_self Horig.len (Finset.mem_Icc.mp h).2
      rw [hIcc, Finset.sum_insert hNotMem, hBr1]
      have hSumPre : (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
            (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (s - 1)) (ch0.bran idx)).batchEnc
              ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' s).2 (ch0.bran idx))) =
          (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
            (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.restarts (s - 1)) (ch0.bran idx)).batchEnc
              ((T.runAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.restarts s).2 (ch0.bran idx))) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := (Finset.mem_Icc.mp hs).2
        have hsl' : s - 1 ≤ Horig.len := by omega
        rw [hRunPre s hsl, hRunPostPre (s - 1) hsl']
      have hLast : (T.S (T.runAfterRestarts P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1 - 1)) (ch0.bran idx)).batchEnc
            ((T.runAfterUpdate P.k (levelM TP P idx) N₀ D' restarts' (Horig.len + 1)).2 (ch0.bran idx)) =
          (T.S (ch0.scState idx) (ch0.bran idx)).batchEnc
            ((T.update (ch0.scState idx) curU ℓi gi).2 (ch0.bran idx)) := by
        simp only [Nat.add_sub_cancel]
        rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, hRunNextPre]
      rw [hSumPre, hLast, add_comm]
      exact Nat.add_le_add_left (Horig.hEncLe h1) _ }

def ChainCoreRel (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams) {N₀ : ℕ}
    (ch : ChainState T P) (H : ∀ k < P.d, LevelHistory T TP P N₀ ch k) : Prop :=
  ∀ k (hk : k + 1 < P.d),
    let Hk := H k (Nat.lt_of_succ_lt hk)
    let Hk1 := H (k + 1) hk
    Hk1.len ≤ Hk.len ∧
    let off := Hk.len - Hk1.len
    Hk.s₀ ≤ off ∧
    (∀ δ ≤ Hk1.len,
      Hk1.D.G δ =
        (T.coreInstanceFrom P.k (levelM TP P k) N₀ Hk.D Hk.restarts Hk.s₀ (ch.bran k)).G
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ, 1 ≤ δ → δ ≤ Hk1.len →
      Hk1.D.U δ =
        (T.coreInstanceFrom P.k (levelM TP P k) N₀ Hk.D Hk.restarts Hk.s₀ (ch.bran k)).U
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ ≤ Hk1.len, ∀ e ∈ (Hk1.D.G δ).E,
      Hk1.D.ℓ δ e =
        (T.coreInstanceFrom P.k (levelM TP P k) N₀ Hk.D Hk.restarts Hk.s₀ (ch.bran k)).ℓ
          ((off - Hk.s₀) + δ) e)

end MinCostFlow.Chain
