module

public import MinCostFlow.Chain.Ordered.Traces
public import MinCostFlow.Chain.Ordered.BudgetHelpers
public import MinCostFlow.Chain.Ordered.BudgetHelpersCost
public import MinCostFlow.Chain.Ordered.RebuildSuffix
public import MinCostFlow.Chain.Ordered.InitPreserves
public import MinCostFlow.Chain.Ordered.ShiftPreserves
public import MinCostFlow.Chain.Ordered.UpdateProofs
public import MinCostFlow.Chain.Ordered.FindCycleProofs
public import MinCostFlow.Chain.Ordered.Lemma5_11
public import MinCostFlow.Chain.Ordered.LevelConnected
public import MinCostFlow.Chain.Ordered.Algorithm2Uncond
public import MinCostFlow.Chain.Ordered.HiddenTraceSteps
public import MinCostFlow.Chain.Ordered.HiddenTraceShift
public import MinCostFlow.Chain.UpdateTraceHelpers
public import MinCostFlow.Chain.UpdatePreLoopHelpers

/-!
# Helpers for ordered `updateLoop` history extension (`MinCostFlow/Chain/Ordered/UpdateTraceHelpers`)

Provides the ordered counterparts of `MinCostFlow/Chain/UpdateTraceHelpers.lean` (`U3.extendOrd`,
`runOrdAfterUpdate_extendDyn_prefix`, `runOrdAfterRestarts_extendDyn_prefix`,
`levelHistory_congr_state`, `extendLevelHistory`, and `ChainCoreRel` with the output-order
clause) and rotation-transport helpers.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

namespace U3

/-! ### Order extension and rotation transport helpers -/

/-- Extend a stage-indexed order sequence `ord` past `len` by a new order `ordNew`. -/
def extendOrd (ord : ℕ → ℕ → List End) (len : ℕ) (ordNew : ℕ → List End) :
    ℕ → ℕ → List End :=
  fun s => if s ≤ len then ord s else ordNew

lemma rotation_ext {G : MGraph} {ρ₁ ρ₂ : Rotation G} (h : ρ₁.order = ρ₂.order) : ρ₁ = ρ₂ := by
  cases ρ₁
  cases ρ₂
  simp only at h
  subst h
  rfl

lemma rotation_cast_order {G₁ G₂ : MGraph} (hG : G₁ = G₂) (ρ : Rotation G₁) :
    (hG ▸ ρ).order = ρ.order := by
  subst hG
  rfl

lemma rotationBatch_cast {β : ℕ} {G₁ G₂ G₁' G₂' : MGraph} {U₁ U₂ : List Update}
    (hG : G₁ = G₂) (hU : U₁ = U₂)
    (h1 : G₁' = G₁.applyBatch U₁) (h2 : G₂' = G₂.applyBatch U₂)
    {ρ₁ : Rotation G₁} {ρ₂ : Rotation G₂}
    {σ₁ : Rotation G₁'} {σ₂ : Rotation G₂'}
    (hρ : ρ₁.order = ρ₂.order) (hσ : σ₁.order = σ₂.order)
    (hB : RotationBatch β U₁ ρ₁ (h1 ▸ σ₁)) :
    RotationBatch β U₂ ρ₂ (h2 ▸ σ₂) := by
  subst hG
  subst hU
  subst h1
  subst h2
  have hρeq : ρ₁ = ρ₂ := rotation_ext hρ
  have hσeq : σ₁ = σ₂ := rotation_ext hσ
  subst hρeq
  subst hσeq
  exact hB

/-- Any graph `D.G 0` carrying a rotation with order `ord 0` satisfies `OrderedUpTo D 0 2 ord`. -/
lemma orderedUpTo_zero_of_rotation {D : DynamicInstance} {ord : ℕ → ℕ → List End}
    (hConst : ∀ t, D.G t = D.G 0)
    (hRot : ∃ ρ : Rotation (D.G 0), ρ.order = ord 0) :
    OrderedUpTo D 0 2 ord := by
  obtain ⟨ρ₀, hρ₀⟩ := hRot
  refine ⟨fun t => (hConst t).symm ▸ ρ₀, ?_, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  intro t ht
  have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
  subst ht0
  exact hρ₀

/-- Extend `OrderedUpTo D len 2 ord` by one batch `curU` whose transition is a `RotationBatch 2`. -/
lemma orderedUpTo_extend_step {D : DynamicInstance} {len : ℕ} {ord : ℕ → ℕ → List End}
    (hOrd : OrderedUpTo D len 2 ord)
    (curU : List Update) (curG : MGraph) (ℓnew gnew : ℕ → ℝ) (ordNew : ℕ → List End)
    (hStepG : curG = (D.G len).applyBatch curU)
    (hStepOrd : ∃ (ρPrev : Rotation (D.G len)) (ρNew : Rotation curG),
      ρPrev.order = ord len ∧ ρNew.order = ordNew ∧ RotationBatch 2 curU ρPrev (hStepG ▸ ρNew)) :
    OrderedUpTo (extendDyn D len curU curG ℓnew gnew) (len + 1) 2 (extendOrd ord len ordNew) := by
  obtain ⟨ρ₀, hρ₀_ord, hρ₀_step⟩ := hOrd
  obtain ⟨ρPrev, ρNew, hρPrev, hρNew, hRB⟩ := hStepOrd
  let D' := extendDyn D len curU curG ℓnew gnew
  let ord' := extendOrd ord len ordNew
  let ρ' : ∀ t, Rotation (D'.G t) := fun t =>
    if ht : t ≤ len then
      (show D.G t = D'.G t by simp [D', extendDyn, ht]) ▸ ρ₀ t
    else
      (show curG = D'.G t by simp [D', extendDyn, ht]) ▸ ρNew
  have hρ'_ord : ∀ t ≤ len + 1, (ρ' t).order = ord' t := by
    intro t _
    by_cases ht : t ≤ len
    · simp only [ρ', ht, ↓reduceDIte, ord', extendOrd, ↓reduceIte]
      rw [rotation_cast_order, hρ₀_ord t ht]
    · simp only [ρ', ht, ↓reduceDIte, ord', extendOrd, ↓reduceIte]
      rw [rotation_cast_order, hρNew]
  refine ⟨ρ', hρ'_ord, ?_⟩
  intro t ht
  by_cases htl : t < len
  · obtain ⟨h1, hB1⟩ := hρ₀_step t htl
    have hGt : D.G t = D'.G t := by simp [D', extendDyn, htl.le]
    have hGt1 : D.G (t + 1) = D'.G (t + 1) := by simp [D', extendDyn, Nat.succ_le_of_lt htl]
    have hUt1 : D.U (t + 1) = D'.U (t + 1) := by simp [D', extendDyn, Nat.succ_le_of_lt htl]
    have h2 : D'.G (t + 1) = (D'.G t).applyBatch (D'.U (t + 1)) := by
      rw [← hGt, ← hGt1, ← hUt1]; exact h1
    refine ⟨h2, rotationBatch_cast hGt hUt1 h1 h2 ?_ ?_ hB1⟩
    · rw [hρ'_ord t (by omega), hρ₀_ord t htl.le]; simp [ord', extendOrd, htl.le]
    · rw [hρ'_ord (t + 1) (by omega), hρ₀_ord (t + 1) (Nat.succ_le_of_lt htl)]
      simp [ord', extendOrd, Nat.succ_le_of_lt htl]
  · have hteq : t = len := by omega
    subst t
    have hGt : D.G len = D'.G len := by simp [D', extendDyn]
    have hGt1 : curG = D'.G (len + 1) := by simp [D', extendDyn]
    have hUt1 : curU = D'.U (len + 1) := by simp [D', extendDyn]
    have h2 : D'.G (len + 1) = (D'.G len).applyBatch (D'.U (len + 1)) := by
      rw [← hGt, ← hGt1, ← hUt1]; exact hStepG
    refine ⟨h2, rotationBatch_cast hGt hUt1 hStepG h2 ?_ ?_ hRB⟩
    · rw [hρ'_ord len (Nat.le_succ _), hρPrev]; simp [ord', extendOrd]
    · rw [hρ'_ord (len + 1) (le_refl _), hρNew]; simp [ord', extendOrd]

end U3

lemma runOrdAfterUpdate_extendDyn_prefix (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) (len : ℕ)
    (Unew : List Update) (Gnew : MGraph) (ℓnew gnew : ℕ → ℝ) (ordNew : ℕ → List End) :
    ∀ s ≤ len, T.runOrdAfterUpdate k M N (extendDyn D len Unew Gnew ℓnew gnew)
      (U3.extendOrd ord len ordNew) (fun r => if r ≤ len then restarts r else []) s =
        T.runOrdAfterUpdate k M N D ord restarts s := by
  intro s hs
  exact T.runOrdAfterUpdate_congr_lt k M N s (by simp [extendDyn]) (by simp [extendDyn])
    (by simp [extendDyn])
    (fun s' _ hs' => by
      have hle : s' ≤ len := le_trans hs' hs
      simp [extendDyn, hle])
    (fun s' hs' => by
      have hle : s' ≤ len := le_trans hs' hs
      simp [U3.extendOrd, hle])
    (fun r hr => by
      have hle : r ≤ len := le_trans (Nat.le_of_lt hr) hs
      simp [hle])

lemma runOrdAfterRestarts_extendDyn_prefix (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) (len : ℕ)
    (Unew : List Update) (Gnew : MGraph) (ℓnew gnew : ℕ → ℝ) (ordNew : ℕ → List End) :
    ∀ s ≤ len, T.runOrdAfterRestarts k M N (extendDyn D len Unew Gnew ℓnew gnew)
      (U3.extendOrd ord len ordNew) (fun r => if r ≤ len then restarts r else []) s =
        T.runOrdAfterRestarts k M N D ord restarts s := by
  intro s hs
  exact T.runOrdAfterRestarts_congr_le k M N s (by simp [extendDyn]) (by simp [extendDyn])
    (by simp [extendDyn])
    (fun s' _ hs' => by
      have hle : s' ≤ len := le_trans hs' hs
      simp [extendDyn, hle])
    (fun s' hs' => by
      have hle : s' ≤ len := le_trans hs' hs
      simp [U3.extendOrd, hle])
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
    (hEncNext : k + 1 < P.d → ch₂.curEnc (k + 1) ≤ ch₁.curEnc (k + 1))
    (hLevelOrd : ch₂.levelOrd k = ch₁.levelOrd k) :
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
  ord := H.ord
  hOrd := H.hOrd
  hEndOrd := by rw [hLevelOrd]; exact H.hEndOrd
  hRun := by rw [hSc]; exact H.hRun
  hOK := H.hOK
  branchSeq := H.branchSeq
  hBranch := H.hBranch
  hBranchTail := by rw [hBr]; exact H.hBranchTail
  hWinFwdBound := H.hWinFwdBound
  hCurFwdEq := by rw [hCurFwd]; exact H.hCurFwdEq
  hDecEq := by rw [hDec, hSc, hBr]; exact H.hDecEq
  hEnc0Le := fun h0 => by rw [hEnc0 h0]; exact H.hEnc0Le h0
  hEncLe := fun h1 => by rw [hBr]; exact le_trans (hEncNext h1) (H.hEncLe h1)

noncomputable def extendLevelHistory {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ} (_hTP : TP.Valid)
    (_hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {ch0 ch1 : ChainState T P} {idx : ℕ} (_hidx : idx < P.d)
    (Horig : LevelHistory T TP P N₀ ch0 idx)
    (curU : List Update) (curG : MGraph) (ℓi gi : ℕ → ℝ) (ordNew : ℕ → List End)
    (hG0eq : curG = (ch0.G idx).applyBatch curU)
    (hBatch : (ch0.G idx).BatchIsValid curU)
    (_hCurGValid : curG.IsValid)
    (hEndG1 : ch1.G idx = curG)
    (hEndOrd1 : ch1.levelOrd idx = ordNew)
    (hStepOrd : ∃ (ρPrev : Rotation (ch0.G idx)) (ρNew : Rotation curG),
      ρPrev.order = ch0.levelOrd idx ∧ ρNew.order = ordNew ∧
      RotationBatch 2 curU ρPrev (hG0eq ▸ ρNew))
    (hℓEq : ℓi = ch1.toTreeChain.chainLen ch1.ℓ idx)
    (hgEq : gi = ch1.toTreeChain.chainGrad ch1.g idx)
    (hCurLenPos : ∀ e ∈ curG.E, 0 < ℓi e)
    (hCurLenStable : ∀ e ∈ curG.E, e ∈ (ch0.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
      ℓi e = ch0.toTreeChain.chainLen ch0.ℓ idx e)
    (hUpd1 : ch1.updCount idx = ch0.updCount idx + curU.length)
    (hThresh1 : ((ch1.updCount idx : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold P.k (levelM TP P idx) N₀)
    (hCurFwd1 : ch1.curFwd idx = ch0.curFwd idx +
      ((T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).2 (ch0.bran idx)).length)
    (hSc1 : ch1.scState idx = (T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).1)
    (hRest1 : ch1.curRestarts idx = ch0.curRestarts idx)
    (hBr1 : ch1.bran idx = ch0.bran idx)
    (hBrLt : ch0.bran idx < P.k)
    (hDec1 : ch1.curDecUpdates idx = ch0.curDecUpdates idx +
      (diffTreeChanges ((T.lsfs (ch0.scState idx) (ch0.bran idx)).F.F.E)
        ((T.lsfs (T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).1 (ch0.bran idx)).F.F.E)).length)
    (hEnc0Le1 : idx = 0 → ch1.curEnc 0 ≤ ch0.curEnc 0 + (ch0.G 0).batchEnc curU)
    (hEncLe1 : idx + 1 < P.d → ch1.curEnc (idx + 1) ≤ ch0.curEnc (idx + 1) +
      (T.S (ch0.scState idx) (ch0.bran idx)).batchEnc
        ((T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).2 (ch0.bran idx))) :
    LevelHistory T TP P N₀ ch1 idx :=
  let D' := extendDyn Horig.D Horig.len curU curG
    (ch1.toTreeChain.chainLen ch1.ℓ idx) (ch1.toTreeChain.chainGrad ch1.g idx)
  let ord' := U3.extendOrd Horig.ord Horig.len ordNew
  let restarts' : ℕ → List ℕ := fun r => if r ≤ Horig.len then Horig.restarts r else []
  have hRestLt' : ∀ r ≤ Horig.len + 1, ∀ j ∈ restarts' r, j < P.k := fun r _ j hj => by
    dsimp only [restarts'] at hj
    split_ifs at hj with hr
    · exact Horig.hRestartsLt r hr j hj
    · contradiction
  have hD'G0 : D'.G 0 = Horig.D.G 0 := by simp [D', extendDyn]
  have hD'ℓ0 : D'.ℓ 0 = Horig.D.ℓ 0 := by simp [D', extendDyn]
  have hRunPre : ∀ s ≤ Horig.len,
      T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s =
        T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s :=
    runOrdAfterUpdate_extendDyn_prefix T P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts
      Horig.len curU curG _ _ ordNew
  have hRunPostPre : ∀ s ≤ Horig.len,
      T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' s =
        T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s :=
    runOrdAfterRestarts_extendDyn_prefix T P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts
      Horig.len curU curG _ _ ordNew
  have hRunNextPre : T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1) =
      T.updateOrd (ch0.scState idx) curU ℓi gi ordNew := by
    rw [T.runOrdAfterUpdate_succ P.k (levelM TP P idx) N₀ D' ord' restarts' Horig.len,
      hRunPostPre Horig.len (le_refl _), ← Horig.hRun]
    simp [D', extendDyn, ord', U3.extendOrd, hℓEq, hgEq]
  have hRunNextPost : T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1) =
      (T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).1 := by
    simp only [SparseCoreRestartTool.runOrdAfterRestarts, restarts',
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
  have hD'Ord : OrderedUpTo D' (Horig.len + 1) 2 ord' := by
    have hStepG' : curG = (Horig.D.G Horig.len).applyBatch curU := by rw [Horig.hEndG]; exact hG0eq
    refine U3.orderedUpTo_extend_step Horig.hOrd curU curG _ _ ordNew hStepG' ?_
    obtain ⟨ρPrev, ρNew, hρPrev, hρNew, hRB⟩ := hStepOrd
    refine ⟨Horig.hEndG.symm ▸ ρPrev, ρNew, ?_, hρNew, ?_⟩
    · rw [U3.rotation_cast_order, hρPrev, Horig.hEndOrd]
    · exact U3.rotationBatch_cast Horig.hEndG.symm rfl hG0eq hStepG'
        (U3.rotation_cast_order _ _).symm rfl hRB
  have hSpec := Horig.hOK.noHidden P.k (Horig.len + 1) (levelM TP P idx) N₀ D' ord' restarts' P.hk
    (hD'G0 ▸ Horig.hG0) hD'Valid hD'Len hD'ℓPos hD'Ord
    (hD'G0 ▸ Horig.hInitMBound) (hD'G0 ▸ Horig.hInitNBound) hRestLt'
    (by
      rw [hUpdSum', ← hUpd1]
      exact hThresh1) ⟨rfl, rfl, rfl, hD'G0, hD'ℓ0⟩
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
    hNoRestartAfterS0 := fun r hr1 _ => by
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
    ord := ord'
    hOrd := hD'Ord
    hEndOrd := by simp [ord', U3.extendOrd, hEndOrd1]
    hRun := by rw [hSc1, hRunNextPost]
    hOK := by rw [hD'G0, hD'ℓ0]; exact Horig.hOK
    branchSeq := fun s => if s ≤ Horig.len then Horig.branchSeq s else ch0.bran idx
    hBranch := fun s => by
      by_cases hs : s ≤ Horig.len
      · simp [hs, Horig.hBranch s]
      · simp [hs, hBrLt]
    hBranchTail := fun s hs1 _ => by
      rw [hBr1]
      by_cases hsl : s ≤ Horig.len
      · simp [hsl, Horig.hBranchTail s hs1 hsl]
      · simp [hsl]
    hWinFwdBound := by
      have hsub1 : (Finset.Icc 1 Horig.s₀).sum (fun s =>
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
              (if s ≤ Horig.len then Horig.branchSeq s else ch0.bran idx)).length) =
          (Finset.Icc 1 Horig.s₀).sum (fun s =>
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
              (Horig.branchSeq s)).length) := by
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
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
              (if s ≤ Horig.len then Horig.branchSeq s else ch0.bran idx)).length) =
          (Finset.Icc 1 Horig.len).sum (fun s =>
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
              (Horig.branchSeq s)).length) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := (Finset.mem_Icc.mp hs).2
        simp only [hsl, ↓reduceIte, hRunPre s hsl]
      have hLastFwd :
          ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1)).2
            (if Horig.len + 1 ≤ Horig.len then Horig.branchSeq (Horig.len + 1) else ch0.bran idx)).length =
          ((T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).2 (ch0.bran idx)).length := by
        simp only [Nat.not_succ_le_self, ↓reduceIte, hRunNextPre]
      rw [hPreFwd, hLastFwd]
    hDecEq := by
      have hSub := (hSpec.2.1 (Horig.len + 1) (Nat.succ_pos _)
        (le_refl _) (ch0.bran idx) hBrLt).1
      simp only [Nat.add_sub_cancel, hRunPostPre Horig.len (le_refl _), ← Horig.hRun,
        hRunNextPost] at hSub
      have hLenEq : (diffTreeChanges ((T.lsfs (ch0.scState idx) (ch0.bran idx)).F.F.E)
          ((T.lsfs (T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).1 (ch0.bran idx)).F.F.E)).length =
          (T.lsfs (ch0.scState idx) (ch0.bran idx)).F.F.E.card -
          (T.lsfs (T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).1 (ch0.bran idx)).F.F.E.card :=
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
            (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts' (s - 1))
              (ch0.bran idx)).batchEnc
              ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' s).2
                (ch0.bran idx))) =
          (Finset.Icc (Horig.s₀ + 1) Horig.len).sum (fun s =>
            (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts
              (s - 1)) (ch0.bran idx)).batchEnc
              ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ Horig.D Horig.ord Horig.restarts s).2
                (ch0.bran idx))) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hsl := (Finset.mem_Icc.mp hs).2
        have hsl' : s - 1 ≤ Horig.len := by omega
        rw [hRunPre s hsl, hRunPostPre (s - 1) hsl']
      have hLast : (T.S (T.runOrdAfterRestarts P.k (levelM TP P idx) N₀ D' ord' restarts'
              (Horig.len + 1 - 1)) (ch0.bran idx)).batchEnc
            ((T.runOrdAfterUpdate P.k (levelM TP P idx) N₀ D' ord' restarts' (Horig.len + 1)).2
              (ch0.bran idx)) =
          (T.S (ch0.scState idx) (ch0.bran idx)).batchEnc
            ((T.updateOrd (ch0.scState idx) curU ℓi gi ordNew).2 (ch0.bran idx)) := by
        simp only [Nat.add_sub_cancel]
        rw [hRunPostPre Horig.len (le_refl _), ← Horig.hRun, hRunNextPre]
      rw [hSumPre, hLast, add_comm]
      exact Nat.add_le_add_left (Horig.hEncLe h1) _ }

/-- Inter-level core-instance and order coupling across adjacent ordered `LevelHistory` records. -/
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
        (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts Hk.s₀ (ch.bran k)).G
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ, 1 ≤ δ → δ ≤ Hk1.len →
      Hk1.D.U δ =
        (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts Hk.s₀ (ch.bran k)).U
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ ≤ Hk1.len, ∀ e ∈ (Hk1.D.G δ).E,
      Hk1.D.ℓ δ e =
        (T.coreInstanceOrdFrom P.k (levelM TP P k) N₀ Hk.D Hk.ord Hk.restarts Hk.s₀ (ch.bran k)).ℓ
          ((off - Hk.s₀) + δ) e) ∧
    (∀ δ ≤ Hk1.len,
      Hk1.ord δ =
        T.rot (T.runOrdAfterRestarts P.k (levelM TP P k) N₀
          Hk.D Hk.ord Hk.restarts (Hk.s₀ + ((off - Hk.s₀) + δ))) (ch.bran k))

end MinCostFlow.Chain.Ordered
