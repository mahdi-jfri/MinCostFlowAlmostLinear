module

public import MinCostFlow.Chain.Ordered.Budget
public import MinCostFlow.Chain.Algorithm1RebuildSuffix
import MinCostFlow.Chain.Ordered.BudgetHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Update-loop invariant and base step for Algorithm 1 with orders

This file defines the loop invariant `UpdateLoopInv` for `updateLoop` in Algorithm 1 with orders
(`Chain/Ordered/Algorithm1.lean`), proves helper lemmas for extending and extracting steps of
`Bundle.OrderedUpTo`, and proves `updateLoop_zero_step` (the base case `rem = 0`, level `P.d`).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section OupdOrdHelpers

/-- Two rotations on the same graph with equal `order` maps are equal. -/
lemma oupd_rotation_ext {G : MGraph} {ρ₁ ρ₂ : Rotation G}
    (h : ρ₁.order = ρ₂.order) : ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; cases h; rfl

/-- Casting a `Rotation` along a graph equality preserves its `order` map. -/
lemma oupd_rotation_cast_order {G₁ G₂ : MGraph} (h : G₁ = G₂) (ρ : Rotation G₁) :
    (h ▸ ρ).order = ρ.order := by
  subst h; rfl

/-- Transport a `RotationBatch` across equalities of endpoints, batches, and order maps. -/
lemma oupd_rotationBatch_cast {β : ℕ} {G₁ G₂ H₁ H₂ : MGraph} {U₁ U₂ : List Update}
    (hG : G₁ = G₂) (hH : H₁ = H₂) (hU : U₁ = U₂)
    {h₁ : H₁ = G₁.applyBatch U₁} {h₂ : H₂ = G₂.applyBatch U₂}
    {ρ₁ : Rotation G₁} {ρ₂ : Rotation G₂}
    {σ₁ : Rotation H₁} {σ₂ : Rotation H₂}
    (hρ : ρ₁.order = ρ₂.order) (hσ : σ₁.order = σ₂.order)
    (hb : RotationBatch β U₁ ρ₁ (h₁ ▸ σ₁)) :
    RotationBatch β U₂ ρ₂ (h₂ ▸ σ₂) := by
  subst hG hH hU
  have hρ' : ρ₁ = ρ₂ := oupd_rotation_ext hρ
  have hσ' : σ₁ = σ₂ := oupd_rotation_ext hσ
  subst hρ' hσ'
  exact hb

/-- Extend an `OrderedUpTo D len 2 ord` witness by one ordered batch step at `len + 1`. -/
lemma oupd_orderedUpTo_extend_one {D D' : DynamicInstance} {len : ℕ}
    {ord ord' : ℕ → ℕ → List End} {Gprev curG : MGraph} {curU : List Update}
    {ordNew : ℕ → List End}
    (hOrd : OrderedUpTo D len 2 ord)
    (hEndG : D.G len = Gprev)
    (hCurGEq : curG = Gprev.applyBatch curU)
    (hD'G : ∀ t ≤ len, D'.G t = D.G t)
    (hD'Gnext : D'.G (len + 1) = curG)
    (hD'U : ∀ t, 1 ≤ t → t ≤ len → D'.U t = D.U t)
    (hD'Unext : D'.U (len + 1) = curU)
    (hord' : ∀ t ≤ len, ord' t = ord t)
    (hord'next : ord' (len + 1) = ordNew)
    (ρBefore : Rotation Gprev) (ρAfter : Rotation curG)
    (hBefore : ρBefore.order = ord len) (hAfter : ρAfter.order = ordNew)
    (hBatch : RotationBatch 2 curU ρBefore (hCurGEq ▸ ρAfter)) :
    OrderedUpTo D' (len + 1) 2 ord' := by
  obtain ⟨ρ, hρOrd, hStep⟩ := hOrd
  let ρ' : ∀ t, Rotation (D'.G t) := fun t =>
    if h1 : t ≤ len then (hD'G t h1).symm ▸ ρ t
    else if h2 : t = len + 1 then (h2 ▸ hD'Gnext).symm ▸ ρAfter
    else sortedRotation (D'.G t)
  refine ⟨ρ', ?_, ?_⟩
  · intro t ht
    by_cases h1 : t ≤ len
    · simp only [ρ', h1, ↓reduceDIte]
      rw [oupd_rotation_cast_order, hρOrd t h1, hord' t h1]
    · have h2 : t = len + 1 := by omega
      subst h2
      simp only [ρ', Nat.not_succ_le_self, ↓reduceDIte]
      rw [oupd_rotation_cast_order, hAfter, hord'next]
  · intro t ht
    by_cases h1 : t < len
    · have htLe : t ≤ len := Nat.le_of_lt h1
      have ht1Le : t + 1 ≤ len := h1
      obtain ⟨hEq, hb⟩ := hStep t h1
      have hEq' : D'.G (t + 1) = (D'.G t).applyBatch (D'.U (t + 1)) := by
        rw [hD'G (t + 1) ht1Le, hD'G t htLe, hD'U (t + 1) (Nat.succ_pos t) ht1Le]
        exact hEq
      refine ⟨hEq', oupd_rotationBatch_cast (hD'G t htLe).symm (hD'G (t + 1) ht1Le).symm
        (hD'U (t + 1) (Nat.succ_pos t) ht1Le).symm ?_ ?_ hb⟩
      · simp only [ρ', htLe, ↓reduceDIte]
        rw [oupd_rotation_cast_order]
      · simp only [ρ', ht1Le, ↓reduceDIte]
        rw [oupd_rotation_cast_order]
    · have htEq : t = len := by omega
      subst t
      have hEq' : D'.G (len + 1) = (D'.G len).applyBatch (D'.U (len + 1)) := by
        rw [hD'Gnext, hD'G len (le_refl _), hEndG, hD'Unext]
        exact hCurGEq
      refine ⟨hEq', oupd_rotationBatch_cast ((hD'G len (le_refl _)).trans hEndG).symm
        hD'Gnext.symm hD'Unext.symm ?_ ?_ hBatch⟩
      · simp only [ρ', le_refl, ↓reduceDIte]
        rw [oupd_rotation_cast_order, hρOrd len (le_refl _), hBefore]
      · simp only [ρ', Nat.not_succ_le_self, ↓reduceDIte]
        rw [oupd_rotation_cast_order]

/-- Extract a single ordered batch step from an `OrderedUpTo` witness at index `t < τ`. -/
lemma oupd_orderedUpTo_step_extract {D : DynamicInstance} {τ : ℕ} {ord : ℕ → ℕ → List End}
    (hOrd : OrderedUpTo D τ 2 ord) {t : ℕ} (ht : t < τ)
    {G1 G2 : MGraph} {U : List Update}
    (hG1 : D.G t = G1) (hG2 : D.G (t + 1) = G2) (hU : D.U (t + 1) = U)
    (hEq : G2 = G1.applyBatch U) :
    ∃ (ρ1 : Rotation G1) (ρ2 : Rotation G2),
      ρ1.order = ord t ∧ ρ2.order = ord (t + 1) ∧
      RotationBatch 2 U ρ1 (hEq ▸ ρ2) := by
  subst hG1 hG2 hU
  obtain ⟨ρ, hρOrd, hStep⟩ := hOrd
  obtain ⟨h, hb⟩ := hStep t ht
  exact ⟨ρ t, ρ (t + 1), hρOrd t (Nat.le_of_lt ht), hρOrd (t + 1) ht, hb⟩

end OupdOrdHelpers

/-- Loop invariant for `updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc` relative
to the pre-update state `stOrig` and top-level batch `(U, g', ℓ')`, maintaining the unconditional
tight `TP.γ_r (P.M₀ ^ 2)` recourse bound via restart-aware windowed recourse (`LevelHistory`)
and the ordered rotation transition `hCurOrd` at level `idx`. -/
structure UpdateLoopInv {T : SparseCoreRestartTool} (TP : SparseCoreParams) {P : ChainParams}
    (N₀ : ℕ) (Λ extraOverflow : ℝ) (stOrig st : ChainState T P) (ℓ' g' : ℕ → ℝ)
    (rem idx : ℕ) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ) : Prop where
  hidxSum : idx + rem = P.d
  hGGe : ∀ j, idx ≤ j → st.G j = stOrig.G j
  hScGe : ∀ j, idx ≤ j → st.scState j = stOrig.scState j
  hRestarts : st.curRestarts = stOrig.curRestarts
  hUpdGe : ∀ j, idx ≤ j → st.updCount j = stOrig.updCount j
  hDecGe : ∀ j, idx ≤ j → st.curDecUpdates j = stOrig.curDecUpdates j
  hEncGt : ∀ j, idx < j → st.curEnc j = stOrig.curEnc j
  hCurFwdGe : ∀ j, idx ≤ j → st.curFwd j = stOrig.curFwd j
  hRecGt : ∀ j, idx < j → st.recUpdates j = stOrig.recUpdates j
  hCurRecAt : st.recUpdates idx = stOrig.recUpdates idx + curU.length
  hBran : st.bran = stOrig.bran
  hLast : st.lastK = stOrig.lastK ∧ st.lastLSFs = stOrig.lastLSFs ∧ st.lastBran = stOrig.lastBran
  hLG : st.ℓ = stOrig.ℓ ∧ st.g = stOrig.g
  hCnt : st.shiftCount = stOrig.shiftCount ∧ st.rebuildCount = stOrig.rebuildCount
  hClosed : st.closedRuntime = stOrig.closedRuntime ∧ st.closedTreeUpdates = stOrig.closedTreeUpdates
  hLastStats : st.curLastRebuilds = stOrig.curLastRebuilds ∧
    st.curLastCost = stOrig.curLastCost ∧ st.curLastTreeUpdates = stOrig.curLastTreeUpdates
  hG0New : 0 < idx → (st.G 0).IsValid ∧ (st.G 0).m ≤ P.M₀ ∧ (st.G 0).n ≤ N₀ ∧
    (stOrig.G 0).V ⊆ (st.G 0).V ∧ (∀ e ∈ (st.G 0).E, 0 < ℓ' e)
  hPreHist : ∀ j < idx, Nonempty (LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } j)
  hPreGSucc : ∀ j, j + 1 < idx → st.G (j + 1) = T.S (st.scState j) (st.bran j)
  hPreV : ∀ j < idx, (st.G j).V ⊆ (st.G 0).V
  hPreM : ∀ j < idx, ((st.G j).m : ℝ) ≤ (levelM TP P j : ℝ)
  hPreEnc0 : 0 < idx → (st.curEnc 0 : ℝ) ≤
    20 * ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ)) *
      Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2)
  hLoopRecReb : ∀ j < idx,
    (st.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
      (st.updCount j : ℝ) ≤ (st.recUpdates j : ℝ)
  hLoopRecFwd : ∀ j < idx,
    (st.curFwd j : ℝ) ≤ TP.γ_r (P.M₀ ^ 2) * (st.updCount j : ℝ) ∧
    ((st.recUpdates (j + 1) : ℝ) - (st.curFwd j : ℝ)) ≤
      TP.γ_r (P.M₀ ^ 2) * ((st.recUpdates j : ℝ) - (st.updCount j : ℝ))
  hPreLastReb : idx = P.d → 0 < P.d →
    ∃ H : LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } (P.d - 1),
      st.curLastRebuilds + (if curU = [] then 0 else 1) ≤
        (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
          ((T.runOrdAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.ord H.restarts s).2
            (st.bran (P.d - 1))).length
  hCurGEq : curG = (stOrig.G idx).applyBatch curU
  hCurGBatch : (stOrig.G idx).BatchIsValid curU
  hCurGValid : curG.IsValid
  hCurGM : (curG.m : ℝ) ≤ (levelM TP P idx : ℝ)
  hCurGV0 : idx = 0 → curG.m ≤ P.M₀ ∧ curG.n ≤ N₀ ∧ (stOrig.G 0).V ⊆ curG.V ∧
    (∀ e ∈ curG.E, 0 < ℓ' e)
  hCurGVPos : 0 < idx → curG.V ⊆ (st.G 0).V
  hCurGFromPrev : 0 < idx → curG = T.S (st.scState (idx - 1)) (st.bran (idx - 1))
  hCurOrd : ∃ (ρBefore : Rotation (stOrig.G idx)) (ρAfter : Rotation curG),
    ρBefore.order = stOrig.levelOrd idx ∧
    ρAfter.order =
      chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState st.bran idx ∧
    RotationBatch 2 curU ρBefore (hCurGEq ▸ ρAfter)
  hCurEnc0 : idx = 0 → st.curEnc 0 = stOrig.curEnc 0 ∧ curEncAcc = (stOrig.G 0).batchEnc curU ∧
    (curEncAcc : ℝ) ≤ extraEncCap P + extraOverflow
  hCurEncPos : 0 < idx → curEncAcc = 0 ∧
    (idx < P.d → (st.curEnc idx : ℝ) ≤
      5 * TP.γ_r (P.M₀ ^ 2) *
        ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (idx - 1) / (P.k : ℝ) + 1))
  hCurLenRange : LevelLenRange TP P N₀ Λ idx curG
    (({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx)
  hCurLenStable : ∀ e ∈ curG.E, e ∈ (stOrig.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
    ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx e =
      stOrig.toTreeChain.chainLen stOrig.ℓ idx e
  hDecMono : ∀ j < P.d, stOrig.curDecUpdates j ≤ st.curDecUpdates j
  hTreeDiff : (diffTreeChanges stOrig.toTreeChain.chainTree.E st.toTreeChain.chainTree.E).length +
    (Finset.range P.d).sum stOrig.curDecUpdates ≤ (Finset.range P.d).sum st.curDecUpdates
  hLvlM : st.lvlM = stOrig.lvlM
  hN0 : st.N₀ = stOrig.N₀

/-- The current lengths at level `idx` of an `UpdateLoopInv` are positive. -/
lemma UpdateLoopInv.hCurLenPos {T : SparseCoreRestartTool} {TP : SparseCoreParams} {P : ChainParams}
    {N₀ : ℕ} {Λ extraOverflow : ℝ} {stOrig st : ChainState T P} {ℓ' g' : ℕ → ℝ}
    {rem idx : ℕ} {curG : MGraph} {curU : List Update} {curEncAcc : ℕ}
    (h : UpdateLoopInv TP N₀ Λ extraOverflow stOrig st ℓ' g' rem idx curG curU curEncAcc) :
    ∀ e ∈ curG.E, 0 <
      ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen
        ℓ' idx e :=
  h.hCurLenRange.pos

/-- Base case (`rem = 0`, `idx = P.d`) of `updateLoop` invariant and budget preservation. -/
lemma updateLoop_zero_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) {Λ : ℝ} (hL : L.IsSpec LP)
    (_hNoReinsTool : T.ToolNoReinsertOrdRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ Λ extraOverflow stOrig st ℓ' g' 0 idx curG curU curEncAcc) :
    let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' 0 idx st curG curU curEncAcc
    ChainInv T L TP LP P N₀ stEnd ∧
    ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) ∧
    (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
    (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
    (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
    (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
      stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hγM₀ hγk hInvOrig
  have hidx : idx = P.d := by have := hLoop.hidxSum; omega
  subst hidx
  dsimp only [updateLoop]
  by_cases hEmp : curU = []
  · subst hEmp
    simp only [↓reduceIte]
    set stEnd : ChainState T P :=
      { st with G := fun j => if j = P.d then curG else st.G j, ℓ := ℓ', g := g' }
    have hCurEqOrig : curG = stOrig.G P.d := by
      simpa [MGraph.applyBatch] using hLoop.hCurGEq
    have hGEqSt : stEnd.G = st.G := by
      ext j
      dsimp only [stEnd]
      split_ifs with h
      · rw [h, hCurEqOrig, hLoop.hGGe P.d (le_refl P.d)]
      · rfl
    have hGEndPd : stEnd.G P.d = stOrig.G P.d := by
      rw [hGEqSt, hLoop.hGGe P.d (le_refl P.d)]
    have hG0Props := hLoop.hG0New P.hd
    have h0n : (stOrig.G 0).n ≤ (stEnd.G 0).n := by
      rw [hGEqSt]; exact Finset.card_le_card hG0Props.2.2.2.1
    have hToTC : ∀ j < P.d, stEnd.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
      intro j hj; simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stEnd]
    have hOrdEq : ∀ i, stEnd.levelOrd i = ({ st with ℓ := ℓ', g := g' } : ChainState T P).levelOrd i := by
      intro i
      unfold ChainState.levelOrd chainLevelOrd
      rw [hGEqSt]
    have hℓdEq : ∀ e ∈ (stOrig.G P.d).E,
        stEnd.toTreeChain.chainLen stEnd.ℓ P.d e =
          stOrig.toTreeChain.chainLen stOrig.ℓ P.d e := by
      intro e he
      set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }
      have hC := chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := Cpartial) ℓ' P.d
        (fun j hj => by change stEnd.G j = Cpartial.G j; simp [stEnd, Cpartial, show j ≠ P.d by omega])
        (fun j hj => by simp [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, stEnd, hj])
      have heCur : e ∈ curG.E := by rwa [hCurEqOrig]
      change stEnd.toTreeChain.chainLen ℓ' P.d e = _
      rw [hC]
      exact hLoop.hCurLenStable e heCur he (fun u hu => nomatch hu)
    have hLastEq : stEnd.lastK = stOrig.lastK ∧ stEnd.lastLSFs = stOrig.lastLSFs ∧
        stEnd.lastBran = stOrig.lastBran := hLoop.hLast
    have hInvEnd : ChainInv T L TP LP P N₀ stEnd := {
      hG0Valid := hGEqSt ▸ hG0Props.1
      hG0m := hGEqSt ▸ hG0Props.2.1
      hG0n := hGEqSt ▸ hG0Props.2.2.1
      hℓPos := hGEqSt ▸ hG0Props.2.2.2.2
      hLastK := hLastEq.1 ▸ hInvOrig.hLastK
      hLastBran := hLastEq.1 ▸ hLastEq.2.2 ▸ hInvOrig.hLastBran
      hLastHolds := fun j hj => by
        have hOrigH := hInvOrig.hLastHolds j (hLastEq.1 ▸ hj)
        have h1 := LSF.Holds.congr_len hOrigH fun e he => (hℓdEq e he).symm
        rw [hGEndPd, hLastEq.2.1]
        exact h1
      hLastMWU := by rw [hGEndPd, hLastEq.1, hLastEq.2.1]; exact hInvOrig.hLastMWU
      hLastSpans := by rw [hGEndPd, hLastEq.1, hLastEq.2.1]; exact hInvOrig.hLastSpans
      hBran := by rw [hLoop.hBran]; exact hInvOrig.hBran
      hGSucc := fun i hi => by
        by_cases h1 : i + 1 < P.d
        · rw [hGEqSt]; exact hLoop.hPreGSucc i h1
        · have hieq : i = P.d - 1 := by omega
          subst hieq
          rw [hGEqSt, show P.d - 1 + 1 = P.d by omega, hLoop.hGGe P.d (le_refl P.d), ← hCurEqOrig]
          exact hLoop.hCurGFromPrev P.hd
      hHist := fun i hi => by
        obtain ⟨H⟩ := hLoop.hPreHist i hi
        exact ⟨{ H with
          hEndG := by rw [hGEqSt]; exact H.hEndG
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' i
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt]) (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndℓ e (hGEqSt ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' i
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt]) (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndg
          hEndOrd := by rw [hOrdEq i]; exact H.hEndOrd }⟩
      hEnc0 := hLoop.hPreEnc0 P.hd
      hLastCap := fun hd => by
        obtain ⟨H, hReb⟩ := hLoop.hPreLastReb rfl hd
        have hSub := Nat.sub_lt hd zero_lt_one
        have hReb' : stEnd.curLastRebuilds ≤ (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
            ((T.runOrdAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.ord H.restarts s).2
              (stEnd.bran (P.d - 1))).length := by
          simpa [stEnd] using hReb
        refine ⟨⟨{ H with
          hEndG := by rw [hGEqSt]; exact H.hEndG
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' (P.d - 1)
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndℓ e (hGEqSt ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' (P.d - 1)
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndg
          hEndOrd := by rw [hOrdEq (P.d - 1)]; exact H.hEndOrd }, hReb'⟩, ?_, ?_⟩
        · obtain ⟨_, hCostO, _⟩ := hInvOrig.hLastCap hd
          rw [hLoop.hLastStats.2.1, hLoop.hLastStats.1]
          refine le_trans hCostO ?_
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hLP.2.2.2.2 (by positivity))
          have harg_pos : 0 < (levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2 := by
            positivity
          have hlog_pos : 0 ≤ Real.log ((levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2) :=
            Real.log_nonneg (by
              have hnn : 0 ≤ (levelM TP P P.d : ℝ) := Nat.cast_nonneg _
              linarith [show (0 : ℝ) ≤ (stOrig.G 0).n from Nat.cast_nonneg _])
          refine pow_le_pow_left₀ hlog_pos (Real.log_le_log harg_pos ?_) _
          have h0n' : ((stOrig.G 0).n : ℝ) ≤ (stEnd.G 0).n := by exact_mod_cast h0n
          linarith
        · rw [hLoop.hLastStats.2.2, hLoop.hLastStats.1]
          exact (hInvOrig.hLastCap hd).2.2
      hRecRebuild := fun j hj => hLoop.hLoopRecReb j hj
      hRecFwd := fun j hj => hLoop.hLoopRecFwd j hj
      hLvlM := hLoop.hLvlM.trans hInvOrig.hLvlM
      hN0 := hLoop.hN0.trans hInvOrig.hN0 }
    have hBudgetEnd : ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) := by
      refine ⟨?_, ?_⟩
      · rw [show stEnd.closedRuntime = stOrig.closedRuntime from hLoop.hClosed.1,
          show stEnd.curRestarts = stOrig.curRestarts from hLoop.hRestarts,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact le_trans hBudgetOrig.1 (by linarith)
      · rw [show stEnd.closedTreeUpdates = stOrig.closedTreeUpdates from hLoop.hClosed.2,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact hBudgetOrig.2
    have hEeq : stEnd.toTreeChain.chainTree.E = st.toTreeChain.chainTree.E := by
      change stEnd.toTreeChain.chainTreeEdges = st.toTreeChain.chainTreeEdges
      unfold TreeChain.chainTreeEdges
      refine Finset.biUnion_congr rfl fun j hj => ?_
      by_cases hjt : j < P.d
      · have hjt' : j < P.d := by change j < stEnd.toTreeChain.d at hjt; exact hjt
        rw [hToTC j hjt']
      · have hjlt : j < P.d + 1 := Finset.mem_range.mp hj
        have hjeq : j = P.d := by omega
        subst hjeq
        simp [TreeChain.activeLSF, ChainState.toTreeChain, stEnd]
    refine ⟨hInvEnd, hBudgetEnd, h0n, fun i => by rw [hLoop.hCnt.1], fun i => by rw [hLoop.hCnt.2], ?_⟩
    unfold ChainState.totalTreeUpdates
    rw [hEeq, hLoop.hClosed.2, hLoop.hLastStats.2.2]
    change (diffTreeChanges stOrig.toTreeChain.chainTree.E st.toTreeChain.chainTree.E).length +
        (stOrig.closedTreeUpdates + (Finset.range P.d).sum stOrig.curDecUpdates + stOrig.curLastTreeUpdates) ≤
      stOrig.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + stOrig.curLastTreeUpdates
    have hTD := hLoop.hTreeDiff
    omega
  · simp only [hEmp, ↓reduceIte]
    set Cpartial : TreeChain :=
      { st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }
    set ℓd := Cpartial.chainLen ℓ' P.d
    set lastRes := L.build curG ℓd
    set lastCost := L.cost curG
    set oldFdE := (st.lastLSFs st.lastBran).F.F.E
    set newFdE := (lastRes.2 0).F.F.E
    set fdChanges := diffTreeChanges oldFdE newFdE
    set stEnd : ChainState T P :=
      { st with
        G := fun j => if j = P.d then curG else st.G j
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        ℓ := ℓ'
        g := g'
        curLastRebuilds := st.curLastRebuilds + 1
        curLastCost := st.curLastCost + lastCost
        curLastTreeUpdates := st.curLastTreeUpdates + fdChanges.length }
    have hG0Props := hLoop.hG0New P.hd
    have hG0Eq : stEnd.G 0 = st.G 0 := by
      have h0d : (0 : ℕ) ≠ P.d := Nat.ne_of_lt P.hd
      simp [stEnd, h0d]
    have hOrdEq : ∀ i, stEnd.levelOrd i = ({ st with ℓ := ℓ', g := g' } : ChainState T P).levelOrd i := by
      intro i
      unfold ChainState.levelOrd chainLevelOrd
      split_ifs
      · rw [hG0Eq]
      · rfl
    have h0n : (stOrig.G 0).n ≤ (stEnd.G 0).n := by
      rw [hG0Eq]; exact Finset.card_le_card hG0Props.2.2.2.1
    have hG0Endn : (stEnd.G 0).n ≤ N₀ := by
      rw [hG0Eq]; exact hG0Props.2.2.1
    have hℓdPos : ∀ e ∈ curG.E, 0 < ℓd e := by
      intro e he
      have heq : ℓd = ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j } : TreeChain).chainLen ℓ' P.d :=
        rfl
      rw [heq]; exact hLoop.hCurLenPos e he
    have hLspec := hL curG ℓd hLoop.hCurGValid hℓdPos
    have hCurGV : curG.V ⊆ (stEnd.G 0).V := by
      rw [hG0Eq]; exact hLoop.hCurGVPos P.hd
    have hCurn : curG.n ≤ (stEnd.G 0).n := Finset.card_le_card hCurGV
    have hLastCostBd : (lastCost : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2)) ^
            LP.p_last := by
      have hlog0 : 0 ≤ Real.log ((curG.m : ℝ) + (curG.n : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ curG.m from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ curG.n from Nat.cast_nonneg _])
      have hlogLe : Real.log ((curG.m : ℝ) + (curG.n : ℝ) + 2) ≤
          Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2) := by
        apply Real.log_le_log (by positivity)
        have hn' : (curG.n : ℝ) ≤ (stEnd.G 0).n := by exact_mod_cast hCurn
        linarith [hLoop.hCurGM]
      have hpowLog := pow_le_pow_left₀ hlog0 hlogLe LP.p_last
      have hmPlus : (curG.m : ℝ) + 1 ≤ (levelM TP P P.d : ℝ) + 1 := by
        linarith [hLoop.hCurGM]
      refine le_trans hLspec.2.2.2.2 ?_
      apply mul_le_mul _ hpowLog (by positivity) (mul_nonneg hLP.2.2.2.2 (by positivity))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmPlus 2) hLP.2.2.2.2
    have hFdCap : (fdChanges.length : ℝ) ≤ 2 * (levelM TP P P.d : ℝ) := by
      have hOldSub : oldFdE ⊆ (stOrig.G P.d).E := by
        change (st.lastLSFs st.lastBran).F.F.E ⊆ (stOrig.G P.d).E
        rw [hLoop.hLast.2.1, hLoop.hLast.2.2]
        exact (hInvOrig.hLastHolds stOrig.lastBran hInvOrig.hLastBran).2.1.2.2.2.2.2.1
      have hNewSub : newFdE ⊆ curG.E := (hLspec.2.1 0 hLspec.1).2.1.2.2.2.2.2.1
      have hOldCard : (oldFdE.card : ℝ) ≤ (levelM TP P P.d : ℝ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hOldSub) (hOrigLev P.d (le_refl P.d)).2.2.1
      have hNewCard : (newFdE.card : ℝ) ≤ (levelM TP P P.d : ℝ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hNewSub) hLoop.hCurGM
      have hle : (fdChanges.length : ℝ) ≤ (oldFdE.card : ℝ) + (newFdE.card : ℝ) := by
        exact_mod_cast diffTreeChanges_length_le_add oldFdE newFdE
      linarith
    have hToTC : ∀ j < P.d, stEnd.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
      intro j hj; simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stEnd]
    have hℓdEq : stEnd.toTreeChain.chainLen stEnd.ℓ P.d = ℓd :=
      chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := Cpartial) ℓ' P.d
        (fun j hj => by change stEnd.G j = Cpartial.G j; simp [stEnd, Cpartial, show j ≠ P.d by omega])
        (fun j hj => by simp [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, stEnd, hj])
    have hInvEnd : ChainInv T L TP LP P N₀ stEnd := {
      hG0Valid := hG0Eq ▸ hG0Props.1
      hG0m := hG0Eq ▸ hG0Props.2.1
      hG0n := hG0Endn
      hℓPos := hG0Eq ▸ hG0Props.2.2.2.2
      hLastK := hLspec.1
      hLastBran := hLspec.1
      hLastHolds := fun j hj => by
        have hGdEq : stEnd.G P.d = curG := by simp [stEnd]
        change (lastRes.2 j).Holds (stEnd.G P.d) (stEnd.toTreeChain.chainLen stEnd.ℓ P.d)
          (LP.σ_last (stEnd.G P.d).n)
        rw [hGdEq, hℓdEq]; exact hLspec.2.1 j hj
      hLastMWU := by simpa [stEnd] using hLspec.2.2.1
      hLastSpans := by simpa [stEnd] using hLspec.2.2.2.1
      hBran := by rw [hLoop.hBran]; exact hInvOrig.hBran
      hGSucc := fun i hi => by
        by_cases h1 : i + 1 < P.d
        · simp only [stEnd, show i + 1 ≠ P.d by omega, ↓reduceIte]
          exact hLoop.hPreGSucc i h1
        · have hieq : i = P.d - 1 := by omega
          subst hieq
          simp only [stEnd, show P.d - 1 + 1 = P.d by omega, ↓reduceIte]
          exact hLoop.hCurGFromPrev P.hd
      hHist := fun i hi => by
        obtain ⟨H⟩ := hLoop.hPreHist i hi
        exact ⟨{ H with
          hEndG := by simp [stEnd, show i ≠ P.d by omega]; exact H.hEndG
          hEndℓ := fun e he => by
            have hGi : stEnd.G i = st.G i := by simp [stEnd, show i ≠ P.d by omega]
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' i
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndℓ e (hGi ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' i
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndg
          hEndOrd := by rw [hOrdEq i]; exact H.hEndOrd }⟩
      hEnc0 := hLoop.hPreEnc0 P.hd
      hLastCap := fun hd => by
        obtain ⟨H, hReb⟩ := hLoop.hPreLastReb rfl hd
        have hSub := Nat.sub_lt hd zero_lt_one
        have hReb' : stEnd.curLastRebuilds ≤ (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
            ((T.runOrdAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.ord H.restarts s).2
              (stEnd.bran (P.d - 1))).length := by
          simpa [stEnd, hEmp] using hReb
        refine ⟨⟨{ H with
          hEndG := by simp [stEnd, show P.d - 1 ≠ P.d by omega]; exact H.hEndG
          hEndℓ := fun e he => by
            have hGi : stEnd.G (P.d - 1) = st.G (P.d - 1) := by
              simp [stEnd, show P.d - 1 ≠ P.d by omega]
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' (P.d - 1)
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndℓ e (hGi ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' (P.d - 1)
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndg
          hEndOrd := by rw [hOrdEq (P.d - 1)]; exact H.hEndOrd }, hReb'⟩, ?_, ?_⟩
        · obtain ⟨_, hCostO, _⟩ := hInvOrig.hLastCap hd
          have hCostO' : (st.curLastCost : ℝ) ≤
              ((st.curLastRebuilds + 1 : ℕ) : ℝ) *
                (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
                  (Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2)) ^
                    LP.p_last) := by
            rw [hLoop.hLastStats.2.1, hLoop.hLastStats.1]
            refine le_trans hCostO ?_
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hLP.2.2.2.2 (by positivity))
            have harg_pos : 0 < (levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2 := by
              positivity
            have hlog_pos : 0 ≤ Real.log ((levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2) :=
              Real.log_nonneg (by
                have hnn : 0 ≤ (levelM TP P P.d : ℝ) := Nat.cast_nonneg _
                linarith [show (0 : ℝ) ≤ (stOrig.G 0).n from Nat.cast_nonneg _])
            refine pow_le_pow_left₀ hlog_pos (Real.log_le_log harg_pos ?_) _
            have h0n' : ((stOrig.G 0).n : ℝ) ≤ (stEnd.G 0).n := by exact_mod_cast h0n
            linarith
          set cap := LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
            (Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2)) ^ LP.p_last
          change ((st.curLastCost + lastCost : ℕ) : ℝ) ≤ ((st.curLastRebuilds + 1 + 1 : ℕ) : ℝ) * cap
          calc
            ((st.curLastCost + lastCost : ℕ) : ℝ)
                = (st.curLastCost : ℝ) + (lastCost : ℝ) := by push_cast; rfl
            _ ≤ ((st.curLastRebuilds + 1 : ℕ) : ℝ) * cap + cap := add_le_add hCostO' hLastCostBd
            _ = ((st.curLastRebuilds + 1 + 1 : ℕ) : ℝ) * cap := by push_cast; ring
        · have hTreeO := (hInvOrig.hLastCap hd).2.2
          rw [← hLoop.hLastStats.2.2, ← hLoop.hLastStats.1] at hTreeO
          change ((st.curLastTreeUpdates + fdChanges.length : ℕ) : ℝ) ≤
            2 * ((st.curLastRebuilds + 1 : ℕ) : ℝ) * (levelM TP P P.d : ℝ)
          push_cast
          linarith
      hRecRebuild := fun j hj => hLoop.hLoopRecReb j hj
      hRecFwd := fun j hj => hLoop.hLoopRecFwd j hj
      hLvlM := hLoop.hLvlM.trans hInvOrig.hLvlM
      hN0 := hLoop.hN0.trans hInvOrig.hN0 }
    have hBudgetEnd : ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) := by
      refine ⟨?_, ?_⟩
      · rw [show stEnd.closedRuntime = stOrig.closedRuntime from hLoop.hClosed.1,
          show stEnd.curRestarts = stOrig.curRestarts from hLoop.hRestarts,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact le_trans hBudgetOrig.1 (by linarith)
      · rw [show stEnd.closedTreeUpdates = stOrig.closedTreeUpdates from hLoop.hClosed.2,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact hBudgetOrig.2
    have hStepDiff : (diffTreeChanges st.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length ≤
        fdChanges.length := by
      have hbi := diffTreeChanges_length_biUnion (Finset.range (P.d + 1))
        (fun j => (st.toTreeChain.activeLSF j).F.F.E)
        (fun j => (stEnd.toTreeChain.activeLSF j).F.F.E)
      have hsplit : Finset.range (P.d + 1) = insert P.d (Finset.range P.d) := by
        ext j; simp only [Finset.mem_range, Finset.mem_insert]; omega
      have hnot : P.d ∉ Finset.range P.d := by simp
      have hzero : (Finset.range P.d).sum (fun j =>
          (diffTreeChanges (st.toTreeChain.activeLSF j).F.F.E
            (stEnd.toTreeChain.activeLSF j).F.F.E).length) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [hToTC j (Finset.mem_range.mp hj), diffTreeChanges_length]
        simp
      change (diffTreeChanges st.toTreeChain.chainTreeEdges stEnd.toTreeChain.chainTreeEdges).length ≤ _
      unfold TreeChain.chainTreeEdges
      refine le_trans hbi ?_
      rw [hsplit, Finset.sum_insert hnot, hzero, add_zero]
      simp [TreeChain.activeLSF, ChainState.toTreeChain, stEnd, fdChanges, oldFdE, newFdE]
    have hTri := diffTreeChanges_length_triangle stOrig.toTreeChain.chainTree.E
      st.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E
    refine ⟨hInvEnd, hBudgetEnd, h0n, fun i => by rw [hLoop.hCnt.1], fun i => by rw [hLoop.hCnt.2], ?_⟩
    unfold ChainState.totalTreeUpdates
    change (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
        (stOrig.closedTreeUpdates + (Finset.range P.d).sum stOrig.curDecUpdates +
          stOrig.curLastTreeUpdates) ≤
      st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates +
        (st.curLastTreeUpdates + fdChanges.length)
    rw [hLoop.hClosed.2, hLoop.hLastStats.2.2]
    linarith [hLoop.hTreeDiff]

end MinCostFlow.Chain.Ordered
