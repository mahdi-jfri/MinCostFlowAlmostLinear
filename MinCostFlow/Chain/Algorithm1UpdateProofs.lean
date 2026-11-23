module

public import MinCostFlow.Chain.Algorithm1UpdateStepNoRebuild
public import MinCostFlow.Chain.Algorithm1Proofs
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Update-loop invariant and budget preservation for Algorithm 1

This file proves `updateLoop_preserves` and `update_preserves`, showing that
`algorithm1_update` preserves `ChainInv` and `ChainBudgetInv`, emits exact `TreeChange`
diffs for `T^𝒢`, and increases `totalTreeUpdates` by at least `changes.length`.
-/

@[expose] public section

namespace MinCostFlow.Chain

lemma updateLoop_preserves_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      UpdateLoopInv TP N₀ extraOverflow stOrig st ℓ' g' rem idx curG curU curEncAcc →
      let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc
      ChainInv T L TP LP P N₀ stEnd ∧
      ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) ∧
      (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
      (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
      (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
      (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
        stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEncAcc hLoop
    exact updateLoop_zero_step T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk hInvOrig
      hBudgetOrig hExtraNN ℓ' g' idx st curG curU curEncAcc hLoop
  | succ rem' ih =>
    intro idx st curG curU curEncAcc hLoop
    by_cases hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length
    · exact updateLoop_succ_over_step T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk hInvOrig
        hBudgetOrig hExtraNN ℓ' g' rem' idx st curG curU curEncAcc hLoop hOver
    · obtain ⟨stNext, nextG, nextU, hEq, hLoopNext⟩ :=
        updateLoop_succ_notOver_step T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk hInvOrig
          hBudgetOrig hExtraNN ℓ' g' rem' idx st curG curU curEncAcc hLoop hOver
      have hIH := ih (idx + 1) stNext nextG nextU 0 hLoopNext
      simpa [hEq] using hIH

lemma updateLoop_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    (hBudgetOrig : ChainBudgetInv TP LP N₀ stOrig) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      UpdateLoopInv TP N₀ 0 stOrig st ℓ' g' rem idx curG curU curEncAcc →
      let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc
      ChainInv T L TP LP P N₀ stEnd ∧
      ChainBudgetInv TP LP N₀ stEnd ∧
      (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
      (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
      (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
      (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
        stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  intro rem idx st curG curU curEncAcc hLoop
  have h := updateLoop_preserves_with_noHidden T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk
    hInvOrig hBudgetOrig.toWith (le_refl 0) ℓ' g' rem idx st curG curU curEncAcc hLoop
  dsimp only at h ⊢
  rcases h with ⟨h1, h2, h3⟩
  exact ⟨h1, ChainBudgetInvWith.toZero (by simpa using h2), h3⟩

lemma updateLoop_preserves (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestart)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    (hBudgetOrig : ChainBudgetInv TP LP N₀ stOrig) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      UpdateLoopInv TP N₀ 0 stOrig st ℓ' g' rem idx curG curU curEncAcc →
      let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc
      ChainInv T L TP LP P N₀ stEnd ∧
      ChainBudgetInv TP LP N₀ stEnd ∧
      (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
      (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
      (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
      (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
        stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates :=
  updateLoop_preserves_noHidden T L TP LP P hTP hLP hT.toNoHidden hL
    hNoReinsTool.toNoHidden hγM₀ hγk hInvOrig hBudgetOrig ℓ' g'

/-- Extra runtime encoding allowance when an external update batch exceeds `P.M₀` updates. -/
noncomputable def largeBatchEncCap (P : ChainParams) (U : List Update) : ℝ :=
  if U.length ≤ P.M₀ then 0
  else 20 * ((P.M₀ : ℝ) + (U.length : ℝ)) * Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2)

lemma largeBatchEncCap_nonneg (P : ChainParams) (U : List Update) :
    0 ≤ largeBatchEncCap P U := by
  unfold largeBatchEncCap
  split_ifs
  · exact le_rfl
  · have hlog : 0 ≤ Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _,
        show (0 : ℝ) ≤ U.length from Nat.cast_nonneg _])
    positivity

lemma update_preserves_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {overflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow)
    (U : List Update) (g' ℓ' : ℕ → ℝ)
    (hBatch : (st.G 0).BatchIsValid U)
    (_hNoReins : NoBatchReinsert (st.G 0) U)
    (hG0'Valid : ((st.G 0).applyBatch U).IsValid)
    (hG0'm : ((st.G 0).applyBatch U).m ≤ P.M₀)
    (hG0'n : ((st.G 0).applyBatch U).n ≤ N₀)
    (hℓ'Pos : ∀ e ∈ ((st.G 0).applyBatch U).E, 0 < ℓ' e)
    (hℓ'Stable : ∀ e ∈ ((st.G 0).applyBatch U).E, e ∈ (st.G 0).E →
      (∀ u ∈ U, ¬ u.Inserts e) → ℓ' e = st.ℓ e) :
    let (st', changes) := algorithm1_update T L TP P N₀ st U g' ℓ'
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInvWith TP LP N₀ st' (overflow + largeBatchEncCap P U) ∧
    (st.G 0).n ≤ (st'.G 0).n ∧
    (∀ i, st.shiftCount i = st'.shiftCount i) ∧
    (∀ i, st.rebuildCount i ≤ st'.rebuildCount i) ∧
    changes.length + st.totalTreeUpdates ≤ st'.totalTreeUpdates := by
  set G₀' := (st.G 0).applyBatch U
  set enc₀ := (st.G 0).batchEnc U
  let st₀ : ChainState T P :=
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
  have hEncCap : (enc₀ : ℝ) ≤ extraEncCap P + largeBatchEncCap P U := by
    have h21 := lemma_2_1_batch hInv.hG0Valid hBatch
    have hm_le : (st.G 0).m ≤ P.M₀ := hInv.hG0m
    have hlog_ext : 0 ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _])
    have hextra_nn : 0 ≤ extraEncCap P := by unfold extraEncCap; positivity
    by_cases hlen : U.length ≤ P.M₀
    · have hsum : ((st.G 0).m : ℝ) + (U.length : ℝ) ≤ 2 * (P.M₀ : ℝ) := by
        exact_mod_cast (by omega : (st.G 0).m + U.length ≤ 2 * P.M₀)
      have hlog0 : 0 ≤ Real.log (((st.G 0).m : ℝ) + (U.length : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (st.G 0).m from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ U.length from Nat.cast_nonneg _])
      have hlogLe : Real.log (((st.G 0).m : ℝ) + (U.length : ℝ) + 2) ≤ Real.log (2 * (P.M₀ : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h1 : (enc₀ : ℝ) ≤ extraEncCap P := by
        unfold extraEncCap
        calc
          (enc₀ : ℝ)
              ≤ 20 * (((st.G 0).m : ℝ) + (U.length : ℝ)) *
                  Real.log (((st.G 0).m : ℝ) + (U.length : ℝ) + 2) := h21
          _ ≤ 20 * (2 * (P.M₀ : ℝ)) * Real.log (2 * (P.M₀ : ℝ) + 2) := by gcongr
          _ = 40 * (P.M₀ : ℝ) * Real.log (2 * (P.M₀ : ℝ) + 2) := by ring
      simpa [largeBatchEncCap, hlen] using h1
    · have hlog0 : 0 ≤ Real.log (((st.G 0).m : ℝ) + (U.length : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (st.G 0).m from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ U.length from Nat.cast_nonneg _])
      have hm_r : ((st.G 0).m : ℝ) ≤ P.M₀ := by exact_mod_cast hm_le
      have hlogLe : Real.log (((st.G 0).m : ℝ) + (U.length : ℝ) + 2) ≤
          Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have h1 : (enc₀ : ℝ) ≤ largeBatchEncCap P U := by
        unfold largeBatchEncCap
        simp only [hlen, ↓reduceIte]
        calc
          (enc₀ : ℝ)
              ≤ 20 * (((st.G 0).m : ℝ) + (U.length : ℝ)) *
                  Real.log (((st.G 0).m : ℝ) + (U.length : ℝ) + 2) := h21
          _ ≤ 20 * ((P.M₀ : ℝ) + (U.length : ℝ)) *
                Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) := by gcongr
      linarith
  have hLoop0 : UpdateLoopInv TP N₀ (largeBatchEncCap P U) st st₀ ℓ' g' P.d 0 G₀' U enc₀ := {
    hidxSum := Nat.zero_add P.d
    hGGe := fun _ _ => rfl
    hScGe := fun _ _ => rfl
    hRestarts := rfl
    hUpdGe := fun _ _ => rfl
    hDecGe := fun _ _ => rfl
    hEncGt := fun _ _ => rfl
    hCurFwdGe := fun _ _ => rfl
    hRecGt := fun j hj => by change (if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j) = _; simp [Nat.ne_of_gt hj]
    hCurRecAt := by change (if (0 : ℕ) = 0 then st.recUpdates 0 + U.length else st.recUpdates 0) = _; rfl
    hBran := rfl
    hLast := ⟨rfl, rfl, rfl⟩
    hLG := ⟨rfl, rfl⟩
    hCnt := ⟨rfl, rfl⟩
    hClosed := ⟨rfl, rfl⟩
    hLastStats := ⟨rfl, rfl, rfl⟩
    hG0New := fun h0 => absurd h0 (lt_irrefl 0)
    hPreHist := fun _ hj => absurd hj (Nat.not_lt_zero _)
    hPreGSucc := fun _ hj => absurd hj (Nat.not_lt_zero _)
    hPreV := fun _ hj => absurd hj (Nat.not_lt_zero _)
    hPreM := fun _ hj => absurd hj (Nat.not_lt_zero _)
    hPreEnc0 := fun h0 => absurd h0 (lt_irrefl 0)
    hLoopRecReb := fun _ hj => absurd hj (Nat.not_lt_zero _)
    hLoopRecFwd := fun _ hj => absurd hj (Nat.not_lt_zero _)
    hPreLastReb := fun h0 hpd => absurd h0 (Nat.ne_of_lt hpd)
    hCurGEq := rfl
    hCurGBatch := hBatch
    hCurGValid := hG0'Valid
    hCurGM := by
      have hm0 : (G₀'.m : ℝ) ≤ P.M₀ := by exact_mod_cast hG0'm
      have hγ1 := hTP.2.2.1 (P.M₀ ^ 2)
      have hmul : (P.M₀ : ℝ) ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := by
        nlinarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _]
      have hceil : (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ 0 ≤
          (levelM TP P 0 : ℝ) := Nat.le_ceil _
      simp only [pow_zero, mul_one] at hceil
      linarith
    hCurGV0 := fun _ => ⟨hG0'm, hG0'n, applyBatch_V_subset (st.G 0) U, hℓ'Pos⟩
    hCurGVPos := fun h0 => absurd h0 (lt_irrefl 0)
    hCurGFromPrev := fun h0 => absurd h0 (lt_irrefl 0)
    hCurEnc0 := fun _ => ⟨rfl, rfl, hEncCap⟩
    hCurEncPos := fun h0 => absurd h0 (lt_irrefl 0)
    hCurLenPos := fun e he => hℓ'Pos e he
    hCurLenStable := fun e he1 he2 hno => hℓ'Stable e he1 he2 hno
    hDecMono := fun _ _ => le_refl _
    hTreeDiff := by
      have hE : st₀.toTreeChain.chainTree.E = st.toTreeChain.chainTree.E := rfl
      rw [hE, diffTreeChanges_length]
      simp [st₀]
    hLvlM := rfl
    hN0 := rfl }
  have hRes := updateLoop_preserves_with_noHidden T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk
    hInv hBudget (largeBatchEncCap_nonneg P U) ℓ' g' P.d 0 st₀ G₀' U enc₀ hLoop0
  dsimp only [algorithm1_update]
  exact hRes

theorem update_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st)
    (U : List Update) (g' ℓ' : ℕ → ℝ)
    (hBatch : (st.G 0).BatchIsValid U)
    (hNoReins : NoBatchReinsert (st.G 0) U)
    (hG0'Valid : ((st.G 0).applyBatch U).IsValid)
    (hG0'm : ((st.G 0).applyBatch U).m ≤ P.M₀)
    (hG0'n : ((st.G 0).applyBatch U).n ≤ N₀)
    (hULen : U.length ≤ P.M₀)
    (hℓ'Pos : ∀ e ∈ ((st.G 0).applyBatch U).E, 0 < ℓ' e)
    (hℓ'Stable : ∀ e ∈ ((st.G 0).applyBatch U).E, e ∈ (st.G 0).E →
      (∀ u ∈ U, ¬ u.Inserts e) → ℓ' e = st.ℓ e) :
    let (st', changes) := algorithm1_update T L TP P N₀ st U g' ℓ'
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInv TP LP N₀ st' ∧
    (st.G 0).n ≤ (st'.G 0).n ∧
    (∀ i, st.shiftCount i = st'.shiftCount i) ∧
    (∀ i, st.rebuildCount i ≤ st'.rebuildCount i) ∧
    changes.length + st.totalTreeUpdates ≤ st'.totalTreeUpdates := by
  have h := update_preserves_with_noHidden T L TP LP P hTP hLP hT hL hNoReinsTool hγM₀ hγk
    hInv hBudget.toWith U g' ℓ' hBatch hNoReins hG0'Valid hG0'm hG0'n hℓ'Pos hℓ'Stable
  dsimp only at h ⊢
  rcases h with ⟨h1, h2, h3⟩
  have hcap0 : (0 : ℝ) + largeBatchEncCap P U = 0 := by simp [largeBatchEncCap, hULen]
  rw [hcap0] at h2
  exact ⟨h1, h2.toZero, h3⟩

/-- **Algorithm 1 `Update(U, g', ℓ')` preservation**: given a valid non-reinserting update batch
`U` of size `|U| ≤ P.M₀` producing a valid graph `G₀'` with `m ≤ P.M₀` and `n ≤ N₀`, positive
lengths `ℓ'` stable on surviving non-inserted edges, `algorithm1_update` preserves `ChainInv` and
`ChainBudgetInv`, does not shrink `(st.G 0).n`, leaves `shiftCount` unchanged, never decreases
`rebuildCount`, and increases `totalTreeUpdates` by at least the number of emitted `TreeChange`s
for `T^𝒢`. -/
theorem update_preserves (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hNoReinsTool : T.ToolNoReinsertRestart)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st)
    (U : List Update) (g' ℓ' : ℕ → ℝ)
    (hBatch : (st.G 0).BatchIsValid U)
    (hNoReins : NoBatchReinsert (st.G 0) U)
    (hG0'Valid : ((st.G 0).applyBatch U).IsValid)
    (hG0'm : ((st.G 0).applyBatch U).m ≤ P.M₀)
    (hG0'n : ((st.G 0).applyBatch U).n ≤ N₀)
    (hULen : U.length ≤ P.M₀)
    (hℓ'Pos : ∀ e ∈ ((st.G 0).applyBatch U).E, 0 < ℓ' e)
    (hℓ'Stable : ∀ e ∈ ((st.G 0).applyBatch U).E, e ∈ (st.G 0).E →
      (∀ u ∈ U, ¬ u.Inserts e) → ℓ' e = st.ℓ e) :
    let (st', changes) := algorithm1_update T L TP P N₀ st U g' ℓ'
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInv TP LP N₀ st' ∧
    (st.G 0).n ≤ (st'.G 0).n ∧
    (∀ i, st.shiftCount i = st'.shiftCount i) ∧
    (∀ i, st.rebuildCount i ≤ st'.rebuildCount i) ∧
    changes.length + st.totalTreeUpdates ≤ st'.totalTreeUpdates :=
  update_preserves_noHidden T L TP LP P hTP hLP hT.toNoHidden hL
    hNoReinsTool.toNoHidden hγM₀ hγk hInv hBudget U g' ℓ' hBatch hNoReins hG0'Valid hG0'm hG0'n
    hULen hℓ'Pos hℓ'Stable

end MinCostFlow.Chain
