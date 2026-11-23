module

public import MinCostFlow.Chain.Ordered.Theorem5_1Helpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rebuild Count Bounds and Unconditional Collapses for the Ordered Chain

Ordered-chain counterpart of `MinCostFlow/Chain/RebuildCollapse.lean`: unconditional rebuild bounds
(`alg2_rebuildCount_last_eq_zero*`, `alg2_rebuildCount_zero_collapse_uncond*`,
`alg2_rebuildCount_zero_le_upd*`) and derived collapse theorems (`Alg2RebuildCollapseHyp*`,
`alg2RebuildCollapseHyp_*`, `rebuildFloorHyp_*`, `theorem_5_1_collapsed*`), built on
`UpdateProofs`, `CollapseBounds`, `Lemma5_11`, `Algorithm2Facts`, and `Algorithm2Uncond`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section UnconditionalRebuildBounds

private lemma rebuildSuffix_updCount_lt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      k < idx →
      (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.1 k = upd k
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k, hk => by
    dsimp only [rebuildSuffix]
    rw [rebuildSuffix_updCount_lt T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k (Nat.lt_succ_of_lt hk)]
    simp [Nat.ne_of_lt hk]

private lemma rebuildSuffix_updCount_eq_zero (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      idx ≤ k → k < idx + rem →
      (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.2.1 k = 0
  | 0, _, _, _, _, _, _, _, _, _, hk1, hk2 => by omega
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k, hk1, hk2 => by
    dsimp only [rebuildSuffix]
    by_cases hkx : k = idx
    · subst hkx
      rw [rebuildSuffix_updCount_lt T L P lvlM N₀ ℓ₀ g₀ rem (k + 1) _ _ _ _ _ _ _ k (Nat.lt_succ_self k)]
      simp
    · exact rebuildSuffix_updCount_eq_zero T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k (by omega) (by omega)

private lemma rebuildSuffix_G_le (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State)
      (bran upd cEnc cDec cFwd : ℕ → ℕ) (k : ℕ),
      k ≤ idx →
      (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).1 k = G k
  | 0, _, _, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, k, hk => by
    dsimp only [rebuildSuffix]
    rw [rebuildSuffix_G_le T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _ k (Nat.le_succ_of_le hk)]
    simp [Nat.ne_of_lt (Nat.lt_succ_of_le hk)]

private lemma algorithm1_rebuild_rebuildCount_lt (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) {i₀ : ℕ} (hi : i₀ < P.d)
    (Gnew : MGraph) (extraEnc : ℕ) :
    (algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.rebuildCount =
      fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j := by
  dsimp only [algorithm1_rebuild]
  rw [dite_eq_left_of_eq_true (eq_true hi)]

private lemma algorithm1_shift_preserves_level0 {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (ch : ChainState T P) (i₀ : ℕ) :
    (algorithm1_shift T L P ch i₀).1.G 0 = ch.G 0 ∧
    (algorithm1_shift T L P ch i₀).1.rebuildCount = ch.rebuildCount ∧
    (algorithm1_shift T L P ch i₀).1.updCount 0 = ch.updCount 0 := by
  dsimp only [algorithm1_shift]
  split_ifs with hlt
  · refine ⟨?_, rfl, ?_⟩
    · exact rebuildSuffix_G_le T L P _ _ _ _ (P.d - (i₀ + 1)) (i₀ + 1) _ _ _ _ _ _ _ 0 (Nat.zero_le _)
    · exact rebuildSuffix_updCount_lt T L P _ _ _ _ (P.d - (i₀ + 1)) (i₀ + 1) _ _ _ _ _ _ _ 0 (by omega)
  · exact ⟨rfl, rfl, rfl⟩

/-- The loop of Algorithm 2 only shifts, so it keeps the level-`0` graph, the rebuild counts and the
update count of level `0`. -/
lemma alg2_loopWith_preserves_counters (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (B : ℕ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
      (lctOps : ℕ),
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ B →
      let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
      res.1.G 0 = ch.G 0 ∧
      res.1.rebuildCount = ch.rebuildCount ∧ res.1.updCount 0 = ch.updCount 0 := by
  intro B
  induction B with
  | zero =>
    intro ch branD passes lctOps hB
    rw [algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · exact ⟨rfl, rfl, rfl⟩
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · have hlt := shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap; omega
        · simp [hCap]
  | succ B ihB =>
    intro ch branD passes lctOps hB
    rw [algorithm2_loopWith.eq_1]; dsimp only
    split_ifs with hGood
    · exact ⟨rfl, rfl, rfl⟩
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)]
          have hlt := shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          let curB := if i.val < cfg.P.d then ch.bran i.val else branD
          let branD' := if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k
          let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
            if i < j then 0
            else if j = i then (if (curB + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j
          let lctOps' := lctOps + 2 * ((walkEdges (algorithm1_findCycle ch).2.1 \ ch.toTreeChain.chainTree.E).card + 1)
          have ihNext := ihB (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 branD' passes' lctOps' (by omega)
          have hSh := algorithm1_shift_preserves_level0 (L := cfg.L) ch i.val
          exact ⟨ihNext.1.trans hSh.1, ihNext.2.1.trans hSh.2.1, ihNext.2.2.trans hSh.2.2⟩
        · simp [hCap]

/-- The chain, external graph and name maps of the state after `algorithm2_updateWith`. -/
lemma algorithm2_updateWith_fields (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e'))).1
    let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    let G₀' := (st.chain.G 0).applyBatch tb.2.2.2.2
    let lp := algorithm2_loopWith cfg κ tb.1 (level0E2I ren G₀' tb.2.1) g' ℓ' ch1 bp1.1 bp1.2
      (st.lctUpdateOps + U_ext.length)
    let stNext := (algorithm2_updateWith cfg κ st U_ext g' ℓ' η).1
    stNext.chain = lp.1 ∧
    stNext.extG = tb.1 ∧
    stNext.extToInt = level0E2I ren G₀' tb.2.1 ∧
    stNext.intToExt = level0I2E ren G₀' tb.2.2.1 ∧
    stNext.nextFresh = level0NF ren G₀' tb.2.2.2.1 := by
  dsimp only [algorithm2_updateWith]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private lemma updateLoop_rebuildCount_last (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) (rem idx : ℕ)
    (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ) (hsum : idx + rem = P.d) :
    (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1.rebuildCount P.d =
      st.rebuildCount P.d := by
  rcases updateLoop_rebuildCount_cases T L TP P N₀ ℓ' g' rem idx st curG curU curEnc hsum with
    heq | ⟨iStar, _, hiLt, heq⟩
  · exact congrFun heq P.d
  · have hne : P.d ≠ iStar := Nat.ne_of_gt hiLt
    rw [heq]
    simp [hne]

/-- **Unconditional clause 2 of `RebuildFloorHyp`**: level `cfg.P.d` never self-rebuilds in
ordered Algorithm 1 / Algorithm 2, so `st.chain.rebuildCount cfg.P.d = 0` at every stage `t`. -/
theorem alg2_rebuildCount_last_eq_zero_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).chain.rebuildCount cfg.P.d = 0 := by
  induction t with
  | zero =>
    simp [minRatioFailState, algorithm2_dsWith, algorithm2_init, algorithm1_initialize]
  | succ t ih =>
    rw [minRatioFailState.eq_2]
    by_cases hupd : isUpdate (t + 1) = true
    · simp only [hupd, ↓reduceIte, algorithm2_dsWith]
      set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
      set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      set ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1
      set bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
        | none => (st.branD, st.passes)
        | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
      have hch1_pd : ch1.rebuildCount cfg.P.d = 0 := by
        dsimp only [ch1, algorithm1_update]
        rw [updateLoop_rebuildCount_last cfg.T cfg.L cfg.TP cfg.P cfg.N₀ _ _ cfg.P.d 0
          _ _ _ _ (Nat.zero_add _)]
        exact ih
      have hLp := alg2_loopWith_preserves_counters cfg κ tb.1
        (level0E2I (level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount)
          ((st.chain.G 0).applyBatch tb.2.2.2.2) tb.2.1) (D.g (t + 1)) (D.ℓ (t + 1))
        (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1)
        ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length) le_rfl
      change (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1.chain.rebuildCount cfg.P.d = 0
      rw [(algorithm2_updateWith_fields cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1,
        hLp.2.1, hch1_pd]
    · have hfalse : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, algorithm2_dsWith, algorithm2_detect]
      exact ih

theorem alg2_rebuildCount_last_eq_zero (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    (minRatioFailState (algorithm2_ds cfg) D η isUpdate t).chain.rebuildCount cfg.P.d = 0 :=
  alg2_rebuildCount_last_eq_zero_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate t

private lemma updateLoop_rebuildCount_zero_step (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) (st : ChainState T P)
    (curG : MGraph) (curU : List Update) (curEnc : ℕ) :
    let stEnd := (updateLoop T L TP P N₀ ℓ' g' P.d 0 st curG curU curEnc).1
    (intRebuildThreshold P N₀ 0 < st.updCount 0 + curU.length →
      stEnd.rebuildCount 0 = st.rebuildCount 0 + 1 ∧ stEnd.updCount 0 = 0) ∧
    (¬ (intRebuildThreshold P N₀ 0 < st.updCount 0 + curU.length) →
      stEnd.rebuildCount 0 = st.rebuildCount 0 ∧ stEnd.updCount 0 = st.updCount 0 + curU.length) := by
  have hd_pos : 0 < P.d := P.hd
  obtain ⟨d', hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd_pos.ne'
  rw [hd', updateLoop.eq_2]
  dsimp only
  constructor
  · intro hOver
    simp only [hOver, ↓reduceIte]
    have hReb : (algorithm1_rebuild T L P { st with ℓ := rebuildStartFn 0 curG ℓ', g := rebuildStartFn 0 curG g' } 0
        (rebuildStartGraph 0 curG) curEnc).1.rebuildCount 0 =
        st.rebuildCount 0 + 1 := by
      rw [algorithm1_rebuild_rebuildCount_lt T L P _ hd_pos (rebuildStartGraph 0 curG) curEnc]
      simp
    have hUpd : (algorithm1_rebuild T L P { st with ℓ := rebuildStartFn 0 curG ℓ', g := rebuildStartFn 0 curG g' } 0
        (rebuildStartGraph 0 curG) curEnc).1.updCount 0 = 0 := by
      dsimp only [algorithm1_rebuild]
      simp only [hd_pos, ↓reduceDIte]
      exact rebuildSuffix_updCount_eq_zero T L P _ _ _ _ (P.d - 0) 0 _ _ _ _ _ _ _ 0 (le_refl 0)
        (by have := hd_pos; omega)
    exact ⟨hReb, hUpd⟩
  · intro hNot
    simp only [hNot, ↓reduceIte]
    have hUpd0 : ∀ rem idx (s : ChainState T P) g u enc, idx + rem = P.d → 1 ≤ idx →
        (updateLoop T L TP P N₀ ℓ' g' rem idx s g u enc).1.updCount 0 = s.updCount 0 := by
      intro rem
      induction rem with
      | zero =>
        intro idx s g u enc _ _
        dsimp only [updateLoop]
        split_ifs <;> rfl
      | succ rem' ihR =>
        intro idx s g u enc hsum hidx
        dsimp only [updateLoop]
        split_ifs with hT
        · dsimp only [algorithm1_rebuild]
          split_ifs with hlt
          · exact rebuildSuffix_updCount_lt T L P _ _ _ _ (P.d - idx) idx _ _ _ _ _ _ _ 0 (by omega)
          · rfl
        · rw [ihR (idx + 1) _ _ _ _ (by omega) (by omega)]
          simp [show (0 : ℕ) ≠ idx by omega]
    refine ⟨?_, ?_⟩
    · rcases updateLoop_rebuildCount_cases T L TP P N₀ ℓ' g' d' 1 _ _ _ 0 (by omega) with
        heq | ⟨iStar, h1, _, heq⟩
      · simpa using congrFun heq 0
      · rw [heq]; simp [show (0 : ℕ) ≠ iStar by omega]
    · rw [hUpd0 d' 1 _ _ _ 0 (by omega) (le_refl 1)]
      simp

private lemma translateBatch_length_eq (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) :
    ∀ U : List Update, (translateBatch curExt e2i i2e nf U).2.2.2.2.length = U.length
  | [] => rfl
  | u :: rest => by
    simp [translateBatch, translateBatch_length_eq _ _ _ _ rest]

/-- **Unconditional level-`0` weighted rebuild collapse**: every level-`0` self-rebuild requires
`intRebuildThreshold P N₀ 0 + 1 ≤ updCount 0 + curU.length`, so ordered Algorithm 1 & 2 satisfy
`rebuildCount 0 * (intRebuildThreshold P N₀ 0 + 1) + updCount 0 ≤ alg2UpdateQueries D isUpdate T`
**unconditionally**. -/
theorem alg2_rebuildCount_zero_collapse_uncond_with (cfg : Alg2Config) (κ : ℝ)
    (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount 0 : ℝ) *
        ((intRebuildThreshold cfg.P cfg.N₀ 0 : ℝ) + 1) +
      ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.updCount 0 : ℝ) ≤
      (alg2UpdateQueries D isUpdate T : ℝ) := by
  set thr : ℕ := intRebuildThreshold cfg.P cfg.N₀ 0
  induction T with
  | zero =>
    unfold alg2UpdateQueries
    simp only [minRatioFailState, algorithm2_dsWith, algorithm2_init, algorithm1_initialize,
      Nat.cast_zero, zero_mul, zero_add]
    have hu0 : (rebuildSuffix cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.ℓ 0) (D.g 0) cfg.P.d 0
        (fun _ => D.G 0)
        (fun _ => cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P 0) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0) (sortedEnds (D.G 0)))
        (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)).2.2.2.1 0 = 0 :=
      rebuildSuffix_updCount_eq_zero cfg.T cfg.L cfg.P _ _ _ _ cfg.P.d 0
        _ _ _ _ _ _ _ 0 (le_refl 0) (by simpa using cfg.P.hd)
    rw [hu0]
    simp
  | succ t ih =>
    have hIcc : alg2UpdateQueries D isUpdate (t + 1) =
        alg2UpdateQueries D isUpdate t + (if isUpdate (t + 1) then (D.U (t + 1)).length else 0) := by
      unfold alg2UpdateQueries
      rw [Finset.sum_Icc_succ_top (Nat.succ_pos t)]
    rw [minRatioFailState.eq_2, hIcc]
    by_cases hupd : isUpdate (t + 1) = true
    · simp only [hupd, ↓reduceIte, algorithm2_dsWith, Nat.cast_add]
      set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
      set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      set ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1
      set bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
        | none => (st.branD, st.passes)
        | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
      have hlen : tb.2.2.2.2.length = (D.U (t + 1)).length :=
        translateBatch_length_eq _ _ _ _ (D.U (t + 1))
      have hStep := updateLoop_rebuildCount_zero_step cfg.T cfg.L cfg.TP cfg.P cfg.N₀
        (fun e' => D.ℓ (t + 1) (tb.2.2.1 e')) (fun e' => D.g (t + 1) (tb.2.2.1 e'))
        { st.chain with recUpdates := fun j => if j = 0 then st.chain.recUpdates 0 + tb.2.2.2.2.length else st.chain.recUpdates j }
        ((st.chain.G 0).applyBatch tb.2.2.2.2) tb.2.2.2.2 ((st.chain.G 0).batchEnc tb.2.2.2.2)
      dsimp only at hStep
      have hch1_le : (ch1.rebuildCount 0 : ℝ) * ((thr : ℝ) + 1) + (ch1.updCount 0 : ℝ) ≤
          (st.chain.rebuildCount 0 : ℝ) * ((thr : ℝ) + 1) + (st.chain.updCount 0 : ℝ) +
            ((D.U (t + 1)).length : ℝ) := by
        change ((updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ _ _ cfg.P.d 0 _ _ _ _).1.rebuildCount 0 : ℝ) * ((thr : ℝ) + 1) +
          ((updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ _ _ cfg.P.d 0 _ _ _ _).1.updCount 0 : ℝ) ≤ _
        by_cases hOver : thr < st.chain.updCount 0 + tb.2.2.2.2.length
        · have hStep' := hStep.1 hOver
          have hSucc : (thr : ℝ) + 1 ≤ (st.chain.updCount 0 : ℝ) + ((D.U (t + 1)).length : ℝ) := by
            rw [← hlen]
            exact_mod_cast (Nat.succ_le_of_lt hOver)
          rw [hStep'.1, hStep'.2, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
          nlinarith
        · have hStep' := hStep.2 hOver
          rw [hStep'.1, hStep'.2, hlen, Nat.cast_add]
          linarith
      have hL := alg2_loopWith_preserves_counters cfg κ tb.1
        (level0E2I (level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount)
          ((st.chain.G 0).applyBatch tb.2.2.2.2) tb.2.1) (D.g (t + 1)) (D.ℓ (t + 1))
        (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1)
        ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length) le_rfl
      change ((algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1.chain.rebuildCount 0 : ℝ) * ((thr : ℝ) + 1) +
        ((algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1.chain.updCount 0 : ℝ) ≤ _
      rw [(algorithm2_updateWith_fields cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1,
        hL.2.1, hL.2.2]
      linarith
    · have hfalse : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
      simp only [hfalse, Bool.false_eq_true, ↓reduceIte, algorithm2_dsWith, algorithm2_detect, add_zero]
      exact ih

theorem alg2_rebuildCount_zero_collapse_uncond (cfg : Alg2Config)
    (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    ((minRatioFailState (algorithm2_ds cfg) D η isUpdate T).chain.rebuildCount 0 : ℝ) *
        ((intRebuildThreshold cfg.P cfg.N₀ 0 : ℝ) + 1) +
      ((minRatioFailState (algorithm2_ds cfg) D η isUpdate T).chain.updCount 0 : ℝ) ≤
      (alg2UpdateQueries D isUpdate T : ℝ) :=
  alg2_rebuildCount_zero_collapse_uncond_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    D η isUpdate T

/-- **Unconditional level-`0` unweighted bound**: `rebuildCount 0 + updCount 0 ≤ alg2UpdateQueries`. -/
theorem alg2_rebuildCount_zero_le_upd_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount 0 +
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.updCount 0 ≤
      alg2UpdateQueries D isUpdate T := by
  have hU := alg2_rebuildCount_zero_collapse_uncond_with cfg κ D η isUpdate T
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
  have h1 : (1 : ℝ) ≤ (intRebuildThreshold cfg.P cfg.N₀ 0 : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (intRebuildThreshold cfg.P cfg.N₀ 0)]
  have h2 : (st.chain.rebuildCount 0 : ℝ) * 1 ≤
      (st.chain.rebuildCount 0 : ℝ) * ((intRebuildThreshold cfg.P cfg.N₀ 0 : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hR : ((st.chain.rebuildCount 0 + st.chain.updCount 0 : ℕ) : ℝ) ≤
      (alg2UpdateQueries D isUpdate T : ℝ) := by
    rw [Nat.cast_add]; linarith
  exact_mod_cast hR

theorem alg2_rebuildCount_zero_le_upd (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    (minRatioFailState (algorithm2_ds cfg) D η isUpdate T).chain.rebuildCount 0 +
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate T).chain.updCount 0 ≤
      alg2UpdateQueries D isUpdate T :=
  alg2_rebuildCount_zero_le_upd_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    D η isUpdate T

end UnconditionalRebuildBounds

section DerivedRebuildCollapse

/-- Scaled rebuild-collapse property (`jtree.tex` line 848) for ordered `algorithm2_dsWith cfg κ`. -/
def Alg2RebuildCollapseHypWith (κ : ℝ) (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : Prop :=
  ∀ i < cfg.P.d,
    ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount i : ℝ) *
      ((cfg.P.M₀ : ℝ) / ((cfg.P.k : ℝ) ^ (i + 1) * (logFactor cfg.P cfg.N₀) ^ 2)) ≤
      16 * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ i * (alg2UpdateQueries D isUpdate T : ℝ) +
        (cfg.P.M₀ : ℝ) / ((cfg.P.k : ℝ) ^ (i + 1) * (logFactor cfg.P cfg.N₀) ^ 2)

/-- Scaled rebuild-collapse property (`jtree.tex` line 848) for ordered `algorithm2_ds`. -/
abbrev Alg2RebuildCollapseHyp (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : Prop :=
  Alg2RebuildCollapseHypWith (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) cfg D η isUpdate T

/-- `Alg2RebuildCollapseHypWith` together with `alg2_rebuildCount_last_eq_zero_with` yields
`RebuildFloorHyp` for `selfReb = st.chain.rebuildCount`. -/
lemma rebuildFloorHyp_of_collapseHyp_with {κ : ℝ} {cfg : Alg2Config} {D : DynamicInstance}
    {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hCol : Alg2RebuildCollapseHypWith κ cfg D η isUpdate T) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      st.chain.rebuildCount st.chain.rebuildCount :=
  ⟨fun i _ => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self i)),
    alg2_rebuildCount_last_eq_zero_with cfg κ D η isUpdate T, hCol⟩

lemma rebuildFloorHyp_of_collapseHyp {cfg : Alg2Config} {D : DynamicInstance}
    {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hCol : Alg2RebuildCollapseHyp cfg D η isUpdate T) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      st.chain.rebuildCount st.chain.rebuildCount :=
  rebuildFloorHyp_of_collapseHyp_with hCol

/-- When `cfg.P.d = 1`, `Alg2RebuildCollapseHypWith` holds **completely unconditionally**. -/
theorem alg2RebuildCollapseHyp_of_d_one_with {cfg : Alg2Config} (κ : ℝ) (_hTP : cfg.TP.Valid)
    (hd : cfg.P.d = 1) (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    Alg2RebuildCollapseHypWith κ cfg D η isUpdate T := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hUncond := alg2_rebuildCount_zero_collapse_uncond_with cfg κ D η isUpdate T
  have hTh := m0_div_logFactor_le_sixteen_mul_intRebuildThreshold_succ cfg.P cfg.N₀ 0
  have hMul : ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount 0 : ℝ) *
      ((cfg.P.M₀ : ℝ) / ((cfg.P.k : ℝ) ^ (0 + 1) * (logFactor cfg.P cfg.N₀) ^ 2)) ≤
      16 * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ 0 * (alg2UpdateQueries D isUpdate T : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hTh
      (Nat.cast_nonneg ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount 0))
    have h2 : (0 : ℝ) ≤ ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.updCount 0 : ℝ) :=
      Nat.cast_nonneg _
    rw [pow_zero, mul_one]
    linarith
  exact le_add_of_le_of_nonneg hMul (by positivity)

theorem alg2RebuildCollapseHyp_of_d_one {cfg : Alg2Config} (hTP : cfg.TP.Valid) (hd : cfg.P.d = 1)
    (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    Alg2RebuildCollapseHyp cfg D η isUpdate T :=
  alg2RebuildCollapseHyp_of_d_one_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hTP hd
    D η isUpdate T

/-- `RebuildFloorHyp` holds unconditionally when `cfg.P.d = 1` for ordered `algorithm2_dsWith cfg κ`. -/
theorem rebuildFloorHyp_of_d_one_with {cfg : Alg2Config} (κ : ℝ) (hTP : cfg.TP.Valid) (hd : cfg.P.d = 1)
    (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      st.chain.rebuildCount st.chain.rebuildCount :=
  rebuildFloorHyp_of_collapseHyp_with (alg2RebuildCollapseHyp_of_d_one_with κ hTP hd D η isUpdate T)

theorem rebuildFloorHyp_of_d_one {cfg : Alg2Config} (hTP : cfg.TP.Valid) (hd : cfg.P.d = 1)
    (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      st.chain.rebuildCount st.chain.rebuildCount :=
  rebuildFloorHyp_of_d_one_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hTP hd D η isUpdate T

/-- For all `d ≥ 1`, `Alg2RebuildCollapseHypWith` follows directly from `cfg.ValidOrdNoHidden`. -/
theorem alg2RebuildCollapseHyp_uncond_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    Alg2RebuildCollapseHypWith κ cfg D η isUpdate T := by
  intro i hi
  have hInv := ((algorithm2_uncond_preserves_with (η := η) κ hV hHist hEdge hLen hmBound hnBound).1
    T (le_refl T)).1
  have hRec := hInv.hRecFwd
  have hZero := algorithm2_uncond_recUpdates_zero_eq_with (η := η) hV κ hHist hEdge
    hLen hmBound hnBound T (le_refl T)
  have hγr_nn : 0 ≤ cfg.TP.γ_r (cfg.P.M₀ ^ 2) :=
    le_trans zero_le_one (hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2))
  have hReb := hInv.hRecRebuild i hi
  have hPow := hRec.recUpdates_le_pow hγr_nn i (le_of_lt hi)
  rw [hZero] at hPow
  have hTh := m0_div_logFactor_le_sixteen_mul_intRebuildThreshold_succ cfg.P cfg.N₀ i
  have hUpd_nn : (0 : ℝ) ≤ ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.updCount i : ℝ) :=
    Nat.cast_nonneg _
  have hMul := mul_le_mul_of_nonneg_left hTh (Nat.cast_nonneg
    ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount i))
  have hLe : ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount i : ℝ) *
      ((cfg.P.M₀ : ℝ) / ((cfg.P.k : ℝ) ^ (i + 1) * (logFactor cfg.P cfg.N₀) ^ 2)) ≤
      16 * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ i * (alg2UpdateQueries D isUpdate T : ℝ) := by
    have : (alg2UpdateQueries D isUpdate T : ℝ) =
        ∑ s ∈ Finset.Icc 1 T, if isUpdate s = true then ((D.U s).length : ℝ) else 0 := by
      unfold alg2UpdateQueries; push_cast; rfl
    have hPowQ : (((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.recUpdates i : ℕ) : ℝ) ≤
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ i * (alg2UpdateQueries D isUpdate T : ℝ) := by
      simpa only [alg2UpdateQueries] using hPow
    linarith
  exact le_add_of_le_of_nonneg hLe (by positivity)

theorem alg2RebuildCollapseHyp_uncond
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    Alg2RebuildCollapseHyp cfg D η isUpdate T :=
  alg2RebuildCollapseHyp_uncond_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound

/-- Unconditional `RebuildFloorHyp` for all `d ≥ 1` under `cfg.ValidOrdNoHidden` for
ordered `algorithm2_dsWith cfg κ`. -/
theorem rebuildFloorHyp_uncond_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      st.chain.rebuildCount st.chain.rebuildCount :=
  rebuildFloorHyp_of_collapseHyp_with
    (alg2RebuildCollapseHyp_uncond_with κ hV hHist hEdge hLen hmBound hnBound)

theorem rebuildFloorHyp_uncond
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      st.chain.rebuildCount st.chain.rebuildCount :=
  rebuildFloorHyp_uncond_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound

/-- Unconditional collapsed total runtime + LCT charge when `cfg.P.d = 1` for ordered `algorithm2_dsWith cfg κ`. -/
theorem theorem_5_1_collapsed_d_one_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    (hd : cfg.P.d = 1)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2)) ∧
    ((∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) →
      (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot) := by
  have hFl := rebuildFloorHyp_of_d_one_with κ hV.hTP hd D η isUpdate T
  exact ⟨theorem_5_1_collapsed_of_floor_with κ hV hHist hEdge hLen hmBound hnBound _ hFl,
    fun hSmall => theorem_5_1_collapsed_of_floor_smallBatch_with
      κ hV hHist hEdge hLen hmBound hnBound hSmall _ hFl⟩

theorem theorem_5_1_collapsed_d_one
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    (hd : cfg.P.d = 1)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSize cfg D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2)) ∧
    ((∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) →
      (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot) :=
  theorem_5_1_collapsed_d_one_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hd hHist hEdge hLen hmBound hnBound

/-- Unconditional collapsed total runtime + LCT charge for all `d ≥ 1` under `cfg.ValidOrdNoHidden`
for ordered `algorithm2_dsWith cfg κ`. -/
theorem theorem_5_1_collapsed_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2)) ∧
    ((∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) →
      (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot) := by
  have hFl := rebuildFloorHyp_uncond_with (η := η) κ hV hHist hEdge hLen hmBound hnBound
  exact ⟨theorem_5_1_collapsed_of_floor_with κ hV hHist hEdge hLen hmBound hnBound _ hFl,
    fun hSmall => theorem_5_1_collapsed_of_floor_smallBatch_with
      κ hV hHist hEdge hLen hmBound hnBound hSmall _ hFl⟩

theorem theorem_5_1_collapsed
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSize cfg D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2)) ∧
    ((∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) →
      (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot) :=
  theorem_5_1_collapsed_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound

end DerivedRebuildCollapse

end MinCostFlow.Chain.Ordered
