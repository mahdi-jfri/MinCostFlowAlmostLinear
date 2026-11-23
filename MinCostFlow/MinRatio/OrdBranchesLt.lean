module

public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.Chain.Ordered.NextFreshBound
public import MinCostFlow.MinRatio.ShiftGuards
import Mathlib.Tactic

/-!
# Branch-index invariant and word-fit bounds for Algorithm 2

Proves that the active branch index at every level of ordered Algorithm 2 stays strictly below
`cfg.P.k` (`BranchesLtK`), unconditionally from `cfg.P.hk : 0 < cfg.P.k`:
- `branchesLtK_init` for `Chain.Ordered.algorithm2_init`;
- `algorithm1_update_bran` and `algorithm1_shift_bran` for Algorithm 1;
- `branchesLtK_loopWith`, `branchesLtK_update`, and `branchesLtK_detect` for Algorithm 2.

Also provides two word-fit helper lemmas used when checking the preconditions of
`ChainRefreshStepSpec` and `ShiftLevelStepSpec`:
- `keyWord_lt_of_nameBound`: derives `2 * (model.nextFresh + U.length) + 1 < 2 ^ w` from
  the name bound on `model.nextFresh`, `U.length ≤ 2 * m`, and a single constant word bound;
- `shiftQuotaWord_le_of_rebuildCount_le`: bounds `shiftQuotaWord` in terms of an upper bound
  on the rebuild counts.
-/

public section

namespace MinCostFlow.MinRatio

open Chain Chain.Ordered

/-- Active branch-index invariant of ordered Algorithm 2: every level `i < d` has
`bran i < k`, and the top-level branch counter `branD` satisfies `branD < k`. -/
@[expose] def BranchesLtK (cfg : Alg2Config) (model : Alg2State cfg) : Prop :=
  (∀ i < cfg.P.d, model.chain.bran i < cfg.P.k) ∧ model.branD < cfg.P.k

theorem rebuildSuffix_bran (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      (∀ j < P.d, bran j < P.k) →
      ∀ j < P.d,
        (Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd).2.2.1 j <
          P.k
  | 0, _, _, _, _, _, _, _, _, hbr, j, hj => hbr j hj
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, hbr, j, hj => by
    unfold Ordered.rebuildSuffix
    dsimp only
    apply rebuildSuffix_bran T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1)
    · intro l hl
      by_cases hli : l = idx
      · subst hli; simp [P.hk]
      · simp [hli, hbr l hl]
    · exact hj

theorem algorithm1_initialize_bran (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ j < P.d, (Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.bran j < P.k := by
  unfold Ordered.algorithm1_initialize
  dsimp only
  exact rebuildSuffix_bran T L P lvlM N₀ ℓ₀ g₀ P.d 0 _ _ _ _ _ _ _ (fun _ _ => P.hk)

theorem algorithm1_rebuild_bran (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (st : ChainState T P) (i₀ : ℕ) (Gnew : MGraph) (extraEnc : ℕ := 0)
    (hbr : ∀ j < P.d, st.bran j < P.k) :
    ∀ j < P.d, (Ordered.algorithm1_rebuild T L P st i₀ Gnew extraEnc).1.bran j < P.k := by
  unfold Ordered.algorithm1_rebuild
  split_ifs with hi
  · dsimp only
    exact rebuildSuffix_bran T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ _ _ _ _ _ _ _ hbr
  · exact hbr

theorem updateLoop_bran (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ),
      (∀ j < P.d, st.bran j < P.k) →
      ∀ j < P.d, (Ordered.updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc).1.bran j < P.k
  | 0, _, st, curG, curU, _, hbr, j, hj => by
    unfold Ordered.updateLoop
    split_ifs <;> exact hbr j hj
  | rem + 1, idx, st, curG, curU, curEncStep, hbr, j, hj => by
    unfold Ordered.updateLoop
    split_ifs with hthr
    · exact algorithm1_rebuild_bran T L P _ idx _ curEncStep (by exact hbr) j hj
    · dsimp only
      exact updateLoop_bran T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0 (by exact hbr) j hj

theorem algorithm1_update_bran (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) (hbr : ∀ j < P.d, st.bran j < P.k) :
    ∀ j < P.d, (Ordered.algorithm1_update T L TP P N₀ st U g' ℓ').1.bran j < P.k := by
  unfold Ordered.algorithm1_update
  dsimp only
  exact updateLoop_bran T L TP P N₀ ℓ' g' P.d 0 _ _ U _ hbr

theorem algorithm1_shift_bran (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (st : ChainState T P) (i₀ : ℕ) (hbr : ∀ j < P.d, st.bran j < P.k) :
    ∀ j < P.d, (Ordered.algorithm1_shift T L P st i₀).1.bran j < P.k := by
  unfold Ordered.algorithm1_shift
  split_ifs with hi
  · dsimp only
    apply rebuildSuffix_bran T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
    intro j hj
    by_cases hji : j = i₀
    · subst hji; simpa using Nat.mod_lt (st.bran j + 1) P.hk
    · simp [hji, hbr j hj]
  · exact hbr

/-- `algorithm2_init` establishes `BranchesLtK`. -/
theorem branchesLtK_init (cfg : Alg2Config) (G : MGraph) (g l : ℕ → ℝ) :
    BranchesLtK cfg (Ordered.algorithm2_init cfg G g l) := by
  refine ⟨?_, cfg.P.hk⟩
  intro i hi
  exact algorithm1_initialize_bran cfg.T cfg.L cfg.P _ cfg.N₀ G l g i hi

/-- `algorithm2_loopWith` preserves `BranchesLtK`. -/
theorem branchesLtK_loopWith (cfg : Alg2Config) (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ)
    (hbr : ∀ i < cfg.P.d, ch.bran i < cfg.P.k) (hbrD : branD < cfg.P.k) :
    let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    (∀ i < cfg.P.d, res.1.bran i < cfg.P.k) ∧ res.2.1 < cfg.P.k := by
  suffices h : ∀ N ch branD passes lctOps,
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ N →
      (∀ i < cfg.P.d, ch.bran i < cfg.P.k) → branD < cfg.P.k →
      let res := Ordered.algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
      (∀ i < cfg.P.d, res.1.bran i < cfg.P.k) ∧ res.2.1 < cfg.P.k from
    h _ ch branD passes lctOps le_rfl hbr hbrD
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ch branD passes lctOps hN hbr hbrD
    dsimp only
    rw [Ordered.algorithm2_loopWith]
    dsimp only
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤ -(κ * cfg.α)
    · rw [dite_eq_left hGood]; exact ⟨hbr, hbrD⟩
    · rw [dite_eq_right hGood]
      split
      · exact ⟨hbr, hbrD⟩
      · rename_i i _
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left hCap]
          have hlt := Ordered.shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          have hbr' := algorithm1_shift_bran cfg.T cfg.L cfg.P ch i.val hbr
          have hbrD' : (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k) < cfg.P.k := by
            split_ifs
            · exact cfg.P.hk
            · exact Nat.mod_lt _ cfg.P.hk
          exact ih (N - 1) (by omega) _ _ _ _ (by omega) hbr' hbrD'
        · rw [dite_eq_right hCap]; exact ⟨hbr, hbrD⟩

/-- `Update` preserves `BranchesLtK`. -/
theorem branchesLtK_update {cfg : Alg2Config} {κ : ℝ} {model : Alg2State cfg}
    {U : List Update} {g l : ℕ → ℝ} {η : ℝ} (hbr : BranchesLtK cfg model) :
    BranchesLtK cfg ((Ordered.algorithm2_dsWithFailureWith cfg κ).update model U g l η).1 := by
  change BranchesLtK cfg (Ordered.algorithm2_updateWith cfg κ model U g l η).1
  unfold Ordered.algorithm2_updateWith
  dsimp only
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  set ch1 := (Ordered.algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain
    tr.2.2.2.2 (fun e' => g (tr.2.2.1 e')) (fun e' => l (tr.2.2.1 e'))).1
  set bp1 := match firstRebuiltLevel cfg.P.d model.chain.rebuildCount ch1.rebuildCount with
    | none => (model.branD, model.passes)
    | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else model.passes j)
  have hch1 : ∀ j < cfg.P.d, ch1.bran j < cfg.P.k :=
    algorithm1_update_bran cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _ hbr.1
  have hbrD1 : bp1.1 < cfg.P.k := by
    dsimp only [bp1]
    cases firstRebuiltLevel cfg.P.d model.chain.rebuildCount ch1.rebuildCount with
    | none => exact hbr.2
    | some _ => exact cfg.P.hk
  have hloop := branchesLtK_loopWith cfg κ tr.1
    (level0E2I (level0Rebuilt cfg.P.d model.chain.rebuildCount ch1.rebuildCount)
      ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.1)
    g l ch1 bp1.1 bp1.2 (model.lctUpdateOps + U.length) hch1 hbrD1
  dsimp only [bp1] at hloop
  split <;> exact hloop

/-- `Detect` preserves `BranchesLtK`. -/
theorem branchesLtK_detect {cfg : Alg2Config} {model : Alg2State cfg}
    (hbr : BranchesLtK cfg model) :
    BranchesLtK cfg (algorithm2_detect cfg model).2 :=
  hbr

/-- Derives the key word-fit premise `2 * (model.nextFresh + U.length) + 1 < 2 ^ w` of
`ChainRefreshStepSpec` from the reached name bound (`alg2_nextFresh_le_with`), `U.length ≤ 2 * m`,
and one constant word-size inequality. -/
theorem keyWord_lt_of_nameBound {cfg : Alg2Config} {G : MGraph} {model : Alg2State cfg}
    {U : List Update} {m w : ℕ}
    (hnf : model.nextFresh ≤ Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0)
    (hU : U.length ≤ 2 * m)
    (hW : 2 * (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * m) + 1 < 2 ^ w) :
    2 * (model.nextFresh + U.length) + 1 < 2 ^ w := by
  omega

/-- Bounds `shiftQuotaWord` at level `i` when every rebuild count at levels `j ≤ i` is at most
`R`: `shiftQuotaWord ≤ (1 + (i + 1) * R) * (10 * ⌈psi⌉₊ * k) ^ (i + 1)`.
Once the contract bounds the number of updates `T` (so `rebuildCount j ≤ T`), this gives
`shiftQuotaWord < 2 ^ w` directly from a polynomial word-size bound. -/
theorem shiftQuotaWord_le_of_rebuildCount_le (P : ChainParams) (psi : ℝ) (rc : ℕ → ℕ)
    (i R : ℕ) (hpsi : 1 ≤ psi) (hR : ∀ j ≤ i, rc j ≤ R) :
    shiftQuotaWord P psi rc i ≤ (1 + (i + 1) * R) * (10 * ⌈psi⌉₊ * P.k) ^ (i + 1) := by
  have hB1 : (1 : ℝ) ≤ 10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ) := by
    have hk : (1 : ℝ) ≤ P.k := by exact_mod_cast P.hk
    have hcp : (1 : ℝ) ≤ ⌈psi⌉₊ := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
      intro h; have := Nat.le_ceil psi; rw [h] at this; norm_num at this; linarith))
    nlinarith
  have hbase : 10 * psi * (P.k : ℝ) ≤ 10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ) := by
    have := Nat.le_ceil psi
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    nlinarith
  have hbase0 : 0 ≤ 10 * psi * (P.k : ℝ) := by
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    nlinarith
  have hgame : gameShiftBound P psi rc i ≤
      ((1 + (i + 1) * R) * (10 * ⌈psi⌉₊ * P.k) ^ (i + 1) : ℕ) := by
    unfold gameShiftBound
    have hpow0 : (10 * psi * (P.k : ℝ)) ^ (i + 1) ≤ (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1) :=
      pow_le_pow_left₀ hbase0 hbase _
    have hsum : ∑ j ∈ Finset.range (i + 1), (rc j : ℝ) * (10 * psi * (P.k : ℝ)) ^ (i + 1 - j) ≤
        ((i + 1 : ℕ) : ℝ) * ((R : ℝ) * (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1)) := by
      calc ∑ j ∈ Finset.range (i + 1), (rc j : ℝ) * (10 * psi * (P.k : ℝ)) ^ (i + 1 - j)
          ≤ ∑ _j ∈ Finset.range (i + 1), (R : ℝ) * (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hrc : (rc j : ℝ) ≤ R := by exact_mod_cast hR j hjle
            have hp1 : (10 * psi * (P.k : ℝ)) ^ (i + 1 - j) ≤
                (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1 - j) :=
              pow_le_pow_left₀ hbase0 hbase _
            have hp2 : (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1 - j) ≤
                (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1) :=
              pow_le_pow_right₀ hB1 (Nat.sub_le _ _)
            exact mul_le_mul hrc (hp1.trans hp2) (pow_nonneg hbase0 _) (Nat.cast_nonneg _)
        _ = ((i + 1 : ℕ) : ℝ) * ((R : ℝ) * (10 * (⌈psi⌉₊ : ℝ) * (P.k : ℝ)) ^ (i + 1)) := by
            simp
    push_cast at hsum ⊢
    nlinarith
  by_contra hlt
  push Not at hlt
  have h1 := (shiftQuotaWord_lt_iff P psi rc i _ (by linarith)).mp hlt
  linarith

end MinCostFlow.MinRatio
