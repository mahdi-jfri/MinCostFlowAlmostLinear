module

public import MinCostFlow.Chain.Ordered.ShiftLoopLevels
public import MinCostFlow.Chain.Ordered.Algorithm2

/-!
# The active sparsified core of level `j` equals the graph of level `j + 1` (`ActiveCoreSucc`)

Proves the chain model fact that for every level `j < P.d`, the active sparsified core of level `j`
equals the graph of level `j + 1` literally (`st.toTreeChain.activeS j = st.toTreeChain.G (j + 1)`,
equivalently `T.S (st.scState j) (st.bran j) = st.G (j + 1)`).

* From invariants: `ChainInv.activeS_eq_G_succ`, `ShiftLoopChainInv.activeS_eq_G_succ`, and
  `unorderedChainInv_activeS_eq_G_succ` project `hGSucc` directly.
* Unconditionally across every ordered Algorithm 1 and Algorithm 2 operation:
  `ActiveCoreEqNext st` is established by `algorithm1_initialize` (`algorithm2_init`) and preserved
  by `algorithm1_rebuild` (when `i₀ = 0` or `Gnew` is the active sparsifier of level `i₀ - 1`),
  `algorithm1_shift`, `algorithm1_update` (`updateLoop`), `algorithm2_loopWith`,
  `algorithm2_updateWith`, and `algorithm2_detect`. Consequently `minRatioFailState_activeCoreEqNext`
  holds for every state produced by `minRatioFailState (algorithm2_dsWith cfg κ)` with no extra
  hypotheses.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle MinCostFlow.Chain

/-! ## 1. The property and direct projections from invariants -/

/-- The active sparsified core of every level `j < P.d` equals the graph of level `j + 1`. -/
def ActiveCoreEqNext {T : SparseCoreRestartTool} {P : ChainParams} (st : ChainState T P) : Prop :=
  ∀ j < P.d, st.toTreeChain.activeS j = st.toTreeChain.G (j + 1)

theorem activeCoreEqNext_iff {T : SparseCoreRestartTool} {P : ChainParams}
    (st : ChainState T P) :
    ActiveCoreEqNext st ↔ ∀ j < P.d, T.S (st.scState j) (st.bran j) = st.G (j + 1) := by
  constructor <;> intro h j hj
  · have h1 := h j hj
    simpa [TreeChain.activeS, ChainState.toTreeChain, hj] using h1
  · simp only [TreeChain.activeS, ChainState.toTreeChain, hj, ↓reduceIte]
    exact h j hj

/-- Under ordered `ChainInv`, `activeS j = G (j + 1)` for every `j < P.d`. -/
theorem ChainInv.activeS_eq_G_succ {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) :
    ActiveCoreEqNext st :=
  (activeCoreEqNext_iff st).mpr fun j hj => (hInv.hGSucc j hj).symm

/-- Under `ShiftLoopChainInv`, `activeS j = G (j + 1)` for every `j < cfg.P.d`. -/
theorem ShiftLoopChainInv.activeS_eq_G_succ {cfg : Alg2Config} {ch : ChainState cfg.T cfg.P}
    (h : ShiftLoopChainInv cfg ch) :
    ActiveCoreEqNext ch :=
  h.1.activeS_eq_G_succ

/-- Under unordered `Chain.ChainInv`, `activeS j = G (j + 1)` for every `j < P.d`. -/
theorem unorderedChainInv_activeS_eq_G_succ {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {st : ChainState T P} (hInv : Chain.ChainInv T L TP LP P N₀ st) :
    ActiveCoreEqNext st :=
  (activeCoreEqNext_iff st).mpr fun j hj => (hInv.hGSucc j hj).symm

/-! ## 2. Unconditional preservation across Algorithm 1 operations -/

private lemma rebuildSuffix_activeCoreEqNext (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      rem + idx = P.d →
      (∀ j < idx, T.S (sc j) (bran j) = G (j + 1)) →
      let res := rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      ∀ j < P.d, T.S (res.2.1 j) (res.2.2.1 j) = res.1 (j + 1)
  | 0, idx, G, sc, bran, upd, cEnc, cDec, cFwd, hsum, hpre => by
    intro res j hj
    have hidx : idx = P.d := by omega
    subst hidx
    exact hpre j hj
  | rem + 1, idx, G, sc, bran, upd, cEnc, cDec, cFwd, hsum, hpre => by
    dsimp only [rebuildSuffix]
    refine rebuildSuffix_activeCoreEqNext T L P lvlM N₀ ℓ₀ g₀ rem (idx + 1) _ _ _ _ _ _ _
      (by omega) ?_
    intro j hj
    by_cases hji : j = idx
    · subst hji
      simp
    · have hjlt : j < idx := by omega
      have hj1ne : j + 1 ≠ idx + 1 := by omega
      simp only [hji, hj1ne, ↓reduceIte]
      exact hpre j hjlt

/-- `algorithm1_initialize` builds a chain satisfying `ActiveCoreEqNext` unconditionally. -/
theorem algorithm1_initialize_activeCoreEqNext (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    ActiveCoreEqNext (algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1 := by
  rw [activeCoreEqNext_iff]
  unfold algorithm1_initialize
  dsimp only
  exact rebuildSuffix_activeCoreEqNext T L P lvlM N₀ ℓ₀ g₀ P.d 0 _ _ _ _ _ _ _ (by omega)
    (fun j hj => by omega)

/-- `algorithm1_rebuild` preserves `ActiveCoreEqNext` for `i₀ ≤ P.d` whenever either `i₀ = 0` or
`Gnew` matches the active sparsifier of level `i₀ - 1` (and all levels below `i₀ - 1` already
match). -/
theorem algorithm1_rebuild_activeCoreEqNext (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ ≤ P.d) (Gnew : MGraph)
    (extraEnc : ℕ)
    (hbelow : ∀ j < i₀, j + 1 < i₀ → T.S (st.scState j) (st.bran j) = st.G (j + 1))
    (hedge : 0 < i₀ → T.S (st.scState (i₀ - 1)) (st.bran (i₀ - 1)) = Gnew) :
    ActiveCoreEqNext (algorithm1_rebuild T L P st i₀ Gnew extraEnc).1 := by
  rw [activeCoreEqNext_iff]
  unfold algorithm1_rebuild
  by_cases hi : i₀ < P.d
  · simp only [hi, ↓reduceDIte]
    refine rebuildSuffix_activeCoreEqNext T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀ _ _ _ _ _ _ _
      (by omega) ?_
    intro j hj
    by_cases h1 : j + 1 = i₀
    · have hj_eq : j = i₀ - 1 := by omega
      subst hj_eq
      simp only [h1, ↓reduceIte]
      exact hedge (by omega)
    · simp only [h1, ↓reduceIte]
      exact hbelow j hj (by omega)
  · simp only [hi, ↓reduceDIte]
    have heq : i₀ = P.d := by omega
    subst heq
    intro j hj
    by_cases h1 : j + 1 = P.d
    · have hj_eq : j = P.d - 1 := by omega
      subst hj_eq
      simp only [h1, ↓reduceIte]
      exact hedge (by omega)
    · simp only [h1, ↓reduceIte]
      exact hbelow j hj (by omega)

/-- `algorithm1_shift` preserves `ActiveCoreEqNext` unconditionally for every `i₀`. -/
theorem algorithm1_shift_activeCoreEqNext (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (st : ChainState T P) (i₀ : ℕ) (hst : ActiveCoreEqNext st) :
    ActiveCoreEqNext (algorithm1_shift T L P st i₀).1 := by
  have hst' := (activeCoreEqNext_iff st).mp hst
  rw [activeCoreEqNext_iff]
  unfold algorithm1_shift
  by_cases hi : i₀ < P.d
  · simp only [hi, ↓reduceDIte]
    refine rebuildSuffix_activeCoreEqNext T L P st.lvlM st.N₀ st.ℓ st.g (P.d - (i₀ + 1)) (i₀ + 1)
      _ _ _ _ _ _ _ (by omega) ?_
    intro j hj
    by_cases hji : j = i₀
    · subst hji
      simp
    · have hjlt : j < i₀ := by omega
      have hj1ne : j + 1 ≠ i₀ + 1 := by omega
      simp only [hji, hj1ne, ↓reduceIte]
      exact hst' j (lt_trans hjlt hi)
  · simp only [hi, ↓reduceDIte]
    exact hst'

private lemma updateLoop_activeCoreEqNext (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      rem + idx = P.d →
      (∀ j < P.d, j + 1 ≠ idx → T.S (st.scState j) (st.bran j) = st.G (j + 1)) →
      (0 < idx → T.S (st.scState (idx - 1)) (st.bran (idx - 1)) = curG) →
      ActiveCoreEqNext (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1
  | 0, idx, st, curG, curU, curEnc, hsum, hst, hcur => by
    have hidx : idx = P.d := by omega
    subst hidx
    rw [activeCoreEqNext_iff]
    unfold updateLoop
    split_ifs <;> dsimp only
    · intro j hj
      by_cases h1 : j + 1 = P.d
      · have hj_eq : j = P.d - 1 := by omega
        subst hj_eq
        simp only [h1, ↓reduceIte]
        exact hcur (by omega)
      · simp only [h1, ↓reduceIte]
        exact hst j hj h1
    · intro j hj
      by_cases h1 : j + 1 = P.d
      · have hj_eq : j = P.d - 1 := by omega
        subst hj_eq
        simp only [h1, ↓reduceIte]
        exact hcur (by omega)
      · simp only [h1, ↓reduceIte]
        exact hst j hj h1
  | rem + 1, idx, st, curG, curU, curEnc, hsum, hst, hcur => by
    unfold updateLoop
    split_ifs with hreb
    · refine algorithm1_rebuild_activeCoreEqNext T L P _ (by omega) _ curEnc ?_ ?_
      · intro j hj hlt
        exact hst j (by omega) (by omega)
      · intro hpos
        have hne0 : idx ≠ 0 := by omega
        simp only [rebuildStartGraph, hne0, ↓reduceIte]
        exact hcur hpos
    · dsimp only
      refine updateLoop_activeCoreEqNext T L TP P N₀ ℓ' g' rem (idx + 1) _ _ _ 0 (by omega) ?_ ?_
      · intro j hj hne
        by_cases hji : j = idx
        · exact absurd (by omega) hne
        · by_cases h1 : j + 1 = idx
          · have hj_eq : j = idx - 1 := by omega
            subst hj_eq
            simp only [hji, h1, ↓reduceIte]
            exact hcur (by omega)
          · simp only [hji, h1, ↓reduceIte]
            exact hst j hj h1
      · intro _
        simp

/-- `algorithm1_update` preserves `ActiveCoreEqNext` unconditionally. -/
theorem algorithm1_update_activeCoreEqNext (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (st : ChainState T P)
    (U : List Update) (g' ℓ' : ℕ → ℝ) (hst : ActiveCoreEqNext st) :
    ActiveCoreEqNext (algorithm1_update T L TP P N₀ st U g' ℓ').1 := by
  unfold algorithm1_update
  dsimp only
  refine updateLoop_activeCoreEqNext T L TP P N₀ ℓ' g' P.d 0 _ _ U _ (by omega) ?_ (fun h => by omega)
  intro j hj _
  exact (activeCoreEqNext_iff st).mp hst j hj

/-! ## 3. Unconditional preservation across Algorithm 2 operations -/

/-- `algorithm2_init` builds a state whose chain satisfies `ActiveCoreEqNext`. -/
theorem algorithm2_init_activeCoreEqNext (cfg : Alg2Config) (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) :
    ActiveCoreEqNext (algorithm2_init cfg G₀ g₀ ℓ₀).chain :=
  algorithm1_initialize_activeCoreEqNext cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀ g₀

/-- The inner shift loop `algorithm2_loopWith` preserves `ActiveCoreEqNext` unconditionally. -/
theorem algorithm2_loopWith_activeCoreEqNext (cfg : Alg2Config) (κ : ℝ) (extG : MGraph)
    (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ),
      ActiveCoreEqNext ch →
      ActiveCoreEqNext (algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).1 := by
  intro ch branD passes lctOps
  induction hB : shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch using Nat.strong_induction_on
      generalizing ch branD passes lctOps with
  | _ B ih =>
    intro hch
    rw [algorithm2_loopWith]
    split_ifs with hGood
    · exact hch
    · cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none => exact hch
      | some i =>
        dsimp only
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)]
          have hlt : shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
              (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 < B := by
            rw [← hB]
            exact shiftRemainingBudget_lt_of_step ch i hCap
          exact ih _ hlt _ _ _ _ rfl
            (algorithm1_shift_activeCoreEqNext cfg.T cfg.L cfg.P ch i.val hch)
        · rw [dite_eq_right_of_eq_false (eq_false hCap)]
          exact hch

/-- `algorithm2_updateWith` preserves `ActiveCoreEqNext` unconditionally. -/
theorem algorithm2_updateWith_activeCoreEqNext (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) (hst : ActiveCoreEqNext st.chain) :
    ActiveCoreEqNext (algorithm2_updateWith cfg κ st U_ext g' ℓ' η).1.chain := by
  unfold algorithm2_updateWith
  dsimp only
  set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
  have h1 := algorithm1_update_activeCoreEqNext cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain
    tb.2.2.2.2 (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e')) hst
  split <;> exact algorithm2_loopWith_activeCoreEqNext cfg κ _ _ _ _ _ _ _ _ h1

/-- `algorithm2_detect` preserves `ActiveCoreEqNext` (it does not change `st.chain`). -/
theorem algorithm2_detect_activeCoreEqNext (cfg : Alg2Config) (st : Alg2State cfg)
    (hst : ActiveCoreEqNext st.chain) :
    ActiveCoreEqNext (algorithm2_detect cfg st).2.chain :=
  hst

/-- Every state produced by `minRatioFailState (algorithm2_dsWith cfg κ)` satisfies
`ActiveCoreEqNext` unconditionally. -/
theorem minRatioFailState_activeCoreEqNext (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (op : ℕ → Bool) :
    ∀ t, ActiveCoreEqNext (minRatioFailState (algorithm2_dsWith cfg κ) D η op t).chain
  | 0 => algorithm2_init_activeCoreEqNext cfg (D.G 0) (D.g 0) (D.ℓ 0)
  | t + 1 => by
    have ih := minRatioFailState_activeCoreEqNext cfg κ D η op t
    rw [minRatioFailState.eq_2]
    split_ifs
    · exact algorithm2_updateWith_activeCoreEqNext cfg κ _ _ _ _ _ ih
    · exact algorithm2_detect_activeCoreEqNext cfg _ ih

end MinCostFlow.Chain.Ordered
