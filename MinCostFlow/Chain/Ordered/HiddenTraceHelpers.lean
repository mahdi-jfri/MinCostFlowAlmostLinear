module

public import MinCostFlow.Chain.Ordered.HiddenTrace
public import MinCostFlow.Chain.HiddenTraceSteps
import MinCostFlow.Chain.Ordered.BudgetHelpers

/-!
# Snapshot and `LevelHistory` helpers for the ordered hidden trace

This file provides the ordered `ChainState` snapshot lemmas and explicit `LevelHistory`
constructors ported from `MinCostFlow.Chain.HiddenTraceSteps`:

* `exists_rotation_levelOrd_of_inv`: extracts a rotation system realizing `st.levelOrd i`
  from `Ordered.ChainInv`.
* `chainInv_last_le_N0`: bounds the last-level vertex count by `cfg.N₀`.
* `chainState_snapHoldsAt`, `chainState_snapHolds`: snapshot `TreeChain.Holds` and per-level MWU
  bounds for an ordered `ChainInv`.
* `chain_validStretch_hstr`: `Game.ValidStretch` for `hstrAt` under `Alg2Config.ValidOrdNoHidden`.
* `zeroLevelHistory`, `levelHistory_of_shift_le`: `0`-step and shift-preserved ordered
  `LevelHistory` constructors.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section LevelHistoryConstructors

/-- Extract a rotation system on `st.G i` whose order is `st.levelOrd i` directly from the
ordered `ChainInv`. -/
lemma exists_rotation_levelOrd_of_inv {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) {i : ℕ} (hi : i < P.d) :
    ∃ ρ : Rotation (st.G i), ρ.order = st.levelOrd i := by
  obtain ⟨H⟩ := hInv.hHist i hi
  obtain ⟨ρ, hρ, _⟩ := H.hOrd
  refine ⟨H.hEndG ▸ ρ H.len, ?_⟩
  have hcast : ∀ {G₁ G₂ : MGraph} (h : G₁ = G₂) (r : Rotation G₁), (h ▸ r).order = r.order := by
    intro G₁ G₂ h r; subst h; rfl
  rw [hcast H.hEndG (ρ H.len), hρ H.len (le_refl _), H.hEndOrd]

/-- Explicit `0`-step ordered `LevelHistory` at level `i < P.d` when level `i` was just
initialized or rebuilt. -/
noncomputable def zeroLevelHistory (T : SparseCoreRestartTool) (TP : SparseCoreParams) (P : ChainParams)
    (N₀ : ℕ) (st : ChainState T P) (i : ℕ) (_hi : i < P.d)
    (_hTP : TP.Valid)
    (hGValid : (st.G i).IsValid)
    (hGm : ((st.G i).m : ℝ) ≤ (levelM TP P i : ℝ))
    (hGn : (st.G i).n ≤ N₀)
    (hℓPos : ∀ e ∈ (st.G i).E, 0 < st.toTreeChain.chainLen st.ℓ i e)
    (hRot : ∃ ρ : Rotation (st.G i), ρ.order = st.levelOrd i)
    (hInit : st.scState i = T.initOrd P.k (levelM TP P i) N₀ (st.G i)
      (st.toTreeChain.chainLen st.ℓ i) (st.toTreeChain.chainGrad st.g i) (st.levelOrd i))
    (hUpd : st.updCount i = 0) (hCurFwd : st.curFwd i = 0)
    (hDec : st.curDecUpdates i = 0) (hRestarts : st.curRestarts i = 0)
    (hEnc0 : i = 0 → st.curEnc 0 = 0)
    (hEncNext : i + 1 < P.d → st.curEnc (i + 1) = 0)
    (hOK : T.ToolOKAt TP P.k (levelM TP P i) N₀ (st.G i) (st.toTreeChain.chainLen st.ℓ i)) :
    LevelHistory T TP P N₀ st i :=
  let D : DynamicInstance :=
    { G := fun _ => st.G i, U := fun _ => [],
      ℓ := fun _ => st.toTreeChain.chainLen st.ℓ i, g := fun _ => st.toTreeChain.chainGrad st.g i }
  { D := D, len := 0, s₀ := 0, hs₀ := le_refl 0,
    restarts := fun _ => [],
    hRestartsLt := fun _ _ _ h => absurd h (List.not_mem_nil),
    hRestartsCount := by simp [hRestarts],
    hS0Fresh := Or.inl rfl,
    hNoRestartAfterS0 := fun _ _ _ h => absurd h (List.not_mem_nil),
    hG0 := hGValid, hD := fun _ ht1 ht2 => by omega, hLen := fun _ ht1 ht2 => by omega,
    hℓPos := fun _ _ e he => hℓPos e he,
    hEndG := rfl, hEndℓ := fun _ _ => rfl, hEndg := rfl,
    hUpd := by simp [hUpd], hThresh := by rw [hUpd]; simp [updateThreshold_nonneg],
    hInitMBound := by exact_mod_cast hGm,
    hInitNBound := hGn,
    ord := fun _ => st.levelOrd i,
    hOrd := by
      rcases hRot with ⟨ρ, hρ⟩
      exact ⟨fun _ => ρ, fun _ _ => hρ, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    hEndOrd := rfl,
    hRun := by
      simp only [SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate,
        List.foldl_nil]
      exact hInit,
    hOK := hOK,
    branchSeq := fun _ => 0, hBranch := fun _ => P.hk,
    hBranchTail := fun _ hs1 hs2 => by omega,
    hWinFwdBound := by simp,
    hCurFwdEq := by simp [hCurFwd],
    hDecEq := by
      rw [hInit]
      simp [hDec, SparseCoreRestartTool.runOrdAfterRestarts,
        SparseCoreRestartTool.runOrdAfterUpdate, D],
    hEnc0Le := fun h0 => by simp [hEnc0 h0], hEncLe := fun h1 => by simp [hEncNext h1] }

/-- Preserve an ordered `LevelHistory` (keeping exact `.D`, `.ord`, and `.len`, resetting `s₀` and
appending the restart at `i₀`) across `algorithm1_shift`. -/
noncomputable def levelHistory_of_shift_le {T : SparseCoreRestartTool} {TP : SparseCoreParams}
    {P : ChainParams} {N₀ : ℕ} {ch ch' : ChainState T P} {i₀ k : ℕ} (_hk : k < P.d) (hki : k ≤ i₀)
    (H : LevelHistory T TP P N₀ ch k)
    (hG : ∀ j ≤ k, ch'.G j = ch.G j)
    (hSuf_sc : if k = i₀ then ch'.scState k = T.restart (ch.scState k) (ch'.bran k)
      else ch'.scState k = ch.scState k)
    (hAct : ∀ j < k, ch'.toTreeChain.activeLSF j = ch.toTreeChain.activeLSF j)
    (hOrdEq : ch'.levelOrd k = ch.levelOrd k)
    (hℓ : ch'.ℓ = ch.ℓ) (hg : ch'.g = ch.g)
    (hUpd : ch'.updCount k = ch.updCount k)
    (hCurFwd : ch'.curFwd k = ch.curFwd k)
    (hCurFwdBd : (ch.curFwd k : ℝ) ≤ TP.γ_r (P.M₀ ^ 2) * (ch.updCount k : ℝ))
    (hBrLtK : ch'.bran k < P.k)
    (hBrLt : k < i₀ → ch'.bran k = ch.bran k)
    (hDec : k = i₀ → ch'.curDecUpdates k = 0)
    (hDecLt : k < i₀ → ch'.curDecUpdates k = ch.curDecUpdates k)
    (hRestarts : ch'.curRestarts k = if k = i₀ then ch.curRestarts k + 1 else ch.curRestarts k)
    (hEnc0 : k = 0 → ch'.curEnc 0 = ch.curEnc 0)
    (hEncNext : k + 1 < P.d → k + 1 ≤ i₀ → ch'.curEnc (k + 1) = ch.curEnc (k + 1))
    (hEncNextGt : k + 1 < P.d → i₀ < k + 1 → ch'.curEnc (k + 1) = 0) :
    LevelHistory T TP P N₀ ch' k :=
  let restarts' : ℕ → List ℕ := fun r =>
    if k = i₀ ∧ r = H.len then H.restarts H.len ++ [ch'.bran k] else H.restarts r
  have hRunPre : ∀ s ≤ H.len,
      T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord restarts' s =
        T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord H.restarts s := fun s hs =>
    T.runOrdAfterUpdate_congr_lt P.k (levelM TP P k) N₀ s rfl rfl rfl (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
      (fun _ _ => rfl)
      (fun r hr => by simp [restarts', show ¬ (k = i₀ ∧ r = H.len) by omega])
  { D := H.D, len := H.len
    s₀ := if k = i₀ then H.len else H.s₀
    hs₀ := by split_ifs <;> [exact le_refl _; exact H.hs₀]
    restarts := restarts',
    hRestartsLt := fun r hr b hb => by
      dsimp only [restarts'] at hb
      split_ifs at hb with hcond
      · simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · rw [hcond.2] at hr
          exact H.hRestartsLt _ hr b hb
        · exact hBrLtK
      · exact H.hRestartsLt r hr b hb
    hRestartsCount := by
      by_cases heq : k = i₀
      · subst heq
        rw [Finset.sum_range_succ]
        have hPreSum : (Finset.range H.len).sum (fun r => (restarts' r).length) =
            (Finset.range H.len).sum (fun r => (H.restarts r).length) :=
          Finset.sum_congr rfl fun r hr => by
            simp [restarts', Nat.ne_of_lt (Finset.mem_range.mp hr)]
        have hLast : (restarts' H.len).length = (H.restarts H.len).length + 1 := by
          simp [restarts']
        rw [hPreSum, hLast, ← add_assoc, ← Finset.sum_range_succ, H.hRestartsCount, hRestarts]
        simp
      · have hPreSum : (Finset.range (H.len + 1)).sum (fun r => (restarts' r).length) =
            (Finset.range (H.len + 1)).sum (fun r => (H.restarts r).length) :=
          Finset.sum_congr rfl fun r _ => by simp [restarts', heq]
        rw [hPreSum, H.hRestartsCount, hRestarts]
        simp [heq]
    hS0Fresh := by
      by_cases heq : k = i₀
      · right; simp [restarts', heq]
      · simp only [heq, ↓reduceIte, restarts', false_and]
        rw [hBrLt (lt_of_le_of_ne hki heq)]
        exact H.hS0Fresh
    hNoRestartAfterS0 := fun r hr1 hr2 => by
      by_cases heq : k = i₀
      · subst heq; simp only [↓reduceIte] at hr1; omega
      · simp only [heq, ↓reduceIte] at hr1
        simp only [restarts', heq, false_and, ↓reduceIte]
        rw [hBrLt (lt_of_le_of_ne hki heq)]
        exact H.hNoRestartAfterS0 r hr1 hr2
    hG0 := H.hG0, hD := H.hD, hLen := H.hLen, hℓPos := H.hℓPos,
    hEndG := by rw [hG k (le_refl _)]; exact H.hEndG,
    hEndℓ := fun e he => by
      have he' : e ∈ (ch.G k).E := by rwa [← hG k (le_refl _)]
      have hCL := chainLen_congr_lt (C₁ := ch'.toTreeChain) (C₂ := ch.toTreeChain) ch.ℓ k
        (fun j hj => hG j hj.le) hAct
      change H.D.ℓ H.len e = ch'.toTreeChain.chainLen ch'.ℓ k e
      rw [hℓ, hCL]; exact H.hEndℓ e he',
    hEndg := by
      have hCG := chainGrad_congr_lt (C₁ := ch'.toTreeChain) (C₂ := ch.toTreeChain) ch.g k
        (fun j hj => hG j hj.le) hAct
      change H.D.g H.len = ch'.toTreeChain.chainGrad ch'.g k
      rw [hg, hCG]; exact H.hEndg,
    hUpd := by rw [hUpd]; exact H.hUpd,
    hThresh := by rw [hUpd]; exact H.hThresh,
    hInitMBound := H.hInitMBound,
    hInitNBound := H.hInitNBound,
    ord := H.ord,
    hOrd := H.hOrd,
    hEndOrd := by rw [hOrdEq]; exact H.hEndOrd,
    hRun := by
      by_cases heq : k = i₀
      · subst heq
        simp only [↓reduceIte] at hSuf_sc
        symm
        unfold SparseCoreRestartTool.runOrdAfterRestarts
        rw [hRunPre H.len (le_refl _)]
        simp only [restarts', ↓reduceIte, and_self, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        change T.restart (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord H.restarts H.len)
          (ch'.bran k) = ch'.scState k
        rw [← H.hRun, hSuf_sc]
      · simp only [heq, ↓reduceIte] at hSuf_sc
        have hPostEq : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord restarts' H.len =
            T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord H.restarts H.len :=
          T.runOrdAfterRestarts_congr_le P.k (levelM TP P k) N₀ H.len rfl rfl rfl
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl) (fun r _ => by simp [restarts', heq])
        rw [hPostEq, hSuf_sc]; exact H.hRun,
    hOK := H.hOK,
    branchSeq := H.branchSeq,
    hBranch := H.hBranch,
    hBranchTail := fun s hs1 hs2 => by
      by_cases heq : k = i₀
      · subst heq; simp only [↓reduceIte] at hs1; omega
      · simp only [heq, ↓reduceIte] at hs1
        rw [hBrLt (lt_of_le_of_ne hki heq)]
        exact H.hBranchTail s hs1 hs2,
    hWinFwdBound := by
      by_cases heq : k = i₀
      · subst heq
        simp only [↓reduceIte]
        have hsub : (Finset.Icc 1 H.len).sum (fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord restarts' s).2 (H.branchSeq s)).length) =
            (Finset.Icc 1 H.len).sum (fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord H.restarts s).2 (H.branchSeq s)).length) :=
          Finset.sum_congr rfl fun s hs => by rw [hRunPre s (Finset.mem_Icc.mp hs).2]
        rw [hsub, ← H.hCurFwdEq, H.hUpd]
        exact hCurFwdBd
      · simp only [heq, ↓reduceIte]
        have hsub : (Finset.Icc 1 H.s₀).sum (fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord restarts' s).2 (H.branchSeq s)).length) =
            (Finset.Icc 1 H.s₀).sum (fun s =>
              ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord H.restarts s).2 (H.branchSeq s)).length) :=
          Finset.sum_congr rfl fun s hs => by
            rw [hRunPre s (le_trans (Finset.mem_Icc.mp hs).2 H.hs₀)]
        rw [hsub]
        exact H.hWinFwdBound,
    hCurFwdEq := by
      rw [hCurFwd, H.hCurFwdEq]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hRunPre s (Finset.mem_Icc.mp hs).2],
    hDecEq := by
      by_cases heq : k = i₀
      · subst heq
        have hPost : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord restarts'
              (if k = k then H.len else H.s₀) = ch'.scState k := by
          simp only [↓reduceIte] at hSuf_sc ⊢
          unfold SparseCoreRestartTool.runOrdAfterRestarts
          rw [hRunPre H.len (le_refl _)]
          simp only [restarts', ↓reduceIte, and_self, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
          change T.restart (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord H.restarts H.len)
            (ch'.bran k) = ch'.scState k
          rw [← H.hRun, hSuf_sc]
        simp only [↓reduceIte, hDec rfl, zero_add]
        rw [← hPost]
        simp only [↓reduceIte]
      · have hlt : k < i₀ := Nat.lt_of_le_of_ne hki heq
        simp only [heq, ↓reduceIte] at hSuf_sc ⊢
        have hPostEq : T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord restarts' H.s₀ =
            T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord H.restarts H.s₀ :=
          T.runOrdAfterRestarts_congr_le P.k (levelM TP P k) N₀ H.s₀ rfl rfl rfl
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl) (fun r _ => by simp [restarts', heq])
        change ch'.curDecUpdates k + (T.lsfs (ch'.scState k) (ch'.bran k)).F.F.E.card =
          (T.lsfs (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord restarts' H.s₀)
            (ch'.bran k)).F.F.E.card
        rw [hDecLt hlt, hSuf_sc, hBrLt hlt, hPostEq]
        exact H.hDecEq,
    hEnc0Le := fun h0 => by rw [hEnc0 h0]; exact H.hEnc0Le h0,
    hEncLe := fun h1 => by
      by_cases hle : k + 1 ≤ i₀
      · have hne : k ≠ i₀ := by omega
        have hlt : k < i₀ := by omega
        change ch'.curEnc (k + 1) ≤ (Finset.Icc ((if k = i₀ then H.len else H.s₀) + 1) H.len).sum fun s =>
          (T.S (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord restarts' (s - 1)) (ch'.bran k)).batchEnc
            ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord restarts' s).2 (ch'.bran k))
        simp only [hne, ↓reduceIte, hEncNext h1 hle, hBrLt hlt]
        have hSumEq : (Finset.Icc (H.s₀ + 1) H.len).sum (fun s =>
              (T.S (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord restarts' (s - 1)) (ch.bran k)).batchEnc
                ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord restarts' s).2 (ch.bran k))) =
            (Finset.Icc (H.s₀ + 1) H.len).sum (fun s =>
              (T.S (T.runOrdAfterRestarts P.k (levelM TP P k) N₀ H.D H.ord H.restarts (s - 1)) (ch.bran k)).batchEnc
                ((T.runOrdAfterUpdate P.k (levelM TP P k) N₀ H.D H.ord H.restarts s).2 (ch.bran k))) := by
          refine Finset.sum_congr rfl fun s hs => ?_
          rcases Finset.mem_Icc.mp hs with ⟨_, hs2⟩
          have hPostPre := T.runOrdAfterRestarts_congr_le (D₁ := H.D) (D₂ := H.D)
            (ord₁ := H.ord) (ord₂ := H.ord)
            (restarts₁ := restarts') (restarts₂ := H.restarts) P.k (levelM TP P k) N₀ (s - 1) rfl rfl rfl
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl) (fun r _ => by simp [restarts', hne])
          rw [hPostPre, hRunPre s hs2]
        rw [hSumEq]
        exact H.hEncLe h1
      · simp [hEncNextGt h1 (by omega)] }

lemma chain_validStretch_hstr {σ_cap : ℝ} {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {C : TreeChain} {ℓ w : ℕ → ℝ}
    (hC_d : C.d = cfg.P.d) (hC_k : C.k = cfg.P.k)
    (hHolds : C.Holds (C.G 0) ℓ σ_cap
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)))
    (hSub : C.ForestsAreSubgraphs)
    (hMWU : ∀ i < cfg.P.d, ∀ e ∈ (C.G i).E,
      (∑ j ∈ Finset.range cfg.P.k, (C.lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀)
    (hℓ_nn : ∀ e ∈ (C.G 0).E, 0 ≤ ℓ e) (hw_nn : ∀ e ∈ (C.G 0).E, 0 ≤ w e) :
    ∀ i : Fin (cfg.P.d + 1),
      let str_i : Fin cfg.P.k → ℝ := fun j =>
        if _hi : i.val < cfg.P.d then hstrAt C w i.val j.val else 0
      (∀ j, 0 ≤ str_i j) ∧ Game.ValidStretch cfg.gameParams.σ str_i := by
  intro i
  dsimp only
  by_cases hi : i.val < cfg.P.d
  · refine ⟨fun j => ?_, ?_⟩
    · simp only [hi, ↓reduceDIte]
      exact hstrAt_nonneg hHolds hSub hℓ_nn hw_nn (by rw [hC_d]; exact hi) (by rw [hC_k]; exact j.isLt)
    · have hcor := corollary_6_4_of_lvl hHolds hSub hℓ_nn hw_nn hV.hσ_mwu_nn (by rw [hC_d]; exact hi)
        (by rw [hC_k]; exact hMWU i.val hi)
      obtain ⟨j, hj, hle⟩ := hcor.2
      refine ⟨⟨j, by rw [← hC_k]; exact hj⟩, ?_⟩
      simp only [hi, ↓reduceDIte]
      exact le_trans hle (le_max_right 0 (cfg.σ_mwu cfg.N₀))
  · refine ⟨fun j => by simp [hi], ⟨⟨0, cfg.P.hk⟩, ?_⟩⟩
    simp [hi, Alg2Config.gameParams, alg2SigmaGame]

end LevelHistoryConstructors

lemma chainInv_last_le_N0 {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {s : ℕ} {ch : ChainState cfg.T cfg.P} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hn : (D.G s).n ≤ cfg.N₀) (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hF : FreshInv (D.G s) (ch.G 0) e2i i2e nf) : (ch.G cfg.P.d).n ≤ cfg.N₀ :=
  calc (ch.G cfg.P.d).n
      ≤ (ch.G 0).n := Finset.card_le_card
        ((level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hγM₀ hV.hγk
          hInv cfg.P.d le_rfl).2.1)
    _ = (D.G s).n := hF.n_eq
    _ ≤ cfg.N₀ := hn

lemma chainState_snapHoldsAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {s : ℕ} {ch : ChainState cfg.T cfg.P}
    {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hF : FreshInv (D.G s) (ch.G 0) e2i i2e nf)
    (hℓ : ch.ℓ = fun e' => D.ℓ s (i2e e'))
    (hn : (D.G s).n ≤ cfg.N₀)
    (hnLast : (ch.G cfg.P.d).n ≤ nLast) :
    ch.toTreeChain.d = cfg.P.d ∧ ch.toTreeChain.k = cfg.P.k ∧
    ch.toTreeChain.Holds (ch.G 0) (fun e' => D.ℓ s (i2e e'))
      (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) ∧
    ch.toTreeChain.ForestsAreSubgraphs ∧
    ∀ i < cfg.P.d, ∀ e ∈ (ch.G i).E,
      (∑ j ∈ Finset.range cfg.P.k, (ch.toTreeChain.lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀ := by
  have hB := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hγM₀ hV.hγk hInv
  have hTH := ChainInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk hInv
  have hn0 : (ch.G 0).n ≤ cfg.N₀ := by rw [hF.n_eq]; exact hn
  have hHolds_raw : ch.toTreeChain.Holds (ch.G 0) ch.ℓ
      (max (cfg.TP.σ cfg.P.k (ch.G 0).n) (cfg.LP.σ_last nLast))
      (max (cfg.σ_mwu (ch.G 0).n) (cfg.LP.σ_mwu (ch.G 0).n))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) := by
    refine ⟨hTH.1.1, hTH.1.2.1, hTH.1.2.2.1, hTH.1.2.2.2.1, ?_, hTH.1.2.2.2.2.2.1, ?_,
      hTH.1.2.2.2.2.2.2.2⟩
    · intro i hi
      refine ⟨hInv.hBran i hi, ?_, (hTH.1.2.2.2.2.1 i hi).2.2.1, (hTH.1.2.2.2.2.1 i hi).2.2.2⟩
      intro j hj
      have hij := (hB i (Nat.le_of_lt hi)).2.2.2.2 hi j hj
      exact ⟨LSF.Holds.mono_σ hij.1 (le_max_left _ _), hij.2.toNoSize⟩
    · intro j hj
      exact LSF.Holds.mono_σ (hInv.hLastHolds j hj)
        (le_trans (hV.hLP.2.1 _ _ hnLast) (le_max_right _ _))
  have hσ_le : max (cfg.TP.σ cfg.P.k (ch.G 0).n) (cfg.LP.σ_last nLast) ≤
      alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast :=
    max_le_max (hV.hTP.2.1 _ _ _ _ (le_refl _) hn0) (le_refl _)
  have hσm_le : max (cfg.σ_mwu (ch.G 0).n) (cfg.LP.σ_mwu (ch.G 0).n) ≤
      max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀) :=
    max_le_max (hV.hσ_mwu_mono _ _ hn0) (hV.hLP.2.2.2.1 _ _ hn0)
  have hHolds : ch.toTreeChain.Holds (ch.G 0) (fun e' => D.ℓ s (i2e e'))
      (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) := by
    rw [← hℓ]
    exact chainHolds_mono hHolds_raw hσ_le hσm_le
  have hSub : ch.toTreeChain.ForestsAreSubgraphs :=
    ch.toTreeChain.forestsAreSubgraphs_of_holds hHolds
  refine ⟨rfl, rfl, hHolds, hSub, fun i hi e he => ?_⟩
  obtain ⟨H⟩ := hInv.hHist i hi
  have hm := hV.hMWU cfg.P.k H.len (levelM cfg.TP cfg.P i) cfg.N₀ H.D H.ord H.restarts
    (levelM_le_sq hV.hTP hV.hγM₀ hV.hγk i) cfg.P.hk
    H.hG0 H.hD H.hLen H.hℓPos H.hOrd H.hInitMBound H.hInitNBound H.hRestartsLt
    (by rw [H.hUpd]; exact H.hThresh) H.len (le_refl _) e (H.hEndG ▸ he)
  have hni : (H.D.G H.len).n ≤ cfg.N₀ := by
    rw [H.hEndG]
    exact le_trans (Finset.card_le_card (hB i hi.le).2.1) hn0
  rw [← H.hRun] at hm
  exact le_trans hm (hV.hσ_mwu_mono _ _ hni)

lemma chainState_snapHolds {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {s : ℕ} {ch : ChainState cfg.T cfg.P}
    {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hF : FreshInv (D.G s) (ch.G 0) e2i i2e nf)
    (hℓ : ch.ℓ = fun e' => D.ℓ s (i2e e'))
    (hn : (D.G s).n ≤ cfg.N₀) :
    ch.toTreeChain.d = cfg.P.d ∧ ch.toTreeChain.k = cfg.P.k ∧
    ch.toTreeChain.Holds (ch.G 0) (fun e' => D.ℓ s (i2e e'))
      (alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀)
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) ∧
    ch.toTreeChain.ForestsAreSubgraphs ∧
    ∀ i < cfg.P.d, ∀ e ∈ (ch.G i).E,
      (∑ j ∈ Finset.range cfg.P.k, (ch.toTreeChain.lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀ :=
  chainState_snapHoldsAt cfg.N₀ hV hInv hF hℓ hn (chainInv_last_le_N0 hV hn hInv hF)

end MinCostFlow.Chain.Ordered
