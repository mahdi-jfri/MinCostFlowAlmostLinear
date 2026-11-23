module

public import MinCostFlow.Chain.UpdateTrace

/-!
# Helpers for `UpdatePreLoop` and `Lemma6_5`

This file collects the auxiliary lemmas needed to advance `Alg2HiddenTrace` across
`algorithm1_update` and `algorithm2_loop`:
* `minRatioHistoryValid_prefix`: prefix monotonicity of `MinRatioHistoryValid`.
* `alg2UncondInv_extℓ_extg`: global functional agreement `st.extℓ = D.ℓ t ∧ st.extg = D.g t`.
* `alg2HiddenTrace_congr`: transfer of `Alg2HiddenTrace` across non-structural fields.
* `applyBatch_mem_E_of_not_inserts`, `notInsertedBetween_succ`,
  `rebuildCount_of_updateLoop_none`, `rebuildCount_of_updateLoop_some`.
* `shiftCount_append_round_adv`, `game_append_two_steps`.
* `lvlSnap_unrebuilt` and `lvl0NoIns_unrebuilt`.
-/

@[expose] public section

namespace MinCostFlow.Chain

/-- Restrict `MinRatioHistoryValid` to any prefix `T' ≤ T`. -/
lemma minRatioHistoryValid_prefix {D : DynamicInstance} {isUpdate : ℕ → Bool} {T T' : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hT' : T' ≤ T) :
    MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T' :=
  ⟨fun t h1 h2 => hHist.1 t h1 (le_trans h2 hT'),
   fun t ht => hHist.2.1 t (le_trans ht hT'),
   fun t h1 ht => hHist.2.2.1 t h1 (le_trans ht hT'),
   fun t h1 ht => hHist.2.2.2 t h1 (le_trans ht hT')⟩

/-- Global functional agreement `st.extℓ = D.ℓ t` and `st.extg = D.g t` along `minRatioFailState`
for `algorithm2_dsWith cfg κ`. -/
lemma alg2UncondInv_extℓ_extg_with {cfg : Alg2Config} (κ : ℝ)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) :
    ∀ t ≤ T,
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).extℓ = D.ℓ t ∧
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).extg = D.g t := by
  intro t
  induction t with
  | zero =>
    intro _
    simp [minRatioFailState, algorithm2_dsWith, algorithm2_init]
  | succ t ih =>
    intro ht
    obtain ⟨ihℓ, ihg⟩ := ih (Nat.le_of_succ_le ht)
    by_cases hupd : isUpdate (t + 1) = true
    · simp only [minRatioFailState, hupd, ↓reduceIte, algorithm2_dsWith, algorithm2_updateWith]
      cases hOpt : (algorithm2_loopWith cfg κ _ _ (D.g (t + 1)) (D.ℓ (t + 1)) _ _ _ _).2.2.2.2 <;>
        exact ⟨rfl, rfl⟩
    · have hfalse : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
      have hDet := hHist.2.2.1 (t + 1) (Nat.succ_pos t) ht hfalse
      simp only [minRatioFailState, hupd, Bool.false_eq_true, ↓reduceIte, algorithm2_dsWith,
        algorithm2_detect]
      exact ⟨ihℓ.trans hDet.2.2.symm, ihg.trans hDet.2.1.symm⟩

/-- Global functional agreement `st.extℓ = D.ℓ t` and `st.extg = D.g t` along `minRatioFailState`. -/
lemma alg2UncondInv_extℓ_extg {cfg : Alg2Config}
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) :
    ∀ t ≤ T,
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate t).extℓ = D.ℓ t ∧
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate t).extg = D.g t :=
  alg2UncondInv_extℓ_extg_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hHist

/-- Transfer `Alg2HiddenTraceAt` across state updates that only touch non-structural fields
(`flow`, `detectAccum`, `lctUpdateOps`, `lctDetectOps`, `largeBatchEnc`, `extG`, `extℓ`, `extg`). -/
def alg2HiddenTrace_congr {σ_cap : ℝ} {cfg : Alg2Config} {D : DynamicInstance}
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st₁ st₂ : Alg2State cfg}
    (tr : Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st₁)
    (hc : st₂.chain = st₁.chain) (hb : st₂.branD = st₁.branD) (hp : st₂.passes = st₁.passes)
    (he2i : st₂.extToInt = st₁.extToInt) (hi2e : st₂.intToExt = st₁.intToExt)
    (hnf : st₂.nextFresh = st₁.nextFresh) :
    Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st₂ := by
  cases st₁
  cases st₂
  dsimp only at hc hb hp he2i hi2e hnf
  subst hc hb hp he2i hi2e hnf
  exact ⟨tr.moves, tr.hmne, tr.initStr, tr.W_game, tr.hv, tr.hf, tr.hPhase, tr.timeOfRound,
    tr.hTimeMono, tr.hTimeEnd, tr.hW_eq, tr.hShiftMatch, tr.hRebMatch, tr.hPassMatch,
    tr.hBranMatch, tr.snapC, tr.snapE2I, tr.snapI2E, tr.snapNF, tr.hSnapEndC, tr.hSnapEndE2I,
    tr.hSnapEndI2E, tr.hSnapEndNF, tr.hSnapFresh, tr.hSnapHolds, tr.reinit, tr.hRebRep,
    tr.hRepRe, tr.hSnapBran, tr.hStrMatch, tr.H, tr.lvlIdx, tr.hLvlReinit, tr.hLvlEnd,
    tr.hLvlMono, tr.hLvlSucc, tr.hLvlSnap, tr.hLvlCore, tr.updRound, tr.hUpdBound, tr.hUpdMono,
    tr.hUpdBand, tr.hLvl0Match, tr.hLvl0NoIns⟩

/-- Any edge in `(G.applyBatch U).E` not inserted by any update in `U` belonged to `G.E`. -/
lemma applyBatch_mem_E_of_not_inserts (G : MGraph) (U : List Update) {e : ℕ}
    (he : e ∈ (G.applyBatch U).E) (hNo : ∀ u ∈ U, ¬ u.Inserts e) : e ∈ G.E := by
  induction U generalizing G with
  | nil => exact he
  | cons u rest ih =>
    have h1 : e ∈ (G.applyUpdate u).E := ih (G.applyUpdate u) he fun v hv => hNo v (by simp [hv])
    have hnu : ¬ u.Inserts e := hNo u (by simp)
    cases u with
    | insert e' a b =>
      simp only [MGraph.applyUpdate, Finset.mem_insert] at h1
      rcases h1 with hEq | hIn
      · exact absurd (by simp [Update.Inserts, hEq]) hnu
      · exact hIn
    | delete e' =>
      simp only [MGraph.applyUpdate] at h1
      exact Finset.mem_of_mem_erase h1
    | split _ _ _ _ =>
      simp only [MGraph.applyUpdate] at h1
      exact h1

/-- Extending `NotInsertedBetween` across one external step. -/
lemma notInsertedBetween_succ (D : DynamicInstance) {e a b : ℕ} (_hab : a ≤ b)
    (hPrev : D.NotInsertedBetween e a b)
    (hStep : ∀ u ∈ D.U (b + 1), ¬ u.Inserts e) :
    D.NotInsertedBetween e a (b + 1) := by
  intro s hs1 hs2 u hu hIns
  by_cases hs_le : s ≤ b
  · exact hPrev s hs1 hs_le u hu hIns
  · have hseq : s = b + 1 := by omega
    subst hseq
    exact hStep u hu hIns

/-- If `firstRebuiltLevel` is `none` after `algorithm1_update`, `rebuildCount` is unchanged. -/
lemma rebuildCount_of_updateLoop_none (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (ℓ' g' : ℕ → ℝ) (st : ChainState T P) (U : List Update)
    (hNone : firstRebuiltLevel P.d st.rebuildCount
      ((algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount) = none) :
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount = st.rebuildCount := by
  dsimp only [algorithm1_update] at hNone ⊢
  let st0 : ChainState T P :=
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
  rcases updateLoop_rebuildCount_cases T L TP P N₀ ℓ' g' P.d 0 st0 ((st.G 0).applyBatch U) U
      ((st.G 0).batchEnc U) (Nat.zero_add P.d) with heq | ⟨i', _, hi', hrb'⟩
  · exact heq
  · rw [hrb', firstRebuiltLevel_eq_of_inc hi' st.rebuildCount] at hNone
    simp at hNone

/-- If `firstRebuiltLevel` is `some iStar` after `algorithm1_update`, `rebuildCount` increments
precisely at `iStar < P.d`. -/
lemma rebuildCount_of_updateLoop_some (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ)
    (ℓ' g' : ℕ → ℝ) (st : ChainState T P) (U : List Update)
    {iStar : ℕ} (hSome : firstRebuiltLevel P.d st.rebuildCount
      ((algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount) = some iStar) :
    iStar < P.d ∧
    (algorithm1_update T L TP P N₀ st U g' ℓ').1.rebuildCount =
      fun j => if j = iStar then st.rebuildCount iStar + 1 else st.rebuildCount j := by
  dsimp only [algorithm1_update] at hSome ⊢
  let st0 : ChainState T P :=
    { st with recUpdates := fun j => if j = 0 then st.recUpdates 0 + U.length else st.recUpdates j }
  rcases updateLoop_rebuildCount_cases T L TP P N₀ ℓ' g' P.d 0 st0 ((st.G 0).applyBatch U) U
      ((st.G 0).batchEnc U) (Nat.zero_add P.d) with heq | ⟨i', _, hi', hrb'⟩
  · rw [heq, firstRebuiltLevel_eq_of_eq st.rebuildCount] at hSome
    simp at hSome
  · rw [hrb', firstRebuiltLevel_eq_of_inc hi' st.rebuildCount] at hSome
    simp only [Option.some.injEq] at hSome
    subst hSome
    exact ⟨hi', hrb'⟩

/-- `shiftCount` after appending a non-shifting round-completing step and an adversary step. -/
lemma shiftCount_append_round_adv {d k : ℕ} (ms : List (Game.Move d k))
    (m₂ : Game.Move d k)
    (hm₂ : m₂ = .advDoNothing ∨ ∃ i₀ newStr, m₂ = .advRebuild i₀ newStr)
    (i : Fin (d + 1)) :
    let m₁ : Game.Move d k := .roundStep .roundCompleting .doNothing (fun _ _ => 0)
    Game.shiftCount (ms ++ [m₁, m₂]) i = Game.shiftCount ms i := by
  intro m₁
  have hcm1 : Game.shiftCount [m₁] i = 0 := by simp [Game.shiftCount, m₁]
  have hcm2 : Game.shiftCount [m₂] i = 0 := by
    rcases hm₂ with rfl | ⟨i₀, newStr, rfl⟩ <;> simp [Game.shiftCount]
  have happ : ms ++ [m₁, m₂] = (ms ++ [m₁]) ++ [m₂] := by simp
  rw [happ, Game.shiftCount, List.countP_append, List.countP_append]
  change Game.shiftCount ms i + Game.shiftCount [m₁] i + Game.shiftCount [m₂] i = Game.shiftCount ms i
  rw [hcm1, hcm2]
  omega

/-- `Game.stateAt` and `Game.passesAt` after appending two valid moves `m₁, m₂` to `ms`. -/
lemma game_append_two_steps (params : Game.GameParams)
    {W' W_old : ℕ → ℝ} {initStr : Fin (params.d + 1) → Fin params.k → ℝ}
    {ms : List (Game.Move params.d params.k)}
    (hW_le : ∀ r ≤ (Game.stateAt W_old params.hk initStr ms ms.length).round, W_old r = W' r)
    (hv : Game.ValidPlayPrefix params W_old initStr ms)
    (hf : Game.FollowsStrategyPrefix params W_old initStr ms)
    (m₁ m₂ : Game.Move params.d params.k)
    (hm1_v : Game.ValidStep params W' (Game.stateAt W_old params.hk initStr ms ms.length) m₁)
    (hm1_s : Game.StrategyStep params (Game.stateAt W_old params.hk initStr ms ms.length)
      (Game.passesAt W_old params.hk initStr ms ms.length) m₁)
    (hm2_v : Game.ValidStep params W'
      (Game.stepState W' params.hk (Game.stateAt W_old params.hk initStr ms ms.length) m₁) m₂)
    (hm2_s : Game.StrategyStep params
      (Game.stepState W' params.hk (Game.stateAt W_old params.hk initStr ms ms.length) m₁)
      (Game.stepPasses params.hk (Game.stateAt W_old params.hk initStr ms ms.length)
        (Game.passesAt W_old params.hk initStr ms ms.length) m₁) m₂) :
    let ms' := ms ++ [m₁, m₂]
    Game.ValidPlayPrefix params W' initStr ms' ∧
    Game.FollowsStrategyPrefix params W' initStr ms' ∧
    Game.stateAt W' params.hk initStr ms' ms'.length =
      Game.stepState W' params.hk
        (Game.stepState W' params.hk (Game.stateAt W_old params.hk initStr ms ms.length) m₁) m₂ ∧
    Game.passesAt W' params.hk initStr ms' ms'.length =
      Game.stepPasses params.hk
        (Game.stepState W' params.hk (Game.stateAt W_old params.hk initStr ms ms.length) m₁)
        (Game.stepPasses params.hk (Game.stateAt W_old params.hk initStr ms ms.length)
          (Game.passesAt W_old params.hk initStr ms ms.length) m₁) m₂ := by
  intro ms'
  have hsc := (stateAt_W_congr W_old W' params.hk initStr ms ms.length hW_le).1.symm
  have hpc := (stateAt_W_congr W_old W' params.hk initStr ms ms.length hW_le).2.symm
  have hv1 := validPlayPrefix_snoc (validPlayPrefix_W_congr W_old W' hW_le hv) m₁ (by rwa [hsc])
  have hf1 := followsStrategyPrefix_snoc (followsStrategyPrefix_W_congr W_old W' hW_le hf) m₁
    (by rwa [hsc, hpc])
  have hlen1 : (ms ++ [m₁]).length = ms.length + 1 := by simp
  have hget1 : (ms ++ [m₁])[ms.length]'(by simp) = m₁ := by simp
  have hs1 : Game.stateAt W' params.hk initStr (ms ++ [m₁]) (ms ++ [m₁]).length =
      Game.stepState W' params.hk (Game.stateAt W_old params.hk initStr ms ms.length) m₁ := by
    rw [hlen1, Game.stateAt_succ W' params.hk initStr (ms ++ [m₁]) (by simp),
      stateAt_append_left W' params.hk initStr ms [m₁] ms.length (le_refl _), hget1, hsc]
  have hp1 : Game.passesAt W' params.hk initStr (ms ++ [m₁]) (ms ++ [m₁]).length =
      Game.stepPasses params.hk (Game.stateAt W_old params.hk initStr ms ms.length)
        (Game.passesAt W_old params.hk initStr ms ms.length) m₁ := by
    rw [hlen1, Game.passesAt_succ W' params.hk initStr (ms ++ [m₁]) (by simp),
      passesAt_append_left W' params.hk initStr ms [m₁] ms.length (le_refl _),
      stateAt_append_left W' params.hk initStr ms [m₁] ms.length (le_refl _), hget1, hsc, hpc]
  have hm' : ms' = (ms ++ [m₁]) ++ [m₂] := by simp [ms', List.append_assoc]
  have hv2 := validPlayPrefix_snoc hv1 m₂ (by rwa [hs1])
  have hf2 := followsStrategyPrefix_snoc hf1 m₂ (by rwa [hs1, hp1])
  have hlen2 : ((ms ++ [m₁]) ++ [m₂]).length = (ms ++ [m₁]).length + 1 := by simp
  have hget2 : ((ms ++ [m₁]) ++ [m₂])[(ms ++ [m₁]).length]'(by simp) = m₂ := by simp
  have hs2 : Game.stateAt W' params.hk initStr ((ms ++ [m₁]) ++ [m₂]) ((ms ++ [m₁]) ++ [m₂]).length =
      Game.stepState W' params.hk (Game.stepState W' params.hk
        (Game.stateAt W_old params.hk initStr ms ms.length) m₁) m₂ := by
    rw [hlen2, Game.stateAt_succ W' params.hk initStr _ (by simp),
      stateAt_append_left W' params.hk initStr (ms ++ [m₁]) [m₂] _ (le_refl _), hget2, hs1]
  have hp2 : Game.passesAt W' params.hk initStr ((ms ++ [m₁]) ++ [m₂]) ((ms ++ [m₁]) ++ [m₂]).length =
      Game.stepPasses params.hk
        (Game.stepState W' params.hk (Game.stateAt W_old params.hk initStr ms ms.length) m₁)
        (Game.stepPasses params.hk (Game.stateAt W_old params.hk initStr ms ms.length)
          (Game.passesAt W_old params.hk initStr ms ms.length) m₁) m₂ := by
    rw [hlen2, Game.passesAt_succ W' params.hk initStr _ (by simp),
      passesAt_append_left W' params.hk initStr (ms ++ [m₁]) [m₂] _ (le_refl _),
      stateAt_append_left W' params.hk initStr (ms ++ [m₁]) [m₂] _ (le_refl _), hget2, hs1, hp1]
  rw [← hm'] at hv2 hf2 hs2 hp2
  exact ⟨hv2, hf2, hs2, hp2⟩

/-- Snapshot agreement (`hLvlSnap`) at an unrebuilt level `i` whose `LevelHistory` `H1`
extends `tr.H i` by one step. -/
lemma lvlSnap_unrebuilt {σ_cap : ℝ} {cfg : Alg2Config} {D : DynamicInstance}
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st) {ch1 : ChainState cfg.T cfg.P}
    (i : ℕ) (hi : i < cfg.P.d) (H1 : LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch1 i)
    (_hLen : H1.len = (tr.H i hi).len + 1)
    (hPref : ∀ s ≤ (tr.H i hi).len,
      H1.D.G s = (tr.H i hi).D.G s ∧ H1.D.U s = (tr.H i hi).D.U s ∧
      H1.D.ℓ s = (tr.H i hi).D.ℓ s ∧ H1.D.g s = (tr.H i hi).D.g s)
    (hPrefRest : ∀ s ≤ (tr.H i hi).len, H1.restarts s = (tr.H i hi).restarts s)
    (r : ℕ) (hr1 : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r)
    (hr2 : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round + 1) :
    let R := (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round
    let snapC' := fun r' => if r' = R + 1 then ch1.toTreeChain else tr.snapC r'
    let idx' := if r = R + 1 then H1.len else tr.lvlIdx r i
    (snapC' r).G i = H1.D.G idx' ∧
    (∀ j < cfg.P.k, (snapC' r).lsfs i j =
      cfg.T.lsfs (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
        H1.D H1.restarts idx') j) ∧
    (tr.reinit ⟨i + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ ≤ r →
      ∀ j < cfg.P.k, (snapC' r).emb i j =
        cfg.T.emb (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
          H1.D H1.restarts idx') j) := by
  intro R snapC' idx'
  by_cases hrR : r = R + 1
  · subst hrR
    simp only [snapC', idx', ↓reduceIte, ChainState.toTreeChain]
    exact ⟨H1.hEndG.symm, fun j _ => by rw [← H1.hRun], fun _ j _ => by rw [← H1.hRun]⟩
  · have hr_le : r ≤ R := by omega
    simp only [snapC', idx', hrR, ↓reduceIte]
    have hidx_le : tr.lvlIdx r i ≤ (tr.H i hi).len := by
      rw [← tr.hLvlEnd i hi]
      exact tr.hLvlMono i hi r R hr1 hr_le (le_refl R)
    have hRunEq := cfg.T.runAfterRestarts_congr_le cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀ (tr.lvlIdx r i)
      (hPref 0 (Nat.zero_le _)).1 (hPref 0 (Nat.zero_le _)).2.2.1
      (hPref 0 (Nat.zero_le _)).2.2.2
      (fun s _ hs => ⟨(hPref s (le_trans hs hidx_le)).2.1,
        (hPref s (le_trans hs hidx_le)).2.2.1,
        (hPref s (le_trans hs hidx_le)).2.2.2⟩)
      (fun s hs => hPrefRest s (le_trans hs hidx_le))
    have hSnapOld := tr.hLvlSnap i hi r hr1 hr_le
    refine ⟨?_, fun j hj => ?_, fun hre1 j hj => ?_⟩
    · rw [(hPref _ hidx_le).1]; exact hSnapOld.1
    · rw [hRunEq]; exact hSnapOld.2.1 j hj
    · rw [hRunEq]; exact hSnapOld.2.2 hre1 j hj

/-- Level-0 no-insertion history (`hLvl0NoIns`) across an external update when level 0 is
NOT rebuilt (`H0'.len = (tr.H 0 cfg.P.hd).len + 1`). -/
lemma lvl0NoIns_unrebuilt {σ_cap : ℝ} {cfg : Alg2Config} {D : DynamicInstance}
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt σ_cap cfg D c_ext w_ext t st) {ch1 : ChainState cfg.T cfg.P}
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (_hExtG : st.extG = D.G t)
    {extG' : MGraph} {e2i' i2e' : ℕ → ℕ} {nf' : ℕ} {U_int : List Update}
    (_hTB : translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1)) =
      (extG', e2i', i2e', nf', U_int))
    (hFresh' : FreshInv extG' (ch1.G 0) e2i' i2e' nf')
    (hCh0eq : ch1.G 0 = (st.chain.G 0).applyBatch U_int)
    (hi2e_old : ∀ e' < st.nextFresh, i2e' e' = st.intToExt e')
    (hYesInsExt : ∀ e ∈ extG'.E, (∃ u ∈ D.U (t + 1), u.Inserts e) → st.nextFresh ≤ e2i' e)
    (H0' : LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch1 0)
    (hLen : H0'.len = (tr.H 0 cfg.P.hd).len + 1)
    (hPref : ∀ s ≤ (tr.H 0 cfg.P.hd).len,
      H0'.D.G s = (tr.H 0 cfg.P.hd).D.G s ∧ H0'.D.U s = (tr.H 0 cfg.P.hd).D.U s ∧
      H0'.D.ℓ s = (tr.H 0 cfg.P.hd).D.ℓ s ∧ H0'.D.g s = (tr.H 0 cfg.P.hd).D.g s)
    (hEndU : H0'.D.U ((tr.H 0 cfg.P.hd).len + 1) = U_int) :
    let R := (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round
    let updRound' := fun τ => if τ = (tr.H 0 cfg.P.hd).len + 1 then R + 1 else tr.updRound τ
    let snapI2E' := fun r' => if r' = R + 1 then i2e' else tr.snapI2E r'
    let timeOfRound' := fun r' => if r' = R + 1 then t + 1 else tr.timeOfRound r'
    ∀ s τ, s ≤ τ → τ ≤ H0'.len →
      ∀ r_s r_τ,
        updRound' s ≤ r_s → r_s ≤ R + 1 → (s < H0'.len → r_s < updRound' (s + 1)) →
        updRound' τ ≤ r_τ → r_τ ≤ R + 1 → (τ < H0'.len → r_τ < updRound' (τ + 1)) →
        r_s ≤ r_τ →
        ∀ e' ∈ (H0'.D.G τ).E,
          (s = τ →
            snapI2E' r_τ e' = snapI2E' r_s e' ∧
            D.NotInsertedBetween (snapI2E' r_τ e') (timeOfRound' r_s) (timeOfRound' r_τ) ∧
            D.ℓ (timeOfRound' r_τ) (snapI2E' r_τ e') = D.ℓ (timeOfRound' r_s) (snapI2E' r_τ e')) ∧
          (H0'.D.NotInsertedBetween e' s τ →
            snapI2E' r_τ e' = snapI2E' r_s e' ∧
            D.NotInsertedBetween (snapI2E' r_τ e') (timeOfRound' r_s) (timeOfRound' r_τ)) := by
  intro R updRound' snapI2E' timeOfRound'
  let len0 := (tr.H 0 cfg.P.hd).len
  have hRebR : tr.updRound len0 ≤ R := (tr.hUpdBound len0 (le_refl _)).2
  intro s τ hsτ hτ_len r_s r_τ hrs1 hrs2 hrs3 hrτ1 hrτ2 hrτ3 hr_st e' he'
  by_cases hτ_old : τ ≤ len0
  · have hs_old : s ≤ len0 := le_trans hsτ hτ_old
    have hrτ_lt : r_τ < R + 1 := by
      have h1 := hrτ3 (by rw [hLen]; exact Nat.lt_succ_of_le hτ_old)
      dsimp only [updRound'] at h1
      split_ifs at h1 with hEq
      · exact h1
      · have hτ1_le : τ + 1 ≤ len0 := by omega
        exact Nat.lt_succ_of_lt (lt_of_lt_of_le h1 (tr.hUpdBound (τ + 1) hτ1_le).2)
    have hrτ_R : r_τ ≤ R := Nat.lt_succ_iff.mp hrτ_lt
    have hrs_R : r_s ≤ R := le_trans hr_st hrτ_R
    have hs_neq : s ≠ len0 + 1 := by omega
    have hτ_neq : τ ≠ len0 + 1 := by omega
    have hrs1' : tr.updRound s ≤ r_s := by
      dsimp only [updRound'] at hrs1
      split_ifs at hrs1
      · omega
      · exact hrs1
    have hrτ1' : tr.updRound τ ≤ r_τ := by
      dsimp only [updRound'] at hrτ1
      split_ifs at hrτ1
      · omega
      · exact hrτ1
    have hrs3' : s < len0 → r_s < tr.updRound (s + 1) := fun hs_lt => by
      have h1 := hrs3 (by rw [hLen]; omega)
      dsimp only [updRound'] at h1
      split_ifs at h1 with hEq
      · omega
      · exact h1
    have hrτ3' : τ < len0 → r_τ < tr.updRound (τ + 1) := fun hτ_lt => by
      have h1 := hrτ3 (by rw [hLen]; omega)
      dsimp only [updRound'] at h1
      split_ifs at h1 with hEq
      · omega
      · exact h1
    have he'_old : e' ∈ ((tr.H 0 cfg.P.hd).D.G τ).E := by rwa [← (hPref τ hτ_old).1]
    have hOld := tr.hLvl0NoIns s τ hsτ hτ_old r_s r_τ hrs1' hrs_R hrs3' hrτ1' hrτ_R hrτ3' hr_st e' he'_old
    simp only [snapI2E', timeOfRound', show r_s ≠ R + 1 by omega, show r_τ ≠ R + 1 by omega,
      ↓reduceIte]
    refine ⟨hOld.1, fun hNIB => hOld.2 fun δ hδ1 hδ2 => ?_⟩
    have hδ_le : δ ≤ len0 := le_trans hδ2 hτ_old
    rw [← (hPref δ hδ_le).2.1]
    exact hNIB δ hδ1 hδ2
  · have hτeq : τ = len0 + 1 := by omega
    subst hτeq
    have hrτ_eq : r_τ = R + 1 := by
      have h1 : updRound' (len0 + 1) = R + 1 := by simp [updRound', len0]
      omega
    subst hrτ_eq
    have he'_ch1 : e' ∈ (ch1.G 0).E := by
      rw [← H0'.hEndG, hLen]; exact he'
    by_cases hs_top : s = len0 + 1
    · subst hs_top
      have hrs_eq : r_s = R + 1 := by
        have h1 : updRound' (len0 + 1) = R + 1 := by simp [updRound', len0]
        omega
      subst hrs_eq
      refine ⟨fun _ => ⟨rfl, fun δ h1 h2 => absurd h2 (by omega), rfl⟩, fun _ => ?_⟩
      exact ⟨rfl, fun δ h1 h2 => absurd h2 (by omega)⟩
    · have hs_le : s ≤ len0 := by omega
      have hrs_lt : r_s < R + 1 := by
        have h1 := hrs3 (by rw [hLen]; exact Nat.lt_succ_of_le hs_le)
        dsimp only [updRound'] at h1
        split_ifs at h1 with hEq
        · exact h1
        · exact Nat.lt_succ_of_lt (lt_of_lt_of_le h1 (tr.hUpdBound (s + 1) (by omega)).2)
      have hrs_R : r_s ≤ R := Nat.lt_succ_iff.mp hrs_lt
      refine ⟨fun heq => absurd heq hs_top, fun hNIB => ?_⟩
      have hNoU : ∀ u ∈ U_int, ¬ u.Inserts e' := fun u hu hIns => by
        exact hNIB (len0 + 1) (by omega) (le_refl _) u (hEndU ▸ hu) hIns
      have he'_st0 : e' ∈ (st.chain.G 0).E :=
        applyBatch_mem_E_of_not_inserts (st.chain.G 0) U_int (hCh0eq ▸ he'_ch1) hNoU
      have he'_lt_nf : e' < st.nextFresh := hFresh.hLtFresh e' he'_st0
      have hi2e_eq : i2e' e' = st.intToExt e' := hi2e_old e' he'_lt_nf
      have hNoExt : ∀ u ∈ D.U (t + 1), ¬ u.Inserts (i2e' e') := fun u hu hIns => by
        have he_ext1 : i2e' e' ∈ extG'.E := (hFresh'.hRight e' he'_ch1).2
        have hge := hYesInsExt (i2e' e') he_ext1 ⟨u, hu, hIns⟩
        have he2i_eq : e2i' (i2e' e') = e' := (hFresh'.hRight e' he'_ch1).1
        omega
      have he'_H0 : e' ∈ ((tr.H 0 cfg.P.hd).D.G len0).E := by
        rw [(tr.H 0 cfg.P.hd).hEndG]; exact he'_st0
      have hNIB_old : (tr.H 0 cfg.P.hd).D.NotInsertedBetween e' s len0 := fun δ h1 h2 => by
        rw [← (hPref δ h2).2.1]
        exact hNIB δ h1 (by omega)
      have hrs1' : tr.updRound s ≤ r_s := by
        dsimp only [updRound'] at hrs1
        split_ifs at hrs1 with hEq
        · omega
        · exact hrs1
      have hrs3' : s < len0 → r_s < tr.updRound (s + 1) := fun hs_lt => by
        have h1 := hrs3 (by rw [hLen]; omega)
        dsimp only [updRound'] at h1
        split_ifs at h1 with hEq
        · omega
        · exact h1
      have hOld := tr.hLvl0NoIns s len0 hs_le (le_refl _) r_s R
        hrs1' hrs_R hrs3' hRebR (le_refl R) (fun hlt => absurd hlt (Nat.lt_irrefl _))
        hrs_R e' he'_H0
      have hEqI2E_old : tr.snapI2E R e' = tr.snapI2E r_s e' ∧
          D.NotInsertedBetween (tr.snapI2E R e') (tr.timeOfRound r_s) (tr.timeOfRound R) := by
        by_cases hs_eq : s = len0
        · have h1 := hOld.1 hs_eq
          exact ⟨h1.1, h1.2.1⟩
        · exact hOld.2 hNIB_old
      have hEndI2E_eq : tr.snapI2E R e' = st.intToExt e' := tr.hSnapEndI2E ▸ rfl
      have hSnapEq : snapI2E' (R + 1) e' = snapI2E' r_s e' := by
        simp only [snapI2E', ↓reduceIte, show r_s ≠ R + 1 by omega]
        rw [hi2e_eq, ← hEndI2E_eq, hEqI2E_old.1]
      refine ⟨hSnapEq, ?_⟩
      simp only [snapI2E', timeOfRound', ↓reduceIte, show r_s ≠ R + 1 by omega]
      rw [hi2e_eq, ← hEndI2E_eq]
      have hTimeLe : tr.timeOfRound r_s ≤ t := by
        calc tr.timeOfRound r_s ≤ tr.timeOfRound R := tr.hTimeMono r_s R hrs_R (le_refl R)
          _ = t := tr.hTimeEnd
      have hNIB_t : D.NotInsertedBetween (tr.snapI2E R e') (tr.timeOfRound r_s) t := by
        have h := hEqI2E_old.2
        rw [tr.hTimeEnd] at h
        exact h
      exact notInsertedBetween_succ D hTimeLe hNIB_t (by rwa [hEndI2E_eq, ← hi2e_eq])

end MinCostFlow.Chain
