module

public import MinCostFlow.Chain.Ordered.HiddenTraceSteps
import MinCostFlow.Chain.Ordered.BudgetHelpers
import MinCostFlow.Chain.Ordered.BudgetHelpersCost
import MinCostFlow.Chain.Ordered.RebuildSuffix

/-!
# Structural and quality helpers for the ordered hidden-trace shift step

Split from `MinCostFlow.Chain.Ordered.HiddenTraceShift` (following
`MinCostFlow.Chain.HiddenTraceShiftHelpers`):

* `alg2HiddenTrace_shift_gameBad`: derives `Game.LossSumCond ∨ Game.BadStretchCond` from
  a failed ratio test via `Alg2HiddenTraceAt.toRepQualityCtx` and `lemma_6_3`.
* `alg2HiddenTrace_shiftStruct_aux`: constructs the shifted ordered `LevelHistory` family `H'`
  (including order preservation `(H' k hk).ord = (H k hk).ord` for `k ≤ i.val`) and active chain
  structural facts across `algorithm1_shift`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- When `algorithm1_findCycle` fails ratio `-κ α`, the Game state satisfies either
`Game.LossSumCond` or `Game.BadStretchCond` (Lemma 6.3). -/
lemma alg2HiddenTrace_shift_gameBad (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrd)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtℓ : st.extℓ = D.ℓ t) (hExtg : st.extg = D.g t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hg : st.chain.g = fun e' => st.extg (st.intToExt e'))
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (hNotGood : ¬ (st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) /
        st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) ≤
      -(alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast * cfg.α))) :
    let gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
    Game.LossSumCond tr.W_game gSt ∨ Game.BadStretchCond cfg.gameParams.σ gSt := by
  set κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast
  set gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  set R := gSt.round
  have hVNH := hV.toNoHidden
  have hℓD : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e') := by rw [hℓ, hExtℓ]
  have hgD : st.chain.g = fun e' => D.g t (st.intToExt e') := by rw [hg, hExtg]
  obtain ⟨ctx, hcd, hck, hcγl, hcγc, hcσ, hcσm, hct, hcC, hc0, hcRep⟩ :=
    tr.toRepQualityCtx hV hHS hInv
  have hTH := ChainInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hVNH.hMWU
    hVNH.hEmb hV.hγM₀ hV.hγk hInv
  have hPb := freshInv_pullback_hiddenAt (tr.hSnapFresh R (le_refl R))
    (tr.hTimeEnd ▸ hHS t (le_refl t))
  rw [tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E] at hPb
  have h0t := hc0 ctx.t (le_refl _)
  have hvp_t : IsValidPair (ctx.G0 ctx.t) (ctx.ℓ0 ctx.t)
      (fun e' => c_ext t (st.intToExt e')) (ctx.w ctx.t) := by
    rw [h0t.1, h0t.2.1, h0t.2.2, hct, tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E]
    exact hPb.2.1
  have hItem3 : (ctx.G0 ctx.t).inner st.chain.g (fun e' => c_ext t (st.intToExt e')) /
      (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) ≤ -cfg.α := by
    rw [h0t.1, h0t.2.2, hct, tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E, hgD]
    exact hPb.2.2.1
  have hRat : (ctx.G0 ctx.t).inner st.chain.g (algorithm1_findCycle st.chain).1 /
      (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) (algorithm1_findCycle st.chain).1 > -(κ * cfg.α) := by
    have hIn : st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) =
        (st.chain.G 0).inner st.chain.g (algorithm1_findCycle st.chain).1 := by
      rw [hg, hFresh.inner_lift]
    have hLn : st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) =
        (st.chain.G 0).lnorm st.chain.ℓ (algorithm1_findCycle st.chain).1 := by
      rw [hℓ, hFresh.lnorm_lift]
    have hGt_eq : ctx.G0 ctx.t = st.chain.G 0 := by rw [h0t.1, hct, tr.hSnapEndC]; rfl
    have hℓt_eq : ctx.ℓ0 ctx.t = st.chain.ℓ := by rw [h0t.2.1, hct, tr.hTimeEnd, tr.hSnapEndI2E, hℓD]
    rw [hGt_eq, hℓt_eq]
    rw [hIn, hLn] at hNotGood
    exact lt_of_not_ge hNotGood
  have hκ_eq : κ = kappaBound ctx.d ctx.γ_ℓ (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      (alg2SigmaGame cfg.σ_mwu cfg.N₀) := by rw [hcd, hcγl]; rfl
  have hRatK : (ctx.G0 ctx.t).inner st.chain.g (algorithm1_findCycle st.chain).1 /
      (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) (algorithm1_findCycle st.chain).1 >
      -(kappaBound ctx.d ctx.γ_ℓ (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
        (alg2SigmaGame cfg.σ_mwu cfg.N₀) * cfg.α) := by
    rwa [← hκ_eq]
  have hSG_nn : 0 ≤ alg2SigmaGame cfg.σ_mwu cfg.N₀ := le_max_left _ _
  have hBad := lemma_6_3 ctx st.chain (by rw [hcC, hct, tr.hSnapEndC]) rfl
    (by rw [h0t.2.1, hct, tr.hTimeEnd, tr.hSnapEndI2E, hℓD])
    (by rw [hcσ]; exact le_refl _)
    (le_trans zero_le_one (le_max_of_le_left (hV.hTP.1 cfg.P.k cfg.N₀ cfg.P.hk)))
    hSG_nn hV.hα hInv.hℓPos hTH.2.1 hTH.2.2 hvp_t hItem3 hRatK
  rcases hBad with hBN | hBH
  · left
    unfold BadNormCond at hBN
    unfold Game.LossSumCond
    have hWR : tr.W_game gSt.round = (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
      have hF0 := (tr.hSnapFresh R (le_refl R)).norm1_pullback (w_ext t)
      rw [tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E] at hF0
      have hW_g : tr.W_game gSt.round = (D.G t).norm1 (w_ext t) := by
        have h := tr.hW_eq R (le_refl R)
        rwa [tr.hTimeEnd] at h
      rw [h0t.1, h0t.2.2, hct, tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E, hF0, hW_g]
    have hSum : (∑ j : Fin (cfg.P.d + 1), tr.W_game (gSt.repT j)) =
        ∑ j ∈ Finset.range (ctx.d + 1), (ctx.G0 (ctx.repT j)).norm1 (ctx.w (ctx.repT j)) := by
      rw [hcd, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hrepR : gSt.repT j ≤ R := (Game.repT_bounds _ _ _ _ _ j).2
      have hj0 := hc0 (gSt.repT j) (by rw [hct]; exact hrepR)
      have hF := (tr.hSnapFresh (gSt.repT j) hrepR).norm1_pullback (w_ext (tr.timeOfRound (gSt.repT j)))
      rw [tr.hW_eq (gSt.repT j) hrepR, ← hF, ← hj0.1, ← hj0.2.2, ← (hcRep j).2]
    rw [hWR, hSum, ← hcd]
    exact hBN
  · right
    obtain ⟨j, hj, hj_gt⟩ := hBH
    rw [hcd] at hj
    refine ⟨⟨j, Nat.lt_succ_of_lt hj⟩, ?_⟩
    have hbr_eq : (gSt.bran ⟨j, Nat.lt_succ_of_lt hj⟩).val = (ctx.C ctx.t).bran j := by
      have := tr.hBranMatch ⟨j, Nat.lt_succ_of_lt hj⟩
      simp only [hj, ↓reduceIte] at this
      rw [this, hcC, hct, tr.hSnapEndC]; rfl
    have hstr_eq := tr.hStrMatch ⟨j, Nat.lt_succ_of_lt hj⟩ (gSt.bran ⟨j, Nat.lt_succ_of_lt hj⟩)
    simp only [hj, ↓reduceDIte] at hstr_eq
    change cfg.gameParams.σ < gSt.str ⟨j, Nat.lt_succ_of_lt hj⟩ (gSt.bran ⟨j, Nat.lt_succ_of_lt hj⟩)
    rw [hstr_eq, hbr_eq, ← (hcRep ⟨j, Nat.lt_succ_of_lt hj⟩).2]
    have hrepR : ctx.repT j ≤ ctx.t := by
      rw [(hcRep ⟨j, Nat.lt_succ_of_lt hj⟩).2, hct]; exact (Game.repT_bounds _ _ _ _ _ _).2
    have hrep0 := hc0 (ctx.repT j) hrepR
    change alg2SigmaGame cfg.σ_mwu cfg.N₀ <
      hstrAt (tr.snapC (ctx.repT j)) (fun e' => w_ext (tr.timeOfRound (ctx.repT j)) (tr.snapI2E (ctx.repT j) e'))
        j ((ctx.C ctx.t).bran j)
    rw [← hrep0.2.2, ← hcC]
    exact hj_gt

lemma alg2HiddenTrace_shiftStruct_aux
    (cfg : Alg2Config) (hV : cfg.ValidOrd) (hVNH : cfg.ValidOrdNoHidden)
    (ch ch' : ChainState cfg.T cfg.P) (i : Fin (cfg.P.d + 1))
    (hCh'_def : ch' = (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hInv' : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch')
    (hℓR : LenInRange (max 0 cfg.Ψ) (ch.G 0) ch.ℓ)
    (H : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch k)
    (hℓ' : ch'.ℓ = ch.ℓ)
    (hg' : ch'.g = ch.g) :
    Nonempty (Σ' (H' : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch' k),
  (∀ k (hk : k < cfg.P.d), k ≤ i.val →
    (H' k hk).D = (H k hk).D ∧ (H' k hk).ord = (H k hk).ord ∧ (H' k hk).len = (H k hk).len ∧
    (k < i.val → (H' k hk).restarts = (H k hk).restarts ∧ (H' k hk).s₀ = (H k hk).s₀)) ∧
  (∀ k (hk : k < cfg.P.d), i.val < k → (H' k hk).len = 0) ∧
  (∀ k ≤ i.val, k < cfg.P.d →
    ch'.G k = ch.G k ∧ (k < i.val → ch'.scState k = ch.scState k) ∧
    (∀ j < cfg.P.k, cfg.T.lsfs (ch'.scState k) j = cfg.T.lsfs (ch.scState k) j)) ∧
  (∀ b < i.val, ch'.bran b = ch.bran b) ∧
  (i.val < cfg.P.d → ch'.bran i.val = (ch.bran i.val + 1) % cfg.P.k) ∧
  (∀ k, i.val < k → k < cfg.P.d →
    ch'.bran k = 0 ∧
    ch'.scState k = cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (ch'.G k)
      (ch'.toTreeChain.chainLen ch'.ℓ k)
      (ch'.toTreeChain.chainGrad ch'.g k)
      (ch'.levelOrd k)) ∧
  (∀ k (_hk : k + 1 < cfg.P.d), i.val < k + 1 →
    ch'.G (k + 1) = cfg.T.S (ch'.scState k) (ch'.bran k)) ∧
  (∀ k (hk : k < cfg.P.d), k ≤ i.val → ∀ s < (H k hk).len,
    (H' k hk).restarts s = (H k hk).restarts s)) := by
  have hch_ℓ : ch'.ℓ = ch.ℓ := hℓ'
  have hch_g : ch'.g = ch.g := hg'
  by_cases hi_lt : i.val < cfg.P.d
  · have hB := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hγM₀ hV.hγk hInv
    have hiB := hB i.val (Nat.le_of_lt hi_lt)
    set newBran := (ch.bran i.val + 1) % cfg.P.k
    have hnb_lt : newBran < cfg.P.k := Nat.mod_lt _ cfg.P.hk
    set sc_i0 := cfg.T.restart (ch.scState i.val) newBran
    set Gnext := cfg.T.S sc_i0 newBran
    let H_i0 := H i.val hi_lt
    let restarts_i0' : ℕ → List ℕ :=
      fun r => if r = H_i0.len then H_i0.restarts H_i0.len ++ [newBran] else H_i0.restarts r
    have hRestLt_i0' : ∀ r ≤ H_i0.len, ∀ j ∈ restarts_i0' r, j < cfg.P.k := by
      intro r hr j hj
      by_cases hr_eq : r = H_i0.len
      · subst hr_eq
        simp only [restarts_i0', ↓reduceIte, List.mem_append, List.mem_singleton] at hj
        rcases hj with hj | rfl
        · exact H_i0.hRestartsLt _ (le_refl _) _ hj
        · exact hnb_lt
      · simp only [restarts_i0', hr_eq, ↓reduceIte] at hj
        exact H_i0.hRestartsLt r hr j hj
    have hRunPre_i0 : ∀ s ≤ H_i0.len,
        cfg.T.runOrdAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.ord restarts_i0' s =
          cfg.T.runOrdAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.ord H_i0.restarts s := by
      intro s hs
      exact cfg.T.runOrdAfterUpdate_congr_lt cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ s rfl rfl rfl
        (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => rfl)
        (fun r hr => by simp [restarts_i0', show r ≠ H_i0.len by omega])
    have hRunRestart : sc_i0 =
        cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.ord restarts_i0' H_i0.len := by
      change cfg.T.restart (ch.scState i.val) newBran =
        (restarts_i0' H_i0.len).foldl cfg.T.restart
          (cfg.T.runOrdAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.ord restarts_i0' H_i0.len).1
      rw [hRunPre_i0 H_i0.len (le_refl _)]
      simp only [restarts_i0', ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [H_i0.hRun]; rfl
    have hSpecPost := H_i0.hOK.noHidden cfg.P.k H_i0.len (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.ord restarts_i0'
      cfg.P.hk H_i0.hG0 H_i0.hD H_i0.hLen H_i0.hℓPos H_i0.hOrd H_i0.hInitMBound H_i0.hInitNBound
      hRestLt_i0' (by rw [H_i0.hUpd]; exact H_i0.hThresh) ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hAtPost := hSpecPost.1 H_i0.len (le_refl _) newBran hnb_lt
    dsimp only at hAtPost
    rw [← hRunRestart, H_i0.hEndG] at hAtPost
    have hLsf_i0_eq : ∀ b < cfg.P.k, cfg.T.lsfs sc_i0 b = cfg.T.lsfs (ch.scState i.val) b := by
      have hBranch := hSpecPost.2.2.1 H_i0.len (le_refl _) (H_i0.restarts H_i0.len) newBran
        (by simp [restarts_i0'])
      dsimp only at hBranch
      rw [hRunPre_i0 H_i0.len (le_refl _)] at hBranch
      have hPostSt : (H_i0.restarts H_i0.len).foldl cfg.T.restart
            (cfg.T.runOrdAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.ord H_i0.restarts H_i0.len).1 =
          ch.scState i.val := by
        simpa [SparseCoreRestartTool.runOrdAfterRestarts] using H_i0.hRun.symm
      rw [hPostSt] at hBranch
      exact hBranch.1
    have hk_pos_R : (0 : ℝ) < cfg.P.k := Nat.cast_pos.mpr cfg.P.hk
    have hActiveNew :
        (cfg.T.lsfs sc_i0 newBran).Holds (ch.G i.val)
            (ch.toTreeChain.chainLen ch.ℓ i.val)
            (cfg.TP.σ cfg.P.k (ch.G 0).n) ∧
          IsSparsifiedCoreGraphAt (ch.G i.val) (cfg.T.lsfs sc_i0 newBran)
            (ch.toTreeChain.chainLen ch.ℓ i.val) (cfg.P.k : ℝ)
            (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2))
            (levelM cfg.TP cfg.P i.val)
            (cfg.T.S sc_i0 newBran) (cfg.T.emb sc_i0 newBran) := by
      have hn_le_i0 : (ch.G i.val).n ≤ (ch.G 0).n := Finset.card_le_card hiB.2.1
      have hHolds := LSF.Holds.mono_σ
        (LSF.Holds.congr_len hAtPost.1 fun e he => H_i0.hEndℓ e he)
        (hV.hTP.2.1 _ _ _ _ (le_refl _) hn_le_i0)
      have hm_le : levelM cfg.TP cfg.P i.val ≤ cfg.P.M₀ ^ 2 :=
        levelM_le_sq hV.hTP hV.hγM₀ hV.hγk i.val
      have hSp' : IsSparsifiedCoreGraphAt (ch.G i.val) (cfg.T.lsfs sc_i0 newBran)
          (ch.toTreeChain.chainLen ch.ℓ i.val) (cfg.P.k : ℝ)
          (cfg.TP.γ_ℓ (levelM cfg.TP cfg.P i.val)) (cfg.TP.γ_c (levelM cfg.TP cfg.P i.val))
          (levelM cfg.TP cfg.P i.val)
          (cfg.T.S sc_i0 newBran) (cfg.T.emb sc_i0 newBran) := by
        rcases hAtPost.2.1 with ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩
        refine ⟨hs1, hs2, fun e he e' he' => ?_, hs4, hs5, hs6⟩
        have he0 : e ∈ (ch.G i.val).E := (Finset.mem_sdiff.mp he).1
        have he'0 : e' ∈ (ch.G i.val).E := by
          have he'S : e' ∈ (cfg.T.S sc_i0 newBran).E := mem_E_of_mem_walkEdges (hs2.2 e he) he'
          exact (Finset.mem_sdiff.mp (hs1.2.1 he'S)).1
        simpa [coreLen, H_i0.hEndℓ e he0, H_i0.hEndℓ e' he'0] using hs3 e he e' he'
      exact ⟨hHolds, isSparsifiedCoreGraphAt_mono hSp' hk_pos_R
        (le_trans zero_le_one (hV.hTP.2.2.1 (levelM cfg.TP cfg.P i.val)))
        (hV.hTP.2.2.2.1 _ _ hm_le) (hV.hTP.2.2.2.2.2.1 _ _ hm_le) (le_refl _)⟩
    have hGnext_v : Gnext.IsValid := by
      have hCore := coreGraph_isValid hiB.1 hActiveNew.1.2.1
      intro e he
      have hEnd := hActiveNew.2.1.2.2 e he
      have hc := hCore e (hActiveNew.2.1.2.1 he)
      rw [hEnd.1, hEnd.2]
      exact ⟨hActiveNew.2.2.1.1 hc.1, hActiveNew.2.2.1.1 hc.2⟩
    have hGnext_V : Gnext.V ⊆ (ch.G 0).V :=
      Finset.Subset.trans (Finset.Subset.trans hActiveNew.2.1.1 hActiveNew.1.2.1.2.2.1) hiB.2.1
    have hGnext_m : (Gnext.m : ℝ) ≤ (levelM cfg.TP cfg.P (i.val + 1) : ℝ) := by
      have hcard : (Gnext.E.card : ℝ) ≤
          (levelM cfg.TP cfg.P i.val : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / cfg.P.k :=
        hActiveNew.2.2.2.2.2.2
      exact_mod_cast levelM_step_nat hV.hTP hV.hγk hcard
    let G0 := fun j => if j = i.val + 1 then Gnext else ch.G j
    let sc0 := fun j => if j = i.val then sc_i0 else ch.scState j
    let bran0 := fun j => if j = i.val then newBran else ch.bran j
    let cDec0 := fun j => if j = i.val then 0 else ch.curDecUpdates j
    let cEnc0 := fun j => if j = i.val + 1 then 0 else ch.curEnc j
    have hℓ_next : LevelLenRange cfg.TP cfg.P cfg.N₀ (max 0 cfg.Ψ) (i.val + 1) (G0 (i.val + 1))
        ((mkPartialChain cfg.T cfg.P G0 sc0 bran0 (G0 (i.val + 1))).chainLen ch.ℓ (i.val + 1)) :=
          fun e he => by
      simp only [G0, ↓reduceIte] at he
      have heGi : e ∈ (ch.G i.val).E := (Finset.mem_sdiff.mp (hActiveNew.2.1.2.1 he)).1
      have hLCon : (mkPartialChain cfg.T cfg.P G0 sc0 bran0 (G0 (i.val + 1))).chainLen
            ch.ℓ i.val = ch.toTreeChain.chainLen ch.ℓ i.val :=
        chainLen_congr_lt ch.ℓ i.val
          (fun m hm => by simp [mkPartialChain, ChainState.toTreeChain, G0, show m ≠ i.val + 1 by omega])
          fun m hm => by
            have hmd : m < cfg.P.d := lt_trans hm hi_lt
            simp only [TreeChain.activeLSF, mkPartialChain, ChainState.toTreeChain, hmd, ↓reduceIte,
              sc0, bran0, Nat.ne_of_lt hm]
      have hAct : (mkPartialChain cfg.T cfg.P G0 sc0 bran0 (G0 (i.val + 1))).activeLSF i.val =
          cfg.T.lsfs sc_i0 newBran := by
        simp [TreeChain.activeLSF, mkPartialChain, hi_lt, sc0, bran0]
      change Real.exp (-max 0 cfg.Ψ) ≤ coreLen _ _ e ∧
        coreLen _ _ e ≤ Real.exp (max 0 cfg.Ψ) * max 2 (cfg.TP.σ cfg.P.k cfg.N₀) ^ (i.val + 1)
      rw [hAct, hLCon]
      have hnonneg : ∀ f ∈ (ch.G i.val).E, 0 ≤ ch.toTreeChain.chainLen ch.ℓ i.val f :=
        fun f hf => (hiB.2.2.2.1 f hf).le
      have hw1 : 1 ≤ (cfg.T.lsfs sc_i0 newBran).wstr e :=
        le_trans (one_le_stretch hActiveNew.1.2.1.2.2.2.2 hnonneg heGi) (hActiveNew.1.2.2.2 e heGi).1
      have hwσ : (cfg.T.lsfs sc_i0 newBran).wstr e ≤ max 2 (cfg.TP.σ cfg.P.k cfg.N₀) :=
        le_trans (hActiveNew.1.2.2.2 e heGi).2
          (le_trans (hV.hTP.2.1 _ _ _ _ le_rfl hInv.hG0n) (le_max_right _ _))
      unfold coreLen
      exact (chainInv_levelLenRange hV.hTP hV.hγM₀ hV.hγk hInv hℓR i.val hi_lt.le).stretch_step
        heGi hw1 hwσ
    have hOrdNext : ∃ ρ : Rotation (G0 (i.val + 1)),
        ρ.order = chainLevelOrd cfg.T G0 sc0 bran0 (i.val + 1) := by
      have hOut := hSpecPost.2.2.2.2.1 H_i0.len H_i0.len (le_refl _) (le_refl _) newBran hnb_lt
        (Or.inr (by simp [restarts_i0'])) (fun _ h1 h2 => by omega)
      have hRot := rotation_of_orderedUpTo hOut (Nat.zero_le (H_i0.len - H_i0.len))
      refine exists_rotation_of_eq ?_ ?_ hRot
      · simp only [SparseCoreRestartTool.coreInstanceOrdFrom, Nat.add_zero, G0, ↓reduceIte, Gnext]
        rw [← hRunRestart]
      · simp only [Nat.add_zero, chainLevelOrd, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel, sc0, bran0]
        rw [← hRunRestart]
    have hRS := rebuildSuffix_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hLP hVNH.hT hV.hL
      hV.hγM₀ hV.hγk ch.ℓ ch.g (cfg.P.d - (i.val + 1)) (i.val + 1)
      G0 sc0 bran0 ch.updCount cEnc0 cDec0 ch.curFwd
      (by omega) (by simpa [G0] using hGnext_v) (by simpa [G0] using hGnext_V)
      (by simp only [G0, show (0 : ℕ) ≠ i.val + 1 by omega, ↓reduceIte]; exact hInv.hG0n)
      (by simpa [G0] using hGnext_m) hℓ_next hOrdNext
    set res := rebuildSuffix cfg.T cfg.L cfg.P ch.lvlM ch.N₀ ch.ℓ ch.g (cfg.P.d - (i.val + 1)) (i.val + 1)
      G0 sc0 bran0 ch.updCount cEnc0 cDec0 ch.curFwd
    have hResEq : res = rebuildSuffix cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ ch.ℓ ch.g
        (cfg.P.d - (i.val + 1)) (i.val + 1) G0 sc0 bran0 ch.updCount cEnc0 cDec0 ch.curFwd := by
      dsimp only [res]; rw [hInv.hLvlM, hInv.hN0]
    rw [← hResEq] at hRS
    have hch_eq : ch' =
        { ch with
          G := res.1, scState := res.2.1,
          curRestarts := fun j =>
            if j = i.val then ch.curRestarts i.val + 1
            else if i.val + 1 ≤ j ∧ j < cfg.P.d then 0
            else ch.curRestarts j,
          bran := res.2.2.1, updCount := res.2.2.2.1,
          curFwd := res.2.2.2.2.2.2.1,
          lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
          shiftCount := fun j => if j = i.val then ch.shiftCount i.val + 1 else ch.shiftCount j,
          closedRuntime := ch.closedRuntime +
            ((Finset.Ico (i.val + 1) cfg.P.d).sum fun j => cfg.T.cost (ch.scState j) + ch.curEnc j) +
            ch.curLastCost,
          curLastRebuilds := 0, curLastCost := res.2.2.2.2.2.2.2.2,
          curEnc := res.2.2.2.2.1,
          closedTreeUpdates := ch.closedTreeUpdates +
            ((Finset.Ico i.val cfg.P.d).sum fun j => ch.curDecUpdates j) +
            ch.curLastTreeUpdates +
            (diffTreeChanges ch.toTreeChain.chainTree.E
              ({ ch with
                  G := res.1, scState := res.2.1, bran := res.2.2.1,
                  lastK := res.2.2.2.2.2.2.2.1.1,
                  lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0 } :
                ChainState cfg.T cfg.P).toTreeChain.chainTree.E).length,
          curDecUpdates := res.2.2.2.2.2.1, curLastTreeUpdates := 0 } := by
      rw [hCh'_def]; simp [algorithm1_shift, hi_lt, res, G0, sc0, bran0, cDec0, cEnc0, newBran, sc_i0, Gnext]
      simp [ChainState.toTreeChain]
    have hchG : ch'.G = res.1 := by rw [hch_eq]
    have hchSc : ch'.scState = res.2.1 := by rw [hch_eq]
    have hchCRest : ch'.curRestarts = fun j =>
        if j = i.val then ch.curRestarts i.val + 1
        else if i.val + 1 ≤ j ∧ j < cfg.P.d then 0
        else ch.curRestarts j := by rw [hch_eq]
    have hchBran : ch'.bran = res.2.2.1 := by rw [hch_eq]
    have hchUpd : ch'.updCount = res.2.2.2.1 := by rw [hch_eq]
    have hchCEnc : ch'.curEnc = res.2.2.2.2.1 := by rw [hch_eq]
    have hchCDec : ch'.curDecUpdates = res.2.2.2.2.2.1 := by rw [hch_eq]
    have hchCFwd : ch'.curFwd = res.2.2.2.2.2.2.1 := by rw [hch_eq]
    have hChCon : ∀ k ≤ cfg.P.d,
        ch'.toTreeChain.chainLen ch'.ℓ k =
          (mkPartialChain cfg.T cfg.P res.1 res.2.1 res.2.2.1 (res.1 cfg.P.d)).chainLen ch.ℓ k ∧
        ch'.toTreeChain.chainGrad ch'.g k =
          (mkPartialChain cfg.T cfg.P res.1 res.2.1 res.2.2.1 (res.1 cfg.P.d)).chainGrad ch.g k := by
      intro k hk
      refine ⟨?_, ?_⟩
      · rw [hch_ℓ]
        exact chainLen_congr_params rfl ch.ℓ hk
          (fun j _ => congrFun hchG j)
          (fun j hj => by
            have hjd := lt_of_lt_of_le hj hk
            simp [ChainState.toTreeChain, hchSc, hchBran])
      · rw [hch_g]
        exact chainGrad_congr_params rfl ch.g hk
          (fun j _ => congrFun hchG j)
          (fun j hj => by
            have hjd := lt_of_lt_of_le hj hk
            simp [ChainState.toTreeChain, hchSc, hchBran])
    have hOrdLe : ∀ k ≤ i.val, ch'.levelOrd k = ch.levelOrd k := by
      intro k hki
      unfold ChainState.levelOrd chainLevelOrd
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte, hchG, hRS.1 0 (Nat.zero_le _), G0, show (0 : ℕ) ≠ i.val + 1 by omega]
      · have hkm : k - 1 < i.val := by omega
        have hkm1 : k - 1 < i.val + 1 := by omega
        simp only [hk0, ↓reduceIte, hchSc, hchBran, (hRS.2.1 (k - 1) hkm1).1,
          (hRS.2.1 (k - 1) hkm1).2.1, sc0, bran0, Nat.ne_of_lt hkm]
    let H' : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch' k := fun k hk =>
      if hki : k ≤ i.val then
        have hk_i1 : k < i.val + 1 := Nat.lt_succ_of_le hki
        have hpre := hRS.2.1 k hk_i1
        levelHistory_of_shift_le hk hki (H k hk)
          (fun j hj => by rw [congrFun hchG j, hRS.1 j (by omega)]; simp [G0, show j ≠ i.val + 1 by omega])
          (by
            by_cases heq : k = i.val
            · subst heq
              simp only [↓reduceIte, hchSc, hpre.1, hchBran, hpre.2.1]
              simp [sc0, bran0, newBran, sc_i0]
            · simp only [heq, ↓reduceIte, hchSc, hpre.1, sc0])
          (fun j hj => by
            have hjl := lt_trans hj hk
            simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjl, ↓reduceIte]
            have hjp := hRS.2.1 j (lt_trans hj hk_i1)
            rw [hchSc, hchBran, hjp.1, hjp.2.1]; simp [sc0, bran0, show j ≠ i.val by omega])
          (hOrdLe k hki)
          hℓ' hg'
          (by rw [hchUpd]; exact hpre.2.2.1)
          (by rw [hchCFwd]; exact hpre.2.2.2.2.2)
          (hInv.hRecFwd k hk).1
          (by
            rw [hchBran, hpre.2.1]
            by_cases heq : k = i.val
            · subst heq; simp [bran0, newBran, hnb_lt]
            · simp [bran0, heq, hInv.hBran k hk])
          (fun hlt => by rw [hchBran, hpre.2.1]; simp [bran0, Nat.ne_of_lt hlt])
          (fun heq => by rw [hchCDec, hpre.2.2.2.2.1]; simp [cDec0, heq])
          (fun hlt => by rw [hchCDec, hpre.2.2.2.2.1]; simp [cDec0, Nat.ne_of_lt hlt])
          (by
            rw [hchCRest]
            by_cases heq : k = i.val
            · subst heq; simp
            · have hnot : ¬ (i.val + 1 ≤ k ∧ k < cfg.P.d) := by omega
              simp only [heq, hnot, ↓reduceIte])
          (fun h0 => by rw [hchCEnc, (hRS.2.1 0 (Nat.zero_lt_succ _)).2.2.2.1]; simp [cEnc0])
          (fun h1 hle => by
            have hne : k + 1 ≠ i.val + 1 := by omega
            rw [hchCEnc, (hRS.2.1 (k + 1) (Nat.lt_succ_of_le hle)).2.2.2.1]
            simp only [cEnc0, hne, ↓reduceIte])
          (fun h1 hgt => by rw [hchCEnc]; exact (hRS.2.2.1 (k + 1) (by omega) h1).2.2.1)
      else
        have hik : i.val + 1 ≤ k := by omega
        have hsuf := hRS.2.2.1 k hik hk
        zeroLevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch' k hk hV.hTP
          (by rw [hchG]; exact hsuf.2.2.2.2.2.1)
          (by rw [hchG]; exact hsuf.2.2.2.2.2.2.2.1)
          (by
            unfold MGraph.n
            rw [hchG]
            exact le_trans (Finset.card_le_card hsuf.2.2.2.2.2.2.1) (by rw [← hchG]; exact hInv'.hG0n))
          (fun e he => by rw [(hChCon k hk.le).1]; rw [hchG] at he; exact hsuf.2.2.2.2.2.2.2.2.1 e he)
          (exists_rotation_levelOrd_of_inv hInv' hk)
          (by
            unfold ChainState.levelOrd
            rw [hchSc, hchG, hchBran, (hChCon k hk.le).1, (hChCon k hk.le).2]
            exact hsuf.2.2.2.2.2.2.2.2.2.1)
          (by rw [hchUpd]; exact hsuf.2.1)
          (by rw [hchCFwd]; exact hsuf.2.2.2.2.1)
          (by rw [hchCDec]; exact hsuf.2.2.2.1)
          (by rw [hchCRest]; simp [show k ≠ i.val by omega, hik, hk])
          (fun h0 => by omega)
          (fun h1 => by rw [hchCEnc]; exact (hRS.2.2.1 (k + 1) (by omega) h1).2.2.1)
          (by rw [hchG, (hChCon k hk.le).1]; exact hsuf.2.2.2.2.2.2.2.2.2.2.2)
    refine ⟨⟨H', fun k hk hki => ?_, fun k hk hik => ?_, fun k hki hk => ?_, fun b hb => ?_,
      fun _ => ?_, fun k hik hk => ?_, fun k hk1 hik => ?_, fun k hk hki s hs => ?_⟩⟩
    · refine ⟨by simp [H', hki, levelHistory_of_shift_le],
        by simp [H', hki, levelHistory_of_shift_le],
        by simp [H', hki, levelHistory_of_shift_le], fun hlt => ?_⟩
      simp [H', hki, levelHistory_of_shift_le, Nat.ne_of_lt hlt]
    · have : ¬ k ≤ i.val := by omega
      simp [H', this, zeroLevelHistory]
    · rw [hchG, hchSc]
      refine ⟨by rw [hRS.1 k (by omega)]; simp [G0, show k ≠ i.val + 1 by omega],
        fun hlt => by rw [(hRS.2.1 k (Nat.lt_succ_of_le hki)).1]; simp [sc0, Nat.ne_of_lt hlt],
        fun j hj => ?_⟩
      rw [(hRS.2.1 k (Nat.lt_succ_of_le hki)).1]
      by_cases heq : k = i.val
      · subst heq; simp only [sc0, ↓reduceIte]; exact hLsf_i0_eq j hj
      · simp [sc0, heq]
    · rw [hchBran, (hRS.2.1 b (by omega)).2.1]; simp [bran0, Nat.ne_of_lt hb]
    · rw [hchBran, (hRS.2.1 i.val (Nat.lt_succ_self _)).2.1]; simp [bran0, newBran]
    · unfold ChainState.levelOrd
      rw [hchBran, hchSc, hchG]
      have hsuf := hRS.2.2.1 k hik hk
      refine ⟨hsuf.1, ?_⟩
      rw [(hChCon k hk.le).1, (hChCon k hk.le).2]
      exact hsuf.2.2.2.2.2.2.2.2.2.1
    · rcases eq_or_lt_of_le (show i.val ≤ k by omega) with rfl | hlt
      · rw [hchG, hchSc, hchBran, hRS.1 (i.val + 1) (le_refl _),
          (hRS.2.1 i.val (Nat.lt_succ_self _)).1, (hRS.2.1 i.val (Nat.lt_succ_self _)).2.1]
        simp [G0, sc0, bran0, Gnext, newBran]
      · rw [hchG, hchSc, hchBran]
        have hsuf := hRS.2.2.1 k hlt (Nat.lt_of_succ_lt hk1)
        rw [hsuf.1]; exact hsuf.2.2.2.2.2.2.2.2.2.2.1
    · simp [H', hki, levelHistory_of_shift_le, Nat.ne_of_lt hs]
  · have hi_eq : i.val = cfg.P.d := by omega
    have hsh_eq : ch' = { ch with
        lastBran := (ch.lastBran + 1) % ch.lastK
        shiftCount := fun j => if j = cfg.P.d then ch.shiftCount cfg.P.d + 1 else ch.shiftCount j
        closedTreeUpdates := ch.closedTreeUpdates +
          (diffTreeChanges ch.toTreeChain.chainTree.E
            ({ ch with
                lastBran := (ch.lastBran + 1) % ch.lastK
                shiftCount := fun j =>
                  if j = cfg.P.d then ch.shiftCount cfg.P.d + 1 else ch.shiftCount j } :
              ChainState cfg.T cfg.P).toTreeChain.chainTree.E).length } := by
      rw [hCh'_def]; simp [algorithm1_shift, hi_lt]
    refine ⟨⟨fun k hk => { H k hk with
        restarts := (H k hk).restarts
        hRestartsLt := (H k hk).hRestartsLt
        hRestartsCount := by rw [hsh_eq]; exact (H k hk).hRestartsCount
        hS0Fresh := by rw [hsh_eq]; exact (H k hk).hS0Fresh
        hNoRestartAfterS0 := by rw [hsh_eq]; exact (H k hk).hNoRestartAfterS0
        hEndG := by rw [hsh_eq]; exact (H k hk).hEndG
        hEndℓ := fun e he => by
          have hCL := chainLen_congr_lt (C₁ := ch'.toTreeChain) (C₂ := ch.toTreeChain) ch.ℓ k
            (fun j _ => by rw [hsh_eq]; rfl) (fun j hj => by
              have hjd := lt_trans hj hk
              simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjd, ↓reduceIte]
              rw [hsh_eq])
          rw [hch_ℓ, hCL]; exact (H k hk).hEndℓ e (by rw [hsh_eq] at he; exact he)
        hEndg := by
          have hCG := chainGrad_congr_lt (C₁ := ch'.toTreeChain) (C₂ := ch.toTreeChain) ch.g k
            (fun j _ => by rw [hsh_eq]; rfl) (fun j hj => by
              have hjd := lt_trans hj hk
              simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjd, ↓reduceIte]
              rw [hsh_eq])
          rw [hch_g, hCG]; exact (H k hk).hEndg
        hUpd := by rw [hsh_eq]; exact (H k hk).hUpd
        hThresh := by rw [hsh_eq]; exact (H k hk).hThresh
        hInitMBound := (H k hk).hInitMBound
        hInitNBound := (H k hk).hInitNBound
        ord := (H k hk).ord
        hOrd := (H k hk).hOrd
        hEndOrd := by rw [hsh_eq]; exact (H k hk).hEndOrd
        hRun := by rw [hsh_eq]; exact (H k hk).hRun
        branchSeq := (H k hk).branchSeq
        hBranch := (H k hk).hBranch
        hBranchTail := by rw [hsh_eq]; exact (H k hk).hBranchTail
        hWinFwdBound := (H k hk).hWinFwdBound
        hCurFwdEq := by rw [hsh_eq]; exact (H k hk).hCurFwdEq
        hDecEq := by rw [hsh_eq]; exact (H k hk).hDecEq
        hEnc0Le := fun h0 => by rw [hsh_eq]; exact (H k hk).hEnc0Le h0
        hEncLe := fun h1 => by rw [hsh_eq]; exact (H k hk).hEncLe h1 },
      fun _ _ _ => ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩, fun k _ hik => by omega,
      fun k _ _ => ⟨by rw [hsh_eq], fun _ => by rw [hsh_eq], fun _ _ => by rw [hsh_eq]⟩,
      fun b _ => by rw [hsh_eq],
      fun h => absurd h hi_lt, fun k hik _ => by omega, fun k _ hik => by omega,
      fun _ _ _ _ _ => rfl⟩⟩

end MinCostFlow.Chain.Ordered
