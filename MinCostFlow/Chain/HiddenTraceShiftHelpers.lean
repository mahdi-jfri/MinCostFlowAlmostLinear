module

public import MinCostFlow.Chain.HiddenTraceSteps

/-!
# Hidden Trace Shift Structural Helper

Split from `MinCostFlow.Chain.HiddenTraceShift`: constructs the shifted
`LevelHistory` family `H'` and active chain structural facts (`hShiftStruct`)
for `alg2HiddenTrace_shiftAt`.
-/

@[expose] public section

namespace MinCostFlow.Chain

lemma alg2HiddenTrace_shiftStruct_aux
    (cfg : Alg2Config) (hV : cfg.Valid) (hVNH : cfg.ValidNoHidden)
    (ch ch' : ChainState cfg.T cfg.P) (i : Fin (cfg.P.d + 1))
    (hCh'_def : ch' = (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hInv' : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch')
    (H : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch k)
    (hℓ' : ch'.ℓ = ch.ℓ)
    (hg' : ch'.g = ch.g) :
    Nonempty (Σ' (H' : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ ch' k),
  (∀ k (hk : k < cfg.P.d), k ≤ i.val →
    (H' k hk).D = (H k hk).D ∧ (H' k hk).len = (H k hk).len ∧
    (k < i.val → (H' k hk).restarts = (H k hk).restarts ∧ (H' k hk).s₀ = (H k hk).s₀)) ∧
  (∀ k (hk : k < cfg.P.d), i.val < k → (H' k hk).len = 0) ∧
  (∀ k ≤ i.val, k < cfg.P.d →
    ch'.G k = ch.G k ∧ (k < i.val → ch'.scState k = ch.scState k) ∧
    (∀ j < cfg.P.k, cfg.T.lsfs (ch'.scState k) j = cfg.T.lsfs (ch.scState k) j)) ∧
  (∀ b < i.val, ch'.bran b = ch.bran b) ∧
  (i.val < cfg.P.d → ch'.bran i.val = (ch.bran i.val + 1) % cfg.P.k) ∧
  (∀ k, i.val < k → k < cfg.P.d →
    ch'.bran k = 0 ∧
    ch'.scState k = cfg.T.init cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (ch'.G k)
      (ch'.toTreeChain.chainLen ch'.ℓ k)
      (ch'.toTreeChain.chainGrad ch'.g k)) ∧
  (∀ k (_hk : k + 1 < cfg.P.d), i.val < k + 1 →
    ch'.G (k + 1) = cfg.T.S (ch'.scState k) (ch'.bran k)) ∧
  (∀ k (hk : k < cfg.P.d), k ≤ i.val → ∀ s < (H k hk).len,
    (H' k hk).restarts s = (H k hk).restarts s)) := by
  have hch_ℓ : ch'.ℓ = ch.ℓ := hℓ'
  have hch_g : ch'.g = ch.g := hg'
  by_cases hi_lt : i.val < cfg.P.d
  · have hB := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hVNH.hT hV.hγM₀ hV.hγk hInv
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
        cfg.T.runAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D restarts_i0' s =
          cfg.T.runAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.restarts s := by
      intro s hs
      exact cfg.T.runAfterUpdate_congr_lt cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ s rfl rfl rfl
        (fun _ _ _ => ⟨rfl, rfl, rfl⟩)
        (fun r hr => by simp [restarts_i0', show r ≠ H_i0.len by omega])
    have hRunRestart : sc_i0 =
        cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D restarts_i0' H_i0.len := by
      change cfg.T.restart (ch.scState i.val) newBran =
        (restarts_i0' H_i0.len).foldl cfg.T.restart
          (cfg.T.runAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D restarts_i0' H_i0.len).1
      rw [hRunPre_i0 H_i0.len (le_refl _)]
      simp only [restarts_i0', ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [H_i0.hRun]; rfl
    have hSpecPost := hVNH.hT cfg.P.k H_i0.len (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D restarts_i0'
      cfg.P.hk H_i0.hG0 H_i0.hD H_i0.hLen H_i0.hℓPos H_i0.hInitMBound H_i0.hInitNBound
      hRestLt_i0' (by rw [H_i0.hUpd]; exact H_i0.hThresh)
    have hAtPost := hSpecPost.1 H_i0.len (le_refl _) newBran hnb_lt
    dsimp only at hAtPost
    rw [← hRunRestart, H_i0.hEndG] at hAtPost
    have hLsf_i0_eq : ∀ b < cfg.P.k, cfg.T.lsfs sc_i0 b = cfg.T.lsfs (ch.scState i.val) b := by
      have hBranch := hSpecPost.2.2.1 H_i0.len (le_refl _) (H_i0.restarts H_i0.len) newBran
        (by simp [restarts_i0'])
      dsimp only at hBranch
      rw [hRunPre_i0 H_i0.len (le_refl _)] at hBranch
      have hPostSt : (H_i0.restarts H_i0.len).foldl cfg.T.restart
            (cfg.T.runAfterUpdate cfg.P.k (levelM cfg.TP cfg.P i.val) cfg.N₀ H_i0.D H_i0.restarts H_i0.len).1 =
          ch.scState i.val := by
        simpa [SparseCoreRestartTool.runAfterRestarts] using H_i0.hRun.symm
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
    have hℓ_next : ∀ e ∈ (G0 (i.val + 1)).E,
        0 < (mkPartialChain cfg.T cfg.P G0 sc0 bran0 (G0 (i.val + 1))).chainLen
          ch.ℓ (i.val + 1) e := fun e he => by
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
      change 0 < coreLen _ _ e
      rw [hAct, hLCon]
      have hnonneg : ∀ f ∈ (ch.G i.val).E, 0 ≤ ch.toTreeChain.chainLen ch.ℓ i.val f :=
        fun f hf => (hiB.2.2.2.1 f hf).le
      have hw1 : 1 ≤ (cfg.T.lsfs sc_i0 newBran).wstr e :=
        le_trans (one_le_stretch hActiveNew.1.2.1.2.2.2.2 hnonneg heGi) (hActiveNew.1.2.2.2 e heGi).1
      unfold coreLen
      exact mul_pos (lt_of_lt_of_le zero_lt_one hw1) (hiB.2.2.2.1 e heGi)
    have hRS := rebuildSuffix_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hLP hVNH.hT hV.hL
      hV.hγM₀ hV.hγk ch.ℓ ch.g (cfg.P.d - (i.val + 1)) (i.val + 1)
      G0 sc0 bran0 ch.updCount cEnc0 cDec0 ch.curFwd
      (by omega) (by simpa [G0] using hGnext_v) (by simpa [G0] using hGnext_V)
      (by simp only [G0, show (0 : ℕ) ≠ i.val + 1 by omega, ↓reduceIte]; exact hInv.hG0n)
      (by simpa [G0] using hGnext_m) hℓ_next
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
          (by rw [hchSc, hchG, (hChCon k hk.le).1, (hChCon k hk.le).2]; exact hsuf.2.2.2.2.2.2.2.2.2.1)
          (by rw [hchUpd]; exact hsuf.2.1)
          (by rw [hchCFwd]; exact hsuf.2.2.2.2.1)
          (by rw [hchCDec]; exact hsuf.2.2.2.1)
          (by rw [hchCRest]; simp [show k ≠ i.val by omega, hik, hk])
          (fun h0 => by omega)
          (fun h1 => by rw [hchCEnc]; exact (hRS.2.2.1 (k + 1) (by omega) h1).2.2.1)
    refine ⟨⟨H', fun k hk hki => ?_, fun k hk hik => ?_, fun k hki hk => ?_, fun b hb => ?_,
      fun _ => ?_, fun k hik hk => ?_, fun k hk1 hik => ?_, fun k hk hki s hs => ?_⟩⟩
    · refine ⟨by simp [H', hki, levelHistory_of_shift_le],
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
    · rw [hchBran, hchSc, hchG]
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
        rw [hsuf.1]; exact hsuf.2.2.2.2.2.2.2.2.2.2
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
        hRun := by rw [hsh_eq]; exact (H k hk).hRun
        branchSeq := (H k hk).branchSeq
        hBranch := (H k hk).hBranch
        hBranchTail := by rw [hsh_eq]; exact (H k hk).hBranchTail
        hWinFwdBound := (H k hk).hWinFwdBound
        hCurFwdEq := by rw [hsh_eq]; exact (H k hk).hCurFwdEq
        hDecEq := by rw [hsh_eq]; exact (H k hk).hDecEq
        hEnc0Le := fun h0 => by rw [hsh_eq]; exact (H k hk).hEnc0Le h0
        hEncLe := fun h1 => by rw [hsh_eq]; exact (H k hk).hEncLe h1 },
      fun _ _ _ => ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩, fun k _ hik => by omega,
      fun k _ _ => ⟨by rw [hsh_eq], fun _ => by rw [hsh_eq], fun _ _ => by rw [hsh_eq]⟩,
      fun b _ => by rw [hsh_eq],
      fun h => absurd h hi_lt, fun k hik _ => by omega, fun k _ hik => by omega,
      fun _ _ _ _ _ => rfl⟩⟩

end MinCostFlow.Chain
