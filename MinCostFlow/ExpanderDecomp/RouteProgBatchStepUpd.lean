module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchStepSp

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Routing Step — Update & Compaction Stage (`RouteProgBatchStepUpd`)

Verifies Phases D–F of one iteration of `batchRouteLoopStmt`: appends any non-empty path chunk,
marks matched endpoints in `matchAStamp` and clears them in `pairB`, compacts `aData`, updates
`aLen[i]`, and increments `i`, restoring `BatchRouteInv` and `BatchRouteRegs`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma batch_upd_r_ne {r : ℕ} (hr : r ≤ 20 ∨ r = 30 ∨ r = 31 ∨ r = 32) :
    r ≠ 29 ∧ r ≠ 25 ∧ r ≠ 26 ∧ r ≠ 27 ∧ r ≠ 28 ∧ r ≠ 24 ∧ r ≠ 23 ∧ r ≠ 22 ∧ r ≠ 21 := by omega

private lemma batchRouteStep_upd_F {w : ℕ} {p : Program}
    {X A ML M_acc : Finset ℕ} {cfg : BatchCfg} {i aOff_i aLen_i : ℕ} {stE : State}
    (hAX : A ⊆ X) (hM_disj_A : Disjoint M_acc A) (haLen_eq : aLen_i = A.card)
    (hdisj_ad_ma : DisjRange (cfg.aDataAddr + aOff_i) A.card (wsMatchAStamp cfg.ws cfg.nX) X.card)
    (hdisj_al_ad : DisjRange cfg.aLenAddr cfg.k cfg.aDataAddr cfg.nX)
    (hi_k : cfg.aLenAddr ≤ cfg.aLenAddr + i ∧ cfg.aLenAddr + i < cfg.aLenAddr + cfg.k)
    (hba_sub : cfg.aDataAddr ≤ cfg.aDataAddr + aOff_i ∧ cfg.aDataAddr + aOff_i + A.card ≤ cfg.aDataAddr + cfg.nX)
    (hw_ao : cfg.aOffAddr + i < 2 ^ w) (hw_al : cfg.aLenAddr + i < 2 ^ w)
    (hw_ad : cfg.aDataAddr + aOff_i + A.card + 5 < 2 ^ w)
    (hw_ma : wsMatchAStamp cfg.ws cfg.nX + X.card + 5 < 2 ^ w)
    (hw_bgen : cfg.batchGenIn + 5 < 2 ^ w) (hw_i : i + 1 < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hstE_ao : stE.mem (cfg.aOffAddr + i) = aOff_i)
    (hstE_al : stE.mem (cfg.aLenAddr + i) = aLen_i)
    (hlistA : ListAt stE.mem (cfg.aDataAddr + aOff_i) ((A.sort (· ≤ ·)).map (locOf X)))
    (hma_stE : ∀ v < X.card, stE.mem (wsMatchAStamp cfg.ws cfg.nX + v) = cfg.batchGenIn + 1 ↔
      origOf X v ∈ M_acc ∪ ML)
    (hr9E : stE.regs 9 = cfg.aOffAddr) (hr10E : stE.regs 10 = cfg.aLenAddr)
    (hr11E : stE.regs 11 = cfg.aDataAddr) (hr16E : stE.regs 16 = wsMatchAStamp cfg.ws cfg.nX)
    (hr17E : stE.regs 17 = cfg.batchGenIn + 1) (hr29E : stE.regs 29 = i) :
    ∀ ω, ∃ st1 cF,
      Runs w p ω
        (seqStmts
          ([ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
           , .assign 24 (.load (.bin .add (.reg 10) (.reg 29))) ] ++
           [batchCompactAStmt] ++
           [ .store (.bin .add (.reg 10) (.reg 29)) (.reg 25)
           , .assign 29 (.bin .add (.reg 29) (.const 1)) ]))
        stE .normal st1 cF ∧
      (∀ r, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 →
        st1.regs r = stE.regs r) ∧
      st1.regs 29 = i + 1 ∧
      st1.mem (cfg.aLenAddr + i) = (A \ ML).card ∧
      ListAt st1.mem (cfg.aDataAddr + aOff_i) (((A \ ML).sort (· ≤ ·)).map (locOf X)) ∧
      (∀ a, a ≠ cfg.aLenAddr + i →
        ¬ (cfg.aDataAddr + aOff_i ≤ a ∧ a < cfg.aDataAddr + aOff_i + A.card) →
        st1.mem a = stE.mem a) ∧
      cF ≤ 45 * A.card + 70 := by
  intro ω
  set aBase := cfg.aDataAddr + aOff_i
  set stF1 : State :=
    { mem := stE.mem, regs := Function.update (Function.update stE.regs 23 aBase) 24 aLen_i, pos := stE.pos }
  have hrunF1 : ∃ cF1,
      Runs w p ω
        (seqStmts
          [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
          , .assign 24 (.load (.bin .add (.reg 10) (.reg 29))) ])
        stE .normal stF1 cF1 ∧ cF1 ≤ 20 := by
    have h0' : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29))))
            , .assign 24 (.load (.bin .add (.reg 10) (.reg 29))) ])
          stE o s c ∧ (o = .normal ∧ s = stF1) ∧ 0 + c ≤ 20 := by
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := aBase)
        (by simp [Expr.eval, BinOp.eval, hr11E, hr9E, hr29E, hw_ao, hstE_ao,
              show cfg.aDataAddr + aOff_i < 2 ^ w by omega, aBase]) ?_
      refine runs_assign_le (v := aLen_i)
        (by simp [Expr.eval, BinOp.eval, hr10E, hr29E, hw_al, hstE_al])
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, cF1, h, ⟨rfl, rfl⟩, hcF1⟩; exact ⟨cF1, h, by omega⟩
  rcases hrunF1 with ⟨cF1, hrunF1, hcF1⟩
  obtain ⟨stF2, cF2, hrunF2, hregsF2, hr25F2, hlistF2, hfrF2, hcF2⟩ :=
    batchCompactA_triple (w := w) (p := p) (X := X)
      (matchAStampAddr := wsMatchAStamp cfg.ws cfg.nX)
      (batchGen := cfg.batchGenIn + 1) (base := aBase)
      (l := (A.sort (· ≤ ·)).map (locOf X)) (M := M_acc ∪ ML)
      (fun v hv => by
        rw [List.mem_map] at hv; rcases hv with ⟨u, hu, rfl⟩
        exact locOf_lt (hAX ((Finset.mem_sort (· ≤ ·)).mp hu)))
      (by simpa [List.length_map, Finset.length_sort] using hdisj_ad_ma)
      (by simp only [List.length_map, Finset.length_sort]; omega)
      hw_ma (by omega) hw4 (st0 := stF1) hlistA hma_stE
      (by simp [stF1, hr16E]) (by simp [stF1, hr17E])
      (by simp [stF1]) (by simp [stF1, haLen_eq]) ω
  have hAM_eq : A \ (M_acc ∪ ML) = A \ ML := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
    exact ⟨fun ⟨hx, hn⟩ => ⟨hx, fun h => hn (Or.inr h)⟩,
           fun ⟨hx, hml⟩ => ⟨hx, fun h => h.elim (fun hm => Finset.disjoint_left.mp hM_disj_A hm hx) hml⟩⟩
  have hfilt_eq : ((A.sort (· ≤ ·)).map (locOf X)).filter (fun v => decide (origOf X v ∉ M_acc ∪ ML)) =
      (((A \ ML).sort (· ≤ ·)).map (locOf X)) := by
    rw [← sort_sdiff_map_locOf hAX, hAM_eq]
  have hr25F2_eq : stF2.regs 25 = (A \ ML).card := by
    rw [hr25F2, hfilt_eq, List.length_map, Finset.length_sort]
  set st1 : State :=
    { mem := Function.update stF2.mem (cfg.aLenAddr + i) (A \ ML).card
      regs := Function.update stF2.regs 29 (i + 1)
      pos := stF2.pos }
  have hr10F2 : stF2.regs 10 = cfg.aLenAddr := by
    rw [hregsF2 10 (by decide) (by decide) (by decide) (by decide)]; simp [stF1, hr10E]
  have hr29F2 : stF2.regs 29 = i := by
    rw [hregsF2 29 (by decide) (by decide) (by decide) (by decide)]; simp [stF1, hr29E]
  have hrunF3 : ∃ cF3,
      Runs w p ω
        (seqStmts
          [ .store (.bin .add (.reg 10) (.reg 29)) (.reg 25)
          , .assign 29 (.bin .add (.reg 29) (.const 1)) ])
        stF2 .normal st1 cF3 ∧ cF3 ≤ 20 := by
    have h0' : ∃ o s c,
        Runs w p ω
          (seqStmts
            [ .store (.bin .add (.reg 10) (.reg 29)) (.reg 25)
            , .assign 29 (.bin .add (.reg 29) (.const 1)) ])
          stF2 o s c ∧ (o = .normal ∧ s = st1) ∧ 0 + c ≤ 20 := by
      dsimp only [seqStmts]
      refine runs_seq_store_le (x := cfg.aLenAddr + i) (v := (A \ ML).card)
        (by simp [Expr.eval, BinOp.eval, hr10F2, hr29F2, hw_al])
        (by simp [Expr.eval, hr25F2_eq]) ?_
      refine runs_assign_le (v := i + 1)
        (by simp [Expr.eval, BinOp.eval, hr29F2, show 1 < 2 ^ w by omega, hw_i])
        ⟨rfl, rfl⟩ (by wram_cost)
    rcases h0' with ⟨_, _, cF3, h, ⟨rfl, rfl⟩, hcF3⟩; exact ⟨cF3, h, by omega⟩
  rcases hrunF3 with ⟨cF3, hrunF3, hcF3⟩
  obtain ⟨c1, hr1, hc1⟩ := batch_runs_seqStmts_append (by simp) (by simp) hrunF1
    (show Runs w p ω (seqStmts [batchCompactAStmt]) stF1 .normal stF2 cF2 from hrunF2)
  obtain ⟨cF, hrunF, hcF⟩ := batch_runs_seqStmts_append (by simp) (by simp) hr1 hrunF3
  refine ⟨st1, cF, hrunF, fun r h23 h24 h25 h26 h27 h28 h29 => ?_, by simp [st1], by simp [st1], ?_, ?_, ?_⟩
  · simp only [st1, Function.update_of_ne h29]; rw [hregsF2 r h25 h26 h27 h28]
    simp only [stF1, Function.update_of_ne h24, Function.update_of_ne h23]
  · intro idx hidx
    have hidx_lt : idx < (A \ ML).card := by simpa using hidx
    have hle_A : (A \ ML).card ≤ A.card := Finset.card_le_card Finset.sdiff_subset
    have hne := disj_ne_l hdisj_al_ad (x := aBase + idx) (by omega) (by omega) hi_k.1 hi_k.2
    have hlistF2' : ListAt stF2.mem aBase (((A \ ML).sort (· ≤ ·)).map (locOf X)) := by
      rwa [hfilt_eq] at hlistF2
    change Function.update stF2.mem (cfg.aLenAddr + i) (A \ ML).card (aBase + idx) = _
    rw [Function.update_of_ne hne]; exact hlistF2' idx hidx
  · intro a hal had; simp only [st1, Function.update_of_ne hal]
    exact hfrF2 a (by simpa [List.length_map, Finset.length_sort] using had)
  · simp only [List.length_map, Finset.length_sort] at hcF2; simp at hc1 hcF; omega

private lemma batchRouteStep_upd_D {w : ℕ} {p : Program}
    {X : Finset ℕ} {cfg : BatchCfg} {cfgAddr pLo pHi cLo cHi hL k i pathHeap1 chunkHeap spHead : ℕ}
    {accCur : ℕ → List (List ((ℕ × ℕ) × List ℕ))} {newPs : List ((ℕ × ℕ) × List ℕ)} {stC : State}
    (hk : cfg.k = k) (hi_lt : i < k)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hhp_lo : pLo ≤ pathHeap1) (hhp_le : pathHeap1 ≤ pHi) (hch_lo : cLo ≤ chunkHeap)
    (hch1_le : (if newPs = [] then chunkHeap else chunkHeap + 2) ≤ cHi)
    (hch_C : ∀ j < k,
      ChunkChainAt stC.mem X pLo pathHeap1 cLo chunkHeap
        (stC.mem (cfg.accHeadAddr + j)) (stC.mem (cfg.accTailAddr + j)) (accCur j))
    (hchDisj_C : ChunksDisj stC.mem cfg.accHeadAddr k (fun j => (accCur j).length))
    (hspPathList : PathListAt stC.mem X pLo pathHeap1 spHead newPs)
    (hr12C : stC.regs 12 = cfg.accHeadAddr) (hr13C : stC.regs 13 = cfg.accTailAddr)
    (hr21C : stC.regs 21 = chunkHeap) (hr22C : stC.regs 22 = spHead)
    (hr25C : stC.regs 25 = newPs.length) (hr29C : stC.regs 29 = i) :
    ∀ ω,
      let chunkHeap1 := if newPs = [] then chunkHeap else chunkHeap + 2
      let accCur1 : ℕ → List (List ((ℕ × ℕ) × List ℕ)) := fun j =>
        if j = i then (if newPs = [] then accCur i else accCur i ++ [newPs]) else accCur j
      ∃ stD cD,
        Runs w p ω batchAppendChunkStmt stC .normal stD cD ∧
        (∀ r, r ≠ 21 → r ≠ 26 → r ≠ 27 → stD.regs r = stC.regs r) ∧
        stD.regs 21 = chunkHeap1 ∧
        (∀ j < k,
          ChunkChainAt stD.mem X pLo pathHeap1 cLo chunkHeap1
            (stD.mem (cfg.accHeadAddr + j)) (stD.mem (cfg.accTailAddr + j)) (accCur1 j)) ∧
        ChunksDisj stD.mem cfg.accHeadAddr k (fun j => (accCur1 j).length) ∧
        (∀ a, ¬ (a = cfg.accHeadAddr + i ∨ a = cfg.accTailAddr + i ∨
                 (cLo ≤ a ∧ a < chunkHeap1)) → stD.mem a = stC.mem a) ∧
        cD ≤ 50 := by
  intro ω
  set chunkHeap1 := if newPs = [] then chunkHeap else chunkHeap + 2
  set accCur1 : ℕ → List (List ((ℕ × ℕ) × List ℕ)) := fun j =>
    if j = i then (if newPs = [] then accCur i else accCur i ++ [newPs]) else accCur j
  have hw4 := hdisj.w_4; have hw_ah := hdisj.w_ah; have hw_at := hdisj.w_at
  have hw_hp := hdisj.w_hp; have hw_ch := hdisj.w_ch
  have hp_sub : pLo + (pHi - pLo) = pHi := by have := hdisj.hp_lo; have := hdisj.hp_hi; omega
  have hc_sub : cLo + (cHi - cLo) = cHi := by have := hdisj.ch_lo; have := hdisj.ch_hi; omega
  by_cases hnil : newPs = []
  · have hcondD : (Expr.reg 25).eval w stC = some 0 := by simp [Expr.eval, hr25C, hnil]
    refine ⟨stC, _, runs_cond_iff.mpr ⟨0, 1, hcondD, by simp [runs_nop_iff], rfl⟩,
      fun _ _ _ _ => rfl, by rw [hr21C]; simp [chunkHeap1, hnil],
      fun j hj => by
        simp only [chunkHeap1, accCur1, hnil, ↓reduceIte]
        by_cases hji : j = i <;> simp [hji] <;> [subst hji; skip] <;> exact hch_C j hj,
      fun j1 hj1 j2 hj2 hne => by
        simp only [accCur1, hnil, ↓reduceIte]
        by_cases h1 : j1 = i <;> by_cases h2 : j2 = i <;> simp [h1, h2]
        · exact absurd (h1.trans h2.symm) hne
        · subst h1; exact hchDisj_C j1 hj1 j2 hj2 hne
        · subst h2; exact hchDisj_C j1 hj1 j2 hj2 hne
        · exact hchDisj_C j1 hj1 j2 hj2 hne,
      fun _ _ => rfl, by simp [Expr.size]⟩
  · have hch2_le_cHi : chunkHeap + 2 ≤ cHi := by simpa [chunkHeap1, hnil] using hch1_le
    have hah_at := hdisj.ah_at; have hah_ch := hdisj.ah_ch; have hat_ch := hdisj.at_ch
    have hah_hp := hdisj.ah_hp; have hat_hp := hdisj.at_hp; have hhp_ch := hdisj.hp_ch
    unfold DisjRange at hah_at hah_ch hat_ch hah_hp hat_hp hhp_ch
    obtain ⟨stD, cD, hrunD, hregsD, hr21D, hchD_i, hcaD_i, hfrD, hotherD, hchFrameD, hcD⟩ :=
      batchAppendChunk_triple (w := w) (p := p) (X := X) (k := k)
        (accHeadAddr := cfg.accHeadAddr) (accTailAddr := cfg.accTailAddr)
        (pLo := pLo) (pHi := pathHeap1) (cLo := cLo) (cHi := chunkHeap)
        (chunks := accCur i) (newPs := newPs) (spHead := spHead)
        hi_lt (by omega) hch_lo hdisj.ch_pos
        (by unfold DisjRange; omega)
        (by unfold DisjRange; rcases hah_ch with x | x <;> omega)
        (by unfold DisjRange; rcases hat_ch with x | x <;> omega)
        (by unfold DisjRange; rcases hah_hp with x | x <;> omega)
        (by unfold DisjRange; rcases hat_hp with x | x <;> omega)
        (by unfold DisjRange; rcases hhp_ch with x | x <;> omega)
        (by omega) (by omega) (by omega) (by omega) hw4
        (hch_C i hi_lt) hspPathList hr12C hr13C hr21C hr22C hr25C hr29C ω
    have hother_ch : ∀ j (hj : j < k), j ≠ i →
        ChunkChainAt stD.mem X pLo pathHeap1 cLo (chunkHeap + 2)
          (stD.mem (cfg.accHeadAddr + j)) (stD.mem (cfg.accTailAddr + j)) (accCur j) ∧
        chunkAddrs stD.mem (stD.mem (cfg.accHeadAddr + j)) (accCur j).length =
          chunkAddrs stC.mem (stC.mem (cfg.accHeadAddr + j)) (accCur j).length := by
      intro j hj hji
      have hht := hotherD j hj hji; rw [hht.1, hht.2]
      have hca := (hch_C j hj).congr_addrs (mem' := stD.mem)
        (fun a ha1 ha2 => hfrD a (by
          rcases hah_hp with x1 | x1 <;> rcases hat_hp with x2 | x2 <;>
            rcases hhp_ch with x3 | x3 <;> omega))
        (fun a ha => by
          have hab := (hch_C j hj).chunkAddrs_bounds a ha
          have hno_t : accCur i = [] ∨
              (a ≠ stC.mem (cfg.accTailAddr + i) + 1 ∧ a + 1 ≠ stC.mem (cfg.accTailAddr + i) + 1) := by
            by_cases hci_nil : accCur i = []
            · exact Or.inl hci_nil
            · right
              have htail_in := (hch_C i hi_lt).tail_mem_chunkAddrs hci_nil
              have hsep := hchDisj_C j hj i hi_lt hji a ha _ htail_in; omega
          exact ⟨hchFrameD a hab.1 (by omega) (hno_t.imp id And.left),
                 hchFrameD (a + 1) (by omega) (by omega) (hno_t.imp id And.right)⟩)
      exact ⟨hca.1.mono_cHi (by omega), hca.2⟩
    refine ⟨stD, cD, hrunD, hregsD, by simpa [chunkHeap1, hnil] using hr21D, ?_, ?_, ?_, hcD⟩
    · intro j hj; simp only [chunkHeap1, accCur1, hnil, ↓reduceIte]
      by_cases hji : j = i
      · subst hji; simp only [↓reduceIte]; simpa [hnil] using hchD_i
      · simp only [hji, ↓reduceIte]; exact (hother_ch j hj hji).1
    · intro j1 hj1 j2 hj2 hne a ha b hb
      simp only [accCur1, hnil, ↓reduceIte] at ha hb
      by_cases h1 : j1 = i
      · subst h1
        have h2 : j2 ≠ j1 := Ne.symm hne
        simp only [↓reduceIte, h2] at ha hb
        have hca1 : chunkAddrs stD.mem (stD.mem (cfg.accHeadAddr + j1)) (accCur j1 ++ [newPs]).length =
            chunkAddrs stC.mem (stC.mem (cfg.accHeadAddr + j1)) (accCur j1).length ++ [chunkHeap] := by
          simpa [hnil] using hcaD_i
        rw [hca1, List.mem_append, List.mem_singleton] at ha; rw [(hother_ch j2 hj2 h2).2] at hb
        rcases ha with ha_old | rfl
        · exact hchDisj_C j1 hj1 j2 hj2 hne a ha_old b hb
        · have hbb := (hch_C j2 hj2).chunkAddrs_bounds b hb; omega
      · by_cases h2 : j2 = i
        · subst h2; simp only [h1, ↓reduceIte] at ha hb
          have hca2 : chunkAddrs stD.mem (stD.mem (cfg.accHeadAddr + j2)) (accCur j2 ++ [newPs]).length =
              chunkAddrs stC.mem (stC.mem (cfg.accHeadAddr + j2)) (accCur j2).length ++ [chunkHeap] := by
            simpa [hnil] using hcaD_i
          rw [hca2, List.mem_append, List.mem_singleton] at hb; rw [(hother_ch j1 hj1 h1).2] at ha
          rcases hb with hb_old | rfl
          · exact hchDisj_C j1 hj1 j2 hj2 hne a ha b hb_old
          · have hab := (hch_C j1 hj1).chunkAddrs_bounds a ha; omega
        · simp only [h1, h2, ↓reduceIte] at ha hb
          rw [(hother_ch j1 hj1 h1).2] at ha; rw [(hother_ch j2 hj2 h2).2] at hb
          exact hchDisj_C j1 hj1 j2 hj2 hne a ha b hb
    · intro a ha; apply hfrD a; simpa [chunkHeap1, hnil] using ha

private lemma batchRouteStep_upd_inv {w : ℕ} {G : Graph} {X : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL i bfsGen dfsGen pathHeap chunkHeap routed pathHeap1 bfsGen1 dfsGen1 : ℕ}
    {pairs curPairs : List (Finset ℕ × Finset ℕ)} {V M_acc A B remVerts ML MR : Finset ℕ}
    {spPaths : List ((ℕ × ℕ) × List ℕ)} {accCur : ℕ → List (List ((ℕ × ℕ) × List ℕ))}
    {mem0 memS0 memC memD memE mem1 : ℕ → ℕ}
    (hnX : cfg.nX = X.card) (hk : cfg.k = pairs.length) (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hi_lt : i < pairs.length) (hinv_len : curPairs.length = pairs.length) (hcur_i : curPairs[i]'(by omega) = (A, B))
    (hinv : BatchRouteInv memS0 mem0 G X cfg cfgAddr pLo pHi cLo cHi hL
      pairs curPairs i V M_acc accCur bfsGen dfsGen pathHeap chunkHeap routed)
    (hdem_drop : totalDemand (pairs.drop i) = A.card + totalDemand (pairs.drop (i + 1)))
    (hsp_sub : remVerts ⊆ V) (hAX : A ⊆ X) (hML_sub : ML ⊆ A) (hMR_sub : MR ⊆ B)
    (hML_card : ML.card = spPaths.length) (hMR_card : MR.card = spPaths.length)
    (hspHeap_lo : pathHeap ≤ pathHeap1) (hspHeap_hi : pathHeap1 ≤ pathHeap + 5 * (V \ remVerts).card)
    (hspBfs_lo : bfsGen ≤ bfsGen1) (hspBfs_hi : bfsGen1 ≤ bfsGen + cfg.d + 1)
    (hspDfs_lo : dfsGen ≤ dfsGen1) (hspDfs_hi : dfsGen1 ≤ dfsGen + cfg.d + 1)
    (hspMask_ok : ∀ v < X.card, memC (wsIsoStamp cfg.ws + v) ≠ cfg.batchGenIn + 1 ↔ origOf X v ∈ remVerts)
    (hspMask_le : ∀ v < X.card, memC (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1)
    (hspVis_le : ∀ v < X.card, memC (wsVisStamp cfg.ws cfg.nX + v) ≤ bfsGen1)
    (hspCur_le : ∀ v < X.card, memC (wsCurStamp cfg.ws cfg.nX + v) ≤ dfsGen1)
    (hspUsed_le : ∀ v < X.card, memC (wsUsedStamp cfg.ws cfg.nX + v) ≤ dfsGen1)
    (hspDead_le : ∀ v < X.card, memC (wsDeadStamp cfg.ws cfg.nX + v) ≤ dfsGen1)
    (hball_C : ∀ v < X.card, memC (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) = memS0 (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v))
    (hlive_C : ∀ v < X.card, memC (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) = memS0 (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v))
    (hsubC : BatchSubCfgsInit memC cfg hL)
    (hstC_fr : ∀ a, ¬ ((cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) ∨ (pathHeap ≤ a ∧ a < pathHeap + 10 * cfg.nX)) → memC a = memS0 a)
    (hch1_le_cHi : (if spPaths = [] then chunkHeap else chunkHeap + 2) ≤ cHi)
    (hchD : ∀ j < pairs.length, ChunkChainAt memD X pLo pathHeap1 cLo (if spPaths = [] then chunkHeap else chunkHeap + 2) (memD (cfg.accHeadAddr + j)) (memD (cfg.accTailAddr + j)) (if j = i then (if spPaths = [] then accCur i else accCur i ++ [spPaths]) else accCur j))
    (hchDisjD : ChunksDisj memD cfg.accHeadAddr pairs.length (fun j => (if j = i then (if spPaths = [] then accCur i else accCur i ++ [spPaths]) else accCur j).length))
    (hfrD : ∀ a, ¬ (a = cfg.accHeadAddr + i ∨ a = cfg.accTailAddr + i ∨ (cLo ≤ a ∧ a < if spPaths = [] then chunkHeap else chunkHeap + 2)) → memD a = memC a)
    (hpbE : ∀ v < X.card, memE (cfg.pairBAddr + v) = if origOf X v ∈ MR then 0 else memD (cfg.pairBAddr + v))
    (hfrE : ∀ a, ¬ ((wsMatchAStamp cfg.ws cfg.nX ≤ a ∧ a < wsMatchAStamp cfg.ws cfg.nX + X.card) ∨ (cfg.pairBAddr ≤ a ∧ a < cfg.pairBAddr + X.card)) → memE a = memD a)
    (hma_stE : ∀ v < X.card, memE (wsMatchAStamp cfg.ws cfg.nX + v) = cfg.batchGenIn + 1 ↔ origOf X v ∈ M_acc ∪ ML)
    (hma_le_stE : ∀ v < X.card, memE (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn + 1)
    (hal_i1 : mem1 (cfg.aLenAddr + i) = (A \ ML).card)
    (hlist_1 : ListAt mem1 (cfg.aDataAddr + memS0 (cfg.aOffAddr + i)) (((A \ ML).sort (· ≤ ·)).map (locOf X)))
    (hst1_eq_stE : ∀ a, a ≠ cfg.aLenAddr + i → ¬ (cfg.aDataAddr + memS0 (cfg.aOffAddr + i) ≤ a ∧ a < cfg.aDataAddr + memS0 (cfg.aOffAddr + i) + A.card) → mem1 a = memE a)
    (hba_sub : cfg.aDataAddr ≤ cfg.aDataAddr + memS0 (cfg.aOffAddr + i) ∧ cfg.aDataAddr + memS0 (cfg.aOffAddr + i) + A.card ≤ cfg.aDataAddr + cfg.nX)
    (hhp_sub : pLo ≤ pathHeap ∧ pathHeap + 10 * cfg.nX ≤ pLo + (pHi - pLo)) (hspHeap_le_pHi : pathHeap1 ≤ pHi) :
    BatchRouteInv mem1 mem0 G X cfg cfgAddr pLo pHi cLo cHi hL
      pairs (curPairs.set i (A \ ML, B \ MR)) (i + 1) remVerts (M_acc ∪ ML)
      (fun j => if j = i then (if spPaths = [] then accCur i else accCur i ++ [spPaths]) else accCur j)
      bfsGen1 dfsGen1 pathHeap1 (if spPaths = [] then chunkHeap else chunkHeap + 2) (routed + spPaths.length) := by
  have hi_cur : i < curPairs.length := by omega
  have hsp_len_le_A : spPaths.length ≤ A.card := by rw [← hML_card]; exact Finset.card_le_card hML_sub
  set chunkHeap1 := if spPaths = [] then chunkHeap else chunkHeap + 2
  set accCur1 : ℕ → List (List ((ℕ × ℕ) × List ℕ)) := fun j =>
    if j = i then (if spPaths = [] then accCur i else accCur i ++ [spPaths]) else accCur j
  set aBase := cfg.aDataAddr + memS0 (cfg.aOffAddr + i)
  have hp_sub : pLo + (pHi - pLo) = pHi := by have := hdisj.hp_lo; have := hdisj.hp_hi; omega
  have hc_sub : cLo + (cHi - cLo) = cHi := by have := hdisj.ch_lo; have := hdisj.ch_hi; omega
  have hch_sub : cLo ≤ cLo ∧ chunkHeap1 ≤ cLo + (cHi - cLo) := by omega
  have hi_k : cfg.aLenAddr ≤ cfg.aLenAddr + i ∧ cfg.aLenAddr + i < cfg.aLenAddr + cfg.k := by omega
  have hi_ah : cfg.accHeadAddr ≤ cfg.accHeadAddr + i ∧ cfg.accHeadAddr + i < cfg.accHeadAddr + cfg.k := by omega
  have hi_at : cfg.accTailAddr ≤ cfg.accTailAddr + i ∧ cfg.accTailAddr + i < cfg.accTailAddr + cfg.k := by omega
  have hma_ws := ws_ma_sub cfg.ws cfg.nX cfg.m2 cfg.k
  have hst1_eq_stC : ∀ a, a ≠ cfg.aLenAddr + i → ¬ (aBase ≤ a ∧ a < aBase + A.card) →
      ¬ (wsMatchAStamp cfg.ws cfg.nX ≤ a ∧ a < wsMatchAStamp cfg.ws cfg.nX + X.card) →
      ¬ (cfg.pairBAddr ≤ a ∧ a < cfg.pairBAddr + X.card) →
      a ≠ cfg.accHeadAddr + i → a ≠ cfg.accTailAddr + i →
      ¬ (cLo ≤ a ∧ a < chunkHeap1) → mem1 a = memC a :=
    fun a hal had hma hpb hah hat hch => by
      rw [hst1_eq_stE a hal had, hfrE a (fun h => h.elim hma hpb),
          hfrD a (fun h => h.elim hah (fun h => h.elim hat hch))]
  have hst1_eq_st0_of : ∀ a, a ≠ cfg.aLenAddr + i →
      ¬ (cfg.aDataAddr ≤ a ∧ a < cfg.aDataAddr + cfg.nX) →
      ¬ (cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) →
      ¬ (cfg.pairBAddr ≤ a ∧ a < cfg.pairBAddr + cfg.nX) →
      a ≠ cfg.accHeadAddr + i → a ≠ cfg.accTailAddr + i →
      ¬ (cLo ≤ a ∧ a < cLo + (cHi - cLo)) → ¬ (pLo ≤ a ∧ a < pLo + (pHi - pLo)) →
      mem1 a = memS0 a := fun a hal had hws hpb hah hat hch hhp =>
    (hst1_eq_stC a hal (sub_not_in hba_sub.1 hba_sub.2 had)
      (sub_not_in hma_ws.1 (by rw [← hnX]; exact hma_ws.2) hws) (by rw [← hnX]; exact hpb)
      hah hat (sub_not_in hch_sub.1 hch_sub.2 hch)).trans
      (hstC_fr a (fun h => h.elim hws (sub_not_in hhp_sub.1 hhp_sub.2 hhp)))
  have hws_nonma : ∀ a, cfg.ws ≤ a → a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k →
      (a < wsMatchAStamp cfg.ws cfg.nX ∨ wsMatchAStamp cfg.ws cfg.nX + X.card ≤ a) →
      mem1 a = memC a := fun a ha1 ha2 hnot_ma =>
    hst1_eq_stC a (disj_ne_l hdisj.al_ws ha1 ha2 hi_k.1 hi_k.2)
      (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_ws ha1 ha2))
      (fun h => hnot_ma.elim (fun h1 => by omega) (fun h2 => by omega))
      (by rw [← hnX]; exact disj_l hdisj.pb_ws ha1 ha2)
      (disj_ne_l hdisj.ah_ws ha1 ha2 hi_ah.1 hi_ah.2)
      (disj_ne_l hdisj.at_ws ha1 ha2 hi_at.1 hi_at.2)
      (sub_not_in hch_sub.1 hch_sub.2 (disj_r hdisj.ws_ch ha1 ha2))
  have hws_nonma' : ∀ a, cfg.ws ≤ a → a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k →
      (a < wsMatchAStamp cfg.ws cfg.nX ∨ wsMatchAStamp cfg.ws cfg.nX + cfg.nX ≤ a) →
      mem1 a = memC a := by simpa [hnX] using hws_nonma
  have hm_ah_D : ∀ j < pairs.length, mem1 (cfg.accHeadAddr + j) = memD (cfg.accHeadAddr + j) := fun j hj =>
    have h1 : cfg.accHeadAddr ≤ cfg.accHeadAddr + j := Nat.le_add_right _ _
    have h2 : cfg.accHeadAddr + j < cfg.accHeadAddr + cfg.k := by omega
    (hst1_eq_stE _ (disj_ne_l hdisj.al_ah h1 h2 hi_k.1 hi_k.2)
      (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_ah h1 h2))).trans
      (hfrE _ (fun h => h.elim (sub_not_in hma_ws.1 (by omega) (disj_r hdisj.ah_ws h1 h2))
        (by rw [← hnX]; exact disj_l hdisj.pb_ah h1 h2)))
  have hhp_D : ∀ a, pLo ≤ a → a < pathHeap1 → mem1 a = memD a := fun a ha1 ha2 =>
    have hp2 : a < pLo + (pHi - pLo) := by omega
    (hst1_eq_stE a (disj_ne_l hdisj.al_hp ha1 hp2 hi_k.1 hi_k.2)
      (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_hp ha1 hp2))).trans
      (hfrE a (fun h => h.elim (sub_not_in hma_ws.1 (by omega) (disj_l hdisj.ws_hp ha1 hp2))
        (by rw [← hnX]; exact disj_l hdisj.pb_hp ha1 hp2)))
  have hch_D : ∀ a, cLo ≤ a → a < chunkHeap1 → mem1 a = memD a := fun a ha1 ha2 =>
    have hc2 : a < cLo + (cHi - cLo) := by omega
    (hst1_eq_stE a (disj_ne_l hdisj.al_ch ha1 hc2 hi_k.1 hi_k.2)
      (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_ch ha1 hc2))).trans
      (hfrE a (fun h => h.elim (sub_not_in hma_ws.1 (by omega) (disj_l hdisj.ws_ch ha1 hc2))
        (by rw [← hnX]; exact disj_l hdisj.pb_ch ha1 hc2)))
  refine
    { cur_len := by simp [hinv_len]
      cur_drop := by
        rw [show (curPairs.set i (A \ ML, B \ MR)).drop (i + 1) = curPairs.drop (i + 1) from by
          apply List.ext_getElem (by simp)
          intro j h1 h2; simp only [List.getElem_drop, List.getElem_set_ne (by omega : i ≠ i + 1 + j)]]
        have h1 := congrArg List.tail hinv.cur_drop; simpa [List.tail_drop] using h1
      cur_valid := by
        have h := validTerminalPairs_set_sdiff hinv.cur_valid hi_cur (ML := ML) (MR := MR)
          (by rwa [hcur_i]) (by rwa [hcur_i]) (by omega)
        simpa [hcur_i] using h
      V_sub := Finset.Subset.trans hsp_sub hinv.V_sub
      M_sub := Finset.union_subset hinv.M_sub (Finset.Subset.trans hML_sub hAX)
      M_disj := fun j hij hjk => by
        have hjk' : j < curPairs.length := by simpa using hjk
        have hne : i ≠ j := by omega
        rw [show (curPairs.set i (A \ ML, B \ MR))[j]'hjk = curPairs[j]'hjk' from by simp [List.getElem_set_ne hne]]
        refine Finset.disjoint_union_left.mpr ⟨hinv.M_disj j (by omega) hjk', ?_⟩
        have hpw := (List.pairwise_iff_getElem.mp (routeTerminalPairs_of_validTerminalPairs hinv.cur_valid).2) i j hi_cur hjk' (by omega)
        rw [hcur_i] at hpw
        exact Disjoint.mono (Finset.Subset.trans hML_sub Finset.subset_union_left) Finset.subset_union_left hpw
      routed_le := by have := hinv.routed_le; omega
      bgen_lo := le_trans hinv.bgen_lo hspBfs_lo
      bgen_hi := by have := hinv.bgen_hi; rw [Nat.add_mul, Nat.one_mul]; omega
      dgen_lo := le_trans hinv.dgen_lo hspDfs_lo
      dgen_hi := by have := hinv.dgen_hi; rw [Nat.add_mul, Nat.one_mul]; omega
      php_lo := le_trans hinv.php_lo hspHeap_lo
      php_hi := by
        have hdj : Disjoint (X \ V) (V \ remVerts) := by
          rw [Finset.disjoint_left]; intro x h1 h2; exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
        have heq : X \ remVerts = (X \ V) ∪ (V \ remVerts) := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
          exact ⟨fun ⟨hxX, hns⟩ => if hxV : x ∈ V then Or.inr ⟨hxV, hns⟩ else Or.inl ⟨hxX, hxV⟩,
                 fun h => h.elim (fun ⟨hxX, hnV⟩ => ⟨hxX, fun h => hnV (hsp_sub h)⟩) (fun ⟨hxV, hns⟩ => ⟨hinv.V_sub hxV, hns⟩)⟩
        have hsplit : (X \ remVerts).card = (X \ V).card + (V \ remVerts).card := by
          rw [heq, Finset.card_union_of_disjoint hdj]
        have := hinv.php_hi; omega
      chp_lo := by simp only [chunkHeap1]; split_ifs <;> have := hinv.chp_lo <;> omega
      chp_hi := by
        simp only [chunkHeap1]; split_ifs with hnil
        · have := hinv.chp_hi; omega
        · have := List.length_pos_of_ne_nil hnil; have := hinv.chp_hi; omega
      csr := hinv.csr.congr
        (fun k hk =>
          have h1 : cfg.offAddr ≤ cfg.offAddr + k := Nat.le_add_right _ _
          have h2 : cfg.offAddr + k < cfg.offAddr + (cfg.nX + 1) := by omega
          hst1_eq_st0_of _ (disj_ne_r hdisj.ro_off_al h1 h2 hi_k.1 hi_k.2) (disj_r hdisj.ro_off_ad h1 h2)
            (disj_r hdisj.ro_off_ws h1 h2) (disj_r hdisj.ro_off_pb h1 h2) (disj_ne_r hdisj.ro_off_ah h1 h2 hi_ah.1 hi_ah.2)
            (disj_ne_r hdisj.ro_off_at h1 h2 hi_at.1 hi_at.2) (disj_r hdisj.ro_off_ch h1 h2) (disj_r hdisj.ro_off_hp h1 h2))
        (fun k hk =>
          have h1 : cfg.nbAddr ≤ cfg.nbAddr + k := Nat.le_add_right _ _
          have h2 : cfg.nbAddr + k < cfg.nbAddr + cfg.m2 := by omega
          hst1_eq_st0_of _ (disj_ne_r hdisj.ro_nb_al h1 h2 hi_k.1 hi_k.2) (disj_r hdisj.ro_nb_ad h1 h2)
            (disj_r hdisj.ro_nb_ws h1 h2) (disj_r hdisj.ro_nb_pb h1 h2) (disj_ne_r hdisj.ro_nb_ah h1 h2 hi_ah.1 hi_ah.2)
            (disj_ne_r hdisj.ro_nb_at h1 h2 hi_at.1 hi_at.2) (disj_r hdisj.ro_nb_ch h1 h2) (disj_r hdisj.ro_nb_hp h1 h2))
        (fun k hk =>
          have h1 : cfg.edgeAddr ≤ cfg.edgeAddr + k := Nat.le_add_right _ _
          have h2 : cfg.edgeAddr + k < cfg.edgeAddr + cfg.m2 := by omega
          hst1_eq_st0_of _ (disj_ne_r hdisj.ro_edge_al h1 h2 hi_k.1 hi_k.2) (disj_r hdisj.ro_edge_ad h1 h2)
            (disj_r hdisj.ro_edge_ws h1 h2) (disj_r hdisj.ro_edge_pb h1 h2) (disj_ne_r hdisj.ro_edge_ah h1 h2 hi_ah.1 hi_ah.2)
            (disj_ne_r hdisj.ro_edge_at h1 h2 hi_at.1 hi_at.2) (disj_r hdisj.ro_edge_ch h1 h2) (disj_r hdisj.ro_edge_hp h1 h2))
      lp := batchRouteStep_upd_lp hnX hi_cur hcur_i hinv.cur_valid hMR_sub hinv.lp
        (fun v hv => by
          have hp1 : cfg.pairBAddr ≤ cfg.pairBAddr + v := Nat.le_add_right _ _
          have hp2 : cfg.pairBAddr + v < cfg.pairBAddr + cfg.nX := by omega
          rw [hst1_eq_stE _ (disj_ne_r hdisj.pb_al hp1 hp2 hi_k.1 hi_k.2)
                (sub_not_in hba_sub.1 hba_sub.2 (disj_r hdisj.pb_ad hp1 hp2)),
              hpbE v hv,
              hfrD _ (fun h => h.elim (disj_ne_r hdisj.pb_ah hp1 hp2 hi_ah.1 hi_ah.2)
                (fun h => h.elim (disj_ne_r hdisj.pb_at hp1 hp2 hi_at.1 hi_at.2)
                  (sub_not_in hch_sub.1 hch_sub.2 (disj_r hdisj.pb_ch hp1 hp2)))),
              hstC_fr _ (fun h => h.elim (disj_r hdisj.pb_ws hp1 hp2)
                (sub_not_in hhp_sub.1 hhp_sub.2 (disj_r hdisj.pb_hp hp1 hp2)))])
        (fun u hu =>
          have h1 : cfg.aOffAddr ≤ cfg.aOffAddr + u := Nat.le_add_right _ _
          have h2 : cfg.aOffAddr + u < cfg.aOffAddr + (cfg.k + 1) := by omega
          hst1_eq_st0_of _ (disj_ne_r hdisj.ro_ao_al h1 h2 hi_k.1 hi_k.2) (disj_r hdisj.ro_ao_ad h1 h2)
            (disj_r hdisj.ro_ao_ws h1 h2) (disj_r hdisj.ro_ao_pb h1 h2) (disj_ne_r hdisj.ro_ao_ah h1 h2 hi_ah.1 hi_ah.2)
            (disj_ne_r hdisj.ro_ao_at h1 h2 hi_at.1 hi_at.2) (disj_r hdisj.ro_ao_ch h1 h2) (disj_r hdisj.ro_ao_hp h1 h2))
        hal_i1
        (fun j hj' hji =>
          have h1 : cfg.aLenAddr ≤ cfg.aLenAddr + j := Nat.le_add_right _ _
          have h2 : cfg.aLenAddr + j < cfg.aLenAddr + cfg.k := by omega
          hst1_eq_st0_of _ (by omega) (disj_r hdisj.al_ad h1 h2) (disj_r hdisj.al_ws h1 h2)
            (disj_l hdisj.pb_al h1 h2) (disj_ne_r hdisj.al_ah h1 h2 hi_ah.1 hi_ah.2)
            (disj_ne_r hdisj.al_at h1 h2 hi_at.1 hi_at.2) (disj_r hdisj.al_ch h1 h2) (disj_r hdisj.al_hp h1 h2))
        hlist_1
        (fun a h1 h2 hdisj_slice =>
          (hst1_eq_stC a (disj_ne_l hdisj.al_ad h1 h2 hi_k.1 hi_k.2) hdisj_slice
            (sub_not_in hma_ws.1 (by omega) (disj_r hdisj.ad_ws h1 h2)) (by rw [← hnX]; exact disj_l hdisj.pb_ad h1 h2)
            (disj_ne_r hdisj.ad_ah h1 h2 hi_ah.1 hi_ah.2) (disj_ne_r hdisj.ad_at h1 h2 hi_at.1 hi_at.2)
            (sub_not_in hch_sub.1 hch_sub.2 (disj_r hdisj.ad_ch h1 h2))).trans
            (hstC_fr a (fun h => h.elim (disj_r hdisj.ad_ws h1 h2) (sub_not_in hhp_sub.1 hhp_sub.2 (disj_r hdisj.ad_hp h1 h2)))))
      iso_ok := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).1]; exact hspMask_ok v hv
      iso_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).1]; exact hspMask_le v hv
      ma_ok := fun v hv => by
        rw [hst1_eq_stE _ (disj_ne_l hdisj.al_ws (x := wsMatchAStamp cfg.ws cfg.nX + v) (by omega) (by omega) hi_k.1 hi_k.2)
          (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_ws (x := wsMatchAStamp cfg.ws cfg.nX + v) (by omega) (by omega)))]; exact hma_stE v hv
      ma_le := fun v hv => by
        rw [hst1_eq_stE _ (disj_ne_l hdisj.al_ws (x := wsMatchAStamp cfg.ws cfg.nX + v) (by omega) (by omega) hi_k.1 hi_k.2)
          (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_ws (x := wsMatchAStamp cfg.ws cfg.nX + v) (by omega) (by omega)))]; exact hma_le_stE v hv
      vis_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).2.1]; exact hspVis_le v hv
      cur_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).2.2.1]; exact hspCur_le v hv
      used_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).2.2.2.1]; exact hspUsed_le v hv
      dead_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).2.2.2.2.1]; exact hspDead_le v hv
      ball_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).2.2.2.2.2.1, hball_C v hv]; exact hinv.ball_le v hv
      live_le := fun v hv => by rw [(ws_nonma_stamps hws_nonma' (by omega)).2.2.2.2.2.2, hlive_C v hv]; exact hinv.live_le v hv
      sub_init := hsubC.of_outside_124 (fun a ha1 ha2 =>
        hws_nonma a ha1 (by unfold batchScratchSize; omega) (Or.inl (by simp [wsMatchAStamp]; omega)))
      chunks := fun j hj => by
        have hat1 : cfg.accTailAddr ≤ cfg.accTailAddr + j := Nat.le_add_right _ _
        have hat2 : cfg.accTailAddr + j < cfg.accTailAddr + cfg.k := by omega
        have hm_at : mem1 (cfg.accTailAddr + j) = memD (cfg.accTailAddr + j) :=
          (hst1_eq_stE _ (disj_ne_l hdisj.al_at hat1 hat2 hi_k.1 hi_k.2)
            (sub_not_in hba_sub.1 hba_sub.2 (disj_l hdisj.ad_at hat1 hat2))).trans
            (hfrE _ (fun h => h.elim (sub_not_in hma_ws.1 (by omega) (disj_r hdisj.at_ws hat1 hat2))
              (by rw [← hnX]; exact disj_l hdisj.pb_at hat1 hat2)))
        rw [hm_ah_D j hj, hm_at]; exact (hchD j hj).congr hhp_D hch_D
      chunks_disj := by
        have hca_eq : ∀ j < pairs.length,
            chunkAddrs mem1 (mem1 (cfg.accHeadAddr + j)) (accCur1 j).length =
            chunkAddrs memD (memD (cfg.accHeadAddr + j)) (accCur1 j).length := fun j hj => by
          rw [hm_ah_D j hj]
          exact ((hchD j hj).congr_addrs hhp_D (fun a ha => by
            have hab := (hchD j hj).chunkAddrs_bounds a ha
            exact ⟨hch_D a hab.1 (by omega), hch_D (a + 1) (by omega) (by omega)⟩)).2
        intro j1 hj1 j2 hj2 hne a ha b hb
        rw [hca_eq j1 hj1] at ha; rw [hca_eq j2 hj2] at hb; exact hchDisjD j1 hj1 j2 hj2 hne a ha b hb
      frame := fun a ha => by
        have ha' := ha; simp only [BatchWriteSet, not_or] at ha'
        rcases ha' with ⟨hpb, hal, had, hah, hat, _, hws, hhp, hch⟩
        exact (hst1_eq_stC a (fun h => hal ⟨by omega, by omega⟩) (sub_not_in hba_sub.1 hba_sub.2 had)
          (sub_not_in hma_ws.1 (by omega) hws) (by rw [← hnX]; exact hpb)
          (fun h => hah ⟨by omega, by omega⟩) (fun h => hat ⟨by omega, by omega⟩)
          (fun h => hch ⟨h.1, lt_of_lt_of_le h.2 hch1_le_cHi⟩)).trans
          ((hstC_fr a (fun h => h.elim hws (fun h => hhp ⟨le_trans hinv.php_lo h.1, by omega⟩))).trans (hinv.frame a ha))
      cfg_ro := fun o ho =>
        have hc1 : cfgAddr ≤ cfgAddr + o := Nat.le_add_right _ _
        have hc2 : cfgAddr + o < cfgAddr + 26 := by omega
        (hst1_eq_st0_of _ (disj_ne_l hdisj.al_cfg hc1 hc2 hi_k.1 hi_k.2) (disj_l hdisj.ad_cfg hc1 hc2)
          (disj_r hdisj.cfg_ws hc1 hc2) (disj_l hdisj.pb_cfg hc1 hc2) (disj_ne_l hdisj.ah_cfg hc1 hc2 hi_ah.1 hi_ah.2)
          (disj_ne_l hdisj.at_cfg hc1 hc2 hi_at.1 hi_at.2) (disj_r hdisj.cfg_ch hc1 hc2) (disj_r hdisj.cfg_hp hc1 hc2)).trans (hinv.cfg_ro o ho) }

/-- Phases D–F of one iteration of `batchRouteLoopStmt`: append chunk, mark matched endpoints,
compact `aData`, update `aLen[i]`, and increment `i`, restoring `BatchRouteInv` and `BatchRouteRegs`. -/
lemma batchRouteStep_upd {w : ℕ} {p : Program}
    {G : Graph} {X : Finset ℕ} {cfg : BatchCfg}
    {cfgAddr pLo pHi cLo cHi hL : ℕ} {pairs curPairs : List (Finset ℕ × Finset ℕ)}
    {i : ℕ} {V M_acc A B : Finset ℕ}
    {accCur : ℕ → List (List ((ℕ × ℕ) × List ℕ))}
    {bfsGen dfsGen pathHeap chunkHeap routed spHead pathHeap1 bfsGen1 dfsGen1 : ℕ}
    {mem0 : ℕ → ℕ} {st0 stC : State}
    (hnX : cfg.nX = X.card) (hk : cfg.k = pairs.length)
    (hm2 : adjCsrOff X (adjOf G X) X.card ≤ cfg.m2)
    (hdisj : BatchDisj w cfgAddr pLo pHi cLo cHi hL cfg)
    (hi_lt : i < pairs.length) (hinv_len : curPairs.length = pairs.length)
    (hcur_i : curPairs[i]'(by omega) = (A, B))
    (hinv : BatchRouteInv st0.mem mem0 G X cfg cfgAddr pLo pHi cLo cHi hL
      pairs curPairs i V M_acc accCur bfsGen dfsGen pathHeap chunkHeap routed)
    (hregs : BatchRouteRegs st0.regs cfg cfgAddr bfsGen dfsGen pathHeap chunkHeap i routed)
    (hdem_drop : totalDemand (pairs.drop i) = A.card + totalDemand (pairs.drop (i + 1)))
    (hregsC_eq : ∀ r, r ≤ 17 ∨ r = 21 ∨ r = 29 ∨ r = 31 ∨ r = 32 → stC.regs r = st0.regs r)
    (hC18 : stC.regs 18 = bfsGen1) (hC19 : stC.regs 19 = dfsGen1)
    (hC20 : stC.regs 20 = pathHeap1) (hC22 : stC.regs 22 = spHead)
    (hC25 : stC.regs 25 = (shortPathBlock (adjOf G X) V A B cfg.d).paths.length)
    (hC30 : stC.regs 30 = routed + (shortPathBlock (adjOf G X) V A B cfg.d).paths.length)
    (hspHeap_lo : pathHeap ≤ pathHeap1)
    (hspHeap_hi : pathHeap1 ≤ pathHeap + 5 * (V \ (shortPathBlock (adjOf G X) V A B cfg.d).remVerts).card)
    (hspBfs_lo : bfsGen ≤ bfsGen1) (hspBfs_hi : bfsGen1 ≤ bfsGen + cfg.d + 1)
    (hspDfs_lo : dfsGen ≤ dfsGen1) (hspDfs_hi : dfsGen1 ≤ dfsGen + cfg.d + 1)
    (hspPathList : PathListAt stC.mem X pLo pathHeap1 spHead (shortPathBlock (adjOf G X) V A B cfg.d).paths)
    (hspMask_ok : ∀ v < X.card, stC.mem (wsIsoStamp cfg.ws + v) ≠ cfg.batchGenIn + 1 ↔
      origOf X v ∈ (shortPathBlock (adjOf G X) V A B cfg.d).remVerts)
    (hspMask_le : ∀ v < X.card, stC.mem (wsIsoStamp cfg.ws + v) ≤ cfg.batchGenIn + 1)
    (hma_C : ∀ v < X.card, stC.mem (wsMatchAStamp cfg.ws cfg.nX + v) = st0.mem (wsMatchAStamp cfg.ws cfg.nX + v))
    (hspVis_le : ∀ v < X.card, stC.mem (wsVisStamp cfg.ws cfg.nX + v) ≤ bfsGen1)
    (hspCur_le : ∀ v < X.card, stC.mem (wsCurStamp cfg.ws cfg.nX + v) ≤ dfsGen1)
    (hspUsed_le : ∀ v < X.card, stC.mem (wsUsedStamp cfg.ws cfg.nX + v) ≤ dfsGen1)
    (hspDead_le : ∀ v < X.card, stC.mem (wsDeadStamp cfg.ws cfg.nX + v) ≤ dfsGen1)
    (hball_C : ∀ v < X.card, stC.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) =
      st0.mem (wsBallStamp cfg.ws cfg.nX cfg.m2 cfg.k + v))
    (hlive_C : ∀ v < X.card, stC.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v) =
      st0.mem (wsLiveStamp cfg.ws cfg.nX cfg.m2 cfg.k + v))
    (hsubC : BatchSubCfgsInit stC.mem cfg hL)
    (hch_C : ∀ j < pairs.length,
      ChunkChainAt stC.mem X pLo pathHeap1 cLo chunkHeap
        (stC.mem (cfg.accHeadAddr + j)) (stC.mem (cfg.accTailAddr + j)) (accCur j))
    (hchDisj_C : ChunksDisj stC.mem cfg.accHeadAddr pairs.length (fun j => (accCur j).length))
    (hstC_fr : ∀ a, ¬ ((cfg.ws ≤ a ∧ a < cfg.ws + batchScratchSize cfg.nX cfg.m2 cfg.k) ∨
                       (pathHeap ≤ a ∧ a < pathHeap + 10 * cfg.nX)) → stC.mem a = st0.mem a) :
    ∀ ω,
      let sp := shortPathBlock (adjOf G X) V A B cfg.d
      let ML := (sp.paths.map fun q => q.1.1).toFinset
      let MR := (sp.paths.map fun q => q.1.2).toFinset
      let chunkHeap1 := if sp.paths = [] then chunkHeap else chunkHeap + 2
      let accCur1 : ℕ → List (List ((ℕ × ℕ) × List ℕ)) := fun j =>
        if j = i then (if sp.paths = [] then accCur i else accCur i ++ [sp.paths]) else accCur j
      ∃ st1 cDF,
        Runs w p ω (seqStmts batchRouteStepUpdStmts) stC .normal st1 cDF ∧
        (∀ r, r ≤ 17 ∨ r = 31 ∨ r = 32 → st1.regs r = st0.regs r) ∧
        BatchRouteInv st1.mem mem0 G X cfg cfgAddr pLo pHi cLo cHi hL
          pairs (curPairs.set i (A \ ML, B \ MR)) (i + 1) sp.remVerts (M_acc ∪ ML) accCur1
          bfsGen1 dfsGen1 pathHeap1 chunkHeap1 (routed + sp.paths.length) ∧
        BatchRouteRegs st1.regs cfg cfgAddr bfsGen1 dfsGen1 pathHeap1 chunkHeap1
          (i + 1) (routed + sp.paths.length) ∧
        cDF ≤ 45 * A.card + 40 * sp.paths.length + 140 := by
  intro ω
  have hi_cur : i < curPairs.length := by omega
  have hvalid_i_sub : A ⊆ X ∧ B ⊆ X := by
    have := hinv.cur_valid.1 (curPairs[i]'hi_cur) (List.getElem_mem hi_cur)
    rw [hcur_i] at this; exact ⟨this.1, this.2.1⟩
  have hvalid_i_disj : Disjoint A B := by
    have := hinv.cur_valid.disjoint_pair (List.getElem_mem hi_cur)
    rwa [hcur_i] at this
  have hM_disj_A : Disjoint M_acc A := by
    have := hinv.M_disj i le_rfl hi_cur; rwa [hcur_i] at this
  set sp := shortPathBlock (adjOf G X) V A B cfg.d
  set ML := (sp.paths.map fun q => q.1.1).toFinset
  set MR := (sp.paths.map fun q => q.1.2).toFinset
  have hsp_sub : sp.remVerts ⊆ V := (shortPathBlockLoop_remVerts_sub _ _ _ _ _ _ _ _).1
  have hsp_ep := shortPathBlock_paths_endpoints_subset G hinv.V_sub A B hvalid_i_disj cfg.d
  have hML_sub : ML ⊆ A := by
    intro x hx; rw [List.mem_toFinset, List.mem_map] at hx
    rcases hx with ⟨q, hq, rfl⟩; exact (hsp_ep.1 q hq).1
  have hMR_sub : MR ⊆ B := by
    intro x hx; rw [List.mem_toFinset, List.mem_map] at hx
    rcases hx with ⟨q, hq, rfl⟩; exact (hsp_ep.1 q hq).2
  have hML_card : ML.card = sp.paths.length := hsp_ep.2.1
  have hMR_card : MR.card = sp.paths.length := hsp_ep.2.2.1
  have hsp_len_le_A : sp.paths.length ≤ A.card := by
    rw [← hML_card]; exact Finset.card_le_card hML_sub
  rcases hinv.lp with ⟨hlp_b, hlp_a⟩
  have ha_i := hlp_a.2 i hi_cur; dsimp only at ha_i; rw [hcur_i] at ha_i
  set aOff_i := st0.mem (cfg.aOffAddr + i)
  set aLen_i := st0.mem (cfg.aLenAddr + i)
  set aBase := cfg.aDataAddr + aOff_i
  have haLen_eq : aLen_i = A.card := ha_i.2.1
  have haOff_hi : aOff_i + aLen_i ≤ X.card := by
    have hmono := localAPairsAt_slot_bound hlp_a (i + 1) curPairs.length (by omega) le_rfl
    have h1 := ha_i.1
    rw [show cfg.aOffAddr + (i + 1) = cfg.aOffAddr + i + 1 by omega] at hmono
    have h2 := hlp_a.1
    omega
  rcases hregs with ⟨hr0, hr1, hr2, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16,
    hr17, hr18, hr19, hr20, hr21, hr29, hr30, hr31, hr32⟩
  have hw4 := hdisj.w_4; have hw_ws := hdisj.w_ws; have hw_ao := hdisj.w_ao; have hw_al := hdisj.w_al
  have hw_ad := hdisj.w_ad; have hw_ah := hdisj.w_ah; have hw_at := hdisj.w_at
  have hw_pb := hdisj.w_pb; have hw_hp := hdisj.w_hp; have hw_ch := hdisj.w_ch
  have hw_nX4 := hdisj.w_nX4; have hw_k := hdisj.w_k; have hw_bgen := hdisj.w_bgen
  have hhp_lo_pLo : pLo ≤ pathHeap := le_trans hdisj.hp_lo hinv.php_lo
  have hhp_le_pHi : pathHeap + 10 * cfg.nX ≤ pHi := by
    have h1 := hinv.php_hi; have h2 : (X \ V).card ≤ X.card := Finset.card_le_card Finset.sdiff_subset
    have h3 := hdisj.hp_hi; omega
  have hspHeap_le_pHi : pathHeap1 ≤ pHi := by
    have h1 : (V \ sp.remVerts).card ≤ X.card :=
      Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset hinv.V_sub)
    omega
  have hch_lo_cLo : cLo ≤ chunkHeap := le_trans hdisj.ch_lo hinv.chp_lo
  have hch_le_cHi : chunkHeap ≤ cHi := by
    have := hinv.chp_hi; have := hinv.routed_le; have := hdisj.ch_hi; omega
  have hp_sub : pLo + (pHi - pLo) = pHi := Nat.add_sub_cancel' (by omega)
  have hc_sub : cLo + (cHi - cLo) = cHi := Nat.add_sub_cancel' (by omega)
  set chunkHeap1 := if sp.paths = [] then chunkHeap else chunkHeap + 2
  set accCur1 : ℕ → List (List ((ℕ × ℕ) × List ℕ)) := fun j =>
    if j = i then (if sp.paths = [] then accCur i else accCur i ++ [sp.paths]) else accCur j
  have hch1_le_cHi : chunkHeap1 ≤ cHi := by
    simp only [chunkHeap1]; split_ifs with hnil
    · exact hch_le_cHi
    · have := List.length_pos_of_ne_nil hnil
      have := hinv.chp_hi; have := hinv.routed_le; have := hdisj.ch_hi; omega
  -- Phase D: batchAppendChunkStmt
  obtain ⟨stD, cD, hrunD, hregsD, hr21D, hchD, hchDisjD, hfrD, hcD⟩ :=
    batchRouteStep_upd_D (p := p) hk hi_lt hdisj (le_trans hhp_lo_pLo hspHeap_lo) hspHeap_le_pHi hch_lo_cLo hch1_le_cHi
      hch_C hchDisj_C hspPathList
      (by rw [hregsC_eq 12 (Or.inl (by decide)), hr12])
      (by rw [hregsC_eq 13 (Or.inl (by decide)), hr13])
      (by rw [hregsC_eq 21 (Or.inr (Or.inl rfl)), hr21])
      hC22 hC25 (by rw [hregsC_eq 29 (Or.inr (Or.inr (Or.inl rfl))), hr29]) ω
  -- Phase E: batchMarkMatchedStmt
  have hspPathList_D : PathListAt stD.mem X pLo pathHeap1 spHead sp.paths :=
    hspPathList.congr (fun a ha1 ha2 => hfrD a (by
      have h1 := hdisj.ah_hp; have h2 := hdisj.at_hp; have h3 := hdisj.hp_ch
      unfold DisjRange at h1 h2 h3
      rcases h1 with x1 | x1 <;> rcases h2 with x2 | x2 <;> rcases h3 with x3 | x3 <;> omega))
  obtain ⟨stE, cE, hrunE, hregsE, hmaE, hpbE, hfrE, hcE⟩ :=
    batchMarkMatched_triple (w := w) (p := p) (X := X)
      (pairBAddr := cfg.pairBAddr) (matchAStampAddr := wsMatchAStamp cfg.ws cfg.nX)
      (batchGen := cfg.batchGenIn + 1) (pLo := pLo) (pHi := pathHeap1)
      (by have h := hdisj.pb_ws; unfold DisjRange at h ⊢; unfold batchScratchSize at h; unfold wsMatchAStamp; rcases h with x | x <;> omega)
      (by have h := hdisj.pb_hp; unfold DisjRange at h ⊢; rcases h with x | x <;> omega)
      (by have h := hdisj.ws_hp; unfold DisjRange at h ⊢; unfold batchScratchSize at h; unfold wsMatchAStamp; rcases h with x | x <;> omega)
      (by omega) (by omega) (by simp [wsMatchAStamp]; unfold batchScratchSize at hw_ws; omega)
      (by omega) (by omega) hw4 sp.paths spHead stD hspPathList_D
      (by rw [hregsD 8 (by decide) (by decide) (by decide), hregsC_eq 8 (by omega), hr8])
      (by rw [hregsD 16 (by decide) (by decide) (by decide), hregsC_eq 16 (by omega), hr16])
      (by rw [hregsD 17 (by decide) (by decide) (by decide), hregsC_eq 17 (by omega), hr17])
      (by rw [hregsD 22 (by decide) (by decide) (by decide), hC22]) ω
  -- Phase F1: reload r23, r24
  have hstE_ao : stE.mem (cfg.aOffAddr + i) = aOff_i := by
    have h1 := hdisj.ro_ao_pb; have h2 := hdisj.ro_ao_ws; have h3 := hdisj.ro_ao_ah
    have h4 := hdisj.ro_ao_at; have h5 := hdisj.ro_ao_ch; have h6 := hdisj.ro_ao_hp
    simp only [DisjRange, batchScratchSize] at h1 h2 h3 h4 h5 h6
    rw [hfrE _ (by unfold wsMatchAStamp; rcases h1 with x | x <;> rcases h2 with y | y <;> omega),
        hfrD _ (by rcases h3 with x | x <;> rcases h4 with y | y <;> rcases h5 with z | z <;> omega),
        hstC_fr _ (by unfold batchScratchSize; rcases h2 with x | x <;> rcases h6 with y | y <;> omega)]
  have hstE_al : stE.mem (cfg.aLenAddr + i) = aLen_i := by
    have h1 := hdisj.pb_al; have h2 := hdisj.al_ws; have h3 := hdisj.al_ah
    have h4 := hdisj.al_at; have h5 := hdisj.al_ch; have h6 := hdisj.al_hp
    simp only [DisjRange, batchScratchSize] at h1 h2 h3 h4 h5 h6
    rw [hfrE _ (by unfold wsMatchAStamp; rcases h1 with x | x <;> rcases h2 with y | y <;> omega),
        hfrD _ (by rcases h3 with x | x <;> rcases h4 with y | y <;> rcases h5 with z | z <;> omega),
        hstC_fr _ (by unfold batchScratchSize; rcases h2 with x | x <;> rcases h6 with y | y <;> omega)]
  -- Phase F: reload r23, r24, compact A, store aLen[i], increment r29
  have hba_sub : cfg.aDataAddr ≤ aBase ∧ aBase + A.card ≤ cfg.aDataAddr + cfg.nX := by omega
  have hch_sub : cLo ≤ cLo ∧ chunkHeap1 ≤ cLo + (cHi - cLo) := by omega
  have hhp_sub : pLo ≤ pathHeap ∧ pathHeap + 10 * cfg.nX ≤ pLo + (pHi - pLo) := by
    have := hinv.php_lo; omega
  have hi_k : cfg.aLenAddr ≤ cfg.aLenAddr + i ∧ cfg.aLenAddr + i < cfg.aLenAddr + cfg.k := by omega
  have hi_ah : cfg.accHeadAddr ≤ cfg.accHeadAddr + i ∧ cfg.accHeadAddr + i < cfg.accHeadAddr + cfg.k := by omega
  have hi_at : cfg.accTailAddr ≤ cfg.accTailAddr + i ∧ cfg.accTailAddr + i < cfg.accTailAddr + cfg.k := by omega
  have hma_ws := ws_ma_sub cfg.ws cfg.nX cfg.m2 cfg.k
  set M_acc1 := M_acc ∪ ML
  have hmaD_eq : ∀ v < X.card, stD.mem (wsMatchAStamp cfg.ws cfg.nX + v) = st0.mem (wsMatchAStamp cfg.ws cfg.nX + v) := by
    intro v hv
    have h1 := hdisj.ah_ws; have h2 := hdisj.at_ws; have h3 := hdisj.ws_ch
    unfold DisjRange batchScratchSize at h1 h2 h3; unfold wsMatchAStamp
    rw [hfrD _ (by rcases h1 with x | x <;> rcases h2 with y | y <;> rcases h3 with z | z <;> omega)]
    exact hma_C v hv
  have hma_stE : ∀ v < X.card, stE.mem (wsMatchAStamp cfg.ws cfg.nX + v) = cfg.batchGenIn + 1 ↔
      origOf X v ∈ M_acc1 := by
    intro v hv; rw [hmaE v hv, hmaD_eq v hv, show (List.map (fun q => q.1.1) sp.paths).toFinset = ML from rfl]
    simp only [M_acc1, Finset.mem_union]
    by_cases hml : origOf X v ∈ ML
    · simp [hml]
    · simp only [hml, ↓reduceIte, or_false]; exact hinv.ma_ok v hv
  have hma_le_stE : ∀ v < X.card, stE.mem (wsMatchAStamp cfg.ws cfg.nX + v) ≤ cfg.batchGenIn + 1 := by
    intro v hv; rw [hmaE v hv]; split_ifs
    · exact le_rfl
    · rw [hmaD_eq v hv]; exact hinv.ma_le v hv
  have hlistA_stE : ListAt stE.mem aBase ((A.sort (· ≤ ·)).map (locOf X)) := by
    intro idx hidx
    have hidx_lt : idx < A.card := by simpa using hidx
    have ha1 : cfg.aDataAddr ≤ aBase + idx := by omega
    have ha2 : aBase + idx < cfg.aDataAddr + cfg.nX := by omega
    rw [hfrE _ (fun h => h.elim (sub_not_in hma_ws.1 (by omega) (disj_r hdisj.ad_ws ha1 ha2))
          (by rw [← hnX]; exact disj_l hdisj.pb_ad ha1 ha2)),
        hfrD _ (fun h => h.elim (disj_ne_r hdisj.ad_ah ha1 ha2 hi_ah.1 hi_ah.2)
          (fun h => h.elim (disj_ne_r hdisj.ad_at ha1 ha2 hi_at.1 hi_at.2)
            (sub_not_in hch_sub.1 hch_sub.2 (disj_r hdisj.ad_ch ha1 ha2)))),
        hstC_fr _ (fun h => h.elim (disj_r hdisj.ad_ws ha1 ha2)
          (sub_not_in hhp_sub.1 hhp_sub.2 (disj_r hdisj.ad_hp ha1 ha2)))]
    exact ha_i.2.2 idx hidx
  obtain ⟨st1, cF, hrunF, hregsF, hr29_1, hal_i1, hlist_1, hst1_eq_stE, hcF⟩ :=
    batchRouteStep_upd_F (p := p) hvalid_i_sub.1 hM_disj_A haLen_eq
      (by have h := hdisj.ad_ws; unfold DisjRange at h ⊢; unfold batchScratchSize at h; unfold wsMatchAStamp; rcases h with x | x <;> omega)
      hdisj.al_ad hi_k hba_sub (by omega) (by omega) (by omega)
      (by simp [wsMatchAStamp]; unfold batchScratchSize at hw_ws; omega)
      hw_bgen (by omega) hw4 hstE_ao hstE_al hlistA_stE hma_stE
      (by rw [hregsE 9 (by decide) (by decide) (by decide), hregsD 9 (by decide) (by decide) (by decide), hregsC_eq 9 (Or.inl (by decide)), hr9])
      (by rw [hregsE 10 (by decide) (by decide) (by decide), hregsD 10 (by decide) (by decide) (by decide), hregsC_eq 10 (Or.inl (by decide)), hr10])
      (by rw [hregsE 11 (by decide) (by decide) (by decide), hregsD 11 (by decide) (by decide) (by decide), hregsC_eq 11 (Or.inl (by decide)), hr11])
      (by rw [hregsE 16 (by decide) (by decide) (by decide), hregsD 16 (by decide) (by decide) (by decide), hregsC_eq 16 (Or.inl (by decide)), hr16])
      (by rw [hregsE 17 (by decide) (by decide) (by decide), hregsD 17 (by decide) (by decide) (by decide), hregsC_eq 17 (Or.inl (by decide)), hr17])
      (by rw [hregsE 29 (by decide) (by decide) (by decide), hregsD 29 (by decide) (by decide) (by decide), hregsC_eq 29 (Or.inr (Or.inr (Or.inl rfl))), hr29]) ω
  -- Stitch Phases D + E + F
  obtain ⟨c1, hr1', hc1'⟩ := batch_runs_seqStmts_append (by simp) (by simp)
    (show Runs w p ω (seqStmts [batchAppendChunkStmt]) stC .normal stD cD from hrunD)
    (show Runs w p ω (seqStmts [batchMarkMatchedStmt]) stD .normal stE cE from hrunE)
  obtain ⟨cDF, hrunDF, hcDF⟩ := batch_runs_seqStmts_append (by simp) (by simp) hr1' hrunF
  have hstmt_eq :
      (([batchAppendChunkStmt] ++ [batchMarkMatchedStmt]) ++
        (([.assign 23 (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 29)))),
           .assign 24 (.load (.bin .add (.reg 10) (.reg 29)))] ++ [batchCompactAStmt]) ++
         [.store (.bin .add (.reg 10) (.reg 29)) (.reg 25),
          .assign 29 (.bin .add (.reg 29) (.const 1))])) = batchRouteStepUpdStmts := rfl
  rw [hstmt_eq] at hrunDF
  have hkeep : ∀ r, r ≤ 20 ∨ r = 30 ∨ r = 31 ∨ r = 32 → st1.regs r = stC.regs r := by
    intro r hr
    rcases batch_upd_r_ne hr with ⟨h29, h25, h26, h27, h28, h24, h23, h22, h21⟩
    rw [hregsF r h23 h24 h25 h26 h27 h28 h29, hregsE r h22 h23 h24, hregsD r h21 h26 h27]
  have hr21_1 : st1.regs 21 = chunkHeap1 := by
    rw [hregsF 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hregsE 21 (by decide) (by decide) (by decide)]; exact hr21D
  refine ⟨st1, cDF, hrunDF,
    fun r hr => (hkeep r (by omega)).trans (hregsC_eq r (by omega)),
    batchRouteStep_upd_inv hnX hk hm2 hdisj hi_lt hinv_len hcur_i hinv hdem_drop
      hsp_sub hvalid_i_sub.1 hML_sub hMR_sub hML_card hMR_card hspHeap_lo hspHeap_hi
      hspBfs_lo hspBfs_hi hspDfs_lo hspDfs_hi hspMask_ok hspMask_le hspVis_le hspCur_le
      hspUsed_le hspDead_le hball_C hlive_C hsubC hstC_fr hch1_le_cHi hchD hchDisjD hfrD
      hpbE hfrE hma_stE hma_le_stE hal_i1 hlist_1 hst1_eq_stE hba_sub hhp_sub hspHeap_le_pHi,
    have hk_le : ∀ r ≤ 17, st1.regs r = st0.regs r := fun r hr =>
      (hkeep r (Or.inl (by omega))).trans (hregsC_eq r (Or.inl hr))
    ⟨(hk_le 0 (by decide)).trans hr0, (hk_le 1 (by decide)).trans hr1, (hk_le 2 (by decide)).trans hr2,
     (hk_le 8 (by decide)).trans hr8, (hk_le 9 (by decide)).trans hr9, (hk_le 10 (by decide)).trans hr10,
     (hk_le 11 (by decide)).trans hr11, (hk_le 12 (by decide)).trans hr12, (hk_le 13 (by decide)).trans hr13,
     (hk_le 14 (by decide)).trans hr14, (hk_le 15 (by decide)).trans hr15, (hk_le 16 (by decide)).trans hr16,
     (hk_le 17 (by decide)).trans hr17,
     (hkeep 18 (Or.inl (by decide))).trans hC18, (hkeep 19 (Or.inl (by decide))).trans hC19,
     (hkeep 20 (Or.inl (by decide))).trans hC20, hr21_1, hr29_1,
     (hkeep 30 (Or.inr (Or.inl rfl))).trans hC30,
     (hkeep 31 (Or.inr (Or.inr (Or.inl rfl)))).trans ((hregsC_eq 31 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans hr31),
     (hkeep 32 (Or.inr (Or.inr (Or.inr rfl)))).trans ((hregsC_eq 32 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hr32)⟩,
    by simp only [List.length_cons, List.length_nil, List.length_append] at hc1' hcDF; omega⟩

end MinCostFlow.ExpanderDecomp
