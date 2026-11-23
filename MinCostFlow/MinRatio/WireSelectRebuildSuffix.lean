module

public import MinCostFlow.MinRatio.WireSelectUpdateLevel
import WordRAM.Tactic

/-!
# Verification of `selectRebuildSuffixBody` and main corollaries for the chain operations

Verifies `selectRebuildSuffixBody` over levels `cur .. C.d` (`jtree.tex`, pages 20–21, 24) and
proves the three main invariant-maintenance corollaries for the chain operations:
1. `selectRebuildSuffix_meetsContract`: recursively rebuilds levels `cur .. C.d`, establishing
   `SelectHeapLevelOk` at every level `j ∈ [cur, C.d]` while preserving every edge previously
   stored at a prefix level `< cur`.
2. `selectInit_establishes_matchesChain`: chain `Initialize` from an empty heap.
3. `selectRebuildShift_preserves_matchesChain`: chain `Rebuild(i₀)` / `Shift(i₀)` preserving
   prefix `< i₀` without touching prefix keys.
4. `selectUpdate_preserves_matchesChain`: chain `Update` combining `selectUpdateLevel` on
   non-rebuilt levels `0 .. r - 1` with `selectRebuildSuffix` on `r .. C'.d`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Space, cost, and contract for `selectRebuildSuffixBody` -/

/-- Space bound for `selectRebuildSuffixBody` over levels `cur .. C.d`. -/
noncomputable def selectRebuildSuffixSpace (mem : ℕ → ℕ) (loc : SelectHeapLoc)
    (C : TreeChain) (cur evalSpace : ℕ) : ℕ :=
  (Finset.Icc cur C.d).sum fun j =>
    selectRebuildLevelSpace (levelCandCount mem loc j) (C.G j).E.card loc.cap loc.Lk evalSpace

/-- Step cost bound for `selectRebuildSuffixBody` over levels `cur .. C.d`. -/
noncomputable def selectRebuildSuffixCost (mem : ℕ → ℕ) (loc : SelectHeapLoc)
    (C : TreeChain) (cur evalCost : ℕ) : ℕ :=
  (Finset.Icc cur C.d).sum (fun j =>
    selectRebuildLevelCost (levelCandCount mem loc j) (C.G j).E.card loc.cap loc.Lk evalCost + 40) + 20

/-- Contract for `selectRebuildSuffixBody` (`[hb, metaBase, cur, d, scratch]`):
rebuilds all levels `cur .. C.d`, establishing `SelectHeapLevelOk` at every level `j ∈ [cur, C.d]`
and preserving every edge previously stored at a prefix level `< cur` that is not a candidate in
`[cur, C.d]`. -/
noncomputable def selectRebuildSuffixContract (w h P : ℕ) (loc : SelectHeapLoc)
    (mloc : SelectLevelMetaLoc) (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ)
    (σ σ_mwu γ_ℓ γ_c : ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ cur scratch size,
      args = [loc.hb, mloc.metaBase, cur, C.d, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      (∀ j, cur ≤ j → j ≤ C.d → ∀ e ∈ (C.G j).E, e < loc.cap / 2) ∧
      (∀ e < loc.cap, mem (loc.posPtr + e) ≠ 0 → e < loc.cap / 2) ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectRebuildSuffixSpace mem loc C cur evalSpace < 2 ^ w
  post args mem ret mem' :=
    let cur := args.getD 2 0
    let scratch := args.getD 4 0
    scratch ≤ ret ∧
    ret ≤ scratch + selectRebuildSuffixSpace mem loc C cur evalSpace ∧
    (∃ size', SelectHeapAt mem' loc h size' ∧
      size' ≤ mem loc.hb + (Finset.Icc cur C.d).sum (fun j => (C.G j).E.card)) ∧
    SelectMetaFrame mem mem' mloc loc h P scratch C g ℓ φ coreLen ∧
    ZeroFrom mem' ret ∧
    (∀ j, cur ≤ j → j ≤ C.d → SelectHeapLevelOk mem' loc h P C g ℓ j) ∧
    (∀ e' < loc.cap, (∀ j, cur ≤ j → j ≤ C.d → e' ∉ (C.activeCore j).E \ (C.activeS j).E) →
      (mem (loc.posPtr + e') = 0 ∨ cur ≤ mem (loc.lvlPtr + e') → mem' (loc.posPtr + e') = 0) ∧
      (mem (loc.posPtr + e') ≠ 0 → mem (loc.lvlPtr + e') < cur →
        mem' (loc.posPtr + e') ≠ 0 ∧ mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
        loc.readNum mem' h e' = loc.readNum mem h e' ∧
        loc.readDen mem' h e' = loc.readDen mem h e'))
  cost args mem := selectRebuildSuffixCost mem loc C (args.getD 2 0) evalCost

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 2. Verification of `selectRebuildSuffixBody` -/

/-- Rebuilding level `cur` cannot increase `levelCandCount` at any other level `j ≠ cur`. -/
private lemma levelCandCount_le_after_rebuild {mem mem' : ℕ → ℕ} {loc : SelectHeapLoc}
    {h P cur j : ℕ} {C : TreeChain} {g ℓ : ℕ → ℝ}
    (hne : j ≠ cur)
    (hok : SelectHeapLevelOk mem' loc h P C g ℓ cur)
    (hpres : ∀ e' < loc.cap, e' ∉ (C.activeCore cur).E \ (C.activeS cur).E →
      (mem (loc.posPtr + e') = 0 ∨ mem (loc.lvlPtr + e') = cur → mem' (loc.posPtr + e') = 0) ∧
      (mem (loc.posPtr + e') ≠ 0 → mem (loc.lvlPtr + e') ≠ cur →
        mem' (loc.posPtr + e') ≠ 0 ∧ mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
        loc.readNum mem' h e' = loc.readNum mem h e' ∧
        loc.readDen mem' h e' = loc.readDen mem h e')) :
    levelCandCount mem' loc j ≤ levelCandCount mem loc j := by
  unfold levelCandCount
  refine Finset.card_le_card fun e he => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at he ⊢
  obtain ⟨heCap, hnz', hl'⟩ := he
  refine ⟨heCap, ?_⟩
  by_cases hcand : e ∈ (C.activeCore cur).E \ (C.activeS cur).E
  · exact (hne (hl'.symm.trans (hok.2 e hcand).2.2.1)).elim
  · by_cases h0 : mem (loc.posPtr + e) = 0 ∨ mem (loc.lvlPtr + e) = cur
    · exact (hnz' ((hpres e heCap hcand).1 h0)).elim
    · push Not at h0
      have hlEq := ((hpres e heCap hcand).2 h0.1 h0.2).2.1
      exact ⟨h0.1, hlEq.symm.trans hl'⟩

private lemma selectHeap_size_le_of_lt {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size B : ℕ}
    (hbij : SelectHeapBijection mem loc size)
    (hLt : ∀ e < loc.cap, mem (loc.posPtr + e) ≠ 0 → e < B) :
    size ≤ B := by
  have hinj : Set.InjOn (fun p => mem (loc.arrPtr + p)) (Finset.range size : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := hbij.2.2.1 p₁ (Finset.mem_range.mp hp₁)
    have h2 := hbij.2.2.1 p₂ (Finset.mem_range.mp hp₂)
    dsimp only at heq
    rw [heq] at h1; omega
  have hmaps : (Finset.range size).image (fun p => mem (loc.arrPtr + p)) ⊆ Finset.range B := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hpLt := Finset.mem_range.mp hp
    have hpos := hbij.2.2.1 p hpLt
    exact Finset.mem_range.mpr (hLt _ (hbij.2.1 p hpLt) (by omega))
  calc size = (Finset.range size).card := (Finset.card_range size).symm
    _ = ((Finset.range size).image (fun p => mem (loc.arrPtr + p))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range B).card := Finset.card_le_card hmaps
    _ = B := Finset.card_range B

/-- `selectRebuildSuffixBody` meets `selectRebuildSuffixContract`. -/
theorem selectRebuildSuffix_meetsContract {w h P self rebuildLvl : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[self]? = some (selectRebuildSuffixBody self rebuildLvl))
    (hReb : MeetsContract w p rebuildLvl
      (selectRebuildLevelContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost)) :
    MeetsContract w p self
      (selectRebuildSuffixContract w h P loc mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen evalSpace evalCost) := by
  apply meetsContract_of_rec (fun args _ => C.d + 1 - args.getD 2 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨cur, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hH, hGEcap, hHeapHalf,
    hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
  change C.d + 1 - cur = rem at hremEq
  subst hremEq
  have hhd0 : mem loc.hb = size := by simpa using hat.1 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hcurw : cur < 2 ^ w := hwords cur (by simp)
  have hdw : C.d < 2 ^ w := hwords C.d (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold selectRebuildSuffixBody
  by_cases hgt : C.d < cur
  · have hIccEmpty : Finset.Icc cur C.d = ∅ := Finset.Icc_eq_empty (by omega)
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hgt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [selectRebuildSuffixContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hIccEmpty,
        Finset.sum_empty, Nat.add_zero, hhd0]
      exact ⟨le_rfl, Nat.le_add_right _ _, ⟨size, hat, le_rfl⟩, ⟨hmeta, fun _ _ _ => rfl⟩, hz,
        fun j hj1 hj2 => by omega,
        fun e' he' _ => ⟨fun h => h.elim id fun hge => by
          by_contra hnz; have := (hat.2.2.1 e' he' hnz).1; omega,
          fun hnz _ => ⟨hnz, trivial, trivial, trivial⟩⟩⟩
    · simp only [selectRebuildSuffixContract, selectRebuildSuffixCost, List.getD_cons_zero,
        List.getD_cons_succ, hIccEmpty, Finset.sum_empty, Expr.size]; omega
  · have hle : cur ≤ C.d := by omega
    have hIccSplit : Finset.Icc cur C.d = insert cur (Finset.Icc (cur + 1) C.d) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotMem : cur ∉ Finset.Icc (cur + 1) C.d := by simp
    have hsumE : (Finset.Icc cur C.d).sum (fun j => (C.G j).E.card) =
        (C.G cur).E.card + (Finset.Icc (cur + 1) C.d).sum (fun j => (C.G j).E.card) := by
      rw [hIccSplit, Finset.sum_insert hnotMem]
    have hspSplit : selectRebuildSuffixSpace mem loc C cur evalSpace =
        selectRebuildLevelSpace (levelCandCount mem loc cur) (C.G cur).E.card loc.cap loc.Lk evalSpace +
        selectRebuildSuffixSpace mem loc C (cur + 1) evalSpace := by
      unfold selectRebuildSuffixSpace
      rw [hIccSplit, Finset.sum_insert hnotMem]
    have hcostSplit : selectRebuildSuffixCost mem loc C cur evalCost =
        selectRebuildLevelCost (levelCandCount mem loc cur) (C.G cur).E.card loc.cap loc.Lk evalCost +
        40 + selectRebuildSuffixCost mem loc C (cur + 1) evalCost := by
      unfold selectRebuildSuffixCost
      rw [hIccSplit, Finset.sum_insert hnotMem]; omega
    have hszHalf : size ≤ loc.cap / 2 := selectHeap_size_le_of_lt hat.2.1 hHeapHalf
    have hCardHalf : (C.G cur).E.card ≤ loc.cap / 2 := by
      have hsub : (C.G cur).E ⊆ Finset.range (loc.cap / 2) :=
        fun e he => Finset.mem_range.mpr (hGEcap cur le_rfl hle e he)
      exact (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    have hszCur : (size - levelCandCount mem loc cur) + (C.G cur).E.card ≤ loc.cap := by omega
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hgt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    -- Step 1: rebuild level `cur`
    refine runs_seq_call_flat hReb (vs := [loc.hb, mloc.metaBase, cur, scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨cur, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hle,
        fun e he => lt_of_lt_of_le (hGEcap cur le_rfl hle e he) (Nat.div_le_self _ _),
        hszCur, hat, hmeta, hdisj, hmetaFr, hz, by omega⟩
    · intro sc1 mem1 pos1 hp1
      obtain ⟨hlo1, hhi1, ⟨sz1, hat1, hsz1⟩, ⟨hmeta1, hfr1⟩, hz1, hok1, hpres1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ, hhd0] at hlo1 hhi1 hsz1 hok1 hpres1 hfr1
      have hhd1 : mem1 loc.hb = sz1 := by simpa using hat1.1 0 (by simp)
      have hsc1W : sc1 < 2 ^ w := by omega
      have hcur1W : cur + 1 < 2 ^ w := by
        have hend := loc.endAddr_eq; unfold selectHeapSize shHdrSize at hend; omega
      have hcntLe : ∀ j ∈ Finset.Icc (cur + 1) C.d, levelCandCount mem1 loc j ≤ levelCandCount mem loc j :=
        fun j hj => levelCandCount_le_after_rebuild (by simp at hj; omega) hok1 hpres1
      have hsp1Le : selectRebuildSuffixSpace mem1 loc C (cur + 1) evalSpace ≤
          selectRebuildSuffixSpace mem loc C (cur + 1) evalSpace := by
        unfold selectRebuildSuffixSpace
        refine Finset.sum_le_sum fun j hj => ?_
        unfold selectRebuildLevelSpace heapClearLevelSpace
        exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hcntLe j hj)) _
      have hcost1Le : selectRebuildSuffixCost mem1 loc C (cur + 1) evalCost ≤
          selectRebuildSuffixCost mem loc C (cur + 1) evalCost := by
        unfold selectRebuildSuffixCost
        refine Nat.add_le_add_right (Finset.sum_le_sum fun j hj => ?_) _
        unfold selectRebuildLevelCost heapClearLevelCost
        have hmul := Nat.mul_le_mul_right (heapDeleteCost loc.cap loc.Lk + 60) (hcntLe j hj)
        omega
      have hmetaFr1 : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem1 a) →
          SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
        fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr1 a ha hout)
      have hHeapHalf1 : ∀ e < loc.cap, mem1 (loc.posPtr + e) ≠ 0 → e < loc.cap / 2 := by
        intro e heCap hnz1
        by_cases hc : e ∈ (C.activeCore cur).E \ (C.activeS cur).E
        · exact hGEcap cur le_rfl hle e (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hc).1).1
        · by_cases h0 : mem (loc.posPtr + e) = 0
          · exact absurd ((hpres1 e heCap hc).1 (Or.inl h0)) hnz1
          · exact hHeapHalf e heCap h0
      -- Step 2: recursive call on `cur + 1 .. C.d`
      refine runs_seq_call_flat ih (vs := [loc.hb, mloc.metaBase, cur + 1, C.d, sc1])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨cur + 1, sc1, sz1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hH,
          fun j hj1 hj2 => hGEcap j (by omega) hj2, hHeapHalf1, hat1, hmeta1,
          selectMetaDisjoint_mono hdisj hlo1, hmetaFr1, hz1, by omega⟩,
          by change C.d + 1 - (cur + 1) < C.d + 1 - cur; omega⟩
      · intro ret mem2 pos2 hp2
        obtain ⟨hlo2, hhi2, ⟨sz2, hat2, hsz2⟩, ⟨hmeta2, hfr2⟩, hz2, hok2, hpres2⟩ := hp2
        simp only [List.getD_cons_zero, List.getD_cons_succ, hhd1] at hlo2 hhi2 hsz2 hok2 hpres2 hfr2
        have hretW : ret < 2 ^ w := by omega
        have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
          fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1 a ha hout)
        -- Disjointness of candidates between level `cur` and levels `cur + 1 .. C.d`
        have hcandDisj : ∀ e ∈ (C.activeCore cur).E \ (C.activeS cur).E,
            ∀ j, cur + 1 ≤ j → j ≤ C.d → e ∉ (C.activeCore j).E \ (C.activeS j).E := by
          intro e he j hj1 hj2 hej
          have hEq := C.level_unique_of_mem_activeCore_diff hH hle hj2 he hej
          omega
        refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · dsimp only [selectRebuildSuffixContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhd0]
          refine ⟨by omega, by omega, ⟨sz2, hat2, by omega⟩, ⟨hmeta2, hfrOut⟩, hz2, ?_, ?_⟩
          · intro j hj1 hj2
            by_cases hjEq : j = cur
            · subst j
              refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
              · by_cases hinSuf : ∃ k, cur + 1 ≤ k ∧ k ≤ C.d ∧ e ∈ (C.activeCore k).E \ (C.activeS k).E
                · obtain ⟨k, hk1, hk2, hek⟩ := hinSuf
                  have hlK := ((hok2 k hk1 hk2).2 e hek).2.2.1
                  omega
                · push Not at hinSuf
                  by_cases h1 : mem1 (loc.posPtr + e) = 0 ∨ cur + 1 ≤ mem1 (loc.lvlPtr + e)
                  · exact (hnz ((hpres2 e heCap hinSuf).1 h1)).elim
                  · push Not at h1
                    have hl1 := ((hpres2 e heCap hinSuf).2 h1.1 h1.2).2.1
                    exact hok1.1 e heCap h1.1 (hl1.symm.trans hl)
              · obtain ⟨heCap, hnz1, hl1, hrep1⟩ := hok1.2 e he
                obtain ⟨k1, k2, k3, k4⟩ := (hpres2 e heCap (hcandDisj e he)).2 hnz1 (by omega)
                exact ⟨heCap, k1, k2.trans hl1, by rw [k3, k4]; exact hrep1⟩
            · exact hok2 j (by omega) hj2
          · intro e' he' hncAll
            have hncCur : e' ∉ (C.activeCore cur).E \ (C.activeS cur).E := hncAll cur le_rfl hle
            have hncSuf : ∀ j, cur + 1 ≤ j → j ≤ C.d → e' ∉ (C.activeCore j).E \ (C.activeS j).E :=
              fun j hj1 hj2 => hncAll j (by omega) hj2
            refine ⟨fun h0ge => ?_, fun hnz0 hlt0 => ?_⟩
            · rcases h0ge with h0 | hge
              · exact (hpres2 e' he' hncSuf).1 (Or.inl ((hpres1 e' he' hncCur).1 (Or.inl h0)))
              · by_cases hEq : mem (loc.lvlPtr + e') = cur
                · exact (hpres2 e' he' hncSuf).1 (Or.inl ((hpres1 e' he' hncCur).1 (Or.inr hEq)))
                · by_cases hnz0 : mem (loc.posPtr + e') = 0
                  · exact (hpres2 e' he' hncSuf).1 (Or.inl ((hpres1 e' he' hncCur).1 (Or.inl hnz0)))
                  · have hl1 := ((hpres1 e' he' hncCur).2 hnz0 hEq).2.1
                    exact (hpres2 e' he' hncSuf).1 (Or.inr (by omega))
            · obtain ⟨g1, g2, g3, g4⟩ := (hpres1 e' he' hncCur).2 hnz0 (by omega)
              obtain ⟨k1, k2, k3, k4⟩ := (hpres2 e' he' hncSuf).2 g1 (by omega)
              exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
        · simp only [Contract.below, selectRebuildSuffixContract, selectRebuildLevelContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega

/-! ## 3. Main corollaries for `Initialize`, `Rebuild(i₀)`, `Shift(i₀)` and `Update` -/

/-- **Chain `Initialize` corollary**: running `selectRebuildSuffix` from `cur = 0` on a fresh
empty select-heap establishes `SelectHeapMatchesChain` for `(C, g, ℓ)`. -/
theorem selectInit_establishes_matchesChain
    {w h P : ℕ} {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {evalSpace evalCost scratch ret : ℕ} {mem mem' : ℕ → ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hd : loc.d = C.d)
    (hPost : (selectRebuildSuffixContract w h P loc mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen
      evalSpace evalCost).post [loc.hb, mloc.metaBase, 0, C.d, scratch] mem ret mem') :
    ∃ size', SelectHeapMatchesChain mem' loc h P C g ℓ size' ∧
      size' ≤ mem loc.hb + (Finset.Icc 0 C.d).sum (fun j => (C.G j).E.card) := by
  obtain ⟨_, _, ⟨size', hat', hsz'⟩, _, _, hok, _⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsz' hok
  exact ⟨size', selectHeapMatchesChain_of_levelOk hH hat' hd (fun i hi => hok i (Nat.zero_le _) hi), hsz'⟩

/-- **Chain `Rebuild(i₀)` / `Shift(i₀)` corollary**: when `C` and `C'` agree on prefix `< i₀`
(with `SelectHeapMatchesChain` on `C` before the step), running `selectRebuildSuffix` on
`i₀ .. C'.d` establishes `SelectHeapMatchesChain` for `(C', g', ℓ')` without touching prefix keys. -/
theorem selectRebuildShift_preserves_matchesChain
    {w h P i₀ size : ℕ} {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {g g' ℓ ℓ' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {evalSpace evalCost scratch ret : ℕ} {mem mem' : ℕ → ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hd' : loc.d = C'.d) (hi0 : i₀ ≤ C.d + 1)
    (hG : ∀ j < i₀, C'.G j = C.G j)
    (hLSF : ∀ j < i₀, C'.activeLSF j = C.activeLSF j)
    (hS : ∀ j < i₀, C'.activeS j = C.activeS j)
    (hEmb : ∀ j < i₀, C'.activeEmb j = C.activeEmb j)
    (hg : ∀ e, g' e = g e) (hℓ : ∀ e, ℓ' e = ℓ e)
    (hMatchOld : SelectHeapMatchesChain mem loc h P C g ℓ size)
    (hPost : (selectRebuildSuffixContract w h P loc mloc C' G' g' ℓ' σ' σ'_mwu γ'_ℓ γ'_c φ coreLen
      evalSpace evalCost).post [loc.hb, mloc.metaBase, i₀, C'.d, scratch] mem ret mem') :
    ∃ size', SelectHeapMatchesChain mem' loc h P C' g' ℓ' size' := by
  obtain ⟨_, _, ⟨size', hat', _⟩, _, _, hokSuf, hpres⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hokSuf hpres
  refine ⟨size', selectHeapMatchesChain_of_levelOk hH' hat' hd' fun i hi => ?_⟩
  by_cases hilt : i < i₀
  · have hOldOk := selectHeapLevelOk_of_matchesChain hH hMatchOld (i := i) (by omega)
    have hcandDisj : ∀ e ∈ (C'.activeCore i).E \ (C'.activeS i).E,
        ∀ j, i₀ ≤ j → j ≤ C'.d → e ∉ (C'.activeCore j).E \ (C'.activeS j).E := fun e he j hj1 hj2 hej => by
      have hEq := C'.level_unique_of_mem_activeCore_diff hH' hi hj2 he hej; omega
    refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
    · by_cases hinSuf : ∃ j, i₀ ≤ j ∧ j ≤ C'.d ∧ e ∈ (C'.activeCore j).E \ (C'.activeS j).E
      · obtain ⟨j, hj1, hj2, hej⟩ := hinSuf
        have hlJ := ((hokSuf j hj1 hj2).2 e hej).2.2.1; omega
      · push Not at hinSuf
        by_cases h0ge : mem (loc.posPtr + e) = 0 ∨ i₀ ≤ mem (loc.lvlPtr + e)
        · exact (hnz ((hpres e heCap hinSuf).1 h0ge)).elim
        · push Not at h0ge
          have hlEq := ((hpres e heCap hinSuf).2 h0ge.1 h0ge.2).2.1
          have hOld := hOldOk.1 e heCap h0ge.1 (hlEq.symm.trans hl)
          exact (selectHeap_prefix_preserved hG hLSF hS hEmb hg hℓ hilt e).1.mpr hOld
    · have hPref := selectHeap_prefix_preserved hG hLSF hS hEmb hg hℓ hilt e
      have hOld : e ∈ (C.activeCore i).E \ (C.activeS i).E := hPref.1.mp he
      obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hOldOk.2 e hOld
      obtain ⟨hwi, hwl⟩ := hPref.2 hOld
      obtain ⟨k1, k2, k3, k4⟩ := (hpres e heCap (hcandDisj e he)).2 hnz0 (by omega)
      exact ⟨heCap, k1, k2.trans hl0, by rw [k3, k4, hwi, hwl]; exact hrep0⟩
  · exact hokSuf i (by omega) hi

/-- **Chain `Update` corollary**: if non-rebuilt levels `0 .. r - 1` have already been updated
via `selectUpdateLevel` (`∀ j < r, SelectHeapLevelOk memMid loc h P C' g' ℓ' j`), and
`selectRebuildSuffix` then rebuilds suffix `r .. C'.d`, the resulting heap satisfies
`SelectHeapMatchesChain` for `(C', g', ℓ')`. -/
theorem selectUpdate_preserves_matchesChain
    {w h P r : ℕ} {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C' : TreeChain} {G' : MGraph} {g' ℓ' : ℕ → ℝ} {σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {evalSpace evalCost scratch ret : ℕ} {memMid mem' : ℕ → ℕ}
    (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c) (hd' : loc.d = C'.d)
    (hPrefOk : ∀ j < r, j ≤ C'.d → SelectHeapLevelOk memMid loc h P C' g' ℓ' j)
    (hPost : (selectRebuildSuffixContract w h P loc mloc C' G' g' ℓ' σ' σ'_mwu γ'_ℓ γ'_c φ coreLen
      evalSpace evalCost).post [loc.hb, mloc.metaBase, r, C'.d, scratch] memMid ret mem') :
    ∃ size', SelectHeapMatchesChain mem' loc h P C' g' ℓ' size' := by
  obtain ⟨_, _, ⟨size', hat', _⟩, _, _, hokSuf, hpres⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hokSuf hpres
  refine ⟨size', selectHeapMatchesChain_of_levelOk hH' hat' hd' fun i hi => ?_⟩
  by_cases hilt : i < r
  · have hMidOk := hPrefOk i hilt hi
    have hcandDisj : ∀ e ∈ (C'.activeCore i).E \ (C'.activeS i).E,
        ∀ j, r ≤ j → j ≤ C'.d → e ∉ (C'.activeCore j).E \ (C'.activeS j).E := fun e he j hj1 hj2 hej => by
      have hEq := C'.level_unique_of_mem_activeCore_diff hH' hi hj2 he hej; omega
    refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
    · by_cases hinSuf : ∃ j, r ≤ j ∧ j ≤ C'.d ∧ e ∈ (C'.activeCore j).E \ (C'.activeS j).E
      · obtain ⟨j, hj1, hj2, hej⟩ := hinSuf
        have hlJ := ((hokSuf j hj1 hj2).2 e hej).2.2.1; omega
      · push Not at hinSuf
        by_cases h0ge : memMid (loc.posPtr + e) = 0 ∨ r ≤ memMid (loc.lvlPtr + e)
        · exact (hnz ((hpres e heCap hinSuf).1 h0ge)).elim
        · push Not at h0ge
          have hlEq := ((hpres e heCap hinSuf).2 h0ge.1 h0ge.2).2.1
          exact hMidOk.1 e heCap h0ge.1 (hlEq.symm.trans hl)
    · obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hMidOk.2 e he
      obtain ⟨k1, k2, k3, k4⟩ := (hpres e heCap (hcandDisj e he)).2 hnz0 (by omega)
      exact ⟨heCap, k1, k2.trans hl0, by rw [k3, k4]; exact hrep0⟩
  · exact hokSuf i (by omega) hi

end MinCostFlow.MinRatio
