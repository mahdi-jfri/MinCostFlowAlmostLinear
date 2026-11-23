module

public import MinCostFlow.MinRatio.WireSelectRebuildSuffix
import WordRAM.Tactic

/-!
# Capacity-slack-free contracts for `selectProcessList`, `selectRebuildLevel`, and `selectRebuildSuffix`

In a valid indexed select heap (`SelectHeapBijection mem loc size`), every active heap position
`p < size` holds a distinct edge ID `< loc.cap` with `pos[e] ≠ 0`. Consequently, whenever an edge
`e < loc.cap` is absent (`pos[e] = 0`), we automatically have `size < loc.cap` by pigeonhole
(`selectHeapBijection_size_lt_of_pos_zero`), without assuming `size + L.length ≤ loc.cap` or
`size + ∑_{j ∈ Icc cur d} (C.G j).E.card ≤ loc.cap`.

This file provides:
* `selectHeapBijection_size_lt_of_pos_zero`: pigeonhole proof that `size < loc.cap` whenever some
  `e < loc.cap` has `pos[e] = 0`.
* `selectHeapMatchesChain_levelCandCount_sum_le`: under `SelectHeapMatchesChain` and nested edge
  sets `(C.G j).E ⊆ (C.G cur).E` (`cur ≤ j ≤ C.d`), the total number of old candidates across
  levels `cur .. C.d` is at most `(C.G cur).E.card`.
* `selectProcessListNoRoomContract`, `selectRebuildLevelNoRoomContract`, and
  `selectRebuildSuffixNoRoomContract` together with their `MeetsContract` proofs for the unchanged
  bodies `selectProcessListBody`, `selectRebuildLevelBody`, and `selectRebuildSuffixBody`, with
  the exact same postconditions and cost bounds as `WireSelectUpdateEdge`, `WireSelectUpdateLevel`,
  and `WireSelectRebuildSuffix`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Pigeonhole capacity lemma and candidate-count sum bound -/

/-- Under `SelectHeapBijection`, any absent edge `e < loc.cap` (`pos[e] = 0`) guarantees
`size < loc.cap`. -/
theorem selectHeapBijection_size_lt_of_pos_zero {mem : ℕ → ℕ} {loc : SelectHeapLoc} {size e : ℕ}
    (hb : SelectHeapBijection mem loc size) (he : e < loc.cap) (h0 : mem (loc.posPtr + e) = 0) :
    size < loc.cap := by
  have hsub : (Finset.range size).image (fun p => mem (loc.arrPtr + p)) ⊆
      (Finset.range loc.cap).erase e := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr (hb.2.1 p hp)⟩
    intro hEq
    have hpos := hb.2.2.1 p hp
    rw [hEq, h0] at hpos
    omega
  have hcard : ((Finset.range size).image (fun p => mem (loc.arrPtr + p))).card = size := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro p1 hp1 p2 hp2 hEq
      exact hb.arr_inj (Finset.mem_range.mp hp1) (Finset.mem_range.mp hp2) hEq
  have herase : ((Finset.range loc.cap).erase e).card = loc.cap - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr he), Finset.card_range]
  have hle : size ≤ loc.cap - 1 := hcard ▸ herase ▸ Finset.card_le_card hsub
  omega

/-- Under `SelectHeapMatchesChain` and nested edge sets `(C.G j).E ⊆ (C.G cur).E` for `cur ≤ j ≤ C.d`,
the sum of `levelCandCount mem loc j` over `j ∈ Finset.Icc cur C.d` is at most `(C.G cur).E.card`
(since stored candidates have unique levels `lvl[e]`). -/
theorem selectHeapMatchesChain_levelCandCount_sum_le
    {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P size cur : ℕ} {C : TreeChain} {G : MGraph}
    {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hMatch : SelectHeapMatchesChain mem loc h P C g ℓ size)
    (hSub : ∀ j, cur ≤ j → j ≤ C.d → (C.G j).E ⊆ (C.G cur).E) :
    (Finset.Icc cur C.d).sum (fun j => levelCandCount mem loc j) ≤ (C.G cur).E.card := by
  let S : ℕ → Finset ℕ := fun j =>
    (Finset.range loc.cap).filter fun e => mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = j
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc cur C.d) : Set ℕ) S := by
    intro j1 _ j2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [S, Finset.mem_filter] at he1 he2
    exact hne (he1.2.2.symm.trans he2.2.2)
  have hbi : (Finset.Icc cur C.d).biUnion S ⊆ (C.G cur).E := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_Icc, S, Finset.mem_filter, Finset.mem_range] at he
    obtain ⟨j, ⟨hj1, hj2⟩, heCap, hnz, hlvl⟩ := he
    have hok := selectHeapLevelOk_of_matchesChain hH hMatch (i := j) hj2
    have hcand := hok.1 e heCap hnz hlvl
    have heG : e ∈ (C.G j).E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hcand).1).1
    exact hSub j hj1 hj2 heG
  calc (Finset.Icc cur C.d).sum (fun j => levelCandCount mem loc j)
      = (Finset.Icc cur C.d).sum (fun j => (S j).card) := rfl
    _ = ((Finset.Icc cur C.d).biUnion S).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (C.G cur).E.card := Finset.card_le_card hbi

/-! ## 2. Capacity-slack-free contracts -/

/-- Capacity-slack-free variant of `selectProcessListContract` (drops `size + (L.length - idx) ≤ loc.cap`). -/
def selectProcessListNoRoomContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (L : List ℕ) (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl listPtr idx scratch size,
      args = [loc.hb, mloc.metaBase, lvl, listPtr, L.length, idx, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      lvl ≤ C.d ∧ idx ≤ L.length ∧
      listPtr + L.length ≤ scratch ∧
      (listPtr + L.length ≤ loc.hb ∨ loc.endAddr ≤ listPtr) ∧
      ListAt mem listPtr L ∧
      (∀ e ∈ L, e < loc.cap ∧ e < mloc.eCap lvl) ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectProcessListSpace (L.length - idx) loc.cap loc.Lk evalSpace < 2 ^ w
  post := (selectProcessListContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost).post
  cost := (selectProcessListContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost).cost

/-- Capacity-slack-free variant of `selectRebuildLevelContract` (drops `(size - oldCand) + mNew ≤ loc.cap`). -/
def selectRebuildLevelNoRoomContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl scratch size,
      args = [loc.hb, mloc.metaBase, lvl, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      lvl ≤ C.d ∧
      (∀ e ∈ (C.G lvl).E, e < loc.cap) ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectRebuildLevelSpace (levelCandCount mem loc lvl) (C.G lvl).E.card
        loc.cap loc.Lk evalSpace < 2 ^ w
  post := (selectRebuildLevelContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost).post
  cost := (selectRebuildLevelContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost).cost

/-- Capacity-slack-free variant of `selectRebuildSuffixContract` (drops `size + ∑ (C.G j).E.card ≤ loc.cap`). -/
noncomputable def selectRebuildSuffixNoRoomContract (w h P : ℕ) (loc : SelectHeapLoc)
    (mloc : SelectLevelMetaLoc) (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ)
    (σ σ_mwu γ_ℓ γ_c : ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ cur scratch size,
      args = [loc.hb, mloc.metaBase, cur, C.d, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      C.Holds G ℓ σ σ_mwu γ_ℓ γ_c ∧
      (∀ j, cur ≤ j → j ≤ C.d → ∀ e ∈ (C.G j).E, e < loc.cap) ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectRebuildSuffixSpace mem loc C cur evalSpace < 2 ^ w
  post := (selectRebuildSuffixContract w h P loc mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen evalSpace evalCost).post
  cost := (selectRebuildSuffixContract w h P loc mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen evalSpace evalCost).cost

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 3. Verification of the three capacity-slack-free contracts -/

/-- `selectProcessListBody` meets `selectProcessListNoRoomContract` with no capacity-slack premise. -/
theorem selectProcessList_meetsContract_noRoom {w h P self procEdge : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {L : List ℕ} {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[self]? = some (selectProcessListBody self procEdge))
    (hEdge : MeetsContract w p procEdge
      (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost)) :
    MeetsContract w p self
      (selectProcessListNoRoomContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost) := by
  apply meetsContract_of_rec (fun args _ => L.length - args.getD 5 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨lvl, listPtr, idx, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, hidxLe,
    hlpSc, hlpDisj, hListAt, hLbd, hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
  change L.length - idx = rem at hremEq
  subst hremEq
  have hhdSize : mem loc.hb = size := by simpa using hat.1 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hlpw : listPtr < 2 ^ w := hwords listPtr (by simp)
  have hlenw : L.length < 2 ^ w := hwords L.length (by simp)
  have hidxw : idx < 2 ^ w := hwords idx (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold selectProcessListBody
  by_cases hlt : idx < L.length
  · have heMem : L[idx] ∈ L := List.getElem_mem hlt
    obtain ⟨heCap, heEcap⟩ := hLbd L[idx] heMem
    have hread : mem (listPtr + idx) = L[idx] := hListAt idx hlt
    have heW : L[idx] < 2 ^ w := by have := loc.endAddr_eq; unfold selectHeapSize shHdrSize at *; omega
    have hspSplit : selectProcessEdgeSpace loc.cap loc.Lk evalSpace +
        selectProcessListSpace (L.length - (idx + 1)) loc.cap loc.Lk evalSpace =
        selectProcessListSpace (L.length - idx) loc.cap loc.Lk evalSpace := by
      unfold selectProcessListSpace
      have h1 : L.length - idx = (L.length - (idx + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    have hcostSplit : selectProcessEdgeCost loc.cap loc.Lk evalCost + 40 +
        selectProcessListCost (L.length - (idx + 1)) loc.cap loc.Lk evalCost =
        selectProcessListCost (L.length - idx) loc.cap loc.Lk evalCost := by
      unfold selectProcessListCost
      have h1 : L.length - idx = (L.length - (idx + 1)) + 1 := by omega
      conv_rhs => rw [h1, Nat.add_mul, Nat.one_mul]
      omega
    refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, hw1])
      ?_ (fun h => absurd h (by decide))
    intro _
    refine runs_seq_assign_flat (v := L[idx]) (by eval_expr) ?_
    refine runs_seq_call_flat hEdge (vs := [loc.hb, mloc.metaBase, lvl, L[idx], scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨lvl, L[idx], scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, heCap, heEcap,
        fun h0 _ => selectHeapBijection_size_lt_of_pos_zero hat.2.1 heCap h0,
        hat, hmeta, hdisj, hmetaFr, hz, by omega⟩
    · intro sc1 mem1 pos1 hp1
      obtain ⟨hlo1, hhi1, ⟨size1, hat1⟩, ⟨hmeta1, hfr1⟩, hz1, hcand1, hncand1, hoth1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hlo1 hhi1 hcand1 hncand1 hoth1 hfr1
      have hsc1W : sc1 < 2 ^ w := by omega
      have hhd1 : mem1 loc.hb = size1 := by simpa using hat1.1 0 (by simp)
      have hsz1Le : size1 ≤ size + 1 := by
        have hsub : (Finset.range size1).image (fun p => mem1 (loc.arrPtr + p)) ⊆
            insert L[idx] ((Finset.range size).image (fun p => mem (loc.arrPtr + p))) := by
          intro x hx
          simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert] at hx ⊢
          obtain ⟨p, hp1', rfl⟩ := hx
          have hxCap : mem1 (loc.arrPtr + p) < loc.cap := hat1.2.1.2.1 p hp1'
          have hnz1 : mem1 (loc.posPtr + mem1 (loc.arrPtr + p)) ≠ 0 := hat1.2.1.pos_arr_ne_zero hp1'
          by_cases hxeq : mem1 (loc.arrPtr + p) = L[idx]
          · exact Or.inl hxeq
          · right
            have hnz0 : mem (loc.posPtr + mem1 (loc.arrPtr + p)) ≠ 0 := (hoth1 _ hxCap hxeq).1.mp hnz1
            rcases hat.2.1.2.2.2 _ hxCap with h0 | ⟨hle, harr⟩
            · exact (hnz0 h0).elim
            · exact ⟨mem (loc.posPtr + mem1 (loc.arrPtr + p)) - 1, by omega, harr⟩
        have hcard1 : ((Finset.range size1).image (fun p => mem1 (loc.arrPtr + p))).card = size1 := by
          rw [Finset.card_image_of_injOn]
          · simp
          · intro p1 hp1' p2 hp2' hEq
            exact hat1.2.1.arr_inj (Finset.mem_range.mp hp1') (Finset.mem_range.mp hp2') hEq
        have hcard0 : (insert L[idx] ((Finset.range size).image (fun p => mem (loc.arrPtr + p)))).card ≤ size + 1 :=
          (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_image_le.trans (by simp)) 1)
        exact hcard1 ▸ (Finset.card_le_card hsub).trans hcard0
      have hListAt1 : ListAt mem1 listPtr L := fun j hj =>
        (hfr1 (listPtr + j) (by omega) (by omega)).trans (hListAt j hj)
      have hdisj1 : SelectMetaDisjoint mloc loc sc1 := selectMetaDisjoint_mono hdisj hlo1
      have hmetaFr1 : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem1 a) →
          SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
        fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr1 a ha hout)
      refine runs_seq_call_flat ih
        (vs := [loc.hb, mloc.metaBase, lvl, listPtr, L.length, idx + 1, sc1])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨lvl, listPtr, idx + 1, sc1, size1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD, by omega,
          by omega, hlpDisj, hListAt1, hLbd, hat1, hmeta1, hdisj1, hmetaFr1, hz1, by omega⟩,
          by change L.length - (idx + 1) < L.length - idx; omega⟩
      · intro ret mem2 pos2 hp2
        obtain ⟨hlo2, hhi2, ⟨size2, hat2, hsz2Le⟩, ⟨hmeta2, hfr2⟩, hz2, hdrop2, hnotdrop2⟩ := hp2
        simp only [List.getD_cons_zero, List.getD_cons_succ, hhd1] at hlo2 hhi2 hsz2Le hdrop2 hnotdrop2 hfr2
        have hretw : ret < 2 ^ w := by omega
        have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
          fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1 a ha hout)
        refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · dsimp only [selectProcessListNoRoomContract, selectProcessListContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhdSize]
          refine ⟨by omega, by omega, ⟨size2, hat2, by omega⟩, ⟨hmeta2, hfrOut⟩, hz2, ?_, ?_⟩
          · intro e heDrop
            rw [List.drop_eq_getElem_cons hlt, List.mem_cons] at heDrop
            rcases heDrop with rfl | heTail
            · by_cases hinTail : L[idx] ∈ L.drop (idx + 1)
              · exact ⟨(hdrop2 _ hinTail).1, fun hnc => ⟨((hdrop2 _ hinTail).2 hnc).1,
                  fun h0 => ((hdrop2 _ hinTail).2 hnc).2.1 ((hncand1 hnc).2.1 h0),
                  fun hnz hne => by
                    obtain ⟨g1, g2, g3, g4⟩ := (hncand1 hnc).2.2.1 hnz hne
                    obtain ⟨k1, k2, k3, k4⟩ := ((hdrop2 _ hinTail).2 hnc).2.2.1 g1 (g2.symm ▸ hne)
                    exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩,
                  fun hnz hl => ((hdrop2 _ hinTail).2 hnc).2.1 ((hncand1 hnc).2.2.2 hnz hl)⟩⟩
              · obtain ⟨k1, k2, k3, k4⟩ := hnotdrop2 L[idx] heCap hinTail
                refine ⟨fun hc => ?_, fun hnc => ⟨?_, fun h0 => ?_, fun hnz hne => ?_, fun hnz hl => ?_⟩⟩
                · obtain ⟨g1, g2, g3⟩ := hcand1 hc
                  exact ⟨k1.mpr g1, k2.trans g2, by rw [k3, k4]; exact g3⟩
                · rintro ⟨hnz2, hl2⟩
                  exact (hncand1 hnc).1 ⟨k1.mp hnz2, k2.symm.trans hl2⟩
                · by_contra hnz2; exact (k1.mp hnz2) ((hncand1 hnc).2.1 h0)
                · obtain ⟨g1, g2, g3, g4⟩ := (hncand1 hnc).2.2.1 hnz hne
                  exact ⟨k1.mpr g1, k2.trans g2, k3.trans g3, k4.trans g4⟩
                · by_contra hnz2; exact (k1.mp hnz2) ((hncand1 hnc).2.2.2 hnz hl)
            · refine ⟨(hdrop2 e heTail).1, fun hnc => ⟨((hdrop2 e heTail).2 hnc).1, fun h0 => ?_, fun hnz hne => ?_, fun hnz hl => ?_⟩⟩
              · by_cases heq : e = L[idx]
                · subst e; exact ((hdrop2 _ heTail).2 hnc).2.1 ((hncand1 hnc).2.1 h0)
                · have heC : e < loc.cap := (hLbd e (List.mem_of_mem_drop heTail)).1
                  have h01 : mem1 (loc.posPtr + e) = 0 := by
                    by_contra hnz1; exact ((hoth1 e heC heq).1.mp hnz1) h0
                  exact ((hdrop2 e heTail).2 hnc).2.1 h01
              · by_cases heq : e = L[idx]
                · subst e
                  obtain ⟨g1, g2, g3, g4⟩ := (hncand1 hnc).2.2.1 hnz hne
                  obtain ⟨k1, k2, k3, k4⟩ := ((hdrop2 _ heTail).2 hnc).2.2.1 g1 (g2.symm ▸ hne)
                  exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
                · have heC : e < loc.cap := (hLbd e (List.mem_of_mem_drop heTail)).1
                  obtain ⟨g1, g2, g3, g4⟩ := hoth1 e heC heq
                  obtain ⟨k1, k2, k3, k4⟩ := ((hdrop2 e heTail).2 hnc).2.2.1 (g1.mpr hnz) (g2.symm ▸ hne)
                  exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
              · by_cases heq : e = L[idx]
                · subst e; exact ((hdrop2 _ heTail).2 hnc).2.1 ((hncand1 hnc).2.2.2 hnz hl)
                · have heC : e < loc.cap := (hLbd e (List.mem_of_mem_drop heTail)).1
                  obtain ⟨g1, g2, _, _⟩ := hoth1 e heC heq
                  exact ((hdrop2 e heTail).2 hnc).2.2.2 (g1.mpr hnz) (g2.trans hl)
          · intro e' he' hnotD
            rw [List.drop_eq_getElem_cons hlt, List.mem_cons, not_or] at hnotD
            obtain ⟨g1, g2, g3, g4⟩ := hoth1 e' he' hnotD.1
            obtain ⟨k1, k2, k3, k4⟩ := hnotdrop2 e' he' hnotD.2
            exact ⟨k1.trans g1, k2.trans g2, k3.trans g3, k4.trans g4⟩
        · simp only [Contract.below, selectProcessListNoRoomContract, selectProcessListContract,
            selectProcessEdgeContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega
  · have hdropNil : L.drop idx = [] := List.drop_eq_nil_of_le (by omega)
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hlt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine WordRAM.runs_ret_le (v := scratch) (by eval_expr) ?_ ?_
    · dsimp only [selectProcessListNoRoomContract, selectProcessListContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hdropNil, hhdSize]
      exact ⟨le_rfl, Nat.le_add_right _ _, ⟨size, hat, Nat.le_add_right _ _⟩,
        ⟨hmeta, fun _ _ _ => rfl⟩, hz,
        fun _ h => (List.not_mem_nil h).elim, fun _ _ _ => ⟨trivial, trivial, trivial, trivial⟩⟩
    · simp only [selectProcessListNoRoomContract, selectProcessListContract, selectProcessListCost,
        List.getD_cons_zero, List.getD_cons_succ, Expr.size]; omega

/-- `selectRebuildLevelBody` meets `selectRebuildLevelNoRoomContract` with no capacity-slack premise. -/
theorem selectRebuildLevel_meetsContract_noRoom {w h P proc clearLvl procList : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selectRebuildLevelBody clearLvl procList))
    (hClear : MeetsContract w p clearLvl (heapClearLevelContract w h loc))
    (hList : ∀ L', MeetsContract w p procList
      (selectProcessListNoRoomContract w h P loc mloc C g ℓ φ coreLen L' evalSpace evalCost)) :
    MeetsContract w p proc
      (selectRebuildLevelNoRoomContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, hGEcap,
    hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
  have hhd0 : mem loc.hb = size := by simpa using hat.1 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hmd : mloc.d = C.d := hmeta.1
  have hmD : mem (mloc.metaBase + smDOff) = mloc.d := hmeta.2.2.1
  have htabL := hmeta.2.2.2.1 lvl hlvlD
  have hDG := hmeta.2.2.2.2.2.1 lvl hlvlD
  have hDdisj := hdisj.2.2.2.1 lvl (by omega)
  have hGEeCap : ∀ e ∈ (C.G lvl).E, e < mloc.eCap lvl := hDG.2.2.1
  have hGm : mem (mloc.GPtr lvl + dgMOff) = (C.G lvl).E.card := hDG.2.2.2.2.2.2.1
  obtain ⟨eL, heLlen, _, heLmem, heLAt, _⟩ := hDG.2.2.2.2.2.2.2.2.2.2.2.2.1
  change eL.length = (C.G lvl).E.card at heLlen
  set oldCand := levelCandCount mem loc lvl
  have hspDef : selectRebuildLevelSpace oldCand (C.G lvl).E.card loc.cap loc.Lk evalSpace =
      heapClearLevelSpace oldCand loc.cap loc.Lk +
        selectProcessListSpace (C.G lvl).E.card loc.cap loc.Lk evalSpace := rfl
  have hDSize : dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl) =
      4 + 7 * mloc.vCap lvl + 9 * mloc.eCap lvl := rfl
  have hmSize : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  have hmdW : mloc.d < 2 ^ w := by have := hdisj.2.1; omega
  have hmd1W : mloc.d + 1 < 2 ^ w := by have := hdisj.2.1; omega
  have hGPtrW : mloc.GPtr lvl < 2 ^ w := by have := hDdisj.1; omega
  have hvCapW : mloc.vCap lvl < 2 ^ w := by have := hDdisj.1; omega
  have heCapW : mloc.eCap lvl < 2 ^ w := by have := hDdisj.1; omega
  apply runs_start_le
  dsimp only [startState]
  unfold selectRebuildLevelBody
  simp only [smDOff, smTableOff]
  refine runs_seq_call_flat hClear (vs := [loc.hb, lvl, scratch]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨lvl, scratch, size, rfl, hw16, hendLe, by omega, hat, hz,
      by change scratch + heapClearLevelSpace oldCand _ _ < 2 ^ w; omega⟩
  · intro sc1 mem1 pos1 hp1
    obtain ⟨hlo1, hhi1, hcntLe1, hat1, hz1, hclr1, hoth1, hfr1_raw⟩ := hp1
    simp only [List.getD_cons_zero, List.getD_cons_succ, hhd0] at hlo1 hhi1 hcntLe1 hat1 hz1 hclr1 hoth1 hfr1_raw
    change sc1 ≤ scratch + heapClearLevelSpace oldCand loc.cap loc.Lk at hhi1
    change oldCand ≤ size at hcntLe1
    change SelectHeapAt mem1 loc h (size - oldCand) at hat1
    have hfr1_out : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem1 a = mem a :=
      fun a ha hout => hfr1_raw a ha (hout.imp id fun h => by
        have hend := loc.endAddr_eq; unfold selectHeapSize shHdrSize at hend
        unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev
          SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr
          SelectHeapLoc.arrPtr shHdrSize
        omega)
    have hsc1W : sc1 < 2 ^ w := by omega
    have hhd1 : mem1 loc.hb = size - oldCand := by simpa using hat1.1 0 (by simp)
    have hmeta1 : SelectLevelMetaAt mem1 mloc h P C g ℓ φ coreLen := hmetaFr mem1 hfr1_out
    have hmetaFr1 : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem1 a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
      fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr1_out a ha hout)
    have hm1_meta (a : ℕ) (ha1 : mloc.metaBase ≤ a) (ha2 : a < mloc.metaBase + selectLevelMetaSize mloc.d) :
        mem1 a = mem a :=
      hfr1_out a (by have := hdisj.2.1; omega) (by rcases hdisj.2.2.1 with h1 | h2 <;> omega)
    have hm1_G (a : ℕ) (ha1 : mloc.GPtr lvl ≤ a)
        (ha2 : a < mloc.GPtr lvl + dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl)) :
        mem1 a = mem a :=
      hfr1_out a (by have := hDdisj.1; omega) (by rcases hDdisj.2.1 with h1 | h2 <;> omega)
    have hm1D : mem1 (mloc.metaBase + 1) = mloc.d :=
      (hm1_meta _ (by omega) (by omega)).trans (by simpa [smDOff] using hmD)
    have hGP1 : mem1 (mloc.metaBase + 2 + lvl) = mloc.GPtr lvl := by
      have := htabL.1; simp only [smEntryAddr, smTableOff, Nat.zero_mul] at this
      exact (hm1_meta _ (by omega) (by omega)).trans this
    have hvC1 : mem1 (mloc.metaBase + 2 + (mloc.d + 1 + lvl)) = mloc.vCap lvl := by
      have := htabL.2.1; simp only [smEntryAddr, smTableOff, Nat.one_mul, Nat.add_assoc] at this
      exact (hm1_meta _ (by omega) (by omega)).trans (by simpa [Nat.add_assoc] using this)
    have heC1 : mem1 (mloc.metaBase + 2 + (2 * (mloc.d + 1) + lvl)) = mloc.eCap lvl := by
      have := htabL.2.2.1; simp only [smEntryAddr, smTableOff, Nat.add_assoc] at this
      exact (hm1_meta _ (by omega) (by omega)).trans (by simpa [Nat.add_assoc] using this)
    have hm1Gm : mem1 (mloc.GPtr lvl + 3) = (C.G lvl).E.card :=
      (hm1_G _ (by omega) (by omega)).trans (by simpa [dgMOff] using hGm)
    have heLLeEcap : (C.G lvl).E.card ≤ mloc.eCap lvl := by
      have hsub : (C.G lvl).E ⊆ Finset.range (mloc.eCap lvl) := fun e he =>
        Finset.mem_range.mpr (hGEeCap e he)
      exact (Finset.card_le_card hsub).trans (by simp)
    have heLAt1 : ListAt mem1 (mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl) eL := fun j hj =>
      (hm1_G _ (by omega) (by rw [heLlen] at hj; omega)).trans (heLAt j hj)
    have hMetaEndW : mloc.metaBase + selectLevelMetaSize mloc.d < 2 ^ w := by have := hdisj.2.1; omega
    have hGEndW : mloc.GPtr lvl + dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl) < 2 ^ w := by have := hDdisj.1; omega
    have hEListW : mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl < 2 ^ w := by omega
    have hGmW : (C.G lvl).E.card < 2 ^ w := by omega
    refine runs_seq_assign_flat (v := mloc.d) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.d + 1) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr lvl) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.vCap lvl) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.eCap lvl) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := (C.G lvl).E.card) (by eval_expr) ?_
    refine runs_seq_assign_flat (v := mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl) (by eval_expr) ?_
    refine runs_seq_call_flat (hList eL)
      (vs := [loc.hb, mloc.metaBase, lvl, mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl,
        eL.length, 0, sc1])
      (by simp [evalArgs, Expr.eval, heLlen]) (by wram_words) ?_ ?_
    · exact ⟨lvl, mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl, 0, sc1, size - oldCand,
        rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD, Nat.zero_le _, by have := hDdisj.1; rw [heLlen]; omega,
        by rcases hDdisj.2.1 with h1 | h2 <;> (rw [heLlen]; omega), heLAt1,
        fun e he => ⟨hGEcap e ((heLmem e).mp he), hGEeCap e ((heLmem e).mp he)⟩,
        hat1, hmeta1, selectMetaDisjoint_mono hdisj hlo1,
        hmetaFr1, hz1, by simp only [Nat.sub_zero, heLlen]; omega⟩
    · intro ret mem2 pos2 hp2
      obtain ⟨hlo2, hhi2, ⟨sz2, hat2, hsz2⟩, ⟨hmeta2, hfr2⟩, hz2, hin2, hout2⟩ := hp2
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, heLlen, hhd1] at hlo2 hhi2 hsz2 hin2 hout2 hfr2
      have hretW : ret < 2 ^ w := by omega
      have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
        fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1_out a ha hout)
      refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · dsimp only [selectRebuildLevelNoRoomContract, selectRebuildLevelContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhd0]
        refine ⟨by omega, by change ret ≤ scratch + selectRebuildLevelSpace oldCand _ _ _ _; omega,
          ⟨sz2, hat2, by change sz2 ≤ (size - oldCand) + _; omega⟩, ⟨hmeta2, hfrOut⟩, hz2, ?_, ?_⟩
        · refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
          · by_cases heG : e ∈ eL
            · by_contra hnc; exact ((hin2 e heG).2 hnc).1 ⟨hnz, hl⟩
            · obtain ⟨k1, k2, _, _⟩ := hout2 e heCap heG
              have hnz1 : mem1 (loc.posPtr + e) ≠ 0 := k1.mp hnz
              have hl1 : mem1 (loc.lvlPtr + e) = lvl := k2.symm.trans hl
              by_cases h0 : mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = lvl
              · exact (hnz1 (hclr1 e heCap h0.1 h0.2)).elim
              · obtain ⟨g1, g2, _, _⟩ := hoth1 e heCap h0
                exact (h0 ⟨g1.mp hnz1, g2.symm.trans hl1⟩).elim
          · have heG : e ∈ (C.G lvl).E := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
            exact ⟨hGEcap e heG, (hin2 e ((heLmem e).mpr heG)).1 he⟩
        · intro e' he' hnc
          refine ⟨fun h0orL => ?_, fun hnz0 hne0 => ?_⟩
          · have h1zero : mem1 (loc.posPtr + e') = 0 := by
              rcases h0orL with h0 | hl
              · by_contra hnz1
                have hnot : ¬ (mem (loc.posPtr + e') ≠ 0 ∧ mem (loc.lvlPtr + e') = lvl) := fun h => h.1 h0
                exact ((hoth1 e' he' hnot).1.mp hnz1) h0
              · by_cases hnz0 : mem (loc.posPtr + e') ≠ 0
                · exact hclr1 e' he' hnz0 hl
                · push Not at hnz0
                  by_contra hnz1
                  have hnot : ¬ (mem (loc.posPtr + e') ≠ 0 ∧ mem (loc.lvlPtr + e') = lvl) := fun h => h.1 hnz0
                  exact ((hoth1 e' he' hnot).1.mp hnz1) hnz0
            by_cases heG : e' ∈ eL
            · exact ((hin2 e' heG).2 hnc).2.1 h1zero
            · by_contra hnz2; exact ((hout2 e' he' heG).1.mp hnz2) h1zero
          · have hnot : ¬ (mem (loc.posPtr + e') ≠ 0 ∧ mem (loc.lvlPtr + e') = lvl) := fun h => hne0 h.2
            obtain ⟨g1, g2, g3, g4⟩ := hoth1 e' he' hnot
            by_cases heG : e' ∈ eL
            · obtain ⟨k1, k2, k3, k4⟩ := ((hin2 e' heG).2 hnc).2.2.1 (g1.mpr hnz0) (g2.symm ▸ hne0)
              exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
            · obtain ⟨k1, k2, k3, k4⟩ := hout2 e' he' heG
              exact ⟨k1.mpr (g1.mpr hnz0), k2.trans g2, k3.trans g3, k4.trans g4⟩
      · simp only [selectRebuildLevelNoRoomContract, selectRebuildLevelContract,
          heapClearLevelContract, selectProcessListNoRoomContract, selectProcessListContract,
          selectRebuildLevelCost, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero,
          heLlen, Expr.size, argsSize]
        omega

private lemma levelCandCount_le_after_rebuild_nr {mem mem' : ℕ → ℕ} {loc : SelectHeapLoc}
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

/-- `selectRebuildSuffixBody` meets `selectRebuildSuffixNoRoomContract` with no capacity-slack premise. -/
theorem selectRebuildSuffix_meetsContract_noRoom {w h P self rebuildLvl : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[self]? = some (selectRebuildSuffixBody self rebuildLvl))
    (hReb : MeetsContract w p rebuildLvl
      (selectRebuildLevelNoRoomContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost)) :
    MeetsContract w p self
      (selectRebuildSuffixNoRoomContract w h P loc mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ coreLen evalSpace evalCost) := by
  apply meetsContract_of_rec (fun args _ => C.d + 1 - args.getD 2 0) hp
  intro rem ih args mem pos ω hwords hpre hremEq
  obtain ⟨cur, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hH, hGEcap,
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
    · dsimp only [selectRebuildSuffixNoRoomContract, selectRebuildSuffixContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hIccEmpty,
        Finset.sum_empty, Nat.add_zero, hhd0]
      exact ⟨le_rfl, Nat.le_add_right _ _, ⟨size, hat, le_rfl⟩, ⟨hmeta, fun _ _ _ => rfl⟩, hz,
        fun j hj1 hj2 => by omega,
        fun e' he' _ => ⟨fun h => h.elim id fun hge => by
          by_contra hnz; have := (hat.2.2.1 e' he' hnz).1; omega,
          fun hnz _ => ⟨hnz, trivial, trivial, trivial⟩⟩⟩
    · simp only [selectRebuildSuffixNoRoomContract, selectRebuildSuffixContract, selectRebuildSuffixCost,
        List.getD_cons_zero, List.getD_cons_succ, hIccEmpty, Finset.sum_empty, Expr.size]; omega
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
    refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hgt, show 0 < 2 ^ w by omega])
      (fun h => absurd rfl h) ?_
    intro _
    refine runs_seq_call_flat hReb (vs := [loc.hb, mloc.metaBase, cur, scratch])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨cur, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hle, hGEcap cur le_rfl hle,
        hat, hmeta, hdisj, hmetaFr, hz, by omega⟩
    · intro sc1 mem1 pos1 hp1
      obtain ⟨hlo1, hhi1, ⟨sz1, hat1, hsz1⟩, ⟨hmeta1, hfr1⟩, hz1, hok1, hpres1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ, hhd0] at hlo1 hhi1 hsz1 hok1 hpres1 hfr1
      have hhd1 : mem1 loc.hb = sz1 := by simpa using hat1.1 0 (by simp)
      have hsc1W : sc1 < 2 ^ w := by omega
      have hcur1W : cur + 1 < 2 ^ w := by
        have hend := loc.endAddr_eq; unfold selectHeapSize shHdrSize at hend; omega
      have hcntLe : ∀ j ∈ Finset.Icc (cur + 1) C.d, levelCandCount mem1 loc j ≤ levelCandCount mem loc j :=
        fun j hj => levelCandCount_le_after_rebuild_nr (by simp at hj; omega) hok1 hpres1
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
      refine runs_seq_call_flat ih (vs := [loc.hb, mloc.metaBase, cur + 1, C.d, sc1])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨cur + 1, sc1, sz1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hH,
          fun j hj1 hj2 => hGEcap j (by omega) hj2, hat1, hmeta1,
          selectMetaDisjoint_mono hdisj hlo1, hmetaFr1, hz1, by omega⟩,
          by change C.d + 1 - (cur + 1) < C.d + 1 - cur; omega⟩
      · intro ret mem2 pos2 hp2
        obtain ⟨hlo2, hhi2, ⟨sz2, hat2, hsz2⟩, ⟨hmeta2, hfr2⟩, hz2, hok2, hpres2⟩ := hp2
        simp only [List.getD_cons_zero, List.getD_cons_succ, hhd1] at hlo2 hhi2 hsz2 hok2 hpres2 hfr2
        have hretW : ret < 2 ^ w := by omega
        have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
          fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1 a ha hout)
        have hcandDisj : ∀ e ∈ (C.activeCore cur).E \ (C.activeS cur).E,
            ∀ j, cur + 1 ≤ j → j ≤ C.d → e ∉ (C.activeCore j).E \ (C.activeS j).E := by
          intro e he j hj1 hj2 hej
          have hEq := C.level_unique_of_mem_activeCore_diff hH hle hj2 he hej
          omega
        refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · dsimp only [selectRebuildSuffixNoRoomContract, selectRebuildSuffixContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhd0]
          refine ⟨by omega, by omega, ⟨sz2, hat2, by omega⟩, ⟨hmeta2, hfrOut⟩, hz2, ?_, ?_⟩
          · intro j hj1 hj2
            by_cases hjEq : j = cur
            · subst j
              refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
              · by_cases hinSuf : ∃ k, cur + 1 ≤ k ∧ k ≤ C.d ∧ e ∈ (C.activeCore k).E \ (C.activeS k).E
                · obtain ⟨k, hk1, hk2, hek⟩ := hinSuf
                  have hlK := ((hok2 k hk1 hk2).2 e hek).2.2.1; omega
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
        · simp only [Contract.below, selectRebuildSuffixNoRoomContract, selectRebuildSuffixContract,
            selectRebuildLevelNoRoomContract, selectRebuildLevelContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega

end MinCostFlow.MinRatio
