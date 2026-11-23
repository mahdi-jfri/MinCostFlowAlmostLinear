module

public import MinCostFlow.MinRatio.SelectRebuildNoRoom
public import MinCostFlow.MinRatio.SelectNonRebuiltOps
import WordRAM.Tactic

/-!
# Capacity-slack-free `selectUpdateLevel` and Branch-A `B.g0Ptr` range copy (`SelectUpdateLevelNoRoom`)

Supplies two helper contracts for the select-maintenance part of `Update`:

1. **Capacity-slack-free `selectUpdateLevel`:**
   `selectUpdateLevelNoRoomContract` drops `size + L.totalLen ≤ loc.cap` from
   `selectUpdateLevelContract` (`WireSelectUpdateLevel.lean`), keeping the exact same postcondition
   and cost (`selectUpdateLevelCost`). `selectUpdateLevel_meetsContract_noRoom` proves it for the
   unchanged `selectUpdateLevelBody` via `selectProcessList_meetsContract_noRoom`
   (`SelectRebuildNoRoom.lean`).
2. **Branch-A `B.g0Ptr` range copy (`selCopyG0RangeBody`):**
   After a level-`0` rebuild (Branch A), the live internal edges of `G_0'` are `0, …, mNew - 1`
   mapped by `invPtr` into external indices `< m`. `selCopyG0RangeBody` copies `gExt[invPtr[e]]`
   into `g0Ptr[e]` for `e = 0 .. mNew - 1` with zero scratch and cost `mNew * (18 * Lk + 60) + 20`,
   updating `D.E0` and `D.g` in `SelBlocksDataAt` (`selCopyG0Range_setG0`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Capacity-slack-free `selectUpdateLevelNoRoomContract` -/

/-- Capacity-slack-free variant of `selectUpdateLevelContract` (drops `size + L.totalLen ≤ loc.cap`). -/
def selectUpdateLevelNoRoomContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (L : LevelDiffLists) (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl diffBase scratch size,
      args = [loc.hb, mloc.metaBase, lvl, diffBase, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      lvl ≤ C.d ∧
      LevelDiffListsAt mem diffBase L ∧
      LevelDiffListsDisjoint mem diffBase L loc scratch ∧
      (∀ e ∈ L.allTouched, e < loc.cap ∧ e < mloc.eCap lvl) ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectUpdateLevelSpace L loc.cap loc.Lk evalSpace < 2 ^ w
  post := (selectUpdateLevelContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost).post
  cost := (selectUpdateLevelContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost).cost

/-! ## 2. Branch-A `B.g0Ptr` range copy (`selCopyG0RangeBody`) -/

/-- Copy `gExt[invPtr[e]]` (`Lk` limbs) into `g0Ptr[e]` for every `e ∈ [0, mNew)`.
Arguments: `[gExt, invPtr, g0Ptr, mNew, Lk]` (`reg 0..4`). -/
def selCopyG0RangeBody (copyTo : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 3)
    (.assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
     .call 7 copyTo
       [.bin .add (.reg 0) (.bin .mul (.reg 6) (.reg 4)),
        .bin .add (.reg 2) (.bin .mul (.reg 5) (.reg 4)), .reg 4]) ;;
  .ret (.const 0)

theorem selCopyG0RangeBody_noRand (copyTo : ℕ) : (selCopyG0RangeBody copyTo).NoRand := by
  simp [selCopyG0RangeBody, forRange, forUp, Stmt.NoRand]

/-- Contract for `selCopyG0RangeBody copyTo` copying `mNew` consecutive level-0 gradients
`0, …, mNew - 1` from external vector `gExt` via `invPtr` into `g0Ptr`. -/
def selCopyG0RangeContract (w m eCap mNew : ℕ) : Contract where
  pre args mem :=
    ∃ gExt invPtr g0Ptr Lk,
      args = [gExt, invPtr, g0Ptr, mNew, Lk] ∧
      1 < 2 ^ w ∧ 0 < Lk ∧ mNew ≤ eCap ∧
      (∀ e < mNew, mem (invPtr + e) < m) ∧
      gExt + m * Lk < 2 ^ w ∧ invPtr + eCap < 2 ^ w ∧ g0Ptr + eCap * Lk < 2 ^ w ∧
      (gExt + m * Lk ≤ g0Ptr ∨ g0Ptr + eCap * Lk ≤ gExt) ∧
      (invPtr + eCap ≤ g0Ptr ∨ g0Ptr + eCap * Lk ≤ invPtr) ∧
      (∀ e < mNew, ∀ t < Lk, mem (gExt + mem (invPtr + e) * Lk + t) < 2 ^ w)
  post args mem ret out :=
    ∃ gExt invPtr g0Ptr Lk,
      args = [gExt, invPtr, g0Ptr, mNew, Lk] ∧ ret = 0 ∧
      (∀ e < mNew, ∀ t < Lk, out (g0Ptr + e * Lk + t) = mem (gExt + mem (invPtr + e) * Lk + t)) ∧
      (∀ a, a < g0Ptr ∨ g0Ptr + eCap * Lk ≤ a → out a = mem a)
  cost args _ :=
    let Lk := args.getD 4 0
    mNew * (18 * Lk + 60) + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

private lemma mul_add_lt_mul_nr {e c L i : ℕ} (he : e < c) (hi : i < L) :
    e * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at this
  omega

private lemma entry_disj_of_ne_nr {e1 e2 Lk t : ℕ} (hne : e1 ≠ e2) (ht : t < Lk) :
    e1 * Lk + t < e2 * Lk ∨ e2 * Lk + Lk ≤ e1 * Lk + t := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at this
    omega
  · right
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at this
    omega

private lemma combine_list_post_nr {loc : SelectHeapLoc} {h lvl : ℕ}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {mem0 mem1 mem2 : ℕ → ℕ} {A B : List ℕ}
    (hA_bd : ∀ e ∈ A, e < loc.cap) (hB_bd : ∀ e ∈ B, e < loc.cap)
    (hA_in : ∀ e ∈ A,
      (e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E →
        mem1 (loc.posPtr + e) ≠ 0 ∧ mem1 (loc.lvlPtr + e) = lvl ∧
        SelectKeyRepresents (loc.readNum mem1 h e) (loc.readDen mem1 h e)
          (walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)) (C.wlenAt ℓ lvl e)) ∧
      (e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
        ¬ (mem1 (loc.posPtr + e) ≠ 0 ∧ mem1 (loc.lvlPtr + e) = lvl) ∧
        (mem0 (loc.posPtr + e) = 0 → mem1 (loc.posPtr + e) = 0) ∧
        (mem0 (loc.posPtr + e) ≠ 0 → mem0 (loc.lvlPtr + e) ≠ lvl →
          mem1 (loc.posPtr + e) ≠ 0 ∧ mem1 (loc.lvlPtr + e) = mem0 (loc.lvlPtr + e) ∧
          loc.readNum mem1 h e = loc.readNum mem0 h e ∧
          loc.readDen mem1 h e = loc.readDen mem0 h e) ∧
        (mem0 (loc.posPtr + e) ≠ 0 → mem0 (loc.lvlPtr + e) = lvl →
          mem1 (loc.posPtr + e) = 0)))
    (hA_out : ∀ e' < loc.cap, e' ∉ A →
      (mem1 (loc.posPtr + e') ≠ 0 ↔ mem0 (loc.posPtr + e') ≠ 0) ∧
      mem1 (loc.lvlPtr + e') = mem0 (loc.lvlPtr + e') ∧
      loc.readNum mem1 h e' = loc.readNum mem0 h e' ∧
      loc.readDen mem1 h e' = loc.readDen mem0 h e')
    (hB_in : ∀ e ∈ B,
      (e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E →
        mem2 (loc.posPtr + e) ≠ 0 ∧ mem2 (loc.lvlPtr + e) = lvl ∧
        SelectKeyRepresents (loc.readNum mem2 h e) (loc.readDen mem2 h e)
          (walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)) (C.wlenAt ℓ lvl e)) ∧
      (e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
        ¬ (mem2 (loc.posPtr + e) ≠ 0 ∧ mem2 (loc.lvlPtr + e) = lvl) ∧
        (mem1 (loc.posPtr + e) = 0 → mem2 (loc.posPtr + e) = 0) ∧
        (mem1 (loc.posPtr + e) ≠ 0 → mem1 (loc.lvlPtr + e) ≠ lvl →
          mem2 (loc.posPtr + e) ≠ 0 ∧ mem2 (loc.lvlPtr + e) = mem1 (loc.lvlPtr + e) ∧
          loc.readNum mem2 h e = loc.readNum mem1 h e ∧
          loc.readDen mem2 h e = loc.readDen mem1 h e) ∧
        (mem1 (loc.posPtr + e) ≠ 0 → mem1 (loc.lvlPtr + e) = lvl →
          mem2 (loc.posPtr + e) = 0)))
    (hB_out : ∀ e' < loc.cap, e' ∉ B →
      (mem2 (loc.posPtr + e') ≠ 0 ↔ mem1 (loc.posPtr + e') ≠ 0) ∧
      mem2 (loc.lvlPtr + e') = mem1 (loc.lvlPtr + e') ∧
      loc.readNum mem2 h e' = loc.readNum mem1 h e' ∧
      loc.readDen mem2 h e' = loc.readDen mem1 h e') :
    (∀ e ∈ A ++ B,
      (e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E →
        mem2 (loc.posPtr + e) ≠ 0 ∧ mem2 (loc.lvlPtr + e) = lvl ∧
        SelectKeyRepresents (loc.readNum mem2 h e) (loc.readDen mem2 h e)
          (walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)) (C.wlenAt ℓ lvl e)) ∧
      (e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
        ¬ (mem2 (loc.posPtr + e) ≠ 0 ∧ mem2 (loc.lvlPtr + e) = lvl) ∧
        (mem0 (loc.posPtr + e) = 0 → mem2 (loc.posPtr + e) = 0) ∧
        (mem0 (loc.posPtr + e) ≠ 0 → mem0 (loc.lvlPtr + e) ≠ lvl →
          mem2 (loc.posPtr + e) ≠ 0 ∧ mem2 (loc.lvlPtr + e) = mem0 (loc.lvlPtr + e) ∧
          loc.readNum mem2 h e = loc.readNum mem0 h e ∧
          loc.readDen mem2 h e = loc.readDen mem0 h e) ∧
        (mem0 (loc.posPtr + e) ≠ 0 → mem0 (loc.lvlPtr + e) = lvl →
          mem2 (loc.posPtr + e) = 0))) ∧
    (∀ e' < loc.cap, e' ∉ A ++ B →
      (mem2 (loc.posPtr + e') ≠ 0 ↔ mem0 (loc.posPtr + e') ≠ 0) ∧
      mem2 (loc.lvlPtr + e') = mem0 (loc.lvlPtr + e') ∧
      loc.readNum mem2 h e' = loc.readNum mem0 h e' ∧
      loc.readDen mem2 h e' = loc.readDen mem0 h e') := by
  refine ⟨fun e he => ?_, fun e' he' hnot => ?_⟩
  · rw [List.mem_append] at he
    by_cases hB : e ∈ B
    · refine ⟨(hB_in e hB).1, fun hnc => ⟨((hB_in e hB).2 hnc).1, fun h0 => ?_, fun hnz hne => ?_, fun hnz hl => ?_⟩⟩
      · by_cases hA : e ∈ A
        · exact ((hB_in e hB).2 hnc).2.1 (((hA_in e hA).2 hnc).2.1 h0)
        · have h01 : mem1 (loc.posPtr + e) = 0 := by
            by_contra hnz1; exact ((hA_out e (hB_bd e hB) hA).1.mp hnz1) h0
          exact ((hB_in e hB).2 hnc).2.1 h01
      · by_cases hA : e ∈ A
        · obtain ⟨g1, g2, g3, g4⟩ := ((hA_in e hA).2 hnc).2.2.1 hnz hne
          obtain ⟨k1, k2, k3, k4⟩ := ((hB_in e hB).2 hnc).2.2.1 g1 (g2.symm ▸ hne)
          exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
        · obtain ⟨g1, g2, g3, g4⟩ := hA_out e (hB_bd e hB) hA
          obtain ⟨k1, k2, k3, k4⟩ := ((hB_in e hB).2 hnc).2.2.1 (g1.mpr hnz) (g2.symm ▸ hne)
          exact ⟨k1, k2.trans g2, k3.trans g3, k4.trans g4⟩
      · by_cases hA : e ∈ A
        · exact ((hB_in e hB).2 hnc).2.1 (((hA_in e hA).2 hnc).2.2.2 hnz hl)
        · obtain ⟨g1, g2, _, _⟩ := hA_out e (hB_bd e hB) hA
          exact ((hB_in e hB).2 hnc).2.2.2 (g1.mpr hnz) (g2.trans hl)
    · have hA : e ∈ A := he.resolve_right hB
      obtain ⟨k1, k2, k3, k4⟩ := hB_out e (hA_bd e hA) hB
      refine ⟨fun hc => ?_, fun hnc => ⟨?_, fun h0 => ?_, fun hnz hne => ?_, fun hnz hl => ?_⟩⟩
      · obtain ⟨g1, g2, g3⟩ := (hA_in e hA).1 hc
        exact ⟨k1.mpr g1, k2.trans g2, by rw [k3, k4]; exact g3⟩
      · rintro ⟨hnz2, hl2⟩; exact ((hA_in e hA).2 hnc).1 ⟨k1.mp hnz2, k2.symm.trans hl2⟩
      · by_contra hnz2; exact (k1.mp hnz2) (((hA_in e hA).2 hnc).2.1 h0)
      · obtain ⟨g1, g2, g3, g4⟩ := ((hA_in e hA).2 hnc).2.2.1 hnz hne
        exact ⟨k1.mpr g1, k2.trans g2, k3.trans g3, k4.trans g4⟩
      · by_contra hnz2; exact (k1.mp hnz2) (((hA_in e hA).2 hnc).2.2.2 hnz hl)
  · rw [List.mem_append, not_or] at hnot
    obtain ⟨g1, g2, g3, g4⟩ := hA_out e' he' hnot.1
    obtain ⟨k1, k2, k3, k4⟩ := hB_out e' he' hnot.2
    exact ⟨k1.trans g1, k2.trans g2, k3.trans g3, k4.trans g4⟩

/-- `selectUpdateLevelBody` meets `selectUpdateLevelNoRoomContract` with no capacity-slack premise. -/
theorem selectUpdateLevel_meetsContract_noRoom {w h P entry procList : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {L : LevelDiffLists} {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[entry]? = some (selectUpdateLevelBody procList))
    (hList : ∀ L' : List ℕ, MeetsContract w p procList
      (selectProcessListNoRoomContract w h P loc mloc C g ℓ φ coreLen L' evalSpace evalCost)) :
    MeetsContract w p entry
      (selectUpdateLevelNoRoomContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, diffBase, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD,
    hLAt, hLDisj, hLbd, hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
  obtain ⟨hLenUG, hAtUG, hLenFD, hAtFD, hLenUS, hAtUS, hLenRE, hAtRE⟩ := hLAt
  obtain ⟨hdSc, hdDisj, hp0Sc, hp0Disj, hp2Sc, hp2Disj, hp4Sc, hp4Disj, hp6Sc, hp6Disj⟩ := hLDisj
  have hhd0 : mem loc.hb = size := by simpa using hat.1 0 (by simp)
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hdbw : diffBase < 2 ^ w := hwords diffBase (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  have hspEq : selectUpdateLevelSpace L loc.cap loc.Lk evalSpace =
      selectProcessListSpace L.uG.length loc.cap loc.Lk evalSpace +
      selectProcessListSpace L.fDel.length loc.cap loc.Lk evalSpace +
      selectProcessListSpace L.uS.length loc.cap loc.Lk evalSpace +
      selectProcessListSpace L.reemb.length loc.cap loc.Lk evalSpace := by
    unfold selectUpdateLevelSpace selectProcessListSpace LevelDiffLists.totalLen
    simp only [Nat.add_mul]
  have hbdUG : ∀ e ∈ L.uG, e < loc.cap ∧ e < mloc.eCap lvl := fun e he =>
    hLbd e (by simp [LevelDiffLists.allTouched, he])
  have hbdFD : ∀ e ∈ L.fDel, e < loc.cap ∧ e < mloc.eCap lvl := fun e he =>
    hLbd e (by simp [LevelDiffLists.allTouched, he])
  have hbdUS : ∀ e ∈ L.uS, e < loc.cap ∧ e < mloc.eCap lvl := fun e he =>
    hLbd e (by simp [LevelDiffLists.allTouched, he])
  have hbdRE : ∀ e ∈ L.reemb, e < loc.cap ∧ e < mloc.eCap lvl := fun e he =>
    hLbd e (by simp [LevelDiffLists.allTouched, he])
  have htot : L.totalLen = L.uG.length + L.fDel.length + L.uS.length + L.reemb.length := rfl
  have hdbW : ∀ k < 8, diffBase + k < 2 ^ w := fun k hk => by omega
  have hwK : ∀ k < 8, k < 2 ^ w := fun k hk => by omega
  have hp0W : mem (diffBase + 0) < 2 ^ w := by omega
  have hp2W : mem (diffBase + 2) < 2 ^ w := by omega
  have hp4W : mem (diffBase + 4) < 2 ^ w := by omega
  have hp6W : mem (diffBase + 6) < 2 ^ w := by omega
  have hl0W : L.uG.length < 2 ^ w := by omega
  have hl2W : L.fDel.length < 2 ^ w := by omega
  have hl4W : L.uS.length < 2 ^ w := by omega
  have hl6W : L.reemb.length < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold selectUpdateLevelBody
  refine runs_seq_call_flat (hList L.uG)
    (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 0), L.uG.length, 0, scratch])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 1 (by omega), hdbW 1 (by omega), hLenUG])
    (by wram_words) ?_ ?_
  · exact ⟨lvl, mem (diffBase + 0), 0, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD,
      Nat.zero_le _, hp0Sc, hp0Disj, hAtUG, hbdUG, hat, hmeta, hdisj, hmetaFr, hz,
      by simp only [Nat.sub_zero]; omega⟩
  · intro sc1 mem1 pos1 hp1
    obtain ⟨hlo1, hhi1, ⟨sz1, hat1, hsz1⟩, ⟨hmeta1, hfr1⟩, hz1, hin1, hout1⟩ := hp1
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, hhd0] at hlo1 hhi1 hsz1 hin1 hout1 hfr1
    have hhd1 : mem1 loc.hb = sz1 := by simpa using hat1.1 0 (by simp)
    have hsc1W : sc1 < 2 ^ w := by omega
    have hm1_db (k : ℕ) (hk : k < 8) : mem1 (diffBase + k) = mem (diffBase + k) :=
      hfr1 (diffBase + k) (by omega) (by omega)
    have hAtFD1 : ListAt mem1 (mem (diffBase + 2)) L.fDel := fun j hj =>
      (hfr1 _ (by omega) (by omega)).trans (hAtFD j hj)
    have hmetaFr1 : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem1 a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
      fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr1 a ha hout)
    refine runs_seq_call_flat (hList L.fDel)
      (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 2), L.fDel.length, 0, sc1])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 2 (by omega), hwK 3 (by omega),
            hdbW 2 (by omega), hdbW 3 (by omega), hm1_db 2 (by omega), hm1_db 3 (by omega), hLenFD])
      (by wram_words) ?_ ?_
    · exact ⟨lvl, mem (diffBase + 2), 0, sc1, sz1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD,
        Nat.zero_le _, by omega, hp2Disj, hAtFD1, hbdFD, hat1, hmeta1,
        selectMetaDisjoint_mono hdisj hlo1, hmetaFr1, hz1, by simp only [Nat.sub_zero]; omega⟩
    · intro sc2 mem2 pos2 hp2
      obtain ⟨hlo2, hhi2, ⟨sz2, hat2, hsz2⟩, ⟨hmeta2, hfr2⟩, hz2, hin2, hout2⟩ := hp2
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, hhd1] at hlo2 hhi2 hsz2 hin2 hout2 hfr2
      have hhd2 : mem2 loc.hb = sz2 := by simpa using hat2.1 0 (by simp)
      have hsc2W : sc2 < 2 ^ w := by omega
      have hfr12 : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
        fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1 a ha hout)
      have hm2_db (k : ℕ) (hk : k < 8) : mem2 (diffBase + k) = mem (diffBase + k) :=
        hfr12 (diffBase + k) (by omega) (by omega)
      have hAtUS2 : ListAt mem2 (mem (diffBase + 4)) L.uS := fun j hj =>
        (hfr12 _ (by omega) (by omega)).trans (hAtUS j hj)
      have hmetaFr2 : ∀ m', (∀ a < sc2, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem2 a) →
          SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
        fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr12 a ha hout)
      refine runs_seq_call_flat (hList L.uS)
        (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 4), L.uS.length, 0, sc2])
        (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 4 (by omega), hwK 5 (by omega),
              hdbW 4 (by omega), hdbW 5 (by omega), hm2_db 4 (by omega), hm2_db 5 (by omega), hLenUS])
        (by wram_words) ?_ ?_
      · exact ⟨lvl, mem (diffBase + 4), 0, sc2, sz2, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD,
          Nat.zero_le _, by omega, hp4Disj, hAtUS2, hbdUS, hat2, hmeta2,
          selectMetaDisjoint_mono hdisj (le_trans hlo1 hlo2), hmetaFr2, hz2,
          by simp only [Nat.sub_zero]; omega⟩
      · intro sc3 mem3 pos3 hp3
        obtain ⟨hlo3, hhi3, ⟨sz3, hat3, hsz3⟩, ⟨hmeta3, hfr3⟩, hz3, hin3, hout3⟩ := hp3
        simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, hhd2] at hlo3 hhi3 hsz3 hin3 hout3 hfr3
        have hhd3 : mem3 loc.hb = sz3 := by simpa using hat3.1 0 (by simp)
        have hsc3W : sc3 < 2 ^ w := by omega
        have hfr13 : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem3 a = mem a :=
          fun a ha hout => (hfr3 a (by omega) hout).trans (hfr12 a ha hout)
        have hm3_db (k : ℕ) (hk : k < 8) : mem3 (diffBase + k) = mem (diffBase + k) :=
          hfr13 (diffBase + k) (by omega) (by omega)
        have hAtRE3 : ListAt mem3 (mem (diffBase + 6)) L.reemb := fun j hj =>
          (hfr13 _ (by omega) (by omega)).trans (hAtRE j hj)
        have hmetaFr3 : ∀ m', (∀ a < sc3, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem3 a) →
            SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen :=
          fun m' hm' => hmetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr13 a ha hout)
        refine runs_seq_call_flat (hList L.reemb)
          (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 6), L.reemb.length, 0, sc3])
          (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 6 (by omega), hwK 7 (by omega),
                hdbW 6 (by omega), hdbW 7 (by omega), hm3_db 6 (by omega), hm3_db 7 (by omega), hLenRE])
          (by wram_words) ?_ ?_
        · exact ⟨lvl, mem (diffBase + 6), 0, sc3, sz3, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD,
            Nat.zero_le _, by omega, hp6Disj, hAtRE3, hbdRE, hat3, hmeta3,
            selectMetaDisjoint_mono hdisj (le_trans (le_trans hlo1 hlo2) hlo3), hmetaFr3, hz3,
            by simp only [Nat.sub_zero]; omega⟩
        · intro sc4 mem4 pos4 hp4
          obtain ⟨hlo4, hhi4, ⟨sz4, hat4, hsz4⟩, ⟨hmeta4, hfr4⟩, hz4, hin4, hout4⟩ := hp4
          simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, hhd3] at hlo4 hhi4 hsz4 hin4 hout4 hfr4
          have hsc4W : sc4 < 2 ^ w := by omega
          have hfr14 : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem4 a = mem a :=
            fun a ha hout => (hfr4 a (by omega) hout).trans (hfr13 a ha hout)
          obtain ⟨hc12_in, hc12_out⟩ := combine_list_post_nr (fun e he => (hbdUG e he).1)
            (fun e he => (hbdFD e he).1) hin1 hout1 hin2 hout2
          obtain ⟨hc13_in, hc13_out⟩ := combine_list_post_nr
            (fun e he => by rw [List.mem_append] at he; exact he.elim (fun h => (hbdUG e h).1) (fun h => (hbdFD e h).1))
            (fun e he => (hbdUS e he).1) hc12_in hc12_out hin3 hout3
          obtain ⟨hc14_in, hc14_out⟩ := combine_list_post_nr
            (fun e he => by
              simp only [List.mem_append] at he
              rcases he with (h | h) | h
              · exact (hbdUG e h).1
              · exact (hbdFD e h).1
              · exact (hbdUS e h).1)
            (fun e he => (hbdRE e he).1) hc13_in hc13_out hin4 hout4
          refine WordRAM.runs_ret_le (v := sc4) (by eval_expr) ?_ ?_
          · dsimp only [selectUpdateLevelNoRoomContract, selectUpdateLevelContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhd0]
            exact ⟨by omega, by omega, ⟨sz4, hat4, by omega⟩, ⟨hmeta4, hfr14⟩, hz4,
              hc14_in, hc14_out⟩
          · simp only [selectUpdateLevelNoRoomContract, selectUpdateLevelContract,
              selectProcessListNoRoomContract, selectProcessListContract,
              selectUpdateLevelCost, selectProcessListCost, LevelDiffLists.totalLen,
              List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, Expr.size, argsSize]
            have hmul : (L.uG.length + L.fDel.length + L.uS.length + L.reemb.length) *
                (selectProcessEdgeCost loc.cap loc.Lk evalCost + 40) =
                L.uG.length * (selectProcessEdgeCost loc.cap loc.Lk evalCost + 40) +
                L.fDel.length * (selectProcessEdgeCost loc.cap loc.Lk evalCost + 40) +
                L.uS.length * (selectProcessEdgeCost loc.cap loc.Lk evalCost + 40) +
                L.reemb.length * (selectProcessEdgeCost loc.cap loc.Lk evalCost + 40) := by
              simp only [Nat.add_mul]
            omega

/-- Verification of `selCopyG0RangeBody copyTo`. -/
theorem selCopyG0Range_meetsContract {w m eCap mNew proc copyTo : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selCopyG0RangeBody copyTo))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (selCopyG0RangeContract w m eCap mNew) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨gExt, invPtr, g0Ptr, Lk, rfl, hw1, hLkPos, hmNewLe, hinvLt, hgExtW, hinvW, hg0W,
    hdisjG, hdisjI, hvalW⟩ := hpre
  have hentExt : ∀ e < mNew, mem (invPtr + e) * Lk + Lk ≤ m * Lk := fun e he => by
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt (hinvLt e he))
    rw [Nat.succ_mul] at this; omega
  have hentEnd : ∀ e < mNew, e * Lk + Lk ≤ eCap * Lk := fun e he => by
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt (lt_of_lt_of_le he hmNewLe))
    rw [Nat.succ_mul] at this; omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := .assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
      .call 7 copyTo
        [.bin .add (.reg 0) (.bin .mul (.reg 6) (.reg 4)),
         .bin .add (.reg 2) (.bin .mul (.reg 5) (.reg 4)), .reg 4])
    (P := fun st => st = startState [gExt, invPtr, g0Ptr, mNew, Lk] mem pos)
    (Inv := fun i st => st.regs 0 = gExt ∧ st.regs 1 = invPtr ∧ st.regs 2 = g0Ptr ∧
      st.regs 3 = mNew ∧ st.regs 4 = Lk ∧ st.regs 5 = i ∧
      (∀ e < i, ∀ t < Lk,
        st.mem (g0Ptr + e * Lk + t) = mem (gExt + mem (invPtr + e) * Lk + t)) ∧
      (∀ a, a < g0Ptr ∨ g0Ptr + i * Lk ≤ a → st.mem a = mem a))
    (18 * Lk + 50) 0 mNew (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [startState]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 := hi.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, hdone, hout⟩
      have hExtEnd := hentExt i hi
      have hG0End := hentEnd i hi
      have hiMul : i * Lk ≤ eCap * Lk := Nat.mul_le_mul_right Lk (le_trans hi.le hmNewLe)
      have hreadExt : st.mem (invPtr + i) = mem (invPtr + i) :=
        hout _ (by rcases hdisjI with h | h <;> omega)
      have hsrcKeep : ∀ t < Lk,
          st.mem (gExt + mem (invPtr + i) * Lk + t) = mem (gExt + mem (invPtr + i) * Lk + t) :=
        fun t ht => hout _ (by rcases hdisjG with h | h <;> omega)
      apply runs_start_le
      refine runs_seq_assign_le (v := mem (invPtr + i)) (by eval_expr) ?_
      refine runs_call_le hcopy
        (vs := [gExt + mem (invPtr + i) * Lk, g0Ptr + i * Lk, Lk])
        (by eval_expr) (by wram_words)
        ⟨gExt + mem (invPtr + i) * Lk, g0Ptr + i * Lk, Lk, rfl, hw1, by omega, by omega,
          by rcases hdisjG with h | h <;> [left; right] <;> omega,
          fun t ht => by rw [hsrcKeep t ht]; exact hvalW i hi t ht⟩ ?_
      intro _ mem' pos' hpost
      obtain ⟨_, hcp, hfr⟩ := hpost
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hcp hfr
      refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simp, fun e he t ht => ?_, fun a ha => ?_⟩,
        by simpa using h5⟩, ?_⟩
      · dsimp only
        by_cases hei : e = i
        · subst hei; rw [hcp t ht, hsrcKeep t ht]
        · rw [hfr _ (by rcases entry_disj_of_ne_nr hei ht with h | h <;> [left; right] <;> omega)]
          exact hdone e (by omega) t ht
      · dsimp only
        rw [Nat.succ_mul] at ha
        rw [hfr _ (by omega)]
        exact hout a (by omega)
      · simp only [copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_reg, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil]
        omega)
  apply runs_start_le
  unfold selCopyG0RangeBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, _, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · refine ⟨gExt, invPtr, g0Ptr, Lk, rfl, rfl, hdone, fun a ha => ?_⟩
    have hmMul : mNew * Lk ≤ eCap * Lk := Nat.mul_le_mul_right Lk hmNewLe
    exact hout a (by omega)
  · simp only [selCopyG0RangeContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]
    nlinarith

/-- Updating `B.g0Ptr` via `selCopyG0RangeBody` updates `D.E0 = Finset.range mNew` and `D.g` in
`SelBlocksDataAt` while preserving all other parts. -/
theorem selCopyG0Range_setG0 {w m P pLast gExt invPtr mNew ret : ℕ} {B : SelectBlocksLoc}
    {D : SelBlocksData} {E0' : Finset ℕ} {gExtVal g' : ℕ → ℝ} {mem mem' : ℕ → ℕ}
    (hpost : (selCopyG0RangeContract w m B.eCap mNew).post
      [gExt, invPtr, B.g0Ptr, mNew, B.Lk] mem ret mem')
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hExt : EdgeValuesAt mem gExt 4 B.Lk P (Finset.range m) gExtVal)
    (hmNewLe : mNew ≤ B.eCap)
    (hinvLt : ∀ e < mNew, mem (invPtr + e) < m)
    (hE0' : E0' = Finset.range mNew)
    (hv : ∀ e < mNew, g' e = gExtVal (mem (invPtr + e))) :
    SelBlocksDataAt mem' B P { D with E0 := E0', g := g' } pLast := by
  obtain ⟨_, _, _, _, hargs, _, hcp, hout⟩ := hpost
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, rfl, rfl, -, rfl, -⟩ := hargs
  refine hblk.setG0 (fun a ha => hout a ?_) ⟨fun e he => ?_, fun e he => ?_⟩
  · unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at ha; omega
  · rw [hE0', Finset.mem_range] at he; omega
  · rw [hE0', Finset.mem_range] at he
    have hs := hExt (mem (invPtr + e)) (Finset.mem_range.mpr (hinvLt e he))
    refine ⟨fun t ht => (hcp e he t ht) ▸ hs.1 t ht, ?_⟩
    unfold Num.fixVal
    rw [Num.intVal_congr (hcp e he), hv e he]
    exact hs.2

end MinCostFlow.MinRatio

end
