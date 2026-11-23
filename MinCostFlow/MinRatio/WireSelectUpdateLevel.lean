module

public import MinCostFlow.MinRatio.WireSelectUpdateEdge
import WordRAM.Tactic

/-!
# Verification of `selectUpdateLevelBody` and `selectRebuildLevelBody`

Verifies the per-level Word-RAM key-update procedures from `WireSelectUpdate.lean` (`jtree.tex`,
pages 20–21, 24):
1. `selectUpdateLevel_meetsContract`: verifies `selectUpdateLevelBody` over all four lists of
   `LevelDiffListsAt` in `selectUpdateLevelCost L loc.cap loc.Lk evalCost` steps.
2. `selectUpdateLevel_establishes_levelOk`: uses `touched_covers_level_changes` (Job 2) to prove
   that `selectUpdateLevelBody` restores `SelectHeapLevelOk` at a non-rebuilt level `lvl`.
3. `selectRebuildLevel_meetsContract`: verifies `selectRebuildLevelBody` (`heapClearLevel` +
   `selectProcessList` over `dgEListBase`) in `selectRebuildLevelCost` steps, establishing
   `SelectHeapLevelOk` at `lvl` while monotonically preserving all other levels.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Contracts for `selectUpdateLevel` and `selectRebuildLevel` -/

/-- Memory bounds and heap-disjointness for `LevelDiffListsAt mem diffBase L` below `hi`. -/
def LevelDiffListsDisjoint (mem : ℕ → ℕ) (diffBase : ℕ) (L : LevelDiffLists)
    (loc : SelectHeapLoc) (hi : ℕ) : Prop :=
  diffBase + 8 ≤ hi ∧
  (diffBase + 8 ≤ loc.hb ∨ loc.endAddr ≤ diffBase) ∧
  mem (diffBase + 0) + L.uG.length ≤ hi ∧
  (mem (diffBase + 0) + L.uG.length ≤ loc.hb ∨ loc.endAddr ≤ mem (diffBase + 0)) ∧
  mem (diffBase + 2) + L.fDel.length ≤ hi ∧
  (mem (diffBase + 2) + L.fDel.length ≤ loc.hb ∨ loc.endAddr ≤ mem (diffBase + 2)) ∧
  mem (diffBase + 4) + L.uS.length ≤ hi ∧
  (mem (diffBase + 4) + L.uS.length ≤ loc.hb ∨ loc.endAddr ≤ mem (diffBase + 4)) ∧
  mem (diffBase + 6) + L.reemb.length ≤ hi ∧
  (mem (diffBase + 6) + L.reemb.length ≤ loc.hb ∨ loc.endAddr ≤ mem (diffBase + 6))

/-- Space bound for `selectUpdateLevelBody` on `L : LevelDiffLists`. -/
def selectUpdateLevelSpace (L : LevelDiffLists) (cap Lk evalSpace : ℕ) : ℕ :=
  selectProcessListSpace L.totalLen cap Lk evalSpace

/-- Contract for `selectUpdateLevelBody` (`[hb, metaBase, lvl, diffBase, scratch]`):
processes all four lists of `L` at level `lvl`, updating every edge in `L.allTouched` and
leaving every edge outside `L.allTouched` untouched. -/
def selectUpdateLevelContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
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
      size + L.totalLen ≤ loc.cap ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectUpdateLevelSpace L loc.cap loc.Lk evalSpace < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 2 0
    let scratch := args.getD 4 0
    scratch ≤ ret ∧ ret ≤ scratch + selectUpdateLevelSpace L loc.cap loc.Lk evalSpace ∧
    (∃ size', SelectHeapAt mem' loc h size' ∧ size' ≤ mem loc.hb + L.totalLen) ∧
    SelectMetaFrame mem mem' mloc loc h P scratch C g ℓ φ coreLen ∧
    ZeroFrom mem' ret ∧
    (∀ e ∈ L.allTouched,
      (e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E →
        mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl ∧
        SelectKeyRepresents (loc.readNum mem' h e) (loc.readDen mem' h e)
          (walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)) (C.wlenAt ℓ lvl e)) ∧
      (e ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
        ¬ (mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = lvl) ∧
        (mem (loc.posPtr + e) = 0 → mem' (loc.posPtr + e) = 0) ∧
        (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) ≠ lvl →
          mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) ∧
          loc.readNum mem' h e = loc.readNum mem h e ∧
          loc.readDen mem' h e = loc.readDen mem h e) ∧
        (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = lvl →
          mem' (loc.posPtr + e) = 0))) ∧
    (∀ e' < loc.cap, e' ∉ L.allTouched →
      (mem' (loc.posPtr + e') ≠ 0 ↔ mem (loc.posPtr + e') ≠ 0) ∧
      mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
      loc.readNum mem' h e' = loc.readNum mem h e' ∧
      loc.readDen mem' h e' = loc.readDen mem h e')
  cost _ _ := selectUpdateLevelCost L loc.cap loc.Lk evalCost

/-- Space bound for `selectRebuildLevelBody`. -/
def selectRebuildLevelSpace (oldCand mNew cap Lk evalSpace : ℕ) : ℕ :=
  heapClearLevelSpace oldCand cap Lk + selectProcessListSpace mNew cap Lk evalSpace

/-- Contract for `selectRebuildLevelBody` (`[hb, metaBase, lvl, scratch]`):
clears all old candidates at level `lvl` and scans `(C.G lvl).E` to establish
`SelectHeapLevelOk mem' loc h P C g ℓ lvl`, while preserving every edge previously stored at a
different level `j ≠ lvl` that is not a candidate at `lvl`. -/
def selectRebuildLevelContract (w h P : ℕ) (loc : SelectHeapLoc) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl scratch size,
      args = [loc.hb, mloc.metaBase, lvl, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧ loc.endAddr ≤ scratch ∧
      loc.d = C.d ∧ mloc.Lk = loc.Lk ∧
      lvl ≤ C.d ∧
      (∀ e ∈ (C.G lvl).E, e < loc.cap) ∧
      (size - levelCandCount mem loc lvl) + (C.G lvl).E.card ≤ loc.cap ∧
      SelectHeapAt mem loc h size ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectMetaDisjoint mloc loc scratch ∧
      (∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
        SelectLevelMetaAt m' mloc h P C g ℓ φ coreLen) ∧
      ZeroFrom mem scratch ∧
      scratch + selectRebuildLevelSpace (levelCandCount mem loc lvl) (C.G lvl).E.card
        loc.cap loc.Lk evalSpace < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 2 0
    let scratch := args.getD 3 0
    let oldCand := levelCandCount mem loc lvl
    scratch ≤ ret ∧
    ret ≤ scratch + selectRebuildLevelSpace oldCand (C.G lvl).E.card loc.cap loc.Lk evalSpace ∧
    (∃ size', SelectHeapAt mem' loc h size' ∧ size' ≤ (mem loc.hb - oldCand) + (C.G lvl).E.card) ∧
    SelectMetaFrame mem mem' mloc loc h P scratch C g ℓ φ coreLen ∧
    ZeroFrom mem' ret ∧
    SelectHeapLevelOk mem' loc h P C g ℓ lvl ∧
    (∀ e' < loc.cap, e' ∉ (C.activeCore lvl).E \ (C.activeS lvl).E →
      (mem (loc.posPtr + e') = 0 ∨ mem (loc.lvlPtr + e') = lvl → mem' (loc.posPtr + e') = 0) ∧
      (mem (loc.posPtr + e') ≠ 0 → mem (loc.lvlPtr + e') ≠ lvl →
        mem' (loc.posPtr + e') ≠ 0 ∧ mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
        loc.readNum mem' h e' = loc.readNum mem h e' ∧
        loc.readDen mem' h e' = loc.readDen mem h e'))
  cost args mem :=
    let lvl := args.getD 2 0
    selectRebuildLevelCost (levelCandCount mem loc lvl) (C.G lvl).E.card loc.cap loc.Lk evalCost

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 2. Helpers and `selectUpdateLevel_meetsContract` -/

theorem selectMetaDisjoint_mono {mloc : SelectLevelMetaLoc} {loc : SelectHeapLoc} {hi hi' : ℕ}
    (h : SelectMetaDisjoint mloc loc hi) (hle : hi ≤ hi') :
    SelectMetaDisjoint mloc loc hi' :=
  ⟨h.1, le_trans h.2.1 hle, h.2.2.1, fun j hj => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := h.2.2.2.1 j hj
    exact ⟨le_trans a1 hle, a2, le_trans a3 hle, a4, fun hjlt => ⟨le_trans (a5 hjlt).1 hle, (a5 hjlt).2⟩⟩,
    h.2.2.2.2.mono hle⟩

private lemma combine_list_post {loc : SelectHeapLoc} {h lvl : ℕ}
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

/-- `selectUpdateLevelBody` meets `selectUpdateLevelContract` in `selectUpdateLevelCost` steps. -/
theorem selectUpdateLevel_meetsContract {w h P entry procList : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {L : LevelDiffLists} {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[entry]? = some (selectUpdateLevelBody procList))
    (hList : ∀ L' : List ℕ, MeetsContract w p procList
      (selectProcessListContract w h P loc mloc C g ℓ φ coreLen L' evalSpace evalCost)) :
    MeetsContract w p entry
      (selectUpdateLevelContract w h P loc mloc C g ℓ φ coreLen L evalSpace evalCost) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, diffBase, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD,
    hLAt, hLDisj, hLbd, hszRoom, hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
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
  -- Call 1: `L.uG`
  refine runs_seq_call_flat (hList L.uG)
    (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 0), L.uG.length, 0, scratch])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 1 (by omega), hdbW 1 (by omega), hLenUG])
    (by wram_words) ?_ ?_
  · exact ⟨lvl, mem (diffBase + 0), 0, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD,
      Nat.zero_le _, hp0Sc, hp0Disj, hAtUG, hbdUG, by omega, hat, hmeta, hdisj, hmetaFr, hz,
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
    -- Call 2: `L.fDel`
    refine runs_seq_call_flat (hList L.fDel)
      (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 2), L.fDel.length, 0, sc1])
      (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 2 (by omega), hwK 3 (by omega),
            hdbW 2 (by omega), hdbW 3 (by omega), hm1_db 2 (by omega), hm1_db 3 (by omega), hLenFD])
      (by wram_words) ?_ ?_
    · exact ⟨lvl, mem (diffBase + 2), 0, sc1, sz1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD,
        Nat.zero_le _, by omega, hp2Disj, hAtFD1, hbdFD, by omega, hat1, hmeta1,
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
      -- Call 3: `L.uS`
      refine runs_seq_call_flat (hList L.uS)
        (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 4), L.uS.length, 0, sc2])
        (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 4 (by omega), hwK 5 (by omega),
              hdbW 4 (by omega), hdbW 5 (by omega), hm2_db 4 (by omega), hm2_db 5 (by omega), hLenUS])
        (by wram_words) ?_ ?_
      · exact ⟨lvl, mem (diffBase + 4), 0, sc2, sz2, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD,
          Nat.zero_le _, by omega, hp4Disj, hAtUS2, hbdUS, by omega, hat2, hmeta2,
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
        -- Call 4: `L.reemb`
        refine runs_seq_call_flat (hList L.reemb)
          (vs := [loc.hb, mloc.metaBase, lvl, mem (diffBase + 6), L.reemb.length, 0, sc3])
          (by simp [evalArgs, Expr.eval, BinOp.eval, hwK 6 (by omega), hwK 7 (by omega),
                hdbW 6 (by omega), hdbW 7 (by omega), hm3_db 6 (by omega), hm3_db 7 (by omega), hLenRE])
          (by wram_words) ?_ ?_
        · exact ⟨lvl, mem (diffBase + 6), 0, sc3, sz3, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD,
            Nat.zero_le _, by omega, hp6Disj, hAtRE3, hbdRE, by omega, hat3, hmeta3,
            selectMetaDisjoint_mono hdisj (le_trans (le_trans hlo1 hlo2) hlo3), hmetaFr3, hz3,
            by simp only [Nat.sub_zero]; omega⟩
        · intro sc4 mem4 pos4 hp4
          obtain ⟨hlo4, hhi4, ⟨sz4, hat4, hsz4⟩, ⟨hmeta4, hfr4⟩, hz4, hin4, hout4⟩ := hp4
          simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, hhd3] at hlo4 hhi4 hsz4 hin4 hout4 hfr4
          have hsc4W : sc4 < 2 ^ w := by omega
          have hfr14 : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem4 a = mem a :=
            fun a ha hout => (hfr4 a (by omega) hout).trans (hfr13 a ha hout)
          obtain ⟨hc12_in, hc12_out⟩ := combine_list_post (fun e he => (hbdUG e he).1)
            (fun e he => (hbdFD e he).1) hin1 hout1 hin2 hout2
          obtain ⟨hc13_in, hc13_out⟩ := combine_list_post
            (fun e he => by rw [List.mem_append] at he; exact he.elim (fun h => (hbdUG e h).1) (fun h => (hbdFD e h).1))
            (fun e he => (hbdUS e he).1) hc12_in hc12_out hin3 hout3
          obtain ⟨hc14_in, hc14_out⟩ := combine_list_post
            (fun e he => by
              simp only [List.mem_append] at he
              rcases he with (h | h) | h
              · exact (hbdUG e h).1
              · exact (hbdFD e h).1
              · exact (hbdUS e h).1)
            (fun e he => (hbdRE e he).1) hc13_in hc13_out hin4 hout4
          refine WordRAM.runs_ret_le (v := sc4) (by eval_expr) ?_ ?_
          · dsimp only [selectUpdateLevelContract]
            simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhd0]
            exact ⟨by omega, by omega, ⟨sz4, hat4, by omega⟩, ⟨hmeta4, hfr14⟩, hz4,
              hc14_in, hc14_out⟩
          · simp only [selectUpdateLevelContract, selectProcessListContract,
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

/-- **Job 2 semantic bridge**: combining `selectUpdateLevel_meetsContract` with
`touched_covers_level_changes` restores `SelectHeapLevelOk` at a non-rebuilt level `lvl`
while preserving every other level's entries (outside `(C'.activeCore lvl).E \ (C'.activeS lvl).E`). -/
theorem selectUpdateLevel_establishes_levelOk
    {w h P : ℕ} {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {L : LevelDiffLists}
    {evalSpace evalCost lvl diffBase scratch ret : ℕ} {mem mem' : ℕ → ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hSpan : C.LastLevelSpans) (hSpan' : C'.LastLevelSpans)
    (hlvl : lvl ≤ C.d) (hlvl' : lvl ≤ C'.d)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ)
    (hEnds : ∀ j ≤ lvl, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.G j).tail f = (C.G j).tail f ∧ (C'.G j).head f = (C.G j).head f)
    {ins : ℕ → ℕ → Prop}
    (hWstr : ∀ j ≤ lvl, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j < lvl, ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E → ins j f → ins (j + 1) f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hcov : LevelDiffCovers C C' lvl ins L)
    (hLbd : ∀ e ∈ L.allTouched, e < loc.cap)
    (hOldOk : SelectHeapLevelOk mem loc h P C g ℓ lvl)
    (hPost : (selectUpdateLevelContract w h P loc mloc C' g' ℓ' φ coreLen L evalSpace evalCost).post
      [loc.hb, mloc.metaBase, lvl, diffBase, scratch] mem ret mem') :
    SelectHeapLevelOk mem' loc h P C' g' ℓ' lvl ∧
    (∀ e' < loc.cap, e' ∉ (C'.activeCore lvl).E \ (C'.activeS lvl).E →
      (mem (loc.posPtr + e') = 0 → mem' (loc.posPtr + e') = 0) ∧
      (mem (loc.posPtr + e') ≠ 0 → mem (loc.lvlPtr + e') ≠ lvl →
        mem' (loc.posPtr + e') ≠ 0 ∧ mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
        loc.readNum mem' h e' = loc.readNum mem h e' ∧
        loc.readDen mem' h e' = loc.readDen mem h e')) := by
  obtain ⟨_, _, _, _, _, hin, hout⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hin hout
  refine ⟨⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩, fun e' he' hnc => ?_⟩
  · by_cases hT : e ∈ L.allTouched
    · by_contra hnc; exact ((hin e hT).2 hnc).1 ⟨hnz, hl⟩
    · obtain ⟨k1, k2, _, _⟩ := hout e heCap hT
      have hOld : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E :=
        hOldOk.1 e heCap (k1.mp hnz) (k2.symm.trans hl)
      exact (touched_covers_level_changes hH hH' hSpan hSpan' hlvl hlvl' φ hPot hPot'
        hEnds hWstr hInsFwd hℓEq hgEq hcov hT).1.mpr hOld
  · by_cases hT : e ∈ L.allTouched
    · exact ⟨hLbd e hT, (hin e hT).1 he⟩
    · have hCov := touched_covers_level_changes hH hH' hSpan hSpan' hlvl hlvl' φ hPot hPot'
        hEnds hWstr hInsFwd hℓEq hgEq hcov hT
      have hOld : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E := hCov.1.mp he
      obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hOldOk.2 e hOld
      obtain ⟨k1, k2, k3, k4⟩ := hout e heCap hT
      obtain ⟨hwi, hwl⟩ := hCov.2 he
      exact ⟨heCap, k1.mpr hnz0, k2.trans hl0, by rw [k3, k4, hwi, hwl]; exact hrep0⟩
  · by_cases hT : e' ∈ L.allTouched
    · exact ⟨((hin e' hT).2 hnc).2.1, ((hin e' hT).2 hnc).2.2.1⟩
    · obtain ⟨k1, k2, k3, k4⟩ := hout e' he' hT
      exact ⟨fun h0 => by by_contra hnz; exact (k1.mp hnz) h0,
        fun hnz _ => ⟨k1.mpr hnz, k2, k3, k4⟩⟩

/-! ## 3. Verification of `selectRebuildLevelBody` -/

/-- `selectRebuildLevelBody` meets `selectRebuildLevelContract` in `selectRebuildLevelCost` steps. -/
theorem selectRebuildLevel_meetsContract {w h P entry clearLvl procList : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    {evalSpace evalCost : ℕ} {p : Program}
    (hp : p.procs[entry]? = some (selectRebuildLevelBody clearLvl procList))
    (hClear : MeetsContract w p clearLvl (heapClearLevelContract w h loc))
    (hList : ∀ L' : List ℕ, MeetsContract w p procList
      (selectProcessListContract w h P loc mloc C g ℓ φ coreLen L' evalSpace evalCost)) :
    MeetsContract w p entry
      (selectRebuildLevelContract w h P loc mloc C g ℓ φ coreLen evalSpace evalCost) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨lvl, scratch, size, rfl, hw16, hpLastW, hendLe, hdLoc, hLkEq, hlvlD, hGEcap, hszRoom,
    hat, hmeta, hdisj, hmetaFr, hz, hroom⟩ := hpre
  have hhd0 : mem loc.hb = size := by simpa using hat.1 0 (by simp)
  have hhbw : loc.hb < 2 ^ w := hwords loc.hb (by simp)
  have hmw : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hlvlw : lvl < 2 ^ w := hwords lvl (by simp)
  have hscw : scratch < 2 ^ w := hwords scratch (by simp)
  obtain ⟨hmd, _, hmD, htab, _, hGAt, _, _, _, _, _, _, _⟩ := hmeta
  have hlvlM : lvl ≤ mloc.d := by omega
  have htabL := htab lvl hlvlD
  have hDdisj := hdisj.2.2.2.1 lvl hlvlM
  have hGL := hGAt lvl hlvlD
  obtain ⟨_, _, hGEeCap, _, _, _, hGm, _, _, _, _, _, ⟨eL, heLlen, _, heLmem, heLAt, _⟩, _, _⟩ := hGL
  have hmEq : (C.G lvl).m = (C.G lvl).E.card := rfl
  rw [hmEq] at hGm heLlen
  set oldCand := levelCandCount mem loc lvl
  change (size - oldCand) + (C.G lvl).E.card ≤ loc.cap at hszRoom
  change scratch + selectRebuildLevelSpace oldCand (C.G lvl).E.card loc.cap loc.Lk evalSpace < 2 ^ w at hroom
  have hspEq : selectRebuildLevelSpace oldCand (C.G lvl).E.card loc.cap loc.Lk evalSpace =
      heapClearLevelSpace oldCand loc.cap loc.Lk +
      selectProcessListSpace (C.G lvl).E.card loc.cap loc.Lk evalSpace := rfl
  have hmetaW : mloc.metaBase + selectLevelMetaSize mloc.d < 2 ^ w := by
    have := hdisj.2.1; omega
  have hGW : mloc.GPtr lvl + dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl) < 2 ^ w := by
    have := hDdisj.1; omega
  have hGsz : dynGraphSize (mloc.vCap lvl) (mloc.eCap lvl) =
      4 + 7 * mloc.vCap lvl + 9 * mloc.eCap lvl := rfl
  have hmSz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  have hmDW : mloc.d < 2 ^ w := by omega
  have hmD1W : mloc.d + 1 < 2 ^ w := by omega
  have hGPW : mloc.GPtr lvl < 2 ^ w := by omega
  have hvCW : mloc.vCap lvl < 2 ^ w := by omega
  have heCW : mloc.eCap lvl < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold selectRebuildLevelBody
  simp only [smDOff, smTableOff]
  -- Step 1: `heapClearLevel`
  refine runs_seq_call_flat hClear (vs := [loc.hb, lvl, scratch]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨lvl, scratch, size, rfl, hw16, hendLe, by omega, hat, hz, by change scratch + heapClearLevelSpace oldCand _ _ < 2 ^ w; omega⟩
  · intro sc1 mem1 pos1 hp1
    obtain ⟨hlo1, hhi1, hcntLe, hat1, hz1, hclr1, hoth1, hfr1⟩ := hp1
    simp only [List.getD_cons_zero, List.getD_cons_succ, hhd0] at hlo1 hhi1 hcntLe hat1 hclr1 hoth1 hfr1
    change sc1 ≤ scratch + heapClearLevelSpace oldCand loc.cap loc.Lk at hhi1
    change oldCand ≤ size at hcntLe
    change SelectHeapAt mem1 loc h (size - oldCand) at hat1
    have hhd1 : mem1 loc.hb = size - oldCand := by simpa using hat1.1 0 (by simp)
    have hsc1W : sc1 < 2 ^ w := by omega
    have hfr1_out : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem1 a = mem a :=
      fun a ha hout => hfr1 a ha (hout.imp id fun h => by
        have hend := loc.endAddr_eq; unfold selectHeapSize shHdrSize at hend
        unfold SelectHeapLoc.numBase SelectHeapLoc.candNext SelectHeapLoc.candPrev
          SelectHeapLoc.candHead SelectHeapLoc.lvlPtr SelectHeapLoc.posPtr
          SelectHeapLoc.arrPtr shHdrSize
        omega)
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
    have hEListPtr : dgEListBase (mloc.GPtr lvl) (mloc.vCap lvl) (mloc.eCap lvl) =
        mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl := rfl
    have heLLeEcap : (C.G lvl).E.card ≤ mloc.eCap lvl := by
      have hsub : (C.G lvl).E ⊆ Finset.range (mloc.eCap lvl) := fun e he =>
        Finset.mem_range.mpr (hGEeCap e he)
      exact (Finset.card_le_card hsub).trans (by simp)
    have heLAt1 : ListAt mem1 (mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl) eL := fun j hj =>
      (hm1_G _ (by omega) (by omega)).trans (heLAt j hj)
    have hEListW : mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl < 2 ^ w := by omega
    have hGmW : (C.G lvl).E.card < 2 ^ w := by omega
    -- Step 2: load `dgEListBase` and call `selectProcessList`
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
    · refine ⟨lvl, mloc.GPtr lvl + 4 + 7 * mloc.vCap lvl + mloc.eCap lvl, 0, sc1, size - oldCand,
        rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hlvlD, Nat.zero_le _, by have := hDdisj.1; omega,
        by rcases hDdisj.2.1 with h1 | h2 <;> omega, heLAt1,
        fun e he => ⟨hGEcap e ((heLmem e).mp he), hGEeCap e ((heLmem e).mp he)⟩,
        by simp only [Nat.sub_zero, heLlen]; omega, hat1, hmeta1, selectMetaDisjoint_mono hdisj hlo1,
        hmetaFr1, hz1, by simp only [Nat.sub_zero, heLlen]; omega⟩
    · intro ret mem2 pos2 hp2
      obtain ⟨hlo2, hhi2, ⟨sz2, hat2, hsz2⟩, ⟨hmeta2, hfr2⟩, hz2, hin2, hout2⟩ := hp2
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero, List.drop_zero, heLlen, hhd1] at hlo2 hhi2 hsz2 hin2 hout2 hfr2
      have hretW : ret < 2 ^ w := by omega
      have hfrOut : ∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mem2 a = mem a :=
        fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1_out a ha hout)
      refine WordRAM.runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · dsimp only [selectRebuildLevelContract]
        simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ, hhd0]
        refine ⟨by omega, by change ret ≤ scratch + selectRebuildLevelSpace oldCand _ _ _ _; omega,
          ⟨sz2, hat2, by change sz2 ≤ (size - oldCand) + _; omega⟩, ⟨hmeta2, hfrOut⟩, hz2, ?_, ?_⟩
        · -- `SelectHeapLevelOk mem2 loc h P C g ℓ lvl`
          refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
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
        · -- Preservation of non-candidates at `lvl`
          intro e' he' hnc
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
      · simp only [selectRebuildLevelContract, heapClearLevelContract, selectProcessListContract,
          selectRebuildLevelCost, List.getD_cons_zero, List.getD_cons_succ, Nat.sub_zero,
          heLlen, Expr.size, argsSize]
        omega

end MinCostFlow.MinRatio
