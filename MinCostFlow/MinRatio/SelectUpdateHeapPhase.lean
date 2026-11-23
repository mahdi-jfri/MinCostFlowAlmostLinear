module

public import MinCostFlow.MinRatio.SelectUpdateLevelNoRoom
public import MinCostFlow.MinRatio.WireSelectSplitPot
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Select-heap update phase for `Update` (`SelectUpdateHeapPhase`)

Verifies Phase 4 of the select-maintenance post-core pass of `Update`, once all level blocks and
metadata (`SelectLevelMetaAt`) have already been updated for the new chain `(C', g', ℓ', φ')`:
1. **Phase 4a (`selectUpdateHeapPrefixLoopBody`):** updates non-rebuilt interior levels
   `j = 0 .. min firstReb d - 1` via `selectUpdateLevel_meetsContract_noRoom` and
   `touched_covers_level_changes_phi`.
2. **Phase 4b (`selectUpdateHeapPhaseBody`):** runs Phase 4a followed by
   `selectRebuildSuffix_meetsContract_noRoom` from `firstReb` to `d` (a 0-iteration no-op when
   `firstReb = d + 1`), restoring full `SelectHeapMatchesChain` for `(C', g', ℓ')` across all
   levels `0 .. d`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-- Recursive loop calling `selectUpdateLevel` for non-rebuilt levels `cur .. limit - 1`.
Arguments: `[hb, metaBase, cur, limit, selOutBase, scratch]` (`reg 0..5`). Returns `scOut`. -/
def selectUpdateHeapPrefixLoopBody (self updLvlProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 2) (.reg 3))
    (.assign 6 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 12) (.reg 2))) ;;
     .call 7 updLvlProc [.reg 0, .reg 1, .reg 2, .reg 6, .reg 5] ;;
     .call 8 self [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1), .reg 3, .reg 4, .reg 7] ;;
     .ret (.reg 8))
    (.ret (.reg 5))

theorem selectUpdateHeapPrefixLoopBody_noRand (self updLvlProc : ℕ) :
    (selectUpdateHeapPrefixLoopBody self updLvlProc).NoRand := by
  simp [selectUpdateHeapPrefixLoopBody, Stmt.NoRand]

/-- Scratch space for `selectUpdateHeapPrefixLoopBody` over `cur .. limit - 1`. -/
def selectUpdateHeapPrefixLoopSpace (diffLists : ℕ → LevelDiffLists)
    (cur limit cap Lk evalSpace : ℕ) : ℕ :=
  (Finset.Ico cur limit).sum fun j =>
    selectUpdateLevelSpace (diffLists j) cap Lk evalSpace

/-- Step cost for `selectUpdateHeapPrefixLoopBody` over `cur .. limit - 1`. -/
def selectUpdateHeapPrefixLoopCost (diffLists : ℕ → LevelDiffLists)
    (cur limit cap Lk evalCost : ℕ) : ℕ :=
  (Finset.Ico cur limit).sum (fun j =>
    selectUpdateLevelCost (diffLists j) cap Lk evalCost + 60) + 10

/-- Phase 4 combined body: run `selectUpdateHeapPrefixLoopBody` on `0 .. min firstReb d - 1`, then
`selectRebuildSuffixBody` from `firstReb` to `d`.
Arguments: `[hb, metaBase, firstReb, d, selOutBase, scratch]` (`reg 0..5`). Returns `scOut`. -/
def selectUpdateHeapPhaseBody (prefLoopProc rebSufProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 2) (.reg 3))
    (.assign 6 (.reg 2))
    (.assign 6 (.reg 3)) ;;
  .call 7 prefLoopProc [.reg 0, .reg 1, .const 0, .reg 6, .reg 4, .reg 5] ;;
  .call 8 rebSufProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 7] ;;
  .ret (.reg 8)

theorem selectUpdateHeapPhaseBody_noRand (prefLoopProc rebSufProc : ℕ) :
    (selectUpdateHeapPhaseBody prefLoopProc rebSufProc).NoRand := by
  simp [selectUpdateHeapPhaseBody, Stmt.NoRand]

/-- Total scratch space for `selectUpdateHeapPhaseBody` (expressed in terms of pre-Phase-4 `mem`). -/
noncomputable def selectUpdateHeapPhaseSpace (mem : ℕ → ℕ) (loc : SelectHeapLoc) (C' : TreeChain)
    (diffLists : ℕ → LevelDiffLists) (firstReb evalSpace : ℕ) : ℕ :=
  selectUpdateHeapPrefixLoopSpace diffLists 0 (min firstReb C'.d) loc.cap loc.Lk evalSpace +
  selectRebuildSuffixSpace mem loc C' firstReb evalSpace

/-- Total step cost for `selectUpdateHeapPhaseBody` (expressed in terms of pre-Phase-4 `mem`). -/
noncomputable def selectUpdateHeapPhaseCost (mem : ℕ → ℕ) (loc : SelectHeapLoc) (C' : TreeChain)
    (diffLists : ℕ → LevelDiffLists) (firstReb evalCost : ℕ) : ℕ :=
  selectUpdateHeapPrefixLoopCost diffLists 0 (min firstReb C'.d) loc.cap loc.Lk evalCost +
  selectRebuildSuffixCost mem loc C' firstReb evalCost + 50

/-- Intermediate per-level invariant for a not-yet-updated level `k` during Phase 4a:
1. Every edge currently stored at level `k` is an old candidate of `C` at level `k`.
2. Every old candidate of `C` at level `k` that has NOT been claimed as a new candidate of `C'`
   at any already-updated level `j < cur` is still stored at level `k` with its old key. -/
def SelectHeapLevelOkMod (mem : ℕ → ℕ) (loc : SelectHeapLoc) (h _P : ℕ)
    (C C' : TreeChain) (g ℓ : ℕ → ℝ) (cur k : ℕ) : Prop :=
  (∀ e < loc.cap, mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = k →
    e ∈ (C.activeCore k).E \ (C.activeS k).E) ∧
  (∀ e ∈ (C.activeCore k).E \ (C.activeS k).E,
    (∀ j < cur, e ∉ (C'.activeCore j).E \ (C'.activeS j).E) →
    e < loc.cap ∧ mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = k ∧
    SelectKeyRepresents (loc.readNum mem h e) (loc.readDen mem h e)
      (walkInner (C.chainGrad g (k + 1)) (C.sparsifierCycle k e)) (C.wlenAt ℓ k e))

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

private lemma selectHeapLevelOkMod_zero {mem : ℕ → ℕ} {loc : SelectHeapLoc} {h P k : ℕ}
    {C C' : TreeChain} {g ℓ : ℕ → ℝ} (hok : SelectHeapLevelOk mem loc h P C g ℓ k) :
    SelectHeapLevelOkMod mem loc h P C C' g ℓ 0 k :=
  ⟨hok.1, fun e he _ => hok.2 e he⟩

/-- One step of `selectUpdateLevel` at level `cur`: establishes `SelectHeapLevelOk` at `cur` for
`C'`, preserves `SelectHeapLevelOk` for all `j < cur`, advances `SelectHeapLevelOkMod` from `cur`
to `cur + 1` for all `k > cur`, and never creates a new entry at any level `k ≠ cur`. -/
private lemma selectUpdateLevel_step_mod
    {w h P cur evalSpace evalCost diffBase scratch ret : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ φ' coreLen : ℕ → ℕ → ℝ} {ins : ℕ → ℕ → Prop} {L : LevelDiffLists}
    {mem mem' : ℕ → ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hSpan : C.LastLevelSpans) (hSpan' : C'.LastLevelSpans)
    (hcur : cur ≤ C.d) (hcur' : cur ≤ C'.d)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ')
    (hEP : EndPotAgree C C' φ φ' cur)
    (hWstr : ∀ j ≤ cur, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j < cur, ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E → ins j f → ins (j + 1) f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hcov : LevelDiffCovers C C' cur ins L)
    (hLbd : ∀ e ∈ L.allTouched, e < loc.cap)
    (hPrefOk : ∀ j < cur, SelectHeapLevelOk mem loc h P C' g' ℓ' j)
    (hModOk : ∀ k, cur ≤ k → k ≤ C.d → SelectHeapLevelOkMod mem loc h P C C' g ℓ cur k)
    (hPost : (selectUpdateLevelContract w h P loc mloc C' g' ℓ' φ' coreLen L evalSpace evalCost).post
      [loc.hb, mloc.metaBase, cur, diffBase, scratch] mem ret mem') :
    (∀ j < cur + 1, SelectHeapLevelOk mem' loc h P C' g' ℓ' j) ∧
    (∀ k, cur + 1 ≤ k → k ≤ C.d → SelectHeapLevelOkMod mem' loc h P C C' g ℓ (cur + 1) k) ∧
    (∀ k, cur < k → levelCandCount mem' loc k ≤ levelCandCount mem loc k) := by
  obtain ⟨_, _, _, _, _, hin, hout⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hin hout
  have hFrameNonCand : ∀ e < loc.cap, e ∉ (C'.activeCore cur).E \ (C'.activeS cur).E →
      (mem (loc.posPtr + e) = 0 → mem' (loc.posPtr + e) = 0) ∧
      (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) ≠ cur →
        mem' (loc.posPtr + e) ≠ 0 ∧ mem' (loc.lvlPtr + e) = mem (loc.lvlPtr + e) ∧
        loc.readNum mem' h e = loc.readNum mem h e ∧
        loc.readDen mem' h e = loc.readDen mem h e) ∧
      (mem (loc.posPtr + e) ≠ 0 → mem (loc.lvlPtr + e) = cur →
        mem' (loc.posPtr + e) = 0) := by
    intro e heCap hnc
    by_cases hT : e ∈ L.allTouched
    · exact ⟨((hin e hT).2 hnc).2.1, ((hin e hT).2 hnc).2.2.1, ((hin e hT).2 hnc).2.2.2⟩
    · obtain ⟨k1, k2, k3, k4⟩ := hout e heCap hT
      refine ⟨fun h0 => by by_contra hnz; exact (k1.mp hnz) h0,
        fun hnz _ => ⟨k1.mpr hnz, k2, k3, k4⟩, fun hnz hl => ?_⟩
      exfalso
      have hOld : e ∈ (C.activeCore cur).E \ (C.activeS cur).E :=
        (hModOk cur le_rfl hcur).1 e heCap hnz hl
      have hCov := touched_covers_level_changes_phi hH hH' hSpan hSpan' hcur hcur' φ φ'
        hPot hPot' hEP hWstr hInsFwd hℓEq hgEq hcov hT
      exact hnc (hCov.1.mpr hOld)
  have hNoNewOther : ∀ k, k ≠ cur → ∀ e < loc.cap,
      mem' (loc.posPtr + e) ≠ 0 → mem' (loc.lvlPtr + e) = k →
      mem (loc.posPtr + e) ≠ 0 ∧ mem (loc.lvlPtr + e) = k := by
    intro k hkne e heCap hnz hl
    by_cases hC : e ∈ (C'.activeCore cur).E \ (C'.activeS cur).E
    · by_cases hT : e ∈ L.allTouched
      · exact absurd (((hin e hT).1 hC).2.1.symm.trans hl) hkne.symm
      · obtain ⟨k1, k2, _, _⟩ := hout e heCap hT
        exact ⟨k1.mp hnz, k2.symm.trans hl⟩
    · have hfr := hFrameNonCand e heCap hC
      have hnz0 : mem (loc.posPtr + e) ≠ 0 := fun h0 => hnz (hfr.1 h0)
      have hl0 : mem (loc.lvlPtr + e) ≠ cur := fun hlEq => hnz (hfr.2.2 hnz0 hlEq)
      exact ⟨hnz0, (hfr.2.1 hnz0 hl0).2.1.symm.trans hl⟩
  have hOkCur : SelectHeapLevelOk mem' loc h P C' g' ℓ' cur := by
    refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
    · by_cases hT : e ∈ L.allTouched
      · by_contra hnc; exact ((hin e hT).2 hnc).1 ⟨hnz, hl⟩
      · obtain ⟨k1, k2, _, _⟩ := hout e heCap hT
        have hOld := (hModOk cur le_rfl hcur).1 e heCap (k1.mp hnz) (k2.symm.trans hl)
        exact (touched_covers_level_changes_phi hH hH' hSpan hSpan' hcur hcur' φ φ'
          hPot hPot' hEP hWstr hInsFwd hℓEq hgEq hcov hT).1.mpr hOld
    · by_cases hT : e ∈ L.allTouched
      · exact ⟨hLbd e hT, (hin e hT).1 he⟩
      · have hCov := touched_covers_level_changes_phi hH hH' hSpan hSpan' hcur hcur' φ φ'
          hPot hPot' hEP hWstr hInsFwd hℓEq hgEq hcov hT
        have hOld := hCov.1.mp he
        have hNotPrev : ∀ j < cur, e ∉ (C'.activeCore j).E \ (C'.activeS j).E := fun j hj hej => by
          have hEq := C'.level_unique_of_mem_activeCore_diff hH' (by omega) hcur' hej he; omega
        obtain ⟨heCap, hnz0, hl0, hrep0⟩ := (hModOk cur le_rfl hcur).2 e hOld hNotPrev
        obtain ⟨k1, k2, k3, k4⟩ := hout e heCap hT
        obtain ⟨hwi, hwl⟩ := hCov.2 he
        exact ⟨heCap, k1.mpr hnz0, k2.trans hl0, by rw [k3, k4, hwi, hwl]; exact hrep0⟩
  refine ⟨fun j hj => ?_, fun k hk1 hk2 => ?_, fun k hk => ?_⟩
  · by_cases hEq : j = cur
    · subst hEq; exact hOkCur
    · have hjlt : j < cur := by omega
      have hOldJ := hPrefOk j hjlt
      refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
      · obtain ⟨hnz0, hl0⟩ := hNoNewOther j (by omega) e heCap hnz hl
        exact hOldJ.1 e heCap hnz0 hl0
      · have hnc : e ∉ (C'.activeCore cur).E \ (C'.activeS cur).E := fun hec => by
          have := C'.level_unique_of_mem_activeCore_diff hH' (by omega) hcur' he hec; omega
        obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hOldJ.2 e he
        obtain ⟨k1, k2, k3, k4⟩ := (hFrameNonCand e heCap hnc).2.1 hnz0 (by omega)
        exact ⟨heCap, k1, k2.trans hl0, by rw [k3, k4]; exact hrep0⟩
  · have hOldK := hModOk k (by omega) hk2
    refine ⟨fun e heCap hnz hl => ?_, fun e he hNot => ?_⟩
    · obtain ⟨hnz0, hl0⟩ := hNoNewOther k (by omega) e heCap hnz hl
      exact hOldK.1 e heCap hnz0 hl0
    · have hnc : e ∉ (C'.activeCore cur).E \ (C'.activeS cur).E := hNot cur (Nat.lt_succ_self cur)
      obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hOldK.2 e he fun j hj => hNot j (by omega)
      obtain ⟨k1, k2, k3, k4⟩ := (hFrameNonCand e heCap hnc).2.1 hnz0 (by omega)
      exact ⟨heCap, k1, k2.trans hl0, by rw [k3, k4]; exact hrep0⟩
  · unfold levelCandCount
    refine Finset.card_le_card fun e he => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at he ⊢
    exact ⟨he.1, hNoNewOther k (by omega) e he.1 he.2.1 he.2.2⟩

set_option maxHeartbeats 1000000 in
/-- Verification of `selectUpdateHeapPrefixLoopBody` over non-rebuilt levels `cur .. limit - 1`. -/
theorem selectUpdateHeapPrefixLoop_runs
    {w P cur limit selOutBase sizeOld evalSpace evalCost scratch pos : ℕ}
    {self updLvlProc : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ φ' coreLen' : ℕ → ℕ → ℝ} {ins : ℕ → ℕ → Prop}
    {diffLists : ℕ → LevelDiffLists} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hpLastW : mloc.pLast < 2 ^ w)
    (hcurLe : cur ≤ limit) (hlimLe : limit ≤ C'.d) (hCd : C.d = C'.d)
    (hdLoc : loc.d = C'.d) (hLkEq : mloc.Lk = loc.Lk)
    (hendLe : loc.endAddr ≤ scratch)
    (hOutLe : selOutBase + 1 + 12 * limit ≤ scratch)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c) (hSpan' : C'.LastLevelSpans)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ')
    (hEP : 0 < limit → EndPotAgree C C' φ φ' (limit - 1))
    (hWstr : ∀ j < limit, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j, j + 1 < limit → ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E →
      ins j f → ins (j + 1) f)
    (hℓEq : 0 < limit → ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : 0 < limit → ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hCov : ∀ j, cur ≤ j → j < limit → LevelDiffCovers C C' j ins (diffLists j))
    (hDiff : ∀ j, cur ≤ j → j < limit →
      let slot := selOutBase + 1 + 12 * j
      LevelDiffListsAt mem slot (diffLists j) ∧
      LevelDiffListsDisjoint mem slot (diffLists j) loc scratch ∧
      (∀ e ∈ (diffLists j).allTouched, e < loc.cap ∧ e < mloc.eCap j))
    (hat : SelectHeapAt mem loc 4 sizeOld)
    (hPrefOk : ∀ j < cur, SelectHeapLevelOk mem loc 4 P C' g' ℓ' j)
    (hModOk : ∀ k, cur ≤ k → k ≤ C.d → SelectHeapLevelOkMod mem loc 4 P C C' g ℓ cur k)
    (hMeta : SelectLevelMetaAt mem mloc 4 P C' g' ℓ' φ' coreLen')
    (hDisj : SelectMetaDisjoint mloc loc scratch)
    (hMetaFr : ∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
      SelectLevelMetaAt m' mloc 4 P C' g' ℓ' φ' coreLen')
    (hpLoop : p.procs[self]? = some (selectUpdateHeapPrefixLoopBody self updLvlProc))
    (hUpdLvl : ∀ j, cur ≤ j → j < limit →
      MeetsContract w p updLvlProc
        (selectUpdateLevelNoRoomContract w 4 P loc mloc C' g' ℓ' φ' coreLen'
          (diffLists j) evalSpace evalCost))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateHeapPrefixLoopSpace diffLists cur limit loc.cap loc.Lk evalSpace < 2 ^ w) :
    ∃ scOut cost out sizeOut,
      Runs w p ω (selectUpdateHeapPrefixLoopBody self updLvlProc)
        (startState [loc.hb, mloc.metaBase, cur, limit, selOutBase, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateHeapPrefixLoopSpace diffLists cur limit loc.cap loc.Lk evalSpace ∧
      SelectHeapAt out.mem loc 4 sizeOut ∧
      (∀ j < limit, SelectHeapLevelOk out.mem loc 4 P C' g' ℓ' j) ∧
      (∀ k, limit ≤ k → k ≤ C.d → SelectHeapLevelOkMod out.mem loc 4 P C C' g ℓ limit k) ∧
      (∀ k, limit ≤ k → levelCandCount out.mem loc k ≤ levelCandCount mem loc k) ∧
      SelectLevelMetaAt out.mem mloc 4 P C' g' ℓ' φ' coreLen' ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → out.mem a = mem a) ∧
      cost ≤ selectUpdateHeapPrefixLoopCost diffLists cur limit loc.cap loc.Lk evalCost := by
  have hHbLtEnd : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
  have hInd : ∀ n cur' sc pos' sz (mCur : ℕ → ℕ),
      limit - cur' = n → cur ≤ cur' → cur' ≤ limit → scratch ≤ sc →
      (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → mCur a = mem a) →
      SelectHeapAt mCur loc 4 sz →
      (∀ j < cur', SelectHeapLevelOk mCur loc 4 P C' g' ℓ' j) →
      (∀ k, cur' ≤ k → k ≤ C.d → SelectHeapLevelOkMod mCur loc 4 P C C' g ℓ cur' k) →
      SelectLevelMetaAt mCur mloc 4 P C' g' ℓ' φ' coreLen' →
      ZeroFrom mCur sc →
      sc + selectUpdateHeapPrefixLoopSpace diffLists cur' limit loc.cap loc.Lk evalSpace < 2 ^ w →
      ∃ scOut cost out sizeOut,
        Runs w p ω (selectUpdateHeapPrefixLoopBody self updLvlProc)
          (startState [loc.hb, mloc.metaBase, cur', limit, selOutBase, sc] mCur pos')
          (.returned scOut) out cost ∧
        sc ≤ scOut ∧
        scOut ≤ sc + selectUpdateHeapPrefixLoopSpace diffLists cur' limit loc.cap loc.Lk evalSpace ∧
        SelectHeapAt out.mem loc 4 sizeOut ∧
        (∀ j < limit, SelectHeapLevelOk out.mem loc 4 P C' g' ℓ' j) ∧
        (∀ k, limit ≤ k → k ≤ C.d → SelectHeapLevelOkMod out.mem loc 4 P C C' g ℓ limit k) ∧
        (∀ k, limit ≤ k → levelCandCount out.mem loc k ≤ levelCandCount mCur loc k) ∧
        SelectLevelMetaAt out.mem mloc 4 P C' g' ℓ' φ' coreLen' ∧
        ZeroFrom out.mem scOut ∧
        (∀ a < sc, (a < loc.hb ∨ loc.endAddr ≤ a) → out.mem a = mCur a) ∧
        cost ≤ selectUpdateHeapPrefixLoopCost diffLists cur' limit loc.cap loc.Lk evalCost := by
    intro n
    induction n with
    | zero =>
      intro cur' sc pos' sz mCur hsub _ hcurLe' _ _ hat0 hPref0 hMod0 hMeta0 hz0 _
      have hEq : cur' = limit := by omega
      have hSp0 : selectUpdateHeapPrefixLoopSpace diffLists cur' limit loc.cap loc.Lk evalSpace = 0 := by
        unfold selectUpdateHeapPrefixLoopSpace; rw [hEq, Finset.Ico_self, Finset.sum_empty]
      let s0 := startState [loc.hb, mloc.metaBase, cur', limit, selOutBase, sc] mCur pos'
      have hRun : Runs w p ω (selectUpdateHeapPrefixLoopBody self updLvlProc) s0 (.returned sc) s0 6 := by
        unfold selectUpdateHeapPrefixLoopBody
        refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s0, startState, hEq], ?_,
          by simp [Expr.size]⟩
        exact runs_ret_iff.mpr ⟨sc, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
      refine ⟨sc, 6, s0, sz, hRun, le_rfl, by omega, hat0, hEq ▸ hPref0, hEq ▸ hMod0,
        fun _ _ => le_rfl, hMeta0, hz0, fun _ _ _ => rfl, ?_⟩
      unfold selectUpdateHeapPrefixLoopCost; omega
    | succ n ih =>
      intro cur' sc pos' sz mCur hsub hGeCur hcurLe' hScGe hAg0 hat0 hPref0 hMod0 hMeta0 hz0 hroom0
      have hcurLt : cur' < limit := by omega
      have hlimPos : 0 < limit := by omega
      have hSpSplit : selectUpdateHeapPrefixLoopSpace diffLists cur' limit loc.cap loc.Lk evalSpace =
          selectUpdateLevelSpace (diffLists cur') loc.cap loc.Lk evalSpace +
          selectUpdateHeapPrefixLoopSpace diffLists (cur' + 1) limit loc.cap loc.Lk evalSpace := by
        unfold selectUpdateHeapPrefixLoopSpace; rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]
      have hCostSplit : selectUpdateHeapPrefixLoopCost diffLists cur' limit loc.cap loc.Lk evalCost =
          (selectUpdateLevelCost (diffLists cur') loc.cap loc.Lk evalCost + 60) +
          selectUpdateHeapPrefixLoopCost diffLists (cur' + 1) limit loc.cap loc.Lk evalCost := by
        unfold selectUpdateHeapPrefixLoopCost; rw [Finset.sum_eq_sum_Ico_succ_bot hcurLt]; omega
      let slotCur := selOutBase + 1 + 12 * cur'
      obtain ⟨hLAt, hLDisj, hLbd⟩ := hDiff cur' hGeCur hcurLt
      have hSlotAg : ∀ t < 8, mCur (slotCur + t) = mem (slotCur + t) := fun t ht =>
        hAg0 _ (by have := hLDisj.1; dsimp only [slotCur]; omega)
          (by rcases hLDisj.2.1 with h | h <;> [left; right] <;> dsimp only [slotCur] <;> omega)
      have hLAtCur : LevelDiffListsAt mCur slotCur (diffLists cur') :=
        ⟨(hSlotAg 1 (by omega)).trans hLAt.1,
         fun i hi => by
           rw [hSlotAg 0 (by omega)]
           exact (hAg0 _ (by have := hLDisj.2.2.1; dsimp only [slotCur]; omega)
             (by rcases hLDisj.2.2.2.1 with h | h <;> [left; right] <;> dsimp only [slotCur] <;> omega)).trans (hLAt.2.1 i hi),
         (hSlotAg 3 (by omega)).trans hLAt.2.2.1,
         fun i hi => by
           rw [hSlotAg 2 (by omega)]
           exact (hAg0 _ (by have := hLDisj.2.2.2.2.1; dsimp only [slotCur]; omega)
             (by rcases hLDisj.2.2.2.2.2.1 with h | h <;> [left; right] <;> dsimp only [slotCur] <;> omega)).trans (hLAt.2.2.2.1 i hi),
         (hSlotAg 5 (by omega)).trans hLAt.2.2.2.2.1,
         fun i hi => by
           rw [hSlotAg 4 (by omega)]
           exact (hAg0 _ (by have := hLDisj.2.2.2.2.2.2.1; dsimp only [slotCur]; omega)
             (by rcases hLDisj.2.2.2.2.2.2.2.1 with h | h <;> [left; right] <;> dsimp only [slotCur] <;> omega)).trans (hLAt.2.2.2.2.2.1 i hi),
         (hSlotAg 7 (by omega)).trans hLAt.2.2.2.2.2.2.1,
         fun i hi => by
           rw [hSlotAg 6 (by omega)]
           exact (hAg0 _ (by have := hLDisj.2.2.2.2.2.2.2.2.1; dsimp only [slotCur]; omega)
             (by rcases hLDisj.2.2.2.2.2.2.2.2.2 with h | h <;> [left; right] <;> dsimp only [slotCur] <;> omega)).trans (hLAt.2.2.2.2.2.2.2 i hi)⟩
      have hLDisjCur : LevelDiffListsDisjoint mCur slotCur (diffLists cur') loc sc := by
        refine ⟨by have := hLDisj.1; dsimp only [slotCur]; omega, hLDisj.2.1,
          by rw [hSlotAg 0 (by omega)]; have := hLDisj.2.2.1; dsimp only [slotCur]; omega,
          by rw [hSlotAg 0 (by omega)]; exact hLDisj.2.2.2.1,
          by rw [hSlotAg 2 (by omega)]; have := hLDisj.2.2.2.2.1; dsimp only [slotCur]; omega,
          by rw [hSlotAg 2 (by omega)]; exact hLDisj.2.2.2.2.2.1,
          by rw [hSlotAg 4 (by omega)]; have := hLDisj.2.2.2.2.2.2.1; dsimp only [slotCur]; omega,
          by rw [hSlotAg 4 (by omega)]; exact hLDisj.2.2.2.2.2.2.2.1,
          by rw [hSlotAg 6 (by omega)]; have := hLDisj.2.2.2.2.2.2.2.2.1; dsimp only [slotCur]; omega,
          by rw [hSlotAg 6 (by omega)]; exact hLDisj.2.2.2.2.2.2.2.2.2⟩
      have hDisjCur : SelectMetaDisjoint mloc loc sc := selectMetaDisjoint_mono hDisj hScGe
      have hMetaFrCur : ∀ m', (∀ a < sc, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mCur a) →
          SelectLevelMetaAt m' mloc 4 P C' g' ℓ' φ' coreLen' := fun m' hm' =>
        hMetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hAg0 a ha hout)
      -- Call `updLvlProc` at `cur'`
      obtain ⟨b1, hb1, o1, st1, c1, hr1, hp1, hc1⟩ :=
        hUpdLvl cur' hGeCur hcurLt [loc.hb, mloc.metaBase, cur', slotCur, sc] mCur pos' ω
          (by intro v hv; simp at hv
              rcases hv with rfl | rfl | rfl | rfl | rfl
              · omega
              · have := hDisj.2.1; omega
              · omega
              · dsimp only [slotCur]; omega
              · omega)
          ⟨cur', slotCur, sc, sz, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, by omega,
            hLAtCur, hLDisjCur, hLbd, hat0, hMeta0, hDisjCur, hMetaFrCur, hz0, by omega⟩
      have hp1' := hp1
      obtain ⟨hsc1Lo, hsc1Hi, ⟨sz1, hat1, _⟩, ⟨hMeta1, hfr1⟩, hz1, _, _⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc1Lo hsc1Hi hfr1
      set sc1 := o1.value
      have hEPcur : EndPotAgree C C' φ φ' cur' := fun j hj => hEP hlimPos j (by omega)
      obtain ⟨hPref1, hMod1, hCand1⟩ :=
        selectUpdateLevel_step_mod (w := w) (evalCost := evalCost) hH hH' hSpan hSpan'
          (by omega) (by omega) hPot hPot' hEPcur (fun j hj => hWstr j (by omega))
          (fun j hj => hInsFwd j (by omega)) (hℓEq hlimPos) (hgEq hlimPos)
          (hCov cur' hGeCur hcurLt) (fun e he => (hLbd e he).1) hPref0 hMod0 hp1'
      -- Recursive call on `cur' + 1`
      obtain ⟨scOut, cRec, out, szOut, hrRec, hscOutLo, hscOutHi, hatOut, hPrefOut, hModOut,
          hCandOut, hMetaOut, hzOut, hfrOut, hcRec⟩ :=
        ih (cur' + 1) sc1 st1.pos sz1 st1.mem (by omega) (by omega) (by omega) (by omega)
          (fun a ha hout => (hfr1 a (by omega) hout).trans (hAg0 a ha hout))
          hat1 hPref1 hMod1 hMeta1 hz1 (by omega)
      -- Stitch the loop step
      let s0 := startState [loc.hb, mloc.metaBase, cur', limit, selOutBase, sc] mCur pos'
      let rg6 := Function.update s0.regs 6 slotCur
      let rg7 := Function.update rg6 7 sc1
      let rg8 := Function.update rg7 8 scOut
      have h1 : Runs w p ω
          (.assign 6 (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 12) (.reg 2))))
          s0 .normal ⟨mCur, rg6, pos'⟩ 8 :=
        runs_assign_iff.mpr ⟨slotCur, by
          simp [Expr.eval, BinOp.eval, s0, startState, show 1 < 2 ^ w by omega,
            show 12 < 2 ^ w by omega, show selOutBase + 1 < 2 ^ w by omega,
            show 12 * cur' < 2 ^ w by omega, show slotCur < 2 ^ w by dsimp only [slotCur]; omega,
            slotCur], rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.call 7 updLvlProc [.reg 0, .reg 1, .reg 2, .reg 6, .reg 5])
          ⟨mCur, rg6, pos'⟩ .normal ⟨st1.mem, rg7, st1.pos⟩ (c1 + 6) :=
        runs_call_iff.mpr ⟨[loc.hb, mloc.metaBase, cur', slotCur, sc], b1, o1, st1, c1,
          by simp [evalArgs, Expr.eval, rg6, s0, startState], hb1, hr1, rfl, rfl,
          by simp [argsSize, Expr.size]; omega⟩
      have h3 : Runs w p ω
          (.call 8 self [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1), .reg 3, .reg 4, .reg 7])
          ⟨st1.mem, rg7, st1.pos⟩ .normal ⟨out.mem, rg8, out.pos⟩ (cRec + 9) :=
        runs_call_iff.mpr ⟨[loc.hb, mloc.metaBase, cur' + 1, limit, selOutBase, sc1], _,
          .returned scOut, out, cRec,
          by simp [evalArgs, Expr.eval, BinOp.eval, rg7, rg6, s0, startState,
            show 1 < 2 ^ w by omega, show cur' + 1 < 2 ^ w by omega],
          hpLoop, hrRec, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
      have h4 : Runs w p ω (.ret (.reg 8)) ⟨out.mem, rg8, out.pos⟩ (.returned scOut)
          ⟨out.mem, rg8, out.pos⟩ 2 :=
        runs_ret_iff.mpr ⟨scOut, by simp [Expr.eval, rg8], rfl, rfl, by simp [Expr.size]⟩
      have hRunFull : Runs w p ω (selectUpdateHeapPrefixLoopBody self updLvlProc) s0
          (.returned scOut) ⟨out.mem, rg8, out.pos⟩ (c1 + cRec + 32) := by
        unfold selectUpdateHeapPrefixLoopBody
        refine runs_cond_iff.mpr ⟨1, _,
          by simp [Expr.eval, BinOp.eval, s0, startState, hcurLt, show 1 < 2 ^ w by omega],
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h2,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h3, h4, rfl⟩), rfl⟩), rfl⟩),
          by simp [Expr.size]; omega⟩
      refine ⟨scOut, c1 + cRec + 32, ⟨out.mem, rg8, out.pos⟩, szOut, hRunFull,
        by omega, by omega, hatOut, hPrefOut, hModOut,
        fun k hk => le_trans (hCandOut k hk) (hCand1 k (by omega)),
        hMetaOut, hzOut,
        fun a ha hout => (hfrOut a (by omega) hout).trans (hfr1 a ha hout), ?_⟩
      simp only [selectUpdateLevelNoRoomContract, selectUpdateLevelContract] at hc1
      rw [hCostSplit]; omega
  exact hInd (limit - cur) cur scratch pos sizeOld mem rfl le_rfl hcurLe le_rfl
    (fun _ _ _ => rfl) hat hPrefOk hModOk hMeta hz hroom

set_option maxHeartbeats 1000000 in
/-- Verification of `selectUpdateHeapPhaseBody`: runs Phase 4a (`0 .. min firstReb d - 1`) followed
by Phase 4b (`selectRebuildSuffix` from `firstReb` to `d`), restoring full `SelectHeapMatchesChain`
for `(C', g', ℓ')` across all levels `0 .. d`. -/
theorem selectUpdateHeapPhase_runs
    {w P firstReb selOutBase sizeOld evalSpace evalCost scratch pos : ℕ}
    {prefLoopProc updLvlProc rebSufProc : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ φ' coreLen' : ℕ → ℕ → ℝ} {ins : ℕ → ℕ → Prop}
    {diffLists : ℕ → LevelDiffLists} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hpLastW : mloc.pLast < 2 ^ w)
    (hFR : firstReb ≤ C'.d + 1) (hCd : C.d = C'.d)
    (hdLoc : loc.d = C'.d) (hLkEq : mloc.Lk = loc.Lk)
    (hendLe : loc.endAddr ≤ scratch)
    (hOutLe : selOutBase + 1 + 12 * min firstReb C'.d ≤ scratch)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c) (hSpan' : C'.LastLevelSpans)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ')
    (hEP : 0 < firstReb → EndPotAgree C C' φ φ' (firstReb - 1))
    (hWstr : ∀ j, j < firstReb → j ≤ C'.d → ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j, j + 1 < firstReb → j < C'.d → ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E →
      ins j f → ins (j + 1) f)
    (hℓEq : 0 < firstReb → ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : 0 < firstReb → ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hCov : ∀ j < min firstReb C'.d, LevelDiffCovers C C' j ins (diffLists j))
    (hNoRebLast : firstReb = C'.d + 1 →
      C'.G C'.d = C.G C'.d ∧ C'.activeLSF C'.d = C.activeLSF C'.d ∧
      (∀ f ∈ (C'.G C'.d).E, ¬ ins C'.d f))
    (hDiff : ∀ j < min firstReb C'.d,
      let slot := selOutBase + 1 + 12 * j
      LevelDiffListsAt mem slot (diffLists j) ∧
      LevelDiffListsDisjoint mem slot (diffLists j) loc scratch ∧
      (∀ e ∈ (diffLists j).allTouched, e < loc.cap ∧ e < mloc.eCap j))
    (hGEcap : ∀ j, firstReb ≤ j → j ≤ C'.d → ∀ e ∈ (C'.G j).E, e < loc.cap)
    (hMatchOld : SelectHeapMatchesChain mem loc 4 P C g ℓ sizeOld)
    (hMeta : SelectLevelMetaAt mem mloc 4 P C' g' ℓ' φ' coreLen')
    (hDisj : SelectMetaDisjoint mloc loc scratch)
    (hMetaFr : ∀ m', (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = mem a) →
      SelectLevelMetaAt m' mloc 4 P C' g' ℓ' φ' coreLen')
    (hpPrefLoop : p.procs[prefLoopProc]? = some (selectUpdateHeapPrefixLoopBody prefLoopProc updLvlProc))
    (hUpdLvl : ∀ j < min firstReb C'.d,
      MeetsContract w p updLvlProc
        (selectUpdateLevelNoRoomContract w 4 P loc mloc C' g' ℓ' φ' coreLen'
          (diffLists j) evalSpace evalCost))
    (hRebSuf : MeetsContract w p rebSufProc
      (selectRebuildSuffixNoRoomContract w 4 P loc mloc C' G' g' ℓ' σ' σ'_mwu γ'_ℓ γ'_c
        φ' coreLen' evalSpace evalCost))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selectUpdateHeapPhaseSpace mem loc C' diffLists firstReb evalSpace < 2 ^ w) :
    ∃ scOut cost out sizeOut,
      Runs w p ω (selectUpdateHeapPhaseBody prefLoopProc rebSufProc)
        (startState [loc.hb, mloc.metaBase, firstReb, C'.d, selOutBase, scratch] mem pos)
        (.returned scOut) out cost ∧
      scratch ≤ scOut ∧
      scOut ≤ scratch + selectUpdateHeapPhaseSpace mem loc C' diffLists firstReb evalSpace ∧
      SelectHeapMatchesChain out.mem loc 4 P C' g' ℓ' sizeOut ∧
      SelectLevelMetaAt out.mem mloc 4 P C' g' ℓ' φ' coreLen' ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, (a < loc.hb ∨ loc.endAddr ≤ a) → out.mem a = mem a) ∧
      cost ≤ selectUpdateHeapPhaseCost mem loc C' diffLists firstReb evalCost := by
  set lim := min firstReb C'.d
  have hHbLtEnd : loc.hb ≤ loc.endAddr := by rw [loc.endAddr_eq]; omega
  have hlimLe : lim ≤ C'.d := Nat.min_le_right _ _
  have hlimLeFR : lim ≤ firstReb := Nat.min_le_left _ _
  have hSpPhase : selectUpdateHeapPhaseSpace mem loc C' diffLists firstReb evalSpace =
      selectUpdateHeapPrefixLoopSpace diffLists 0 lim loc.cap loc.Lk evalSpace +
      selectRebuildSuffixSpace mem loc C' firstReb evalSpace := rfl
  have hCostPhase : selectUpdateHeapPhaseCost mem loc C' diffLists firstReb evalCost =
      selectUpdateHeapPrefixLoopCost diffLists 0 lim loc.cap loc.Lk evalCost +
      selectRebuildSuffixCost mem loc C' firstReb evalCost + 50 := rfl
  -- Step 1: Phase 4a (`selectUpdateHeapPrefixLoopBody` over `0 .. lim - 1`)
  obtain ⟨sc1, c1, st1, sz1, hr1, hsc1Lo, hsc1Hi, hat1, hPref1, hMod1, hCand1, hMeta1, hz1, hfr1, hc1⟩ :=
    selectUpdateHeapPrefixLoop_runs hw16 hpLastW (Nat.zero_le lim) hlimLe hCd hdLoc hLkEq
      hendLe hOutLe hH hSpan hH' hSpan' hPot hPot'
      (fun hpos => fun j hj => hEP (by omega) j (by omega))
      (fun j hj => hWstr j (by omega) (by omega))
      (fun j hj => hInsFwd j (by omega) (by omega))
      (fun hpos => hℓEq (by omega)) (fun hpos => hgEq (by omega))
      (fun j _ hj => hCov j hj) (fun j _ hj => hDiff j hj)
      hMatchOld.1 (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun k _ hk => selectHeapLevelOkMod_zero (selectHeapLevelOk_of_matchesChain hH hMatchOld hk))
      hMeta hDisj hMetaFr hpPrefLoop (fun j _ hj => hUpdLvl j hj) hz (by omega)
  -- Candidate counts on `firstReb .. C'.d` did not increase across Phase 4a
  have hSufSpLe : selectRebuildSuffixSpace st1.mem loc C' firstReb evalSpace ≤
      selectRebuildSuffixSpace mem loc C' firstReb evalSpace := by
    unfold selectRebuildSuffixSpace
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : firstReb ≤ j := (Finset.mem_Icc.mp hj).1
    have hle := hCand1 j (by omega)
    unfold selectRebuildLevelSpace heapClearLevelSpace
    gcongr
  have hSufCostLe : selectRebuildSuffixCost st1.mem loc C' firstReb evalCost ≤
      selectRebuildSuffixCost mem loc C' firstReb evalCost := by
    unfold selectRebuildSuffixCost
    refine Nat.add_le_add_right (Finset.sum_le_sum fun j hj => ?_) 20
    have hj1 : firstReb ≤ j := (Finset.mem_Icc.mp hj).1
    have hle := hCand1 j (by omega)
    unfold selectRebuildLevelCost heapClearLevelCost
    gcongr
  -- Step 2: Phase 4b (`selectRebuildSuffix` from `firstReb` to `C'.d`)
  have hMetaFr1 : ∀ m', (∀ a < sc1, (a < loc.hb ∨ loc.endAddr ≤ a) → m' a = st1.mem a) →
      SelectLevelMetaAt m' mloc 4 P C' g' ℓ' φ' coreLen' := fun m' hm' =>
    hMetaFr m' fun a ha hout => (hm' a (by omega) hout).trans (hfr1 a ha hout)
  have hMetaW : mloc.metaBase < 2 ^ w := by have := hDisj.2.1; omega
  have hdW : C'.d < 2 ^ w := by
    have h1 := hDisj.2.1
    have h2 : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    rw [h2, hMeta.1] at h1; omega
  have hFRW : firstReb < 2 ^ w := by omega
  obtain ⟨b2, hb2, o2, st2, c2, hr2, hp2, hc2⟩ :=
    hRebSuf [loc.hb, mloc.metaBase, firstReb, C'.d, sc1] st1.mem st1.pos ω
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨firstReb, sc1, sz1, rfl, hw16, hpLastW, by omega, hdLoc, hLkEq, hH', hGEcap,
        hat1, hMeta1, selectMetaDisjoint_mono hDisj hsc1Lo, hMetaFr1, hz1, by omega⟩
  have hp2' := hp2
  obtain ⟨hsc2Lo, hsc2Hi, _, ⟨hMeta2, hfr2⟩, hz2, _, _⟩ := hp2
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc2Lo hsc2Hi hfr2 hc2
  set sc2 := o2.value
  -- Combine `hPref1` (and level `C'.d` when `firstReb = C'.d + 1`) with `selectUpdate_preserves_matchesChain`
  have hPrefFull : ∀ j < firstReb, j ≤ C'.d → SelectHeapLevelOk st1.mem loc 4 P C' g' ℓ' j := by
    intro j hjFR hjD
    by_cases hlt : j < lim
    · exact hPref1 j hlt
    · have hFREq : firstReb = C'.d + 1 := by omega
      have hjEq : j = C'.d := by omega
      subst hjEq
      obtain ⟨hGdEq, hLSFdEq, hNoInsD⟩ := hNoRebLast hFREq
      have hModD : SelectHeapLevelOkMod st1.mem loc 4 P C C' g ℓ C'.d C'.d := by
        have hlimEq : lim = C'.d := by omega
        simpa only [hlimEq] using hMod1 C'.d hlimLe (by omega)
      have hCoreEq : (C'.activeCore C'.d).E = (C.activeCore C'.d).E := by
        simp [TreeChain.activeCore, coreGraph, hGdEq, hLSFdEq]
      have hSEq : (C'.activeS C'.d).E = (C.activeS C'.d).E := by
        simp [TreeChain.activeS, hCd]
      have hEmbEq : ∀ e, C'.activeEmb C'.d e = C.activeEmb C'.d e := fun e => by
        simp [TreeChain.activeEmb, hCd]
      refine ⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩
      · rw [hCoreEq, hSEq]; exact hModD.1 e heCap hnz hl
      · have hOld : e ∈ (C.activeCore C'.d).E \ (C.activeS C'.d).E := by rwa [← hCoreEq, ← hSEq]
        have hNotPrev : ∀ k < C'.d, e ∉ (C'.activeCore k).E \ (C'.activeS k).E := fun k hk hek => by
          have := C'.level_unique_of_mem_activeCore_diff hH' (by omega) le_rfl hek he; omega
        obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hModD.2 e hOld hNotPrev
        have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan (by omega) hOld
        have hWstrCycle : ∀ k ≤ C'.d, ∀ f ∈ walkEdges (C.sparsifierCycle C'.d e),
            (C'.activeLSF k).wstr f = (C.activeLSF k).wstr f := by
          intro k hk f hfW
          have hfGd : f ∈ (C.G C'.d).E :=
            (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed hfW)).1
          have hfGd' : f ∈ (C'.G C'.d).E := hGdEq.symm ▸ hfGd
          have hNotInsK : ¬ ins k f := by
            intro hinsK
            have hUp : ∀ m, k ≤ m → m ≤ C'.d → ins m f := by
              intro m hkm
              induction m with
              | zero =>
                intro _
                have hk0 : k = 0 := by omega
                rw [← hk0]; exact hinsK
              | succ m ih =>
                intro hmD
                by_cases hkm' : k = m + 1
                · subst hkm'; exact hinsK
                · exact hInsFwd m (by omega) (by omega) f
                    (C'.G_E_subset_of_le hH' hmD le_rfl hfGd')
                    (C.G_E_subset_of_le hH (by omega) (by omega) hfGd)
                    (ih (by omega) (by omega))
            exact hNoInsD f hfGd' (hUp C'.d hk le_rfl)
          exact hWstr k (by omega) hk f
            (C'.G_E_subset_of_le hH' hk le_rfl hfGd')
            (C.G_E_subset_of_le hH (by omega) (by omega) hfGd) hNotInsK
        obtain ⟨hwi, hwl⟩ := walkInner_and_wlenAt_eq_of_unchanged_emb_phi C C' hH hSpan hH' hSpan'
          (by omega) le_rfl φ φ' (fun k hk => hPot k (by omega)) (fun k hk => hPot' k hk)
          (by simpa [hFREq] using hEP (by omega))
          hWstrCycle (hℓEq (by omega)) (hgEq (by omega)) hOld he (hEmbEq e)
        exact ⟨heCap, hnz0, hl0, by rw [hwi, hwl]; exact hrep0⟩
  obtain ⟨sizeOut, hMatchOut⟩ :=
    selectUpdate_preserves_matchesChain (w := w) (evalCost := evalCost) hH' hdLoc hPrefFull hp2'
  -- Stitch `selectUpdateHeapPhaseBody`
  let s0 := startState [loc.hb, mloc.metaBase, firstReb, C'.d, selOutBase, scratch] mem pos
  let rg6 := Function.update s0.regs 6 lim
  let rg7 := Function.update rg6 7 sc1
  let rg8 := Function.update rg7 8 sc2
  have hLimRun : ∃ cL,
      Runs w p ω (.cond (.bin .lt (.reg 2) (.reg 3)) (.assign 6 (.reg 2)) (.assign 6 (.reg 3)))
        s0 .normal ⟨mem, rg6, pos⟩ cL ∧ cL ≤ 8 := by
    by_cases hlt : firstReb < C'.d
    · have hlimEq : lim = firstReb := Nat.min_eq_left (Nat.le_of_lt hlt)
      have rT : Runs w p ω (.assign 6 (.reg 2)) s0 .normal ⟨mem, rg6, pos⟩ 2 :=
        runs_assign_iff.mpr ⟨lim, by simp [Expr.eval, s0, startState, hlimEq], rfl, rfl, by simp [Expr.size]⟩
      exact ⟨_, runs_cond_iff.mpr ⟨1, _,
        by simp [Expr.eval, BinOp.eval, s0, startState, hlt, show 1 < 2 ^ w by omega],
        by simpa using rT, rfl⟩, by simp [Expr.size]⟩
    · have hlimEq : lim = C'.d := Nat.min_eq_right (by omega)
      have rF : Runs w p ω (.assign 6 (.reg 3)) s0 .normal ⟨mem, rg6, pos⟩ 2 :=
        runs_assign_iff.mpr ⟨lim, by simp [Expr.eval, s0, startState, hlimEq], rfl, rfl, by simp [Expr.size]⟩
      exact ⟨_, runs_cond_iff.mpr ⟨0, _,
        by simp [Expr.eval, BinOp.eval, s0, startState, hlt, show 0 < 2 ^ w by omega],
        rF, rfl⟩, by simp [Expr.size]⟩
  obtain ⟨cL, rLim, hcL⟩ := hLimRun
  have rCall1 : Runs w p ω (.call 7 prefLoopProc [.reg 0, .reg 1, .const 0, .reg 6, .reg 4, .reg 5])
      ⟨mem, rg6, pos⟩ .normal ⟨st1.mem, rg7, st1.pos⟩ (c1 + 7) :=
    runs_call_iff.mpr ⟨[loc.hb, mloc.metaBase, 0, lim, selOutBase, scratch], _, .returned sc1, st1, c1,
      by simp [evalArgs, Expr.eval, rg6, s0, startState, show 0 < 2 ^ w by omega],
      hpPrefLoop, hr1, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have rCall2 : Runs w p ω (.call 8 rebSufProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 7])
      ⟨st1.mem, rg7, st1.pos⟩ .normal ⟨st2.mem, rg8, st2.pos⟩ (c2 + 6) :=
    runs_call_iff.mpr ⟨[loc.hb, mloc.metaBase, firstReb, C'.d, sc1], b2, o2, st2, c2,
      by simp [evalArgs, Expr.eval, rg7, rg6, s0, startState],
      hb2, hr2, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  have rRet : Runs w p ω (.ret (.reg 8)) ⟨st2.mem, rg8, st2.pos⟩ (.returned sc2)
      ⟨st2.mem, rg8, st2.pos⟩ 2 :=
    runs_ret_iff.mpr ⟨sc2, by simp [Expr.eval, rg8], rfl, rfl, by simp [Expr.size]⟩
  have rFull : Runs w p ω (selectUpdateHeapPhaseBody prefLoopProc rebSufProc) s0
      (.returned sc2) ⟨st2.mem, rg8, st2.pos⟩ (cL + c1 + c2 + 18) := by
    unfold selectUpdateHeapPhaseBody
    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, rLim,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCall1,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, rCall2, rRet, rfl⟩), rfl⟩), by omega⟩)
  refine ⟨sc2, cL + c1 + c2 + 18, ⟨st2.mem, rg8, st2.pos⟩, sizeOut, rFull,
    by omega, by rw [hSpPhase]; omega, hMatchOut, hMeta2, hz2,
    fun a ha hout => (hfr2 a (by omega) hout).trans (hfr1 a ha hout), ?_⟩
  simp only [selectRebuildSuffixNoRoomContract, selectRebuildSuffixContract,
    List.getD_cons_zero, List.getD_cons_succ] at hc2
  rw [hCostPhase]; omega

end MinCostFlow.MinRatio
