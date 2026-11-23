module

public import MinCostFlow.MinRatio.WireShiftDeepSelectFinalize
import Mathlib.Tactic

/-!
# Definitions and layout helpers for rebuilt suffix block update (`SelectUpdateSuffixDefs`)

Defines the Phase 3b procedure `selectUpdateSuffixBlocksBody`, its scratch space and step cost,
and the address-disjointness helpers used in `SelectUpdateSuffixBlocks.lean`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

/-- Phase 3b body: if `firstReb ≤ d`, refresh rebuilt interior blocks `firstReb .. d - 1`, read out
`G_d` via `op 3`, refill last level `d`, and fill level potentials `φ_{firstReb} .. φ_d`.
Arguments: `[metaBase, firstReb, d, levelTable, lvlMeta, termHandle, termBran, Lk, slotSz, pLast,
scratch]` (`reg 0..10`). Returns `scOut`. -/
def selectUpdateSuffixBlocksBody (initIntLoop op3 fillLast phiLoop : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.bin .add (.reg 2) (.const 1)))
    (.call 11 initIntLoop [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8, .reg 10] ;;
     .assign 12 (.bin .sub (.reg 2) (.const 1)) ;;
     .assign 13 (.load (.bin .add (.reg 3) (.reg 12))) ;;
     .assign 14 (.load (.bin .add (.bin .add (.reg 3) (.bin .add (.reg 2) (.const 1))) (.reg 12))) ;;
     .call 15 op3 [.reg 13, .reg 14, .reg 11] ;;
     .assign 16 (.load (.reg 11)) ;;
     .assign 17 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .mul (.const 4) (.bin .add (.reg 2) (.const 1)))) (.reg 12))) ;;
     .call 18 fillLast [.reg 0, .reg 2, .reg 5, .reg 6, .reg 17, .reg 7, .reg 9, .reg 16, .reg 15] ;;
     .call 19 phiLoop [.reg 0, .reg 1, .reg 2, .reg 7, .reg 18] ;;
     .ret (.reg 19))
    (.ret (.reg 10))

theorem selectUpdateSuffixBlocksBody_noRand (initIntLoop op3 fillLast phiLoop : ℕ) :
    (selectUpdateSuffixBlocksBody initIntLoop op3 fillLast phiLoop).NoRand := by
  simp [selectUpdateSuffixBlocksBody, Stmt.NoRand]

/-- Scratch space for `selectUpdateSuffixBlocksBody` (0 when `firstReb > P.d`). -/
noncomputable def selectUpdateSuffixBlocksSpace {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (firstReb L capExp : ℕ) : ℕ :=
  if firstReb ≤ P.d then
    selectInitInteriorLoopSpace C firstReb L capExp + 1 +
    selectFillLastLevelSpace (C.G P.d).m (C.toTreeChain.activeLSF P.d).F.F.m L +
    selectPhiLoopSpace C.toTreeChain firstReb L
  else 0

/-- Step cost for `selectUpdateSuffixBlocksBody` (`12` when `firstReb > P.d`). -/
noncomputable def selectUpdateSuffixBlocksCost {T : SparseCoreRestartTool} {P : ChainParams}
    (oldF : ℕ → MGraph) (oldGd : MGraph) (C : ChainState T P)
    (readoutCost firstReb L capExp slot : ℕ) : ℕ :=
  if firstReb ≤ P.d then
    selectRefreshInteriorLoopCost oldF C readoutCost firstReb L capExp slot +
    readoutCost +
    selectFillLastLevelCost oldGd.n oldGd.m (oldF P.d).n (oldF P.d).m
      (C.G P.d).n (C.G P.d).m (C.toTreeChain.activeLSF P.d).F.F.n
      (C.toTreeChain.activeLSF P.d).F.F.m L +
    selectPhiLoopCost C.toTreeChain firstReb L + 120
  else 12

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

lemma prevLen_disj_last {B : SelectBlocksLoc} (hdPos : 0 < B.d) :
    B.lenPtr (B.d - 1) + B.eCap * B.Lk ≤ B.fPtr B.d ∧
    B.lenPtr (B.d - 1) + B.eCap * B.Lk ≤ B.lenPtr B.d ∧
    B.lenPtr (B.d - 1) + B.eCap * B.Lk ≤ B.lastGPtr := by
  have h1 : B.lenPtr (B.d - 1) + B.eCap * B.Lk ≤ B.fPtr (B.d - 1) + B.levelSize := by
    unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; omega
  have h2 : B.fPtr (B.d - 1) + B.levelSize = B.fPtr B.d := by
    unfold SelectBlocksLoc.fPtr
    cases hd : B.d with | zero => omega | succ k => simp [Nat.succ_mul]; omega
  have h3 : B.fPtr B.d ≤ B.lenPtr B.d := by unfold SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr; omega
  have h4 := B.blk_le_last (le_refl B.d)
  omega

lemma regLast_F_Len_in_B {B : SelectBlocksLoc} {a : ℕ}
    (h : B.regLast a ∨ B.regF B.d a ∨ B.regLen B.d a) : B.base ≤ a ∧ a < B.endAddr := by
  have hbl := B.blk_le_last (le_refl B.d)
  have hbf : B.base ≤ B.fPtr B.d := by unfold SelectBlocksLoc.fPtr; omega
  have hle : B.lastGPtr + dynGraphSize B.vCap B.eCap ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  rcases h with hL | hF | hLn
  · unfold SelectBlocksLoc.regLast SelectBlocksLoc.g0Ptr at hL; omega
  · unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr at hF
    unfold SelectBlocksLoc.levelSize at hbl; omega
  · unfold SelectBlocksLoc.regLen SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr
      SelectBlocksLoc.phiPtr at hLn
    unfold SelectBlocksLoc.levelSize at hbl; omega

lemma phiLoop_disj_helper {B : SelectBlocksLoc} {sb metaBase pLast sc d vCap eCap L : ℕ}
    {gPtr : ℕ → ℕ} (hBd : B.d = d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hsbLeBase : sb ≤ B.base) (hMetaEnd : metaBase + selectLevelMetaSize B.d = B.base)
    (hEndLeSc : B.endAddr ≤ sc)
    (hGEnd : ∀ j < d, gPtr j + dynGraphSize vCap eCap ≤ sc ∧
      (gPtr j + dynGraphSize vCap eCap ≤ sb ∨ B.endAddr ≤ gPtr j)) :
    let mloc := selectMlocOf B metaBase gPtr pLast
    ∀ j ≤ d,
      SelectPhiPrefixBelow mloc j sc ∧ SelectPhiTargetDisjoint mloc j sc ∧
      mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ sc ∧
      (∀ j', j ≤ j' → j' ≤ d →
        mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.GPtr j' ∨
          mloc.GPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) ∧
      (∀ j', j < j' → j' ≤ d →
        mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.fPtr j' ∨
          mloc.fPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) := by
  intro mloc j hj
  have hLastLeG0 : B.lastGPtr + dynGraphSize vCap eCap = B.g0Ptr := by rw [← hBv, ← hBe]; rfl
  have hG0LeEnd : B.g0Ptr + eCap * L = B.endAddr := by rw [← hBe, ← hBLk]; rfl
  have hphiBnd : ∀ k ≤ d,
      B.base ≤ B.fPtr k ∧ B.fPtr k + dynGraphSize vCap eCap = B.phiPtr k ∧
      B.phiPtr k + vCap * L ≤ B.fPtr k + B.levelSize ∧ B.fPtr k + B.levelSize ≤ B.lastGPtr := by
    intro k hk
    refine ⟨by unfold SelectBlocksLoc.fPtr; omega, by rw [← hBv, ← hBe]; rfl, ?_, B.blk_le_last (by omega)⟩
    unfold SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize; rw [hBv, hBe, hBLk]; omega
  have hGPBnd : ∀ k ≤ d, mloc.GPtr k + dynGraphSize (mloc.vCap k) (mloc.eCap k) ≤ sc := fun k hk => by
    dsimp only [mloc, selectMlocOf]; rw [hBd, hBv, hBe]
    by_cases hlt : k < d
    · simp only [hlt, ↓reduceIte]; exact (hGEnd k hlt).1
    · simp only [hlt, ↓reduceIte]; omega
  have hjB := hphiBnd j hj
  refine ⟨⟨by simp only [mloc, selectMlocOf]; omega,
      by simp only [mloc, selectMlocOf]; rw [hBe, hBLk]; omega,
      fun k hk => ⟨hGPBnd k (by omega), by
        have := hphiBnd k (by omega); simp only [mloc, selectMlocOf]; rw [hBv, hBLk]; omega⟩⟩,
    ⟨by simp only [mloc, selectMlocOf]; rw [hBv, hBLk]; omega,
     by simp only [mloc, selectMlocOf]; rw [hBv, hBe]; omega,
     Or.inl (by simp only [mloc, selectMlocOf]; omega),
     Or.inr (by simp only [mloc, selectMlocOf]; rw [hBv, hBLk]; omega),
     Or.inl (by simp only [mloc, selectMlocOf]; rw [hBv, hBe]; omega),
     fun k hk => by
       have hlt : k < d := by omega
       have hkj := B.blk_le_of_lt hk
       have hkB := hphiBnd k (by omega)
       refine ⟨?_, Or.inl ?_⟩
       · simp only [mloc, selectMlocOf, hBd, hlt, ↓reduceIte, hBv, hBe, hBLk]
         rcases (hGEnd k hlt).2 with h1 | h2 <;> [left; right] <;> omega
       · simp only [mloc, selectMlocOf, hBv, hBLk]; omega⟩,
    hGPBnd j hj,
    fun j' hj1 hj2 => by
      dsimp only [mloc, selectMlocOf]; rw [hBd, hBv, hBe, hBLk]
      by_cases hlt : j' < d
      · simp only [hlt, ↓reduceIte]; rcases (hGEnd j' hlt).2 with h1 | h2 <;> [right; left] <;> omega
      · simp only [hlt, ↓reduceIte]; left; omega,
    fun j' hj1 _ => by
      have hlt := B.blk_le_of_lt hj1
      left; simp only [mloc, selectMlocOf, hBv, hBLk]; omega⟩

end MinCostFlow.MinRatio
