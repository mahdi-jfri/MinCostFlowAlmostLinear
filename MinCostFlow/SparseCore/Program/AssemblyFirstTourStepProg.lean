module

public import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepSync
public import MinCostFlow.SparseCore.Program.OutProcs
public import WordRAM.CopyWords

import Mathlib.Tactic

/-!
# Deterministic Word-RAM procedures for the block-by-block tour step (`AssemblyFirstTourStepProg`)

Defines the three deterministic Word-RAM procedures implementing `AsmFirstTourBlockStepAt` on
`tourAsmRep` using P2's operations (`tourOp 0, 1, 3`, `tourDedupSelBody` at `bTour + 75`),
P7's helper (`outIdxSmallSide`), and `copyWords`:

1. `asmFirstTourConsumeRelStmt fCut fSmallSide` (`[tourH, spPtr, nSplits, statePtr, hCur]`):
   consumes all leading `isRelease = true` entries from `spPtr` starting at `spIdx = mem[statePtr]`,
   calling `tourOp 1` (`cut`) and `outIdxSmallSide` for each release and updating
   `statePtr = [spIdx, splitPtr, last]`.
2. `asmFirstTourApplyMoveStmt fDedup fApplyEdits` (`[tourH, ePtr, hCur]`):
   deduplicates a `moveEnds` edit's key list via `tourDedupSelBody` (`bTour + 75`) into a valid
   1-edit `OrdEditsAt` buffer at `hCur` and applies it via `tourOp 0` (`applyEdits`).
3. `asmFirstTourBlockStepStmt fCopy fConsumeRel fApplyMove fApplyEdits fCut fChRoot fSmallSide`
   (`[tourH, batch, words, edits, editWords, spPtr, h]`):
   applies `OrdEditsForBatch` block by block alongside `batch` and `spPtr`, followed by
   `editRotBlock`, writing `splitPtr` at `h`.

Also proves determinism (`asmFirstTourBlockProcs_noRand`) and verifies the two helper procedures
(`asmFirstTourApplyMove_runs` and `asmFirstTourConsumeRel_runs`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-! ## 1. Procedures and space/cost constants -/

public section

/-- Multiplier of P7's `outSmallSide` (`sig_outSmallSide_runs_outProcs`). Kept non-exposed so
downstream proofs never unfold `Classical.choose sig_outSmallSide_runs_outProcs`. -/
noncomputable def outSmallSideMul : ℕ :=
  Classical.choose sig_outSmallSide_runs_outProcs

theorem outSmallSideMul_spec :
    ∀ (S : OutTourSpec) (w vCap eCap : ℕ) (p : Program) (b nm sm fm lm : ℕ),
      OutProcsAt p b nm sm fm lm → (vCap + eCap + 2) ^ 2 < 2 ^ w →
      ∀ (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH r₁ r₂ v v' last h : ℕ)
        (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        let side := if (s.markedList r₁).length ≤ (s.markedList r₂).length then 0 else 1
        let Y := s.markedList (if side = 0 then r₁ else r₂)
        (∀ a ∈ [tourH, r₁, r₂, v, v', last, h], a < 2 ^ w) → r₁ < vCap → r₂ < vCap →
        (s.cord r₁).Nodup → (s.cord r₂).Nodup →
        (∀ x ∈ s.markedList r₁ ++ s.markedList r₂, x.1 < eCap) →
        T.rep.rep tourH s tx mem → (∀ a, T.rep.foot tourH tx a → a < h) → 0 < h →
        (last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx (last + 4))) →
        ZeroFrom mem h → h + outSmallSideSpace S (2 * eCap) < 2 ^ w →
        ∃ body, p.procs[outIdxSmallSide b]? = some body ∧ ∃ o st' c tx',
          Runs w p ω body (startState [tourH, r₁, r₂, v, v', last, h] mem pos) o st' c ∧
          T.rep.rep tourH s tx' st'.mem ∧
          st'.mem h = v ∧ st'.mem (h + 1) = v' ∧ st'.mem (h + 2) = side ∧ st'.mem (h + 4) = 0 ∧
          EndListAt st'.mem (st'.mem (h + 3)) Y ∧
          Y.length ≤ (s.markedList (if side = 0 then r₂ else r₁)).length ∧
          h + 5 ≤ st'.mem (h + 3) ∧ o.value = st'.mem (h + 3) + 1 + Y.length ∧
          o.value ≤ h + outSmallSideSpace S (2 * eCap) ∧ ZeroFrom st'.mem o.value ∧
          (last ≠ 0 → st'.mem (last + 4) = h) ∧
          (∀ a < h, ¬ T.rep.foot tourH tx a → (last = 0 ∨ a ≠ last + 4) → st'.mem a = mem a) ∧
          (∀ a, T.rep.foot tourH tx' a →
            T.rep.foot tourH tx a ∨ (h + 5 ≤ a ∧ a < st'.mem (h + 3))) ∧
          c + T.rep.phi tourH tx' st'.mem ≤
            outSmallSideMul * (S.mul + 1) * (Y.length + 1) * ordStoreLog eCap + T.rep.phi tourH tx mem :=
  Classical.choose_spec sig_outSmallSide_runs_outProcs

end

@[expose] public section

/-- Helper 1 (`[tourH, spPtr, nSplits, statePtr, hCur]`): consumes consecutive `isRelease = true`
entries from `spPtr` starting at `spIdx = mem[statePtr]`, calling `fCut` (`tourOp 1`) and
`fSmallSide` (`outIdxSmallSide`), updating `[spIdx, splitPtr, last]` at `statePtr`, and returning
the new `hCur`. -/
def asmFirstTourConsumeRelStmt (fCut fSmallSide : ℕ) : Stmt :=
  .assign 5 (.load (.reg 3)) ;;                                           -- spIdx
  .assign 6 (.load (.bin .add (.reg 3) (.const 1))) ;;                    -- splitPtr
  .assign 7 (.load (.bin .add (.reg 3) (.const 2))) ;;                    -- last
  .assign 8 (.const 0) ;;                                                 -- cont flag
  .cond (.bin .lt (.reg 5) (.reg 2))
    (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
      (.bin .mul (.const 4) (.reg 5)))))
    .nop ;;
  .loop (.reg 8)
    (.assign 9 (.bin .add (.bin .add (.reg 1) (.const 1))
      (.bin .mul (.const 4) (.reg 5))) ;;                                 -- entryPtr
     .assign 10 (.load (.bin .add (.reg 9) (.const 1))) ;;                -- e
     .assign 11 (.load (.bin .add (.reg 9) (.const 2))) ;;                -- kept
     .assign 12 (.load (.bin .add (.reg 9) (.const 3))) ;;                -- fresh
     .call 4 fCut [.reg 0, .reg 10, .reg 12, .reg 4] ;;
     .assign 13 (.reg 4) ;;                                               -- recPtr
     .call 4 fSmallSide [.reg 0, .reg 11, .reg 12, .reg 11, .reg 12, .reg 7, .reg 13] ;;
     .cond (.bin .eq (.reg 6) (.const 0)) (.assign 6 (.reg 13)) .nop ;;
     .assign 7 (.reg 13) ;;
     .assign 5 (.bin .add (.reg 5) (.const 1)) ;;
     .assign 8 (.const 0) ;;
     .cond (.bin .lt (.reg 5) (.reg 2))
       (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const 1))
         (.bin .mul (.const 4) (.reg 5)))))
       .nop) ;;
  .store (.reg 3) (.reg 5) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 6) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 7) ;;
  .ret (.reg 4)

/-- Helper 2 (`[tourH, ePtr, hCur]`): writes a deduplicated 1-edit `moveEnds` record at `hCur`
via `fDedup` (`bTour + 75`) and applies it via `fApplyEdits` (`tourOp 0`), returning the new
`hCur`. -/
def asmFirstTourApplyMoveStmt (fDedup fApplyEdits : ℕ) : Stmt :=
  .assign 3 (.load (.reg 1)) ;;                                           -- tag
  .assign 4 (.load (.bin .add (.reg 1) (.const 1))) ;;                    -- v
  .assign 5 (.load (.bin .add (.reg 1) (.const 2))) ;;                    -- v'
  .assign 6 (.load (.bin .add (.reg 1) (.const 3))) ;;                    -- m
  .assign 7 (.bin .add (.reg 1) (.const 4)) ;;                            -- keysPtr
  .store (.reg 2) (.const 1) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 3) ;;
  .store (.bin .add (.reg 2) (.const 2)) (.reg 4) ;;
  .store (.bin .add (.reg 2) (.const 3)) (.reg 5) ;;
  .assign 8 (.bin .add (.reg 2) (.const 5)) ;;                            -- outKeysPtr
  .call 9 fDedup [.reg 0, .reg 7, .reg 6, .reg 8] ;;                      -- m'
  .store (.bin .add (.reg 2) (.const 4)) (.reg 9) ;;
  .assign 10 (.bin .add (.const 5) (.reg 9)) ;;                           -- w1 = 5 + m'
  .assign 11 (.bin .add (.reg 2) (.reg 10)) ;;                            -- h1 = hCur + w1
  .call 12 fApplyEdits [.reg 0, .reg 2, .reg 10, .reg 11] ;;
  .ret (.reg 12)

/-- Main block-by-block tour step procedure `[tourH, batch, words, edits, editWords, spPtr, h]`. -/
def asmFirstTourBlockStepStmt (fCopy fConsumeRel fApplyMove fApplyEdits fCut fChRoot fSmallSide : ℕ) :
    Stmt :=
  .assign 7 (.bin .add (.reg 6) (.const 1)) ;;                            -- statePtr = h + 1
  .assign 8 (.bin .add (.reg 6) (.const 4)) ;;                            -- edCopy = h + 4
  .call 15 fCopy [.reg 3, .reg 8, .reg 4] ;;
  .assign 9 (.bin .add (.reg 8) (.reg 4)) ;;                              -- hCur = edCopy + editWords
  .assign 10 (.load (.reg 5)) ;;                                          -- nSplits = mem[spPtr]
  .call 9 fConsumeRel [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9] ;;
  .assign 11 (.load (.reg 1)) ;;                                          -- nUpd = mem[batch]
  .assign 12 (.bin .add (.reg 1) (.const 1)) ;;                           -- uPtr
  .assign 13 (.bin .add (.reg 8) (.const 1)) ;;                           -- ePtr
  .assign 14 (.const 0) ;;                                                -- eIdx
  .assign 15 (.const 0) ;;                                                -- i
  .loop (.bin .lt (.reg 15) (.reg 11))
    (.assign 16 (.load (.reg 12)) ;;                                      -- tag
     .cond (.bin .eq (.reg 16) (.const 0))
       (-- `.insert e a b`: wrap 2 insertBefore edits (8 words) and apply
        .store (.reg 9) (.const 2) ;;
        .call 17 fCopy [.reg 13, .bin .add (.reg 9) (.const 1), .const 8] ;;
        .call 9 fApplyEdits [.reg 0, .reg 9, .const 9, .bin .add (.reg 9) (.const 9)] ;;
        .assign 12 (.bin .add (.reg 12) (.const 4)) ;;
        .assign 13 (.bin .add (.reg 13) (.const 8)) ;;
        .assign 14 (.bin .add (.reg 14) (.const 2)))
       (.cond (.bin .eq (.reg 16) (.const 1))
         (-- `.delete e`: check `isOpen(e)` in tourRep
          .assign 17 (.load (.bin .add (.reg 12) (.const 1))) ;;          -- e
          .assign 18 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
          .assign 19 (.load (.bin .add (.reg 18) (.bin .mul (.const 2) (.reg 17)))) ;; -- uNode
          .assign 20 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
          .assign 21 (.load (.bin .add (.bin .add (.reg 20) (.bin .mul (.const 17) (.reg 19)))
            (.const 9))) ;;                                               -- isOpen
          .cond (.bin .eq (.reg 21) (.const 0))
            (-- forest delete: consume split entry, cut, dropEdge, outSmallSide, consumeReleases
             .assign 22 (.load (.reg 7)) ;;                               -- spIdx
             .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1))
               (.bin .mul (.const 4) (.reg 22))) ;;                       -- entryPtr
             .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;       -- kept
             .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;       -- fresh
             .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
             .call 9 fCut [.reg 0, .reg 17, .reg 25, .reg 9] ;;
             .store (.reg 9) (.const 1) ;;
             .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
             .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
             .call 9 fApplyEdits [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)] ;;
             .assign 26 (.reg 9) ;;                                       -- recPtr
             .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;        -- last
             .call 9 fSmallSide [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
             .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
               (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
               .nop ;;
             .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
             .call 9 fConsumeRel [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9])
            (-- non-forest delete: wrap `[1, 0, e]` and apply
             .store (.reg 9) (.const 1) ;;
             .store (.bin .add (.reg 9) (.const 1)) (.const 0) ;;
             .store (.bin .add (.reg 9) (.const 2)) (.reg 17) ;;
             .call 9 fApplyEdits [.reg 0, .reg 9, .const 3, .bin .add (.reg 9) (.const 3)]) ;;
          .assign 12 (.bin .add (.reg 12) (.const 2)) ;;
          .assign 13 (.bin .add (.reg 13) (.const 2)) ;;
          .assign 14 (.bin .add (.reg 14) (.const 1)))
         (-- `.split v v' ...`: applyMove, consume split entry, changeRoot, outSmallSide, consumeRel
          .assign 17 (.load (.bin .add (.reg 12) (.const 1))) ;;          -- v
          .assign 18 (.load (.bin .add (.reg 12) (.const 2))) ;;          -- v'
          .assign 19 (.load (.bin .add (.reg 12) (.const 3))) ;;          -- kt
          .assign 20 (.load (.bin .add (.reg 12) (.const 4))) ;;          -- kh
          .assign 21 (.load (.bin .add (.reg 13) (.const 3))) ;;          -- m
          .call 9 fApplyMove [.reg 0, .reg 13, .reg 9] ;;
          .assign 22 (.load (.reg 7)) ;;                                  -- spIdx
          .assign 23 (.bin .add (.bin .add (.reg 5) (.const 1))
            (.bin .mul (.const 4) (.reg 22))) ;;                          -- entryPtr
          .assign 24 (.load (.bin .add (.reg 23) (.const 2))) ;;          -- kept
          .assign 25 (.load (.bin .add (.reg 23) (.const 3))) ;;          -- fresh
          .store (.reg 7) (.bin .add (.reg 22) (.const 1)) ;;
          .assign 26 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
          .assign 27 (.load (.bin .add (.reg 26) (.reg 18))) ;;           -- isRoot[v']
          .assign 28 (.reg 17) ;;                                         -- rTmp := v
          .cond (.bin .eq (.reg 27) (.const 1)) (.assign 28 (.reg 18)) .nop ;;
          .call 9 fChRoot [.reg 0, .reg 28, .reg 25, .reg 9] ;;
          .assign 26 (.reg 9) ;;                                          -- recPtr
          .assign 27 (.load (.bin .add (.reg 7) (.const 2))) ;;           -- last
          .call 9 fSmallSide [.reg 0, .reg 24, .reg 25, .reg 24, .reg 25, .reg 27, .reg 26] ;;
          .cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.const 0))
            (.store (.bin .add (.reg 7) (.const 1)) (.reg 26))
            .nop ;;
          .store (.bin .add (.reg 7) (.const 2)) (.reg 26) ;;
          .call 9 fConsumeRel [.reg 0, .reg 5, .reg 10, .reg 7, .reg 9] ;;
          .assign 12 (.bin .add (.bin .add (.reg 12) (.const 5))
            (.bin .add (.reg 19) (.reg 20))) ;;
          .assign 13 (.bin .add (.bin .add (.reg 13) (.const 4)) (.reg 21)) ;;
          .assign 14 (.bin .add (.reg 14) (.const 1)))) ;;
     .assign 15 (.bin .add (.reg 15) (.const 1))) ;;
  -- Trailing `rotateTo` block (`editRotBlock U ed`)
  .assign 16 (.load (.reg 8)) ;;                                          -- totalEdits
  .assign 17 (.bin .sub (.reg 16) (.reg 14)) ;;                           -- remRot
  .cond (.bin .lt (.const 0) (.reg 17))
    (.assign 18 (.bin .sub (.bin .add (.reg 8) (.reg 4)) (.reg 13)) ;;    -- rotWords
     .store (.reg 9) (.reg 17) ;;
     .call 19 fCopy [.reg 13, .bin .add (.reg 9) (.const 1), .reg 18] ;;
     .assign 20 (.bin .add (.const 1) (.reg 18)) ;;
     .call 9 fApplyEdits [.reg 0, .reg 9, .reg 20, .bin .add (.reg 9) (.reg 20)])
    .nop ;;
  .store (.reg 6) (.load (.bin .add (.reg 7) (.const 1))) ;;              -- mem[h] := splitPtr
  .ret (.reg 9)

/-- The 3-procedure relocatable block for the block-by-block tour step starting at base `bSelf`.
* `bSelf + 0`: `asmFirstTourConsumeRelStmt`
* `bSelf + 1`: `asmFirstTourApplyMoveStmt`
* `bSelf + 2`: `asmFirstTourBlockStepStmt` (main entry) -/
def asmFirstTourBlockProcs (bSelf bTour bOut bCopy : ℕ) : List Stmt :=
  [ asmFirstTourConsumeRelStmt (tourOp bTour 1) (outIdxSmallSide bOut),
    asmFirstTourApplyMoveStmt (bTour + 75) (tourOp bTour 0),
    asmFirstTourBlockStepStmt bCopy (bSelf + 0) (bSelf + 1) (tourOp bTour 0) (tourOp bTour 1)
      (tourOp bTour 3) (outIdxSmallSide bOut) ]

/-- Heap space per consumed split (cut + `outSmallSide`). -/
def tourSplitStepSpace (eCap : ℕ) : ℕ :=
  2 + outSmallSideSpace tourOutSpec (2 * eCap)

/-- Total heap space of `asmFirstTourBlockStepStmt`: quadratic in `vCap + eCap + words + editWords`
and completely free of `limbMul`. -/
def tourBlockStepSpace (vCap eCap words editWords : ℕ) : ℕ :=
  64 + 160 * (words + editWords) + vCap * tourSplitStepSpace eCap

/-- Cost multiplier of `asmFirstTourApplyMoveStmt` per word of the `moveEnds` edit. -/
def tourApplyMoveMul : ℕ :=
  tourMul + 150

end

public section

/-- Parametric cost multiplier for `asmFirstTourConsumeRelStmt` (kept parametric so rewriting by
`tourConsumeRelMulFn_eq` never reduces `tourMul` or `outSmallSideMul` in the kernel). -/
@[expose] def tourConsumeRelMulFn (mTour mOut mSpec : ℕ) : ℕ :=
  mTour + mOut * (mSpec + 1) + 200

theorem tourConsumeRelMulFn_eq (mTour mOut mSpec : ℕ) :
    tourConsumeRelMulFn mTour mOut mSpec = mTour + mOut * (mSpec + 1) + 200 := rfl

/-- Concrete cost multiplier per consumed release split. -/
noncomputable abbrev tourConsumeRelMul : ℕ :=
  tourConsumeRelMulFn tourMul outSmallSideMul tourOutSpec.mul

theorem asmFirstTourBlockProcs_noRand (bSelf bTour bOut bCopy : ℕ) :
    ∀ s ∈ asmFirstTourBlockProcs bSelf bTour bOut bCopy, s.NoRand := by
  intro s hs
  simp only [asmFirstTourBlockProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · simp [asmFirstTourConsumeRelStmt, Stmt.NoRand]
  · simp [asmFirstTourApplyMoveStmt, Stmt.NoRand]
  · simp [asmFirstTourBlockStepStmt, Stmt.NoRand]

/-- Pinned-order/forest projection of `tourDSRep vCap eCap` to `OutTourAbs` (`τ`, `phi`, `foot`
literally identical to `tourAsmRep vCap eCap`), so `outSmallSide` preserves `ord` and `rf`
without needing `TourCordOK`. -/
@[expose] def tourPinnedOutRep (vCap eCap : ℕ) (ord : ℕ → List End) (rf : RootedForest) : DSRep OutTourAbs where
  τ := (tourDSRep vCap eCap).τ
  rep b s x mem := s.cord = coreTour ord rf ∧ (tourDSRep vCap eCap).rep b ⟨ord, rf, s.marked⟩ x mem
  phi := (tourDSRep vCap eCap).phi
  foot := (tourDSRep vCap eCap).foot

theorem tourPinnedOutRep_local (vCap eCap : ℕ) (ord : ℕ → List End) (rf : RootedForest) :
    (tourPinnedOutRep vCap eCap ord rf).Local := fun b s x mem mem' hag => by
  have h := tourDS_local vCap eCap b ⟨ord, rf, s.marked⟩ x mem mem' hag
  exact ⟨fun ⟨hc, hr⟩ => ⟨hc, h.1 hr⟩, h.2⟩

/-- `tourProcs b` meets `OutTourAt tourOutSpec` on `tourPinnedOutRep vCap eCap ord rf`. -/
@[expose] def tourPinnedOutAt (w vCap eCap : ℕ) (p : Program) (b : ℕ) (hp : HasTourProcs p b)
    (ord : ℕ → List End) (rf : RootedForest) :
    OutTourAt tourOutSpec w vCap eCap p
      (tourOp b 8) (tourOp b 7) (tourOp b 11) (tourOp b 9) where
  rep := tourPinnedOutRep vCap eCap ord rf
  rep_local := tourPinnedOutRep_local vCap eCap ord rf
  nextMarked_runs := fun tourH key v h s tx mem pos ω _ _ _ _ _ hmem ⟨hcord_eq, hR⟩ hfoot hz hsp => by
    have hmem' : endOfKey key ∈ coreTour ord rf v := hcord_eq ▸ hmem
    obtain ⟨_, _, ⟨u, hxu⟩, _⟩ := coreTour_mem_info hR.valid hmem'
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hresp', hcost⟩ :=
      tourOp_nextMarked_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hxu hw1 (by omega)
        hfoot hz hsp
    have hnm_eq := tourNextMarked_eq_outNextMarked hR.valid hmem'
    refine ⟨_, hp.op8_body, o, st', c, x', hrun, ⟨hcord_eq, hrep'⟩, ?_, by omega, hresp', ?_⟩
    · rw [hans, hnm_eq]; simp only [OutTourAbs.nextMarked, hcord_eq]
      cases (afterEnd (endOfKey key) (coreTour ord rf v) ++ [endOfKey key]).find?
        (fun z => decide (z ∈ s.marked)) <;> rfl
    · rw [ordStoreLog_eq_tourLog]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      dsimp only [tourPinnedOutRep, tourDSRep, tourOutSpec] at hcost ⊢; omega
  setMark_runs := fun tourH key flag v h s tx mem pos ω _ _ _ hfl _ _ hmem ⟨hcord_eq, hR⟩ hfoot hz hsp => by
    have hmem' : endOfKey key ∈ coreTour ord rf v := hcord_eq ▸ hmem
    obtain ⟨_, hopen, ⟨u, hxu⟩, _⟩ := coreTour_mem_info hR.valid hmem'
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, _, x', hrep', hresp', hcost⟩ :=
      tourOp_setMark_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hxu hopen hfl
        hw1 (by omega) hfoot hz (by dsimp only [tourOutSpec] at hsp; omega)
    have hsm_eq : tourSetMark ⟨ord, rf, s.marked⟩ (endOfKey key) flag =
        ⟨ord, rf, (s.setMark (endOfKey key) flag).marked⟩ := by
      simp only [OutTourAbs.setMark, tourSetMark]; split_ifs <;> rfl
    refine ⟨_, hp.op7_body, o, st', c, x', hrun,
      ⟨by simp [OutTourAbs.setMark, hcord_eq], hsm_eq ▸ hrep'⟩,
      ⟨hresp'.1, le_trans hresp'.2.1 (by dsimp only [tourOutSpec]; omega),
       hresp'.2.2.1, hresp'.2.2.2.1, hresp'.2.2.2.2⟩, ?_⟩
    rw [ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_forest
    dsimp only [tourPinnedOutRep, tourDSRep, tourOutSpec] at hcost ⊢; omega
  firstMarked_runs := fun tourH r h s tx mem pos ω _ hrLt _ ⟨hcord_eq, hR⟩ hfoot hz hsp => by
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hresp', hcost⟩ :=
      tourOp_firstMarked_runs (pos := pos) (ordStoreRep_local vCap eCap) C C.markTests
        C.markTests_cost C.markDesc_body C.findFirstMark_body ω hR hrLt hw1 (by omega) hfoot hz hsp
    have hml : s.markedList r = tourMarkedList ⟨ord, rf, s.marked⟩ r := by
      simp only [OutTourAbs.markedList, tourMarkedList, hcord_eq]
    refine ⟨_, hp.op11_body, o, st', c, x', hrun, ⟨hcord_eq, hrep'⟩, ?_, by omega, hresp', ?_⟩
    · rw [hans, hml]; cases (tourMarkedList ⟨ord, rf, s.marked⟩ r).head? <;> rfl
    · rw [ordStoreLog_eq_tourLog]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      dsimp only [tourPinnedOutRep, tourDSRep, tourOutSpec] at hcost ⊢; omega
  listMarked_runs := fun tourH r h s tx mem pos ω _ hrLt _ ⟨hcord_eq, hR⟩ hfoot hz hsp => by
    have hml : s.markedList r = tourMarkedList ⟨ord, rf, s.marked⟩ r := by
      simp only [OutTourAbs.markedList, tourMarkedList, hcord_eq]
    have hsp' : h + 1 + (tourMarkedList ⟨ord, rf, s.marked⟩ r).length < 2 ^ w := by
      dsimp only [tourOutSpec] at hsp; rw [← hml]; omega
    have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot (by omega : h + 1 < 2 ^ w)
    let C := hp.toListExact (w := w) (by omega)
    obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hz', hfr', hft', hcost⟩ :=
      tourOp_listMarked_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hrLt
        hfoot hz hsp'
    refine ⟨_, hp.op9_body, o, st', c, x', hrun, ⟨hcord_eq, hrep'⟩, by rwa [hml], by rw [hval', hml],
      ⟨by omega, by dsimp only [tourOutSpec] at hval' ⊢; rw [hval', hml]; omega,
       hz', hfr', fun a ha => Or.inl (hft' a ha)⟩, ?_⟩
    rw [hml]
    have hmono := Nat.mul_le_mul_right (ordStoreLog eCap)
      (Nat.mul_le_mul_right ((tourMarkedList ⟨ord, rf, s.marked⟩ r).length + 1) tourMul_ge_query)
    dsimp only [tourPinnedOutRep, tourDSRep, tourOutSpec] at hcost ⊢; omega

/-! ## 2. Verification of Helper 2 (`asmFirstTourApplyMoveStmt`) -/

/-- **Verification of `asmFirstTourApplyMoveStmt`**: deduplicates a `moveEnds` edit stored at `ePtr`
(`ordHandleOf tourH vCap eCap ≤ ePtr`, `ePtr + 4 + m ≤ hCur`), builds a valid 1-edit `OrdEditsAt`
block `[1, tag, v, v', m', keys…]` at `hCur`, and calls `tourOp 0` (`applyEdits`), advancing `s` to
`tourApplyEdit s edit` with space `≤ 13 * m + 77` and cost
`≤ tourApplyMoveMul * (4 + m + 2) * ordStoreLog eCap + Δφ`. -/
theorem asmFirstTourApplyMove_runs {w vCap eCap bTour tourH ePtr hCur pos : ℕ} {p : Program}
    (hpT : HasTourProcs p bTour) (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    {s : AsmTourAbs} {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    {v v' m : ℕ} {sel : Finset End} {c : Bool}
    (hrep : (tourAsmRep vCap eCap).rep tourH s tx mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH tx a → a < hCur)
    (hzero : ZeroFrom mem hCur)
    (hePtr_ge : ordHandleOf tourH vCap eCap ≤ ePtr)
    (hePtr_le : ePtr + 4 + m ≤ hCur)
    (htag : mem ePtr = 1 ∨ mem ePtr = 2)
    (hdec : decodeOrdEdit mem ePtr = (.moveEnds v v' sel c, 4 + m))
    (hvalid : AsmTourEditValid vCap eCap s (.moveEnds v v' sel c))
    (hroom : hCur + (13 * m + 77) < 2 ^ w) :
    ∃ o st' cost tx',
      Runs w p ω (asmFirstTourApplyMoveStmt (bTour + 75) (tourOp bTour 0))
        (startState [tourH, ePtr, hCur] mem pos) o st' cost ∧
      (tourAsmRep vCap eCap).rep tourH (asmTourApplyEdit s (.moveEnds v v' sel c)) tx' st'.mem ∧
      hCur ≤ o.value ∧ o.value ≤ hCur + (13 * m + 77) ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < hCur, ¬ (tourAsmRep vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH tx' a →
        (tourAsmRep vCap eCap).foot tourH tx a ∨ (hCur ≤ a ∧ a < o.value)) ∧
      cost + (tourAsmRep vCap eCap).phi tourH tx' st'.mem ≤
        tourApplyMoveMul * (4 + m + 2) * ordStoreLog eCap +
          (tourAsmRep vCap eCap).phi tourH tx mem := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH (asmTourToTour s) tx mem at hrep
  have hord_le : ordHandleOf tourH vCap eCap ≤ hCur := hrep.fixed_le_heap hfoot
  have hwide : 18 ≤ 2 ^ w := (tourDS_wide_of_foot hrep hfoot (by omega : hCur + 1 < 2 ^ w)).2
  have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
  -- Extract raw fields of `decodeOrdEdit mem ePtr`
  have htag0 : mem ePtr ≠ 0 := by rcases htag with h1 | h2 <;> omega
  simp only [decodeOrdEdit, htag0, ↓reduceIte, htag, Prod.mk.injEq, OrdEdit.moveEnds.injEq] at hdec
  obtain ⟨⟨hv_eq, hv'_eq, hsel_eq, hc_eq⟩, hm_eq⟩ := hdec
  have hm_eq' : mem (ePtr + 3) = m := by omega
  set tag := mem ePtr
  set keysPtr := ePtr + 4
  set outKeysPtr := hCur + 5
  set rawKeys : List End := (readList mem keysPtr m).map endOfKey
  have hraw_len : rawKeys.length = m := by simp [rawKeys, readList]
  have hraw_mem : ∀ i (hi : i < m), mem (keysPtr + i) = endKey (rawKeys[i]'(by omega)) := by
    intro i hi
    simp only [rawKeys, List.getElem_map, readList, List.getElem_range]
    exact (endKey_endOfKey' (mem (keysPtr + i))).symm
  have hraw_lt : ∀ z ∈ rawKeys, z.1 < eCap := fun z hz =>
    hvalid.2.2.2.2.2.2 z (by rw [← hsel_eq, List.mem_toFinset]; simpa [rawKeys, hm_eq'] using hz)
  -- Prefix loads + stores writing `[1, tag, v, v']` at `hCur .. hCur + 3`
  set s0 := startState [tourH, ePtr, hCur] mem pos
  set r1 := Function.update s0.regs 3 tag
  set r2 := Function.update r1 4 v
  set r3 := Function.update r2 5 v'
  set r4 := Function.update r3 6 m
  set r5 := Function.update r4 7 keysPtr
  set r6 := Function.update r5 8 outKeysPtr
  set mem1 := Function.update mem hCur 1
  set mem2 := Function.update mem1 (hCur + 1) tag
  set mem3 := Function.update mem2 (hCur + 2) v
  set mem4 := Function.update mem3 (hCur + 3) v'
  have hmem4_lt : ∀ a < hCur, mem4 a = mem a := fun a ha => by
    simp only [mem4, mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hmem4_ge : ∀ a, hCur + 4 ≤ a → mem4 a = mem a := fun a ha => by
    simp only [mem4, mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have ha1 : Runs w p ω (.assign 3 (.load (.reg 1))) s0 .normal ⟨mem, r1, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState])) rfl,
      rfl, rfl, rfl⟩
  have ha2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 1) (.const 1)))) ⟨mem, r1, pos⟩ .normal
      ⟨mem, r2, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega)) hv_eq, rfl, rfl, rfl⟩
  have ha3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 1) (.const 2)))) ⟨mem, r2, pos⟩ .normal
      ⟨mem, r3, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨v', Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega)) hv'_eq, rfl, rfl, rfl⟩
  have ha4 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 1) (.const 3)))) ⟨mem, r3, pos⟩ .normal
      ⟨mem, r4, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨m, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega)) hm_eq', rfl, rfl, rfl⟩
  have ha5 : Runs w p ω (.assign 7 (.bin .add (.reg 1) (.const 4))) ⟨mem, r4, pos⟩ .normal
      ⟨mem, r5, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨keysPtr,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hst1 : Runs w p ω (.store (.reg 2) (.const 1)) ⟨mem, r5, pos⟩ .normal ⟨mem1, r5, pos⟩ 3 :=
    runs_store_iff.mpr ⟨hCur, 1, Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, s0, startState]),
      Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hst2 : Runs w p ω (.store (.bin .add (.reg 2) (.const 1)) (.reg 3)) ⟨mem1, r5, pos⟩ .normal
      ⟨mem2, r5, pos⟩ 5 :=
    runs_store_iff.mpr ⟨hCur + 1, tag,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1]), rfl, rfl, rfl⟩
  have hst3 : Runs w p ω (.store (.bin .add (.reg 2) (.const 2)) (.reg 4)) ⟨mem2, r5, pos⟩ .normal
      ⟨mem3, r5, pos⟩ 5 :=
    runs_store_iff.mpr ⟨hCur + 2, v,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2]), rfl, rfl, rfl⟩
  have hst4 : Runs w p ω (.store (.bin .add (.reg 2) (.const 3)) (.reg 5)) ⟨mem3, r5, pos⟩ .normal
      ⟨mem4, r5, pos⟩ 5 :=
    runs_store_iff.mpr ⟨hCur + 3, v',
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq (by simp [r5, r4, r3]), rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 8 (.bin .add (.reg 2) (.const 5))) ⟨mem4, r5, pos⟩ .normal
      ⟨mem4, r6, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨outKeysPtr,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5, r4, r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  -- Call `tourDedupSelBody` at `bTour + 75`
  have hloc4 := (tourDS_local vCap eCap) tourH (asmTourToTour s) tx mem mem4 fun a ha =>
    (hmem4_lt a (hfoot a ha)).symm
  have hrep4 : TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH (asmTourToTour s) tx mem4 := hloc4.1 hrep
  obtain ⟨m', stD, cD, U, hrunD, hm'_le, hUlen, hUnd, hUset, hUmem, hDfr, hcD⟩ :=
    tourDedupSelBody_runs (p := p) (outPtr := outKeysPtr) (pos := pos) ω hrep4.toCore hraw_len
      (fun i hi => (hmem4_lt (keysPtr + i) (by omega)).trans (hraw_mem i hi))
      hraw_lt (by omega) (by omega) (by omega) hwide
  have heArgsD : evalArgs w ⟨mem4, r6, pos⟩ [.reg 0, .reg 7, .reg 6, .reg 8] =
      some [tourH, keysPtr, m, outKeysPtr] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6, r5, r4, r3, r2, r1, s0, startState])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6, r5])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6, r5, r4])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r6])) <| evalArgs_nil _ _
  set r7 := Function.update r6 9 m'
  have hcallD : Runs w p ω (.call 9 (bTour + 75) [.reg 0, .reg 7, .reg 6, .reg 8])
      ⟨mem4, r6, pos⟩ .normal ⟨stD.mem, r7, stD.pos⟩
      (argsSize [.reg 0, .reg 7, .reg 6, .reg 8] + cD + 1) :=
    runs_call_iff.mpr ⟨_, _, .returned m', stD, cD, heArgsD, hpT.get 75 (by decide), hrunD, rfl, rfl, rfl⟩
  -- Store `m'` at `hCur + 4`, compute `w1 = 5 + m'`, `h1 = hCur + w1`
  set mem5 := Function.update stD.mem (hCur + 4) m'
  set w1 := 5 + m'
  set h1 := hCur + w1
  set r8 := Function.update r7 10 w1
  set r9 := Function.update r8 11 h1
  have hst5 : Runs w p ω (.store (.bin .add (.reg 2) (.const 4)) (.reg 9))
      ⟨stD.mem, r7, stD.pos⟩ .normal ⟨mem5, r7, stD.pos⟩ 5 :=
    runs_store_iff.mpr ⟨hCur + 4, m',
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]))
        (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq (by simp [r7]), rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 10 (.bin .add (.const 5) (.reg 9)))
      ⟨mem5, r7, stD.pos⟩ .normal ⟨mem5, r8, stD.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨w1,
      Expr.eval_add (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r7])) (by omega),
      rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 11 (.bin .add (.reg 2) (.reg 10)))
      ⟨mem5, r8, stD.pos⟩ .normal ⟨mem5, r9, stD.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨h1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8, r7, r6, r5, r4, r3, r2, r1, s0, startState]))
        (Expr.eval_reg_of_eq (by simp [r8])) (by omega), rfl, rfl, rfl⟩
  -- Verify `OrdEditsAt mem5 hCur [.moveEnds v v' sel c] w1` and call `tourOp 0` via `tourDS_implements`
  have hmem5_lt : ∀ a < hCur, mem5 a = mem a := fun a ha => by
    dsimp only [mem5]
    rw [Function.update_of_ne (by omega), hDfr a (Or.inl (by omega)), hmem4_lt a ha]
  have hmem5_zero : ZeroFrom mem5 h1 := fun a ha => by
    dsimp only [mem5]
    rw [Function.update_of_ne (by omega), hDfr a (Or.inr (by omega)), hmem4_ge a (by omega)]
    exact hzero a (by omega)
  have hmem5_hdr : mem5 hCur = 1 ∧ mem5 (hCur + 1) = tag ∧ mem5 (hCur + 2) = v ∧
      mem5 (hCur + 3) = v' ∧ mem5 (hCur + 4) = m' := by
    refine ⟨?_, ?_, ?_, ?_, Function.update_self _ _ _⟩
    · simp only [mem5]; rw [Function.update_of_ne (by omega), hDfr hCur (Or.inl (by omega))]
      simp [mem4, mem3, mem2, mem1]
    · simp only [mem5]; rw [Function.update_of_ne (by omega), hDfr (hCur + 1) (Or.inl (by omega))]
      simp [mem4, mem3, mem2]
    · simp only [mem5]; rw [Function.update_of_ne (by omega), hDfr (hCur + 2) (Or.inl (by omega))]
      simp [mem4, mem3]
    · simp only [mem5]; rw [Function.update_of_ne (by omega), hDfr (hCur + 3) (Or.inl (by omega))]
      simp [mem4]
  have hUset_sel : U.toFinset = sel := by
    rw [hUset, ← hsel_eq]; simp [rawKeys, hm_eq']
  have hrl5 : (readList mem5 (hCur + 5) m').map endOfKey = U := by
    apply List.ext_getElem (by simp [readList, hUlen])
    intro i hi1 hi2
    simp only [List.getElem_map, readList, List.getElem_range]
    have hm5k : mem5 (hCur + 5 + i) = endKey (U[i]'hi2) := by
      dsimp only [mem5]
      rw [Function.update_of_ne (by omega)]
      exact hUmem i hi2
    rw [hm5k, endOfKey_endKey']
  have hdec5 : decodeOrdEdit mem5 (hCur + 1) = (.moveEnds v v' sel c, 4 + m') := by
    simp only [decodeOrdEdit, hmem5_hdr.2.1, htag0, ↓reduceIte, htag, hmem5_hdr.2.2.1,
      hmem5_hdr.2.2.2.1, hmem5_hdr.2.2.2.2, show hCur + 1 + 1 = hCur + 2 by omega,
      show hCur + 1 + 2 = hCur + 3 by omega, show hCur + 1 + 3 = hCur + 4 by omega,
      show hCur + 1 + 4 = hCur + 5 by omega, hrl5, hUset_sel, hc_eq]
  have hread5 : readOrdEdits mem5 hCur = [.moveEnds v v' sel c] := by
    simp [readOrdEdits, hmem5_hdr.1, decodeOrdEdits, hdec5]
  have hcard_sel : m' = sel.card := by
    rw [← hUlen, ← List.toFinset_card_of_nodup hUnd, hUset_sel]
  have hEdAt5 : OrdEditsAt mem5 hCur (readOrdEdits mem5 hCur) w1 := by
    refine ⟨rfl, ?_, ?_⟩
    · simp only [hmem5_hdr.1, decodeOrdEdits, hdec5, List.sum_cons, List.sum_nil]; omega
    · rw [hread5]
      simp only [ordEditsEnc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, OrdEdit.enc]
      omega
  have hloc5 := (tourDS_local vCap eCap) tourH (asmTourToTour s) tx mem mem5 fun a ha =>
    (hmem5_lt a (hfoot a ha)).symm
  have hImpl := (tourDS_implements w vCap eCap p bTour hpT hw).2
  have htourW : tourH < 2 ^ w :=
    lt_trans (hfoot tourH (tourAsmRep_handle_foot vCap eCap tourH tx)) (by omega)
  have hargsW : ∀ a ∈ [tourH, hCur, w1, h1], a < 2 ^ w := by
    intro a ha; simp at ha; rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hpre0 : (tourContract vCap eCap tourMul tourAlloc).pre 0 (asmTourToTour s)
      [tourH, hCur, w1, h1] mem5 :=
    ⟨tourH, hCur, w1, h1, rfl, hEdAt5, le_refl _, by
      rw [hread5]; exact ⟨(asmTourEditValid_iff vCap eCap s _).mp hvalid, trivial⟩⟩
  have hha : heapArg [tourH, hCur, w1, h1] = h1 := rfl
  have hsp0 : heapArg [tourH, hCur, w1, h1] + (tourContract vCap eCap tourMul tourAlloc).space 0
      (asmTourToTour s) [tourH, hCur, w1, h1] mem5 < 2 ^ w := by
    rw [hha]
    simp only [tourContract, tourAlloc, tourOp0Space, List.getD_cons_zero, List.getD_cons_succ]
    omega
  obtain ⟨bd0, hbd0, o0, st0, c0, hrun0, s0', tx', hrep0, hpost0, hresp0, hcost0⟩ :=
    hImpl.2.2 0 tourH (asmTourToTour s) tx [tourH, hCur, w1, h1] mem5 stD.pos ω hargsW rfl
      (hloc5.1 hrep) hpre0
      (fun a ha => by rw [hha]; exact lt_of_lt_of_le (hfoot a ha) (by omega))
      (by rw [hha]; exact hmem5_zero) hsp0
  have hs0'_eq : s0' = asmTourToTour (asmTourApplyEdit s (.moveEnds v v' sel c)) := by
    simp only [tourContract, List.getD_cons_succ, List.getD_cons_zero] at hpost0
    rw [hpost0, hread5]; rfl
  subst hs0'_eq
  have heArgs0 : evalArgs w ⟨mem5, r9, stD.pos⟩ [.reg 0, .reg 2, .reg 10, .reg 11] =
      some [tourH, hCur, w1, h1] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r9, r8])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [r9])) <| evalArgs_nil _ _
  set r10 := Function.update r9 12 o0.value
  have hcall0 : Runs w p ω (.call 12 (tourOp bTour 0) [.reg 0, .reg 2, .reg 10, .reg 11])
      ⟨mem5, r9, stD.pos⟩ .normal ⟨st0.mem, r10, st0.pos⟩
      (argsSize [.reg 0, .reg 2, .reg 10, .reg 11] + c0 + 1) :=
    runs_call_iff.mpr ⟨_, bd0, o0, st0, c0, heArgs0, hbd0, hrun0, rfl, rfl, rfl⟩
  have hret0 : Runs w p ω (.ret (.reg 12)) ⟨st0.mem, r10, st0.pos⟩ (.returned o0.value)
      ⟨st0.mem, r10, st0.pos⟩ 2 :=
    runs_ret_iff.mpr ⟨o0.value, Expr.eval_reg_of_eq (by simp [r10]), rfl, rfl, rfl⟩
  have hrunAll :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha2,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha3,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha4,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha5,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst1,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst2,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst3,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst4,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
                        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallD,
                          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst5,
                            runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha7,
                              runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha8,
                                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall0, hret0, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  rw [hha] at hresp0
  have hsp0_eval : (tourContract vCap eCap tourMul tourAlloc).space 0 (asmTourToTour s)
      [tourH, hCur, w1, h1] mem5 = 12 * w1 + 12 := rfl
  have hlo0 : h1 ≤ o0.value := hresp0.1
  have hhi0 : o0.value ≤ h1 + (12 * w1 + 12) := by rw [← hsp0_eval]; exact hresp0.2.1
  refine ⟨.returned o0.value, ⟨st0.mem, r10, st0.pos⟩, _, tx', hrunAll, hrep0,
    by change hCur ≤ o0.value; omega, by change o0.value ≤ hCur + (13 * m + 77); omega,
    by simpa [Outcome.value] using hresp0.2.2.1,
    fun a ha hnf => (hresp0.2.2.2.1 a (by omega) hnf).trans (hmem5_lt a ha),
    fun a ha => by
      rcases hresp0.2.2.2.2 a ha with h0 | ⟨hge, hlt⟩
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, by change a < o0.value; exact hlt⟩, ?_⟩
  simp only [argsSize, Expr.size, tourContract, List.getD_cons_zero, List.getD_cons_succ,
    ← ordStoreLog_eq_tourLog] at hcost0 ⊢
  rw [← hloc5.2] at hcost0
  have hw1_le : w1 + 1 ≤ 4 + m + 2 := by omega
  have h1m : tourMul * (w1 + 1) * ordStoreLog eCap ≤ tourMul * (4 + m + 2) * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw1_le)
  have h2m : 95 * m + 200 ≤ 150 * (4 + m + 2) * ordStoreLog eCap :=
    le_trans (by omega) (Nat.le_mul_of_pos_right _ htl)
  have hdist : tourApplyMoveMul * (4 + m + 2) * ordStoreLog eCap =
      tourMul * (4 + m + 2) * ordStoreLog eCap + 150 * (4 + m + 2) * ordStoreLog eCap := by
    unfold tourApplyMoveMul; ring
  dsimp only [tourAsmRep] at hcost0 ⊢
  omega

end

end MinCostFlow.SparseCore.Program
