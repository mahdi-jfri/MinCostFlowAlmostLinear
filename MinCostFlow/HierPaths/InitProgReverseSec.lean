module

public import MinCostFlow.HierPaths.InitProgReverseWriter

/-!
# Relocatable reverse-index writer

The reverse index reuses the projected edge writer and the stable bucket builder.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.LowStretch

/-- Procedures called by the reverse-index writer, in relocation order. -/
def initReverseHelpers (a k : ℕ) : List Stmt :=
  [(projectedW a false).body (k + 9), initEndpointWriter 0 (k + 40),
    initRepeatRows (k + 4), initBucketMove (k + 5) (k + 4) (k + 6), initFillWord,
    initBucket (k + 7) (k + 8), moveDown, csrB, initBucketGather] ++
    initProjectedHelpers false (k + 9) ++ endpointHelpers (k + 40)

/-- The relocatable writer for section 6. -/
def reverseBucketW (a : ℕ) : SecW a where
  body k := initReverseWriter k (k + 1) (k + 2) (k + 3)
  helpers := initReverseHelpers a
  l S G _ := initReverseSection S G
  cost S G _ := initReverseWriterCost S G
  scratch S G _ := initReverseWriterScratch S G
  noRand k := by
    obtain ⟨hb, hh⟩ := (projectedW a false).noRand (k + 9)
    change (∀ s ∈ initProjectedHelpers false (k + 9), s.NoRand) at hh
    refine ⟨initReverseWriter_noRand _ _ _ _, ?_⟩
    simp [initReverseHelpers, hb, endpointHelpers, initEndpointWriter, Stmt.NoRand,
      initRepeatRows_noRand, initBucketMove_noRand, initBucket_noRand, initBucketGather_noRand,
      initFillWord_noRand, moveDown, forRange, forUp, csrB_noRand,
      initEndpointDepth_noRand, initEndpointLevel_noRand, initEndpointChild_noRand,
      initEndpointRange_noRand, initEndpointRow_noRand, initCSRSeek_noRand,
      initCSRCount_noRand, initEndpointCopy_noRand]
    intro s hs
    rcases hs with h | h
    · exact hh s h
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact initEndpointDepth_noRand _ | exact initEndpointLevel_noRand _ |
        exact initEndpointChild_noRand _ | exact initEndpointRange_noRand _ |
        exact initEndpointRow_noRand _ _ _ _ | exact initCSRSeek_noRand |
        exact initCSRCount_noRand | exact initEndpointCopy_noRand | exact initFillWord_noRand
  spec w p f k hp hh S G := by
    have hProj : p.HasAt (k + 9) ((projectedW a false).helpers (k + 9)) := by
      intro i hi
      have hn : i < (initProjectedHelpers false (k + 9)).length := hi
      have hi₀ : 9 + i < (initReverseHelpers a k).length := by simp [initReverseHelpers]; omega
      have h := hh (9 + i) hi₀
      have happend (l m r : List Stmt) (hi : i < m.length) :
          ((l ++ m) ++ r)[l.length + i]'(by simp; omega) = m[i] := by
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
        simp
      have he : (initReverseHelpers a k)[9 + i] = (initProjectedHelpers false (k + 9))[i] :=
        happend _ _ _ hn
      rw [he] at h
      simpa [projectedW, Nat.add_assoc] using h
    have hSort : p.HasAt (k + 7) [csrB] := by
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst i
      simpa [initReverseHelpers] using hh 7 (by simp [initReverseHelpers])
    have hClear := hh 4 (by simp [initReverseHelpers])
    have hEnd := initEndpointWriter_meetsContract (w := w) (S := S) (a := a) (G := G)
      (field := 0) (by decide)
      (hh 1 (by simp [initReverseHelpers]))
      (hh 40 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 41 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 42 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 43 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 44 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 45 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 46 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 47 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
      (hh 48 (by simp [initReverseHelpers, initProjectedHelpers, endpointHelpers]))
    exact initReverseWriter_meetsContract hp
      ((projectedW a false).spec w p k (k + 9) (by
        simpa [initReverseHelpers] using hh 0 (by simp [initReverseHelpers])) hProj S G) hEnd
      (hh 2 (by simp [initReverseHelpers])) hClear
      (initBucketMove_meetsContract (hh 3 (by simp [initReverseHelpers]))
        (initBucket_meetsContract (hh 5 (by simp [initReverseHelpers])) hSort
          (hh 8 (by simp [initReverseHelpers])))
        (initFillWord_meetsContract hClear)
        (moveDown_meetsContract (hh 6 (by simp [initReverseHelpers]))))

end MinCostFlow.HierPaths

end
