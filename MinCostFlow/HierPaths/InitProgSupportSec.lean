module

public import MinCostFlow.HierPaths.InitProgSupportWriter

/-!
# Relocatable support-index writer

The support writer calls the projected vertex writer and two column
writers before sorting their records by vertex.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.LowStretch

def initSupportHelpers (a k : ℕ) : List Stmt :=
  [(projectedW a true).body (k + 15), initSupportColumnProc (k + 4) (k + 5),
    initSupportColumnProc (k + 6) (k + 7), initBucketMove (k + 10) (k + 11) (k + 12),
    initSupportEmit true false, initSupportRows (k + 8), initSupportEmit false false,
    initSupportRows (k + 9), initSupportEmit true true, initSupportEmit false true,
    initBucket (k + 13) (k + 14), initFillWord, moveDown, csrB, initBucketGather] ++
    initProjectedHelpers true (k + 15)

/-- The relocatable writer for section 9. -/
def supportBucketW (a : ℕ) : SecW a where
  body k := initSupportWriter k (k + 1) (k + 2) (k + 3)
  helpers := initSupportHelpers a
  l S G _ := initSupportSection S G
  cost S G _ := initSupportWriterCost S G
  scratch S G _ := initSupportWriterScratch S G
  noRand k := by
    obtain ⟨hb, hh⟩ := (projectedW a true).noRand (k + 15)
    change (∀ s ∈ initProjectedHelpers true (k + 15), s.NoRand) at hh
    refine ⟨initSupportWriter_noRand _ _ _ _, ?_⟩
    simpa [initSupportHelpers, hb, initSupportColumnProc_noRand, initSupportEmit_noRand,
      initSupportRows_noRand, initBucketMove_noRand, initBucket_noRand, initBucketGather_noRand,
      initFillWord_noRand, moveDown, forRange, forUp, csrB_noRand, Stmt.NoRand] using hh
  spec w p f k hp hh S G := by
    have hProj : p.HasAt (k + 15) ((projectedW a true).helpers (k + 15)) := by
      intro i hi
      have hn : i < (initProjectedHelpers true (k + 15)).length := hi
      have hi₀ : 15 + i < (initSupportHelpers a k).length := by simp [initSupportHelpers]; omega
      have h := hh (15 + i) hi₀
      have happend (l m : List Stmt) (hi : i < m.length) :
          (l ++ m)[l.length + i]'(by simp; omega) = m[i] := by
        rw [List.getElem_append_right (by omega)]
        simp
      have he : (initSupportHelpers a k)[15 + i] = (initProjectedHelpers true (k + 15))[i] :=
        happend _ _ hn
      rw [he] at h
      simpa [projectedW, Nat.add_assoc] using h
    have hSort : p.HasAt (k + 13) [csrB] := by
      intro i hi
      have : i = 0 := by simp at hi; omega
      subst i
      simpa [initSupportHelpers] using hh 13 (by simp [initSupportHelpers])
    refine initSupportWriter_meetsContract hp
      ((projectedW a true).spec w p k (k + 15) (by
        simpa [initSupportHelpers] using hh 0 (by simp [initSupportHelpers])) hProj S G)
      (initSupportColumnProc_meetsContract (hh 1 (by simp [initSupportHelpers]))
        (hh 4 (by simp [initSupportHelpers])) (initSupportRows_meetsContract
          (hh 5 (by simp [initSupportHelpers])) (hh 8 (by simp [initSupportHelpers]))))
      (initSupportColumnProc_meetsContract (hh 2 (by simp [initSupportHelpers]))
        (hh 6 (by simp [initSupportHelpers])) (initSupportRows_meetsContract
          (hh 7 (by simp [initSupportHelpers])) (hh 9 (by simp [initSupportHelpers]))))
      (initBucketMove_meetsContract (hh 3 (by simp [initSupportHelpers]))
        (initBucket_meetsContract (hh 10 (by simp [initSupportHelpers])) hSort
          (hh 14 (by simp [initSupportHelpers])))
        (initFillWord_meetsContract (hh 11 (by simp [initSupportHelpers])))
        (moveDown_meetsContract (hh 12 (by simp [initSupportHelpers]))))

end MinCostFlow.HierPaths

end
