module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullDefs

/-!
# What `dsStepHead` keeps

The first call of the step, `dsStepHeadStmt`, runs `dsUpdateSLevels` and then `dsStepPrefix`.
Each one writes only a few areas: the first the generation word, the words of the sets `S_i`
and its heap `[headHeap, r₁)`; the second the graphs `G` and `H`, the bucket words and its
output `[heapStep + 5, heapStep + 5 + len)`. This file turns their two frame conditions into the
facts that the rest of the step uses (`stepPosHead_keep`): the header without the generation
word, the words from `domGen` to `sGen`, the words from `sBit` to `heapStep`, the words from
`heapAff` on, and the `minH` words before `dsStepPrefix` are those of the memory before the step.

`stepPosLayout` lists the order of the areas of the state block (`StateLayout.lean`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

public section

/-- The order of the areas of the state block at `b`. -/
lemma stepPosLayout (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧ b ≤ b + dsGenOff ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap + eCap + eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap ≤ dsPiPtrBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap ≤ dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) = dsVSGenBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap + (L + 1) * vCap = dsSHeadBase b L vCap eCap ∧
    dsSHeadBase b L vCap eCap + (L + 1) = dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap = dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap ∧
    dsGPtr b = b + dsHdrSize ∧ dgEPresBase (dsHPtr b vCap eCap) vCap =
      dsHPtr b vCap eCap + 4 + 7 * vCap ∧
    dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := by
  have hfa := dsFixedSize_add b L vCap eCap
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hfa, rfl,
    rfl, rfl⟩ <;>
  simp only [dsGPtr, dsHdrSize, dsGenOff, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
    dsHNextBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsSGenBase, dsRevHeadBase,
    dsRevGenBase] <;> omega

/-- The words that `dsStepHead` keeps, from its two frame conditions. Here `mid` is the memory
between its two calls and `mem2` the memory after it. -/
theorem stepPosHead_keep {L vCap eCap b heapStep len j r₁ : ℕ} {mem0 mid mem2 : ℕ → ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hr₁ : r₁ ≤ heapStep + 5 + len + 4 * j)
    (hfrS : ∀ addr, dsUpdateSLevelsFrameCond L vCap eCap b (heapStep + 5 + len) r₁ addr →
      mid addr = mem0 addr)
    (hfrP : ∀ addr, (addr < heapStep + 5 ∨ heapStep + 5 + len ≤ addr) →
      (addr < dsGPtr b ∨ (dsAuxPtr b vCap eCap ≤ addr ∧ addr < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b L vCap eCap ≤ addr) → mem2 addr = mid addr) :
    (∀ addr, addr < dsGPtr b → addr ≠ b + dsGenOff → mem2 addr = mem0 addr) ∧
    (∀ addr, dsDomGenBase b L vCap eCap ≤ addr → addr < dsSGenBase b L vCap eCap →
      mem2 addr = mem0 addr) ∧
    (∀ addr, dsSBitBase b L vCap eCap ≤ addr → addr < heapStep → mem2 addr = mem0 addr) ∧
    (∀ addr, heapStep + 5 + len + 4 * j ≤ addr → mem2 addr = mem0 addr) ∧
    mem2 (b + dsGenOff) = mid (b + dsGenOff) ∧
    (∀ addr, addr < dsDomGenBase b L vCap eCap → mid addr = mem0 addr ∨ addr = b + dsGenOff) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, _,
    h20⟩ := stepPosLayout b L vCap eCap
  have hpos := dsFixedSize_pos L vCap eCap
  have hdg : dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by omega
  -- The frame condition of `dsUpdateSLevels` holds outside the generation word, the `S` words
  -- and its heap.
  have hS_out : ∀ addr, addr ≠ b + dsGenOff →
      (addr < dsSGenBase b L vCap eCap ∨ dsSBitBase b L vCap eCap ≤ addr) →
      (addr < heapStep + 5 + len ∨ r₁ ≤ addr) → mid addr = mem0 addr := by
    intro addr hg hS hh
    refine hfrS addr ⟨hg, fun i hi => ?_, fun i hi v hv => ?_, fun i hi => ?_, hh⟩
    · omega
    · have : i * vCap + v < (L + 1) * vCap := by
        calc i * vCap + v < i * vCap + vCap := by omega
          _ = (i + 1) * vCap := by rw [Nat.succ_mul]
          _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
  refine ⟨fun addr ha hg => ?_, fun addr ha hb => ?_, fun addr ha hb => ?_, fun addr ha => ?_,
    ?_, fun addr ha => ?_⟩
  · rw [hfrP addr (Or.inl (by omega)) (Or.inl ha)]
    exact hS_out addr hg (Or.inl (by omega)) (Or.inl (by omega))
  · rw [hfrP addr (Or.inl (by omega)) (Or.inr (Or.inr ha))]
    exact hS_out addr (by omega) (Or.inl hb) (Or.inl (by omega))
  · rw [hfrP addr (Or.inl (by omega)) (Or.inr (Or.inr (by omega)))]
    exact hS_out addr (by omega) (Or.inr ha) (Or.inl (by omega))
  · rw [hfrP addr (Or.inr (by omega)) (Or.inr (Or.inr (by omega)))]
    exact hS_out addr (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  · exact hfrP _ (Or.inl (by omega)) (Or.inl h1)
  · by_cases hg : addr = b + dsGenOff
    · exact Or.inr hg
    · exact Or.inl (hS_out addr hg (Or.inl (by omega)) (Or.inl (by omega)))

end

end MinCostFlow.DynSpanner.Program
