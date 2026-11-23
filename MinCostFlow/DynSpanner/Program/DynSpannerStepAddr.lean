module

public import MinCostFlow.DynSpanner.Program.StateLayout

import Mathlib.Tactic.Ring

/-!
# Where the words of the state block lie

The fixed block of `DynSpannerStateAt` (`StateLayout.lean`) is a header, three graphs, and then the
arrays of the levels, from `dsMinHBase` on. The proofs of the step move the state through many
calls, and each call changes only some ranges of memory. To carry a fact over a call, a proof must
show that the words the fact reads lie outside the range the call writes. This file gives these
locations once: every word of an array of the levels lies in `[dsMinHBase, dsSBitBase)`, and every
stamp word lies in `[dsSBitBase + vCap, b + dsFixedSize)`.
-/

namespace MinCostFlow.DynSpanner.Program

public section

/-- An index `i * cap + e` of a table of `n` rows of length `cap` lies below `n * cap`. -/
lemma idx_lt_rows {n cap i e : ℕ} (hi : i < n) (he : e < cap) : i * cap + e < n * cap :=
  calc i * cap + e < i * cap + cap := by omega
    _ = (i + 1) * cap := by ring
    _ ≤ n * cap := Nat.mul_le_mul_right _ hi

/-- The `minH` word of an edge lies in the arrays of the levels. -/
lemma minH_in_levels {b L vCap eCap e : ℕ} (he : e < eCap) :
    dsMinHBase b vCap eCap ≤ dsMinHBase b vCap eCap + e ∧
      dsMinHBase b vCap eCap + e < dsSBitBase b L vCap eCap := by
  simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
    dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
    dsHNextBase]
  omega

/-- A word `base + i` of a table indexed by levels lies in the arrays of the levels, for the
tables `domGen`, `sGen` and `sHead`. -/
lemma levelWord_in_levels {b L vCap eCap i : ℕ} (hi : i ≤ L) :
    (dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap + i ∧
      dsDomGenBase b L vCap eCap + i < dsSBitBase b L vCap eCap) ∧
    (dsMinHBase b vCap eCap ≤ dsSGenBase b L vCap eCap + i ∧
      dsSGenBase b L vCap eCap + i < dsSBitBase b L vCap eCap) ∧
    (dsMinHBase b vCap eCap ≤ dsSHeadBase b L vCap eCap + i ∧
      dsSHeadBase b L vCap eCap + i < dsSBitBase b L vCap eCap) := by
  simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
    dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
    dsHNextBase]
  omega

/-- A word of a table of edge rows (`edgeDomGen`, `piPtr`) lies in the arrays of the levels. -/
lemma edgeWord_in_levels {b L vCap eCap i e : ℕ} (hi : i ≤ L) (he : e < eCap) :
    (dsMinHBase b vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap + i * eCap + e ∧
      dsEdgeDomGenBase b L vCap eCap + i * eCap + e < dsSBitBase b L vCap eCap) ∧
    (dsMinHBase b vCap eCap ≤ dsPiPtrBase b L vCap eCap + i * eCap + e ∧
      dsPiPtrBase b L vCap eCap + i * eCap + e < dsSBitBase b L vCap eCap) := by
  have h := idx_lt_rows (n := L + 1) (Nat.lt_succ_of_le hi) he
  simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
    dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
    dsHNextBase]
  omega

/-- A word of a table of vertex rows (`revGen`, `revHead`, `vsGen`) lies in the arrays of the
levels. -/
lemma vertexWord_in_levels {b L vCap eCap i v : ℕ} (hi : i ≤ L) (hv : v < vCap) :
    (dsMinHBase b vCap eCap ≤ dsRevGenBase b L vCap eCap + i * vCap + v ∧
      dsRevGenBase b L vCap eCap + i * vCap + v < dsSBitBase b L vCap eCap) ∧
    (dsMinHBase b vCap eCap ≤ dsRevHeadBase b L vCap eCap + i * vCap + v ∧
      dsRevHeadBase b L vCap eCap + i * vCap + v < dsSBitBase b L vCap eCap) ∧
    (dsMinHBase b vCap eCap ≤ dsVSGenBase b L vCap eCap + i * vCap + v ∧
      dsVSGenBase b L vCap eCap + i * vCap + v < dsSBitBase b L vCap eCap) := by
  have h := idx_lt_rows (n := L + 1) (Nat.lt_succ_of_le hi) hv
  simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
    dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
    dsHNextBase]
  omega

/-- The vertex stamp words lie after the `sBit` words and inside the fixed block. -/
lemma vStampWord_in_block {b L vCap eCap v : ℕ} (hv : v < vCap) :
    dsSBitBase b L vCap eCap + vCap ≤ dsVStampBase b L vCap eCap + v ∧
      dsVStampBase b L vCap eCap + v < b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase]
  omega

/-- The edge stamp words (`eStamp`, `keptStamp`) lie after the `sBit` words and inside the fixed
block. -/
lemma eStampWord_in_block {b L vCap eCap e : ℕ} (he : e < eCap) :
    (dsSBitBase b L vCap eCap + vCap ≤ dsEStampBase b L vCap eCap + e ∧
      dsEStampBase b L vCap eCap + e < b + dsFixedSize L vCap eCap) ∧
    (dsSBitBase b L vCap eCap + vCap ≤ dsKeptStampBase b L vCap eCap + e ∧
      dsKeptStampBase b L vCap eCap + e < b + dsFixedSize L vCap eCap) := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase]
  omega

/-- The graphs `G` and `H` lie in the block after the header and before the graph `aux`. -/
lemma graphs_in_block (b vCap eCap : ℕ) :
    b + dsHdrSize ≤ dsGPtr b ∧ dsGPtr b + dynGraphSize vCap eCap ≤ dsHPtr b vCap eCap ∧
      dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap ∧
      dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap :=
  ⟨le_refl _, le_refl _, le_refl _, rfl⟩

/-- The `sBit` words lie in the fixed block, after the arrays of the levels. -/
lemma sBit_in_block (b L vCap eCap : ℕ) :
    dsSBitBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase]
  omega

/-- The order of the parts of the fixed block: the word `t` of the header, the graph `aux`, the
arrays of the levels, and the `sBit` words. -/
lemma block_order (b L vCap eCap : ℕ) :
    b + dsTOff < dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap ≤ dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
  refine ⟨?_, rfl, ?_, sBit_in_block b L vCap eCap⟩
  · simp only [dsAuxPtr, dsHPtr, dsGPtr, dsTOff, dsHdrSize]; omega
  · simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
      dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase, dsHPrevBase,
      dsHNextBase]
    omega

/-- The `domGen` words lie before the `sBit` words. -/
lemma domGen_lt_sBit (b L vCap eCap : ℕ) : dsDomGenBase b L vCap eCap < dsSBitBase b L vCap eCap := by
  simp only [dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase,
    dsPiPtrBase, dsEdgeDomGenBase]
  omega

end

end MinCostFlow.DynSpanner.Program
