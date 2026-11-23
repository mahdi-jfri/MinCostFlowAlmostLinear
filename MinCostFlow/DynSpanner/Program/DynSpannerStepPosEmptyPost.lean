module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosEmptyGlue
public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueB

/-!
# The shared post of the empty branch of a `0 < j` step

When `E_aff = ∅`, the procedure `dsStepPosEmptyStmt` calls `dsStepFinishStmt` (the records of
`U_H`, the new buckets, the cleared levels above `j`, and the empty walk table of level `j`) and
then stores three words at `heapStep`. This file shows that the memory afterwards satisfies
`StepPosMidPost`, the post that both branches share before the epilogue.

The proof has two parts. `stepPosE_frames` is pure address arithmetic: it follows each word of
the final memory back to the memory where it was last written. `stepPosE_midPost` then checks
each clause of `StepPosMidPost` from the posts of the calls.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

public section

/-- Frame facts for the empty branch. The memories are `mem0` (start of the step), `mem2` (after
`dsStepHead`), `memAff` (after `dsAffStage`), `memMid` (after `dsStepTail`), `memFin` (after
`dsSetLevelWalks`, which writes no walk since level `j` gets no edge) and `memFinal` (after the
three stores). Each conclusion says which earlier memory a word of `memFinal` comes from. -/
lemma stepPosE_frames
    {b L vCap eCap j heapStep headHeap r₁ heapAff prefWords sPrevLen uh cSize dPtr : ℕ}
    {mem0 mem2 memAff memMid memFin memFinal : ℕ → ℕ}
    (hj : j ≤ L)
    (hAr : b + dsFixedSize L vCap eCap ≤ heapStep ∧ heapStep + 5 + prefWords ≤ headHeap ∧
      headHeap ≤ r₁ ∧ r₁ ≤ heapAff ∧ heapAff + 2 + sPrevLen ≤ uh ∧ uh + 1 + cSize ≤ dPtr)
    (hHdr_02 : ∀ addr, b ≤ addr → addr < dsGPtr b → addr ≠ b + dsGenOff → mem2 addr = mem0 addr)
    (hDom_02 : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr → addr < dsSGenBase b L vCap eCap →
      mem2 addr = mem0 addr)
    (hAff_frame : ∀ addr, addr < heapAff → addr ≠ b + dsGenOff →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsSBitBase b L vCap eCap ∨ dsSBitBase b L vCap eCap + vCap ≤ addr) →
      (addr < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memAff addr = mem2 addr)
    (hTailFr : ∀ addr, (addr < uh ∨ uh + 1 + cSize ≤ addr) →
      (addr < dsHPtr b vCap eCap ∨ dsAuxPtr b vCap eCap ≤ addr) →
      (addr < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      (addr < dsDomGenBase b L vCap eCap + (j + 1) ∨
        dsDomGenBase b L vCap eCap + (L + 1) ≤ addr) →
      (addr < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ addr) →
      memMid addr = memAff addr)
    (hSLW_fr : ∀ addr, dsLevelWalksFrameCond L vCap eCap b j uh uh addr →
      memFin addr = memMid addr)
    (hFinalEq : memFinal = Function.update
      (Function.update (Function.update memFin heapStep uh) (heapStep + 1) dPtr)
      (heapStep + 2) 0) :
    (memFinal heapStep = uh ∧ memFinal (heapStep + 1) = dPtr ∧ memFinal (heapStep + 2) = 0) ∧
    (∀ a < heapStep, memFinal a = memFin a) ∧
    (∀ a, uh ≤ a → memFinal a = memMid a) ∧
    (∀ a, uh + 1 + cSize ≤ a → memFinal a = memAff a) ∧
    memMid (b + dsGenOff) = memAff (b + dsGenOff) ∧
    (∀ a, a < dsDomGenBase b L vCap eCap → a ≠ b + dsGenOff → memFinal a = memMid a) ∧
    (∀ a, b ≤ a → a < dsGPtr b → a ≠ b + dsGenOff → memFinal a = mem0 a) ∧
    (∀ a, dsGPtr b ≤ a → a < dsGPtr b + dynGraphSize vCap eCap → memFinal a = mem2 a) ∧
    (∀ a, dsAuxPtr b vCap eCap ≤ a → a < dsAuxPtr b vCap eCap + dynGraphSize vCap eCap →
      memFinal a = memAff a) ∧
    (∀ i : Fin (L + 1), i.1 < j →
      memFinal (dsDomGenBase b L vCap eCap + i.1) = mem0 (dsDomGenBase b L vCap eCap + i.1) ∧
      (∀ e < eCap,
        memFinal (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ∧
        memFinal (dsPiPtrBase b L vCap eCap + i.1 * eCap + e) =
          mem0 (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)) ∧
      (∀ v < vCap,
        memFinal (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
          mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ∧
        memFinal (dsRevHeadBase b L vCap eCap + i.1 * vCap + v) =
          mem0 (dsRevHeadBase b L vCap eCap + i.1 * vCap + v))) ∧
    (∀ i, j < i → i < L + 1 → memFinal (dsDomGenBase b L vCap eCap + i) =
      memMid (dsDomGenBase b L vCap eCap + i)) ∧
    (∀ i : Fin (L + 1), j < i.1 →
      (∀ e < eCap, memFinal (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
        mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e)) ∧
      (∀ v < vCap, memFinal (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
        mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v))) ∧
    (∀ i, j ≤ i → i < L + 1 → memFinal (dsSGenBase b L vCap eCap + i) =
      memMid (dsSGenBase b L vCap eCap + i)) ∧
    (∀ i : Fin (L + 1), i.1 < j →
      memFinal (dsSGenBase b L vCap eCap + i.1) = mem2 (dsSGenBase b L vCap eCap + i.1)) ∧
    (∀ i : Fin (L + 1),
      memFinal (dsSHeadBase b L vCap eCap + i.1) = mem2 (dsSHeadBase b L vCap eCap + i.1) ∧
      ∀ v < vCap, memFinal (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v)) ∧
    (∀ v < vCap, memFinal (dsSBitBase b L vCap eCap + v) =
      memAff (dsSBitBase b L vCap eCap + v)) ∧
    (∀ e < eCap, memFinal (dsEStampBase b L vCap eCap + e) =
      memAff (dsEStampBase b L vCap eCap + e)) ∧
    (∀ e < eCap, memFinal (dsKeptStampBase b L vCap eCap + e) =
      mem2 (dsKeptStampBase b L vCap eCap + e)) ∧
    (∀ a, heapStep + 3 ≤ a → a < heapAff → memFinal a = mem2 a) ∧
    (∀ a, heapAff ≤ a → a < uh → memFinal a = memAff a) ∧
    (∀ a < heapStep, (a < b ∨ b + dsFixedSize L vCap eCap ≤ a) → memFinal a = mem2 a) := by
  have hfl := fixed_layout_order b L vCap eCap
  have hgo := genOff_lt_hPtr b L vCap eCap
  obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6⟩ := hAr
  have hfixU : b + dsFixedSize L vCap eCap ≤ uh := by omega
  have hL1 : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hL2 : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hL3 : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hF_fin : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 →
      memFinal a = memFin a := fun a h0 h1 h2 => by
    rw [hFinalEq, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]
  have hF_lt : ∀ a < heapStep, memFinal a = memFin a := fun a ha =>
    hF_fin a (by omega) (by omega) (by omega)
  have hF_uh : ∀ a, uh ≤ a → memFinal a = memMid a := fun a ha =>
    (hF_fin a (by omega) (by omega) (by omega)).trans
      (hSLW_fr a (slw_frame_of_range hj hfixU le_rfl (Or.inr (Or.inr (Or.inr ha)))))
  have hF_end : ∀ a, uh + 1 + cSize ≤ a → memFinal a = memAff a := fun a ha =>
    (hF_uh a (by omega)).trans (hTailFr a (Or.inr ha) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)))
  have hgen_mid : memMid (b + dsGenOff) = memAff (b + dsGenOff) :=
    hTailFr _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))
  have hF_ltDom : ∀ a, a < dsDomGenBase b L vCap eCap → a ≠ b + dsGenOff →
      memFinal a = memMid a := fun a ha hne =>
    (hF_lt a (by omega)).trans (hSLW_fr a (dsLevelWalksFrameCond_lt_domGen hfixU ha hne))
  have hF_hdr : ∀ a, b ≤ a → a < dsGPtr b → a ≠ b + dsGenOff → memFinal a = mem0 a :=
    fun a h1 h2 hne =>
      (hF_ltDom a (by omega) hne).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans
        ((hAff_frame a (by omega) hne (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans (hHdr_02 a h1 h2 hne)))
  have hF_G : ∀ a, dsGPtr b ≤ a → a < dsGPtr b + dynGraphSize vCap eCap → memFinal a = mem2 a :=
    fun a h1 h2 =>
      (hF_ltDom a (by omega) (by omega)).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans
        (hAff_frame a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))))
  have hF_aux : ∀ a, dsAuxPtr b vCap eCap ≤ a →
      a < dsAuxPtr b vCap eCap + dynGraphSize vCap eCap → memFinal a = memAff a :=
    fun a h1 h2 =>
      (hF_ltDom a (by omega) (by omega)).trans
        (hTailFr a (Or.inl (by omega)) (Or.inr h1) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)))
  have hF_dom0 : ∀ a, dsDomGenBase b L vCap eCap ≤ a → a < dsSGenBase b L vCap eCap →
      (a < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a) →
      dsLevelWalksFrameCond L vCap eCap b j uh uh a → memFinal a = mem0 a :=
    fun a h1 h2 hd hslw =>
      (hF_lt a (by omega)).trans ((hSLW_fr a hslw).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr h1) hd
          (Or.inl (by omega))).trans
        ((hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans (hDom_02 a h1 h2))))
  have hF_S2 : ∀ a, dsSGenBase b L vCap eCap ≤ a → a < dsSBitBase b L vCap eCap →
      (a < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) →
      memFinal a = mem2 a := fun a h1 h2 hs =>
    (hF_lt a (by omega)).trans
      ((hSLW_fr a (slw_frame_of_range hj hfixU le_rfl (Or.inr (Or.inl ⟨h1, by omega⟩)))).trans
      ((hTailFr a (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) hs).trans
      (hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inl h2)
        (Or.inl (by omega)) (Or.inl (by omega)))))
  -- Words of the fixed block after the `S` rows, and heap words below `uh`.
  have hF_hi : ∀ a, dsEStampBase b L vCap eCap ≤ a → a < uh →
      (a < heapStep ∨ heapStep + 3 ≤ a) → memFinal a = memAff a :=
    fun a h1 h2 h3 =>
      (hF_fin a (by omega) (by omega) (by omega)).trans
        ((hSLW_fr a (slw_frame_of_range hj hfixU le_rfl
          (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))).trans
        (hTailFr a (Or.inl h2) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inr (by omega))))
  refine ⟨⟨?_, ?_, ?_⟩, hF_lt, hF_uh, hF_end, hgen_mid, hF_ltDom, hF_hdr, hF_G, hF_aux,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFinalEq, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [hFinalEq, Function.update_of_ne (by omega), Function.update_self]
  · rw [hFinalEq, Function.update_self]
  · intro i hi
    have hneq : i.1 ≠ j := Nat.ne_of_lt hi
    have hiL : i.1 ≤ L := Nat.le_of_lt_succ i.2
    refine ⟨hF_dom0 _ (Nat.le_add_right _ _) (by omega) (Or.inl (by omega))
      (slw_frame_of_other_lvl hj hiL hneq hfixU (Or.inl rfl)),
      fun e he => ⟨?_, ?_⟩, fun v hv => ⟨?_, ?_⟩⟩
    · have := idx_lt_rows i.2 he
      exact hF_dom0 _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixU (Or.inr (Or.inl ⟨e, he, rfl⟩)))
    · have := idx_lt_rows i.2 he
      exact hF_dom0 _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixU (Or.inr (Or.inr (Or.inl ⟨e, he, rfl⟩))))
    · have := idx_lt_rows i.2 hv
      exact hF_dom0 _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixU
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩)))))
    · have := idx_lt_rows i.2 hv
      exact hF_dom0 _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixU
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hv, rfl⟩)))))
  · intro i hi1 hi2
    exact (hF_lt _ (by omega)).trans
      (hSLW_fr _ (slw_frame_of_other_lvl hj (by omega) (Nat.ne_of_gt hi1) hfixU (Or.inl rfl)))
  · intro i hi
    have hneq : i.1 ≠ j := Nat.ne_of_gt hi
    have hiL : i.1 ≤ L := Nat.le_of_lt_succ i.2
    refine ⟨fun e he => ?_, fun v hv => ?_⟩
    · have := idx_lt_rows i.2 he
      exact hF_dom0 _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixU (Or.inr (Or.inl ⟨e, he, rfl⟩)))
    · have := idx_lt_rows i.2 hv
      exact hF_dom0 _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixU
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩)))))
  · intro i hi1 hi2
    exact (hF_lt _ (by omega)).trans
      (hSLW_fr _ (slw_frame_of_range hj hfixU le_rfl
        (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by omega⟩))))
  · intro i hi
    exact hF_S2 _ (Nat.le_add_right _ _) (by omega) (Or.inl (by omega))
  · intro i
    refine ⟨hF_S2 _ (by omega) (by omega) (Or.inr (by omega)), fun v hv => ?_⟩
    have := idx_lt_rows i.2 hv
    exact hF_S2 _ (by omega) (by omega) (Or.inr (by omega))
  · intro v hv
    exact (hF_lt _ (by omega)).trans
      ((hSLW_fr _ (slw_frame_of_range hj hfixU le_rfl
        (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans
      (hTailFr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))))
  · intro e he
    exact hF_hi _ (Nat.le_add_right _ _) (by omega) (Or.inl (by omega))
  · intro e he
    exact (hF_hi _ (by omega) (by omega) (Or.inl (by omega))).trans
      (hAff_frame _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl (by omega)))
  · intro a h1 h2
    exact (hF_hi a (by omega) (by omega) (Or.inr h1)).trans
      (hAff_frame a h2 (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)))
  · intro a h1 h2
    exact hF_hi a (by omega) h2 (Or.inr (by omega))
  · intro a ha hout
    rcases hout with hlt | hge
    · exact (hF_ltDom a (by omega) (by omega)).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans
        (hAff_frame a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))))
    · exact (hF_hi a (by omega) (by omega) (Or.inl ha)).trans
        (hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inr (by omega)))

/-- More frame facts for the empty branch, derived from four of the conclusions of
`stepPosE_frames`: the words of the graph `H`, of `minH`, of level `j` and of the step's own
heap. -/
lemma stepPosE_frames_extra
    {b L vCap eCap j heapStep headHeap r₁ heapAff prefWords sPrevLen uh : ℕ}
    {mem2 memAff memMid memFin memFinal : ℕ → ℕ}
    (hj : j ≤ L)
    (hAr : b + dsFixedSize L vCap eCap ≤ heapStep ∧ heapStep + 5 + prefWords ≤ headHeap ∧
      headHeap ≤ r₁ ∧ r₁ ≤ heapAff ∧ heapAff + 2 + sPrevLen ≤ uh)
    (hF_lt : ∀ a < heapStep, memFinal a = memFin a)
    (hF_ltDom : ∀ a, a < dsDomGenBase b L vCap eCap → a ≠ b + dsGenOff → memFinal a = memMid a)
    (hF_heap2 : ∀ a, heapStep + 3 ≤ a → a < heapAff → memFinal a = mem2 a)
    (hF_heapAff : ∀ a, heapAff ≤ a → a < uh → memFinal a = memAff a) :
    (∀ a, dsHPtr b vCap eCap ≤ a → a < dsHPtr b vCap eCap + dynGraphSize vCap eCap →
      memFinal a = memMid a) ∧
    (∀ a, dsMinHBase b vCap eCap ≤ a → a < dsDomGenBase b L vCap eCap →
      memFinal a = memMid a) ∧
    (∀ e < eCap, memFinal (dsMinHBase b vCap eCap + e) = memMid (dsMinHBase b vCap eCap + e)) ∧
    memFinal (b + dsGenOff) = memFin (b + dsGenOff) ∧
    memFinal (dsDomGenBase b L vCap eCap + j) = memFin (dsDomGenBase b L vCap eCap + j) ∧
    (∀ e < eCap,
      memFinal (dsEdgeDomGenBase b L vCap eCap + j * eCap + e) =
        memFin (dsEdgeDomGenBase b L vCap eCap + j * eCap + e) ∧
      memFinal (dsPiPtrBase b L vCap eCap + j * eCap + e) =
        memFin (dsPiPtrBase b L vCap eCap + j * eCap + e)) ∧
    (∀ v < vCap,
      memFinal (dsRevGenBase b L vCap eCap + j * vCap + v) =
        memFin (dsRevGenBase b L vCap eCap + j * vCap + v) ∧
      memFinal (dsRevHeadBase b L vCap eCap + j * vCap + v) =
        memFin (dsRevHeadBase b L vCap eCap + j * vCap + v)) ∧
    (∀ v < vCap, memFinal (dsVStampBase b L vCap eCap + v) =
      memFin (dsVStampBase b L vCap eCap + v)) ∧
    (∀ a, headHeap ≤ a → a < r₁ → memFinal a = mem2 a) ∧
    (∀ a, heapStep + 5 ≤ a → a < heapStep + 5 + prefWords → memFinal a = mem2 a) ∧
    (∀ i < sPrevLen, memFinal (heapAff + 2 + i) = memAff (heapAff + 2 + i)) := by
  have hfl := fixed_layout_order b L vCap eCap
  have hgo := genOff_lt_hPtr b L vCap eCap
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := hAr
  have hjL : j < L + 1 := Nat.lt_succ_of_le hj
  refine ⟨fun a h1 h2 => hF_ltDom a (by omega) (by omega),
    fun a h1 h2 => hF_ltDom a h2 (by omega),
    fun e he => hF_ltDom _ (by omega) (by omega),
    hF_lt _ (by omega), hF_lt _ (by omega), fun e he => ?_, fun v hv => ?_,
    fun v hv => hF_lt _ (by omega),
    fun a h1 h2 => hF_heap2 a (by omega) (by omega),
    fun a h1 h2 => hF_heap2 a (by omega) (by omega),
    fun i hi => hF_heapAff _ (by omega) (by omega)⟩
  · have := idx_lt_rows hjL he
    exact ⟨hF_lt _ (by omega), hF_lt _ (by omega)⟩
  · have := idx_lt_rows hjL hv
    exact ⟨hF_lt _ (by omega), hF_lt _ (by omega)⟩

/-- The memory after the call of `dsStepFinishStmt` and the three stores of
`dsStepPosEmptyStmt` satisfies `StepPosMidPost`, with next free word `dPtr`. The list of `D` is
empty, since `D = ∅` when `E_aff = ∅` (`stepPosE_res_eqs`). -/
theorem stepPosE_midPost (ctx : StepPosEmptyCtx)
    {c : UTCtx} {r : RBCtx} {retFin : ℕ} {memFin memFinal : ℕ → ℕ}
    (hcInfo : c.da.w = ctx.w ∧ c.da.eCap = ctx.eCap ∧ c.vCap = ctx.vCap ∧
      c.da.lo = ctx.j ∧ c.da.hi = ctx.L + 1 ∧ c.da.out = ctx.uhTailHdr + 1 ∧
      c.es = [] ∧ c.size = 2 * ctx.oldBucketsSum)
    (hrInfo : r.L = ctx.L ∧ r.vCap = ctx.vCap ∧ r.eCap = ctx.eCap ∧ r.b = ctx.b ∧
      r.j = ctx.j ∧ r.es = [])
    (hPermRecs : (restrictUpdate ctx.u ctx.st.H ++ c.recs).Perm ctx.res.UH)
    (hApplyRecs : (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H)).applyBatch c.recs =
      ctx.res.state.H)
    (hDelIns : ∀ u' ∈ c.recs, isDelOrIns u')
    (hminNew : ∀ e < ctx.eCap,
      (minHRebuild ctx.j ∅ r.m0 e = 0 ↔ e ∉ ctx.res.state.H.E) ∧
      (e ∈ ctx.res.state.H.E → ∃ i : Fin (ctx.L + 1),
        minHRebuild ctx.j ∅ r.m0 e = i.1 + 1 ∧
        e ∈ (ctx.res.state.H_level i).E ∧
        ∀ k' : Fin (ctx.L + 1), k'.1 < i.1 → e ∉ (ctx.res.state.H_level k').E))
    (hnewB : ∀ i : Fin (ctx.L + 1), ∀ e, e ∈ r.newB i.1 ↔
      e ∈ ctx.res.state.H.E ∧ minHRebuild ctx.j ∅ r.m0 e = i.1 + 1)
    (hFinPost :
      (dsStepFinishContract c (ctx.st.H.applyBatch (restrictUpdate ctx.u ctx.st.H))
        ctx.uhTailHdr r ctx.G' [] (fun _ => []) (fun _ => False)
        ctx.eAffPtr ctx.retAff ctx.uhTailHdr).post
        ([dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          ctx.retAff, ctx.uhTailHdr + 1, ctx.retAff, 0,
          dgEPresBase (dsHPtr ctx.b ctx.vCap ctx.eCap) ctx.vCap,
          dsGPtr ctx.b, dsHPtr ctx.b ctx.vCap ctx.eCap, ctx.uhTailHdr] ++
         [dsHNextBase ctx.b ctx.vCap ctx.eCap, dsHHeadBase ctx.b ctx.vCap ctx.eCap,
          dsHDegDummyBase ctx.b ctx.L ctx.vCap ctx.eCap, ctx.j, ctx.L + 1,
          dsMinHBase ctx.b ctx.vCap ctx.eCap, ctx.b, ctx.retAff, 0] ++
         [dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap, dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap,
          ctx.j + 1, ctx.j, ctx.L + 1] ++
         [ctx.b, ctx.j, ctx.eAffPtr, 0, ctx.retAff, ctx.uhTailHdr])
        ctx.memAff retFin memFin)
    (hFinalEq : memFinal = Function.update
      (Function.update (Function.update memFin ctx.heapStep ctx.uhTailHdr)
        (ctx.heapStep + 1) ctx.dPtr) (ctx.heapStep + 2) 0) :
    StepPosMidPost ctx.G₀ ctx.L ctx.q ctx.vCap ctx.eCap ctx.b ctx.k ctx.impl ctx.us ctx.u
      ctx.mem0 ctx.mem2 ctx.x ctx.headHeap ctx.r₁ ctx.heapStep ctx.heapAff ctx.sPrevList
      ctx.prefWords memFinal ctx.dPtr := by
  obtain ⟨_, hc_e, hc_v, _, _, hc_out, _, hc_size⟩ := hcInfo
  obtain ⟨hr_L, hr_v, hr_e, hr_b, hr_j, hr_es⟩ := hrInfo
  have hj_le : ctx.j ≤ ctx.L := chooseLevel_le ctx.L ctx.q (ctx.k + 1)
  have hres_eqs := stepPosE_res_eqs ctx
  have hfl := fixed_layout_order ctx.b ctx.L ctx.vCap ctx.eCap
  rcases hFinPost with ⟨memMid, _, hTailPost, hSLWPost⟩
  rcases hTailPost with ⟨_, hTail_H, hTail_hdr, hTail_body, hTail_Bk, hTail_minH, hTail_domZ,
    hTail_sZ, hTail_fr⟩
  rcases hSLWPost with ⟨eLP, mEP, hP, hSLW_args, hSLW_ge, hSLW_le, hSLW_gen, hSLW_dg_eq,
    hSLW_vst, hSLW_edg_le, hSLW_edg_eq, _, ⟨revJ, hSLW_rev⟩, hSLW_fr⟩
  simp only [List.cons.injEq, and_true] at hSLW_args
  obtain ⟨-, -, rfl, -, rfl, rfl⟩ := hSLW_args
  have hret_eq : retFin = ctx.uhTailHdr := by
    simp only [List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero] at hSLW_le
    exact le_antisymm hSLW_le hSLW_ge
  simp only [hr_b, hr_L, hr_v, hr_e, hr_j, hret_eq] at hSLW_fr hSLW_rev hSLW_gen hSLW_dg_eq
  simp only [hr_b, hr_L, hr_v, hr_e, hr_j] at hSLW_vst hSLW_edg_le hSLW_edg_eq
  -- The arithmetic of the addresses.
  have hAr : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ ctx.heapStep ∧
      ctx.heapStep + 5 + ctx.prefWords ≤ ctx.headHeap ∧ ctx.headHeap ≤ ctx.r₁ ∧
      ctx.r₁ ≤ ctx.heapAff ∧ ctx.heapAff + 2 + ctx.sPrevList.length ≤ ctx.uhTailHdr ∧
      ctx.uhTailHdr + 1 + c.size ≤ ctx.dPtr := by
    have h1 := ctx.hhead_in
    have h2 := ctx.hret_ge
    refine ⟨ctx.hfix_step, h1.1, h1.2.1, h1.2.2, ?_, ?_⟩
    · show _ ≤ ctx.retAff + ctx.eCap
      omega
    · rw [hc_size]
  have hRet_le : ctx.retAff ≤ ctx.dPtr := by
    show ctx.retAff ≤ ctx.retAff + ctx.eCap + 1 + 2 * ctx.oldBucketsSum
    omega
  have hTailFr' : ∀ a, (a < ctx.uhTailHdr ∨ ctx.uhTailHdr + 1 + c.size ≤ a) →
      (a < dsHPtr ctx.b ctx.vCap ctx.eCap ∨ dsAuxPtr ctx.b ctx.vCap ctx.eCap ≤ a) →
      (a < dsMinHBase ctx.b ctx.vCap ctx.eCap ∨ dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap ≤ a) →
      (a < dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.j + 1) ∨
        dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.L + 1) ≤ a) →
      (a < dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.j ∨
        dsSGenBase ctx.b ctx.L ctx.vCap ctx.eCap + (ctx.L + 1) ≤ a) →
      memMid a = ctx.memAff a := fun a h1 h2 h3 h4 h5 =>
    hTail_fr a (by rw [hc_out]; exact h1)
      (by rw [hr_b, hr_v, hr_e, hc_v, hc_e, hfl.2.2.1]; exact h2)
      (by rw [hr_b, hr_v, hr_e, hr_L]; exact h3)
      (fun hgw => by simp only [RBCtx.GenWord, hr_b, hr_L, hr_v, hr_e, hr_j] at hgw; omega)
  obtain ⟨hF_st, hF_lt, hF_uh, hF_end, hgen_mid, hF_ltDom, hF_hdr, hF_G, hF_aux, hF_domLt,
    hF_domGt, hF_domGt0, hF_sGe, hF_Slt, hF_Svs, hF_sBit, hF_eSt, hF_kept, hF_heap2,
    hF_heapAff, hF_out2⟩ :=
    stepPosE_frames hj_le hAr ctx.hHdr_02 ctx.hDom_02 ctx.hAff_frame hTailFr' hSLW_fr hFinalEq
  obtain ⟨hF_H, hF_minR, hF_minE, hF_gen, hF_domJ, hF_edJ, hF_revJ, hF_vSt, hF_headR, hF_prefR,
    hF_sPrevR⟩ :=
    stepPosE_frames_extra hj_le ⟨hAr.1, hAr.2.1, hAr.2.2.1, hAr.2.2.2.1, hAr.2.2.2.2.1⟩
      hF_lt hF_ltDom hF_heap2 hF_heapAff
  have hgen_fin : memFinal (ctx.b + dsGenOff) = ctx.memAff (ctx.b + dsGenOff) + 1 := by
    rw [hF_gen, hSLW_gen, hgen_mid]; rfl
  have hdom_fin : memFinal (dsDomGenBase ctx.b ctx.L ctx.vCap ctx.eCap + ctx.j) =
      ctx.memAff (ctx.b + dsGenOff) + 1 := by
    rw [hF_domJ, hSLW_dg_eq, hgen_mid]
  have hHE_cap : ∀ e ∈ ctx.res.state.H.E, e < ctx.eCap := by
    have hk1 := (step_inv ctx.hVG₀ (lt_of_lt_of_le ctx.hj_pos hj_le) ctx.hq ctx.hGm₀
      (canonicalSparsify_spec_absorb ctx.impl ctx.mMax) ctx.hBV ctx.hds ctx.hu_some ctx.hPref).1
    have hst1 : runState (L := ctx.L) ctx.G₀ ctx.q (canonicalSparsify ctx.impl) ctx.us
        (ctx.k + 1) = ctx.res.state := by
      simp only [runState, ctx.hu_some]
    have hsub : ctx.res.state.H.E ⊆ ctx.G'.E := by
      have h1 := hk1.H_sub.2.1
      rw [← hk1.G_eq, hst1, hres_eqs.1] at h1
      exact h1
    have hdu := (batchIsValid_take ctx.us ctx.G₀ ctx.k ctx.hBV ctx.hds).2.2 ctx.u ctx.hu_some
    exact fun e he => ctx.hState.2.2.2.2.2.2.2.2.2.2.1 e (E_applyUpdate_subset hdu.2 (hsub he))
  have hminE : ∀ e < ctx.eCap, memFinal (dsMinHBase ctx.b ctx.vCap ctx.eCap + e) =
      minHRebuild ctx.j ∅ r.m0 e := fun e he => by
    have hm := hTail_minH e (by rw [hr_e]; exact he)
    rw [hr_b, hr_v, hr_e, hr_j, hr_es, List.toFinset_nil] at hm
    rw [hF_minE e he, hm]
  refine ⟨ctx.uhTailHdr, ctx.dPtr, c, r, revJ, [],
    hF_st.1, hF_st.2.1, hF_st.2.2, hAr.2.2.2.2.1, hAr.2.2.2.2.2, le_of_eq (Nat.add_zero _),
    fun a ha => (hF_end a (le_trans hAr.2.2.2.2.2 ha)).trans
      (ctx.hZeroAff a (le_trans hRet_le ha)),
    (hF_uh _ le_rfl).trans hTail_hdr, ?_, hPermRecs, hDelIns, List.nodup_nil,
    by rw [hres_eqs.2.2]; rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
    hr_L, hr_v, hr_e, hr_b, hr_j, ?_, ?_, ?_, ?_, ?_,
    by rw [hgen_fin]; exact Nat.le_add_left 1 _,
    by rw [hgen_fin, ctx.hAff_gen]; exact Nat.le_succ_of_le (Nat.le_succ _),
    by rw [hgen_fin, ctx.hAff_gen]; omega,
    by rw [hres_eqs.1]; exact dynGraphAt_of_agree ctx.hG'_graph hF_G, ?_,
    dynGraphAt_of_agree ctx.hAff_aux hF_aux, ?_,
    fun e he => by rw [hminE e he]; exact hminNew e he, ?_, hF_domLt, ?_, ?_, ?_, ?_, ?_, ?_,
    hF_prefR, listAt_of_agree hF_sPrevR ctx.hAff_sPrev, ?_⟩
  -- The batch body of the records of `U_H`.
  · intro K
    have hb := hTail_body K
    rw [hc_out] at hb
    exact hb.of_agree fun i _ => hF_uh _ (Nat.le_add_right_of_le (Nat.le_succ _))
  -- The header words `q, t, L, vCap, eCap`.
  · rw [hF_hdr _ (by simp [dsQOff]) (by simp [dsQOff, dsGPtr, dsHdrSize])
      (by simp [dsQOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr _ (by simp [dsTOff]) (by simp [dsTOff, dsGPtr, dsHdrSize])
      (by simp [dsTOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr _ (by simp [dsLOff]) (by simp [dsLOff, dsGPtr, dsHdrSize])
      (by simp [dsLOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr _ (by simp [dsVCapOff]) (by simp [dsVCapOff, dsGPtr, dsHdrSize])
      (by simp [dsVCapOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [hF_hdr _ (by simp [dsECapOff]) (by simp [dsECapOff, dsGPtr, dsHdrSize])
      (by simp [dsECapOff, dsGenOff])]
    exact ctx.hState.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- The graph `H` and the buckets.
  · rw [← hApplyRecs]
    rw [hr_b, hr_v, hr_e, hc_v, hc_e] at hTail_H
    exact dynGraphAt_of_agree hTail_H hF_H
  · rw [hr_L, hr_v, hr_e, hr_b] at hTail_Bk
    exact hTail_Bk.of_agree_range hF_minR
  -- The new buckets.
  · intro i e
    rw [hnewB i e]
    constructor
    · rintro ⟨heH, hmh⟩
      exact ⟨heH, by rw [hminE e (hHE_cap e heH), hmh]⟩
    · rintro ⟨heH, hmh⟩
      rw [hminE e (hHE_cap e heH)] at hmh
      exact ⟨heH, hmh⟩
  -- The words of the old state's heap.
  · intro a ha
    have halt : a < ctx.heapStep := ctx.hfoot_lt a ha
    rcases ha with ⟨iv, hiv, hlo, hhi⟩
    have hge : ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a :=
      le_trans (ctx.hState.2.2.1 iv hiv) hlo
    exact (hF_out2 a halt (Or.inr hge)).trans (ctx.hFoot_02 a ⟨iv, hiv, hlo, hhi⟩)
  -- Level `j`: its domain is empty.
  · refine ⟨by rw [hdom_fin]; exact Nat.succ_pos _, le_of_eq (hdom_fin.trans hgen_fin.symm),
      fun e he => ⟨?_, ?_⟩, fun e he => absurd he (by rw [hres_eqs.2.1]; exact Finset.notMem_empty e),
      fun v hv => ?_⟩
    · rw [(hF_edJ e he).1, hF_gen]
      exact hSLW_edg_le e he
    · rw [(hF_edJ e he).1, hF_domJ, hSLW_edg_eq e he, hres_eqs.2.1]
      simp
    · obtain ⟨hrev_le, hrev_nd, hrev_mem, hrev_ll⟩ := hSLW_rev v hv
      refine ⟨by rw [(hF_revJ v hv).1, hF_gen]; exact hrev_le, hrev_nd,
        fun e => by rw [hrev_mem e, hres_eqs.2.1]; simp, ?_⟩
      rw [hF_domJ, (hF_revJ v hv).1, (hF_revJ v hv).2]
      split_ifs with hcond
      · simp only [hcond] at hrev_ll
        refine (hrev_ll.of_agree fun a ha => ?_).mono fun a ha => ?_
        · rcases ha with hf | ⟨h1, h2⟩
          · exact hf.elim
          · exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
        · rcases ha with hf | ⟨h1, h2⟩
          · exact hf.elim
          · exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)
      · simp only [hcond, ↓reduceIte] at hrev_ll
        exact hrev_ll
  -- Levels above `j`.
  · intro i hi
    have h0 := hTail_domZ i.1 (by rw [hr_j]; exact hi) (by rw [hr_L]; exact i.2)
    rw [hr_b, hr_L, hr_v, hr_e] at h0
    exact ⟨by rw [hF_domGt i.1 hi i.2]; exact h0, (hF_domGt0 i hi).1, (hF_domGt0 i hi).2⟩
  -- The words of the sets `S_i`.
  · intro i
    split_ifs with hij
    · exact ⟨hF_Slt i hij, (hF_Svs i).1, (hF_Svs i).2, hF_headR⟩
    · have hj_le_i : ctx.j ≤ i.1 := Nat.le_of_not_lt hij
      have h0 := hTail_sZ i.1 (by rw [hr_j]; exact hj_le_i) (by rw [hr_L]; exact i.2)
      rw [hr_b, hr_L, hr_v, hr_e] at h0
      exact ⟨by rw [hF_sGe i.1 hj_le_i i.2]; exact h0, (hF_Svs i).1, (hF_Svs i).2⟩
  -- `sBit` and `vStamp`.
  · intro v hv
    exact ⟨by rw [hF_sBit v hv]; exact ctx.hAff_sBit v hv,
      by rw [hF_vSt v hv, hF_gen]; exact hSLW_vst v hv⟩
  -- `eStamp` and `keptStamp`.
  · intro e he
    exact ⟨by rw [hF_eSt e he, hgen_fin]; exact Nat.le_succ_of_le (ctx.hAff_eStamp e he),
      by rw [hF_kept e he]; exact ctx.hKept_02 e he⟩
  -- The frame below `heapStep`.
  · intro a ha hnm
    have hout : a < ctx.b ∨ ctx.b + dsFixedSize ctx.L ctx.vCap ctx.eCap ≤ a := by
      by_contra h
      push Not at h
      exact hnm (Or.inl ⟨h.1, by rw [ctx.hState.1, ctx.hState.2.1]; exact h.2⟩)
    exact (hF_out2 a ha hout).trans (ctx.hFrame_02 a ha hnm)

end

end MinCostFlow.DynSpanner.Program
