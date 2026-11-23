module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelWalksDefs
import MinCostFlow.DynSpanner.Program.DynSpannerStepPosNEGlueB

/-!
# Memory-frame agreement lemmas for the nonempty `E_aff` branch of a positive-level step

This file proves the three batches of frame agreement lemmas (`stepPosNE_mid_frames_a`,
`stepPosNE_mid_frames_b`, and `stepPosNE_mid_frames_c`) relating the final memory `memFinal` of
`dsStepPosNonEmptyStmt` back to the intermediate stage memories. They are used by
`stepPosNE_midPost` in `DynSpannerStepPosNEGlueC.lean`.
-/

public section

namespace MinCostFlow.DynSpanner.Program

open WordRAM

private lemma idx_lt_mul_c {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m :=
  calc i * m + e < i * m + m := Nat.add_lt_add_left he _
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ hi

/-- First batch of frame agreement lemmas from `memFinal` back to earlier memories. -/
lemma stepPosNE_mid_frames_a
    {b L vCap eCap j heapStep heapAff scratchPtr retSp heapFin retFin uhTailHdr cSize dPtr dTot
      nextHeap dLen : ℕ}
    {mem0 mem2 memAff memSp memReemb memMid memFin memGen memCol memFinal : ℕ → ℕ}
    (hj : j ≤ L)
    (hAr :
      b + dsFixedSize L vCap eCap ≤ heapStep ∧
      heapStep + 5 ≤ heapAff ∧
      heapAff < scratchPtr ∧
      scratchPtr < retSp ∧
      retSp + eCap ≤ heapFin ∧
      heapFin ≤ retFin ∧
      retFin ≤ uhTailHdr ∧
      uhTailHdr + 1 + cSize ≤ dPtr ∧
      dPtr + dTot ≤ nextHeap)
    (hHdr_02 : ∀ addr, b ≤ addr → addr < dsGPtr b → addr ≠ b + dsGenOff → mem2 addr = mem0 addr)
    (hDom_02 : ∀ addr, dsDomGenBase b L vCap eCap ≤ addr → addr < dsSGenBase b L vCap eCap →
      mem2 addr = mem0 addr)
    (hAff_frame : ∀ addr, addr < heapAff → addr ≠ b + dsGenOff →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsSBitBase b L vCap eCap ∨ dsSBitBase b L vCap eCap + vCap ≤ addr) →
      (addr < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memAff addr = mem2 addr)
    (hlt_scr_ag : ∀ addr, addr < scratchPtr →
      (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) → memSp addr = memAff addr)
    (hRe_lt : ∀ addr, addr < retSp → memReemb addr = memSp addr)
    (hTailFr : ∀ addr, (addr < uhTailHdr ∨ uhTailHdr + 1 + cSize ≤ addr) →
      (addr < dsHPtr b vCap eCap ∨ dsAuxPtr b vCap eCap ≤ addr) →
      (addr < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      (addr < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ addr) →
      (addr < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ addr) →
      memMid addr = memReemb addr)
    (hSLW_fr : ∀ addr, dsLevelWalksFrameCond L vCap eCap b j heapFin retFin addr →
      memFin addr = memMid addr)
    (hGenEq : memGen = Function.update memFin (b + dsGenOff) (memFin (b + dsGenOff) + 1))
    (hColFr : ∀ addr, (addr < dsEStampBase b L vCap eCap ∨
        dsEStampBase b L vCap eCap + eCap ≤ addr) →
      (addr < dPtr ∨ dPtr + dTot ≤ addr) → memCol addr = memGen addr)
    (hFinalEq : memFinal = Function.update
      (Function.update (Function.update memCol heapStep uhTailHdr) (heapStep + 1) dPtr)
      (heapStep + 2) dLen) :
    (∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → memFinal a = memCol a) ∧
    (∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → a ≠ b + dsGenOff →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      (a < dPtr ∨ dPtr + dTot ≤ a) → memFinal a = memFin a) ∧
    (∀ a, a < dsDomGenBase b L vCap eCap → a ≠ b + dsGenOff → memFinal a = memMid a) ∧
    (∀ a, a < dsHPtr b vCap eCap → a ≠ b + dsGenOff → memFinal a = memAff a) ∧
    (∀ a, dsAuxPtr b vCap eCap ≤ a → a < dsMinHBase b vCap eCap → memFinal a = memAff a) ∧
    (∀ a, heapStep + 3 ≤ a → a < scratchPtr → memFinal a = memAff a) ∧
    (∀ a, a < heapStep → (a < b ∨ b + dsFixedSize L vCap eCap ≤ a) → memFinal a = mem2 a) ∧
    (∀ a, dsDomGenBase b L vCap eCap ≤ a → a < dsSGenBase b L vCap eCap →
      (a < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a) →
      dsLevelWalksFrameCond L vCap eCap b j heapFin retFin a → memFinal a = mem0 a) ∧
    (∀ a, dsSGenBase b L vCap eCap ≤ a → a < dsSBitBase b L vCap eCap →
      (a < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) →
      memFinal a = mem2 a) ∧
    (∀ a, b ≤ a → a < dsGPtr b → a ≠ b + dsGenOff → memFinal a = mem0 a) := by
  have hfl := fixed_layout_order b L vCap eCap
  have hgo := genOff_lt_hPtr b L vCap eCap
  have hF_col : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → memFinal a = memCol a :=
    fun a h0 h1 h2 => by
      rw [hFinalEq, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]
  have hF_fin : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → a ≠ b + dsGenOff →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      (a < dPtr ∨ dPtr + dTot ≤ a) → memFinal a = memFin a :=
    fun a h0 h1 h2 hg he hd =>
      (hF_col a h0 h1 h2).trans ((hColFr a he hd).trans (by rw [hGenEq, Function.update_of_ne hg]))
  have hF_mid_ltDom : ∀ a, a < dsDomGenBase b L vCap eCap → a ≠ b + dsGenOff →
      memFinal a = memMid a := fun a ha hne =>
    (hF_fin a (by omega) (by omega) (by omega) hne (Or.inl (by omega)) (Or.inl (by omega))).trans
      (hSLW_fr a (dsLevelWalksFrameCond_lt_domGen (by omega) ha hne))
  have hF_aff_ltH : ∀ a, a < dsHPtr b vCap eCap → a ≠ b + dsGenOff → memFinal a = memAff a :=
    fun a ha hne =>
      (hF_mid_ltDom a (by omega) hne).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inl ha) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans
        ((hRe_lt a (by omega)).trans (hlt_scr_ag a (by omega) (fun v hv => by omega))))
  have hF_aff_aux : ∀ a, dsAuxPtr b vCap eCap ≤ a → a < dsMinHBase b vCap eCap →
      memFinal a = memAff a := fun a ha1 ha2 =>
    (hF_mid_ltDom a (by omega) (by omega)).trans
      ((hTailFr a (Or.inl (by omega)) (Or.inr ha1) (Or.inl ha2)
        (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((hRe_lt a (by omega)).trans (hlt_scr_ag a (by omega) (fun v hv => by omega))))
  have hF_aff_heap : ∀ a, heapStep + 3 ≤ a → a < scratchPtr → memFinal a = memAff a :=
    fun a ha1 ha2 =>
      (hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
        (Or.inl (by omega))).trans
        ((hSLW_fr a (slw_frame_of_range hj (by omega) (by omega)
          (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inr (by omega))).trans
        ((hRe_lt a (by omega)).trans (hlt_scr_ag a ha2 (fun v hv => by omega)))))
  have hF_mem2_out : ∀ a, a < heapStep → (a < b ∨ b + dsFixedSize L vCap eCap ≤ a) →
      memFinal a = mem2 a := by
    intro a ha hout
    rcases hout with hlt | hge
    · exact (hF_aff_ltH a (by omega) (by omega)).trans
        (hAff_frame a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)))
    · exact (hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
          (Or.inl (by omega))).trans
        ((hSLW_fr a (slw_frame_of_range hj (by omega) (by omega)
          (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inr (by omega))).trans
        ((hRe_lt a (by omega)).trans
        ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
          (hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
            (Or.inr (by omega)) (Or.inr (by omega)))))))
  have hF_mem0_dom : ∀ a, dsDomGenBase b L vCap eCap ≤ a → a < dsSGenBase b L vCap eCap →
      (a < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a) →
      dsLevelWalksFrameCond L vCap eCap b j heapFin retFin a → memFinal a = mem0 a :=
    fun a ha1 ha2 hd hslw =>
      (hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega))).trans
        ((hSLW_fr a hslw).trans
        ((hTailFr a (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr ha1) hd
          (Or.inl (by omega))).trans
        ((hRe_lt a (by omega)).trans
        ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
        ((hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans (hDom_02 a ha1 ha2))))))
  have hF_mem2_S : ∀ a, dsSGenBase b L vCap eCap ≤ a → a < dsSBitBase b L vCap eCap →
      (a < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) →
      memFinal a = mem2 a := fun a ha1 ha2 hs =>
    (hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))).trans
      ((hSLW_fr a (slw_frame_of_range hj (by omega) (by omega)
        (Or.inr (Or.inl ⟨ha1, by omega⟩)))).trans
      ((hTailFr a (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) hs).trans
      ((hRe_lt a (by omega)).trans
      ((hlt_scr_ag a (by omega) (fun v hv => by omega)).trans
        (hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inl ha2)
          (Or.inl (by omega)) (Or.inl (by omega)))))))
  have hF_hdr0 : ∀ a, b ≤ a → a < dsGPtr b → a ≠ b + dsGenOff → memFinal a = mem0 a :=
    fun a ha1 ha2 hne =>
      (hF_aff_ltH a (by omega) hne).trans
        ((hAff_frame a (by omega) hne (Or.inl (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega))).trans (hHdr_02 a ha1 ha2 hne))
  exact ⟨hF_col, hF_fin, hF_mid_ltDom, hF_aff_ltH, hF_aff_aux, hF_aff_heap, hF_mem2_out,
    hF_mem0_dom, hF_mem2_S, hF_hdr0⟩

/-- Second batch of frame agreement lemmas from `memFinal` back to earlier memories. -/
lemma stepPosNE_mid_frames_b
    {b L vCap eCap j heapStep heapAff scratchPtr retSp heapFin retFin uhTailHdr cSize dPtr dTot
      nextHeap : ℕ}
    {mem2 memAff memSp memReemb memMid memFin memGen memCol memFinal : ℕ → ℕ}
    (hj : j ≤ L)
    (hAr :
      b + dsFixedSize L vCap eCap ≤ heapStep ∧
      heapStep + 5 ≤ heapAff ∧
      heapAff < scratchPtr ∧
      scratchPtr < retSp ∧
      retSp + eCap ≤ heapFin ∧
      heapFin ≤ retFin ∧
      retFin ≤ uhTailHdr ∧
      uhTailHdr + 1 + cSize ≤ dPtr ∧
      dPtr + dTot ≤ nextHeap)
    (hAff_frame : ∀ addr, addr < heapAff → addr ≠ b + dsGenOff →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsSBitBase b L vCap eCap ∨ dsSBitBase b L vCap eCap + vCap ≤ addr) →
      (addr < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memAff addr = mem2 addr)
    (hlt_scr_ag : ∀ addr, addr < scratchPtr →
      (∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v) → memSp addr = memAff addr)
    (hRe_lt : ∀ addr, addr < retSp → memReemb addr = memSp addr)
    (hZeroFin : ZeroFrom memReemb heapFin)
    (hTailFr : ∀ addr, (addr < uhTailHdr ∨ uhTailHdr + 1 + cSize ≤ addr) →
      (addr < dsHPtr b vCap eCap ∨ dsAuxPtr b vCap eCap ≤ addr) →
      (addr < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ addr) →
      (addr < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ addr) →
      (addr < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ addr) →
      memMid addr = memReemb addr)
    (hSLW_fr : ∀ addr, dsLevelWalksFrameCond L vCap eCap b j heapFin retFin addr →
      memFin addr = memMid addr)
    (hGenEq : memGen = Function.update memFin (b + dsGenOff) (memFin (b + dsGenOff) + 1))
    (hColFr : ∀ addr, (addr < dsEStampBase b L vCap eCap ∨
        dsEStampBase b L vCap eCap + eCap ≤ addr) →
      (addr < dPtr ∨ dPtr + dTot ≤ addr) → memCol addr = memGen addr)
    (hF_col : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → memFinal a = memCol a)
    (hF_fin : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → a ≠ b + dsGenOff →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      (a < dPtr ∨ dPtr + dTot ≤ a) → memFinal a = memFin a) :
    (∀ a, uhTailHdr ≤ a → a < uhTailHdr + 1 + cSize → memFinal a = memMid a) ∧
    ZeroFrom memFinal nextHeap ∧
    memMid (b + dsGenOff) = memAff (b + dsGenOff) ∧
    memFinal (b + dsGenOff) = memFin (b + dsGenOff) + 1 ∧
    (∀ e < eCap, memMid (retSp + e) = memReemb (retSp + e)) ∧
    (∀ i, j < i → i < L + 1 → memFinal (dsDomGenBase b L vCap eCap + i) =
      memMid (dsDomGenBase b L vCap eCap + i)) ∧
    (∀ i, j ≤ i → i < L + 1 → memFinal (dsSGenBase b L vCap eCap + i) =
      memMid (dsSGenBase b L vCap eCap + i)) ∧
    (∀ v < vCap, memFinal (dsSBitBase b L vCap eCap + v) =
      memAff (dsSBitBase b L vCap eCap + v)) ∧
    (∀ e < eCap, memGen (dsEStampBase b L vCap eCap + e) =
      memAff (dsEStampBase b L vCap eCap + e)) ∧
    (∀ e < eCap, memFinal (dsKeptStampBase b L vCap eCap + e) =
      mem2 (dsKeptStampBase b L vCap eCap + e)) := by
  have hfl := fixed_layout_order b L vCap eCap
  have hgo := genOff_lt_hPtr b L vCap eCap
  have hF_uh : ∀ a, uhTailHdr ≤ a → a < uhTailHdr + 1 + cSize → memFinal a = memMid a :=
    fun a ha1 ha2 =>
      (hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
        (Or.inl (by omega))).trans
        (hSLW_fr a (slw_frame_of_range hj (by omega) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))))
  have hZero : ZeroFrom memFinal nextHeap := fun a ha => by
    rw [hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)),
      hSLW_fr a (slw_frame_of_range hj (by omega) (by omega) (Or.inr (Or.inr (Or.inr (by omega))))),
      hTailFr a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))]
    exact hZeroFin a (by omega)
  have hgen_mid : memMid (b + dsGenOff) = memAff (b + dsGenOff) :=
    (hTailFr _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((hRe_lt _ (by omega)).trans (hlt_scr_ag _ (by omega) (fun v hv => by omega)))
  have hgen_fin : memFinal (b + dsGenOff) = memFin (b + dsGenOff) + 1 := by
    rw [hF_col _ (by omega) (by omega) (by omega),
      hColFr _ (Or.inl (by omega)) (Or.inl (by omega)), hGenEq, Function.update_self]
  have hMid_retSp : ∀ e < eCap, memMid (retSp + e) = memReemb (retSp + e) := fun e he =>
    hTailFr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega))
  have hF_mid_domGt : ∀ i, j < i → i < L + 1 → memFinal (dsDomGenBase b L vCap eCap + i) =
      memMid (dsDomGenBase b L vCap eCap + i) := fun i hi1 hi2 =>
    (hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))).trans
      (hSLW_fr _ (slw_frame_of_other_lvl hj (by omega) (Nat.ne_of_gt hi1) (by omega) (Or.inl rfl)))
  have hF_mid_sGe : ∀ i, j ≤ i → i < L + 1 → memFinal (dsSGenBase b L vCap eCap + i) =
      memMid (dsSGenBase b L vCap eCap + i) := fun i hi1 hi2 =>
    (hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))).trans
      (hSLW_fr _ (slw_frame_of_range hj (by omega) (by omega)
        (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by omega⟩))))
  have hF_sBit : ∀ v < vCap, memFinal (dsSBitBase b L vCap eCap + v) =
      memAff (dsSBitBase b L vCap eCap + v) := fun v hv =>
    (hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
      (Or.inl (by omega))).trans
      ((hSLW_fr _ (slw_frame_of_range hj (by omega) (by omega)
        (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans
      ((hTailFr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hRe_lt _ (by omega)).trans (hlt_scr_ag _ (by omega) (fun v' hv' => by omega)))))
  have hG_eSt : ∀ e < eCap, memGen (dsEStampBase b L vCap eCap + e) =
      memAff (dsEStampBase b L vCap eCap + e) := fun e he => by
    rw [hGenEq, Function.update_of_ne (by omega)]
    exact (hSLW_fr _ (slw_frame_of_range hj (by omega) (by omega)
        (Or.inr (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by omega⟩))))).trans
      ((hTailFr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hRe_lt _ (by omega)).trans (hlt_scr_ag _ (by omega) (fun v' hv' => by omega))))
  have hF_kept : ∀ e < eCap, memFinal (dsKeptStampBase b L vCap eCap + e) =
      mem2 (dsKeptStampBase b L vCap eCap + e) := fun e he =>
    (hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inl (by omega))).trans
      ((hSLW_fr _ (slw_frame_of_range hj (by omega) (by omega)
        (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans
      ((hTailFr _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hRe_lt _ (by omega)).trans
      ((hlt_scr_ag _ (by omega) (fun v' hv' => by omega)).trans
        (hAff_frame _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inr (by omega)) (Or.inl (by omega)))))))
  exact ⟨hF_uh, hZero, hgen_mid, hgen_fin, hMid_retSp, hF_mid_domGt, hF_mid_sGe, hF_sBit, hG_eSt,
    hF_kept⟩

/-- Array-specialized frame equalities for `StepPosMidPost`, keeping `stepPosNE_midPost` free of
`omega` calls in a large context. -/
lemma stepPosNE_mid_frames_c
    {b L vCap eCap j heapStep headHeap r₁ heapAff prefWords sPrevLen scratchPtr retSp heapFin
      retFin uhTailHdr cSize dPtr dTot nextHeap dLen : ℕ}
    {mem0 mem2 memAff memMid memFin memCol memFinal : ℕ → ℕ}
    (hj : j ≤ L)
    (hAr :
      b + dsFixedSize L vCap eCap ≤ heapStep ∧
      heapStep + 5 + prefWords ≤ headHeap ∧
      headHeap ≤ r₁ ∧ r₁ ≤ heapAff ∧
      heapAff + 2 + sPrevLen ≤ scratchPtr ∧
      scratchPtr < retSp ∧
      retSp + eCap ≤ heapFin ∧
      heapFin ≤ retFin ∧
      retFin ≤ uhTailHdr ∧
      uhTailHdr + 1 + cSize ≤ dPtr ∧
      dPtr + dTot ≤ nextHeap)
    (hAff_frame : ∀ addr, addr < heapAff → addr ≠ b + dsGenOff →
      (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
      (addr < dsSBitBase b L vCap eCap ∨ dsSBitBase b L vCap eCap + vCap ≤ addr) →
      (addr < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ addr) →
      (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
      memAff addr = mem2 addr)
    (hFinalEq : memFinal = Function.update
      (Function.update (Function.update memCol heapStep uhTailHdr) (heapStep + 1) dPtr)
      (heapStep + 2) dLen)
    (hF_col : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → memFinal a = memCol a)
    (hF_fin : ∀ a, a ≠ heapStep → a ≠ heapStep + 1 → a ≠ heapStep + 2 → a ≠ b + dsGenOff →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      (a < dPtr ∨ dPtr + dTot ≤ a) → memFinal a = memFin a)
    (hF_mid_ltDom : ∀ a, a < dsDomGenBase b L vCap eCap → a ≠ b + dsGenOff → memFinal a = memMid a)
    (hF_aff_ltH : ∀ a, a < dsHPtr b vCap eCap → a ≠ b + dsGenOff → memFinal a = memAff a)
    (hF_aff_aux : ∀ a, dsAuxPtr b vCap eCap ≤ a → a < dsMinHBase b vCap eCap → memFinal a = memAff a)
    (hF_aff_heap : ∀ a, heapStep + 3 ≤ a → a < scratchPtr → memFinal a = memAff a)
    (hF_mem0_dom : ∀ a, dsDomGenBase b L vCap eCap ≤ a → a < dsSGenBase b L vCap eCap →
      (a < dsDomGenBase b L vCap eCap + (j + 1) ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a) →
      dsLevelWalksFrameCond L vCap eCap b j heapFin retFin a → memFinal a = mem0 a)
    (hF_mem2_S : ∀ a, dsSGenBase b L vCap eCap ≤ a → a < dsSBitBase b L vCap eCap →
      (a < dsSGenBase b L vCap eCap + j ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) →
      memFinal a = mem2 a) :
    (memFinal heapStep = uhTailHdr ∧ memFinal (heapStep + 1) = dPtr ∧ memFinal (heapStep + 2) = dLen) ∧
    (∀ i, memFinal (dPtr + i) = memCol (dPtr + i)) ∧
    (∀ a, dsGPtr b ≤ a → a < dsGPtr b + dynGraphSize vCap eCap → memFinal a = mem2 a) ∧
    (∀ a, dsHPtr b vCap eCap ≤ a → a < dsHPtr b vCap eCap + dynGraphSize vCap eCap → memFinal a = memMid a) ∧
    (∀ a, dsAuxPtr b vCap eCap ≤ a → a < dsAuxPtr b vCap eCap + dynGraphSize vCap eCap → memFinal a = memAff a) ∧
    (∀ a, dsMinHBase b vCap eCap ≤ a → a < dsDomGenBase b L vCap eCap → memFinal a = memMid a) ∧
    (∀ e < eCap, memFinal (dsMinHBase b vCap eCap + e) = memMid (dsMinHBase b vCap eCap + e)) ∧
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
    (memFinal (dsDomGenBase b L vCap eCap + j) = memFin (dsDomGenBase b L vCap eCap + j) ∧
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
      (∀ a, retSp ≤ a → a < uhTailHdr → memFinal a = memFin a) ∧
      (∀ a, heapFin ≤ a → a < retFin → heapStep + 5 ≤ a ∧ a < nextHeap)) ∧
    (∀ i : Fin (L + 1), j < i.1 →
      (∀ e < eCap, memFinal (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
        mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e)) ∧
      (∀ v < vCap, memFinal (dsRevGenBase b L vCap eCap + i.1 * vCap + v) =
        mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v))) ∧
    (∀ i : Fin (L + 1), i.1 < j →
      memFinal (dsSGenBase b L vCap eCap + i.1) = mem2 (dsSGenBase b L vCap eCap + i.1) ∧
      memFinal (dsSHeadBase b L vCap eCap + i.1) = mem2 (dsSHeadBase b L vCap eCap + i.1) ∧
      (∀ v < vCap, memFinal (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v))) ∧
    (∀ i : Fin (L + 1),
      memFinal (dsSHeadBase b L vCap eCap + i.1) = mem2 (dsSHeadBase b L vCap eCap + i.1) ∧
      ∀ v < vCap, memFinal (dsVSGenBase b L vCap eCap + i.1 * vCap + v) =
        mem2 (dsVSGenBase b L vCap eCap + i.1 * vCap + v)) ∧
    (∀ v < vCap, memFinal (dsVStampBase b L vCap eCap + v) = memFin (dsVStampBase b L vCap eCap + v)) ∧
    (∀ e < eCap, memFinal (dsEStampBase b L vCap eCap + e) = memCol (dsEStampBase b L vCap eCap + e)) ∧
    (∀ a, headHeap ≤ a → a < r₁ → memFinal a = mem2 a) ∧
    (∀ a, heapStep + 5 ≤ a → a < heapStep + 5 + prefWords → memFinal a = mem2 a) ∧
    (∀ i < sPrevLen, memFinal (heapAff + 2 + i) = memAff (heapAff + 2 + i)) := by
  have hfl := fixed_layout_order b L vCap eCap
  have hgo := genOff_lt_hPtr b L vCap eCap
  have hL1 : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hL2 : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hL3 : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hfixH : b + dsFixedSize L vCap eCap ≤ heapFin := by omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFinalEq, Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [hFinalEq, Function.update_of_ne (by omega), Function.update_self]
  · rw [hFinalEq, Function.update_self]
  · intro i; exact hF_col _ (by omega) (by omega) (by omega)
  · intro a ha1 ha2
    exact (hF_aff_ltH a (by omega) (by omega)).trans
      (hAff_frame a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)))
  · intro a ha1 ha2; exact hF_mid_ltDom a (by omega) (by omega)
  · intro a ha1 ha2; exact hF_aff_aux a ha1 (by omega)
  · intro a ha1 ha2; exact hF_mid_ltDom a ha2 (by omega)
  · intro e he; exact hF_mid_ltDom _ (by omega) (by omega)
  · intro i hi
    have hneq : i.1 ≠ j := Nat.ne_of_lt hi
    have hiL : i.1 ≤ L := Nat.le_of_lt_succ i.2
    refine ⟨hF_mem0_dom _ (Nat.le_add_right _ _) (by omega) (Or.inl (by omega))
      (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inl rfl)),
      fun e he => ⟨?_, ?_⟩, fun v hv => ⟨?_, ?_⟩⟩
    · have := idx_lt_mul_c i.2 he
      exact hF_mem0_dom _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inr (Or.inl ⟨e, he, rfl⟩)))
    · have := idx_lt_mul_c i.2 he
      exact hF_mem0_dom _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inr (Or.inr (Or.inl ⟨e, he, rfl⟩))))
    · have := idx_lt_mul_c i.2 hv
      exact hF_mem0_dom _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩)))))
    · have := idx_lt_mul_c i.2 hv
      exact hF_mem0_dom _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hv, rfl⟩)))))
  · refine ⟨hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      fun e he => ?_, fun v hv => ?_,
      fun a ha1 ha2 => hF_fin a (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)),
      fun a ha1 ha2 => ⟨by omega, by omega⟩⟩
    · have := idx_lt_mul_c (by omega : j < L + 1) he
      exact ⟨hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
        hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))⟩
    · have := idx_lt_mul_c (by omega : j < L + 1) hv
      exact ⟨hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
        hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))⟩
  · intro i hi
    have hneq : i.1 ≠ j := Nat.ne_of_gt hi
    have hiL : i.1 ≤ L := Nat.le_of_lt_succ i.2
    refine ⟨fun e he => ?_, fun v hv => ?_⟩
    · have := idx_lt_mul_c i.2 he
      exact hF_mem0_dom _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inr (Or.inl ⟨e, he, rfl⟩)))
    · have := idx_lt_mul_c i.2 hv
      exact hF_mem0_dom _ (by omega) (by omega) (Or.inr (by omega))
        (slw_frame_of_other_lvl hj hiL hneq hfixH (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, hv, rfl⟩)))))
  · intro i hi
    refine ⟨hF_mem2_S _ (Nat.le_add_right _ _) (by omega) (Or.inl (by omega)),
      hF_mem2_S _ (by omega) (by omega) (Or.inr (by omega)), fun v hv => ?_⟩
    have := idx_lt_mul_c i.2 hv
    exact hF_mem2_S _ (by omega) (by omega) (Or.inr (by omega))
  · intro i
    refine ⟨hF_mem2_S _ (by omega) (by omega) (Or.inr (by omega)), fun v hv => ?_⟩
    have := idx_lt_mul_c i.2 hv
    exact hF_mem2_S _ (by omega) (by omega) (Or.inr (by omega))
  · intro v hv
    exact hF_fin _ (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · intro e he
    exact hF_col _ (by omega) (by omega) (by omega)
  · intro a ha1 ha2
    exact (hF_aff_heap a (by omega) (by omega)).trans
      (hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)))
  · intro a ha1 ha2
    exact (hF_aff_heap a (by omega) (by omega)).trans
      (hAff_frame a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)))
  · intro i hi
    exact hF_aff_heap _ (by omega) (by omega)

end MinCostFlow.DynSpanner.Program
