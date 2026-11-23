module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepZeroJoin
import Mathlib.Tactic.Ring

/-!
# Memory postcondition assembly for Phase 1 (`DynSpannerStepZeroClearPost`)

Assembles the memory half of `StepZeroClearPost` from the raw postconditions and frame equations
of the 7 procedure calls in `dsStepZeroClearBody`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

private lemma idx_lt_mul_cp {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m :=
  calc i * m + e < i * m + m := Nat.add_lt_add_left he _
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ hi

public section

/-- Assemble the memory part of `StepZeroClearPost` from the raw postconditions and frames of
calls 1–7. -/
theorem stepZero_clear_post_mem {G₀ : MGraph} {impl : SparsifyImpl}
    {mMax w L q vCap eCap b k : ℕ} {us : List Update} {u : Update}
    {len heapStep prefWords : ℕ} {oldHEdges : List ℕ}
    {mem0 mem1 mem2 mem4 mem5 mem6 mem7 mem8 : ℕ → ℕ} {x : DynSpannerMeta L}
    (hw16 : 16 ≤ 2 ^ w) (hVG₀ : G₀.IsValid) (hGm₀ : G₀.m ≤ mMax) (hBV : G₀.BatchIsValid us)
    (hds : ∀ u' ∈ us, isDelOrSplit u') (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) us s)
    (hState : DynSpannerStateAt L vCap eCap b mem0 x
      (runState (L := L) G₀ q (canonicalSparsify impl) us k))
    (hupd_cap : UpdateWithinCaps vCap eCap u) (hfix : b + dsFixedSize L vCap eCap ≤ heapStep)
    (hz0 : ZeroFrom mem0 heapStep)
    (hsp_lt :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      let G' := st.G.applyUpdate u
      let H_mid := st.H.applyBatch (restrictUpdate u st.H)
      heapStep + 5 + len + H_mid.m + dsInitCoreSpaceBound impl mMax vCap eCap G' < 2 ^ w)
    (hgen_w :
      let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
      mem0 (b + dsGenOff) + 2 + (st.G.applyUpdate u).m < 2 ^ w)
    (hw'_le :
      let G' := (runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u
      G'.E.Nonempty →
        wordSize impl.cw (canonSparsifyInput (activeSubgraph G') (activeSubgraph G') idEmb) ≤ w)
    (hpref_le : prefWords ≤ len)
    (hPrefBat1 : BatchBodyAt mem1 (heapStep + 5)
      (runState (L := L) G₀ q (canonicalSparsify impl) us k).H
      (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H) prefWords)
    (hG1 : DynGraphAt mem1 (dsGPtr b) vCap eCap
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).G.applyUpdate u))
    (hH5 : DynGraphAt mem5 (dsHPtr b vCap eCap) vCap eCap emptyMGraph)
    (hold_nd : oldHEdges.Nodup)
    (hold_mem : ∀ e, e ∈ oldHEdges ↔
      e ∈ ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).E)
    (hold_len : oldHEdges.length =
      ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).m)
    (hold_ec : ∀ e ∈ oldHEdges, e < eCap)
    (hold_at2 : ListAt mem2 (heapStep + 5 + len) oldHEdges)
    (hmin6 : ∀ e < eCap, mem6 (dsMinHBase b vCap eCap + e) = 0)
    (hbuck6 : ∀ i : Fin (L + 1),
      IsDoublyLinkedList mem6 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
      mem6 (dsHDegDummyBase b L vCap eCap + i.1) = 0)
    (hzD7 : ∀ i, 1 ≤ i → i < L + 1 → mem7 (dsDomGenBase b L vCap eCap + i) = 0)
    (hzS7 : ∀ i, 0 ≤ i → i < L + 1 → mem7 (dsSGenBase b L vCap eCap + i) = 0)
    (hgen4 : mem4 (b + dsGenOff) = mem0 (b + dsGenOff) + 1)
    (hst4 : ∀ e ∈ oldHEdges, mem4 (dsEStampBase b L vCap eCap + e) = mem0 (b + dsGenOff) + 1)
    (hfr1 : ∀ a, a < heapStep + 5 ∨ heapStep + 5 + len ≤ a →
      (a < dsGPtr b ∨ (dsAuxPtr b vCap eCap ≤ a ∧ a < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b L vCap eCap ≤ a) → mem1 a = mem0 a)
    (hfr2 : ∀ a, a < heapStep + 5 + len ∨
      heapStep + 5 + len + ((runState (L := L) G₀ q (canonicalSparsify impl) us k).H.applyBatch
        (restrictUpdate u (runState (L := L) G₀ q (canonicalSparsify impl) us k).H)).m ≤ a →
      mem2 a = mem1 a)
    (hfr4 : ∀ a, a ≠ b + dsGenOff → (∀ e ∈ oldHEdges, a ≠ dsEStampBase b L vCap eCap + e) →
      mem4 a = mem2 a)
    (hfr5 : ∀ a, a < dsHPtr b vCap eCap ∨ dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ a →
      mem5 a = mem4 a)
    (hfr6 : ∀ a, a < dsMinHBase b vCap eCap ∨ dsDomGenBase b L vCap eCap ≤ a → mem6 a = mem5 a)
    (hfr7 : ∀ a, (a < dsDomGenBase b L vCap eCap + 1 ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a) →
      (a < dsSGenBase b L vCap eCap ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) → mem7 a = mem6 a)
    (hfr8 : ∀ a, a ≠ b + dsTOff → mem8 a = mem7 a)
    (hT8 : mem8 (b + dsTOff) = k + 1) :
    let st := runState (L := L) G₀ q (canonicalSparsify impl) us k
    let G' := st.G.applyUpdate u
    let H_mid := st.H.applyBatch (restrictUpdate u st.H)
    let gOld := mem0 (b + dsGenOff) + 1
    let heapInit := heapStep + 5 + len + H_mid.m
    (dsInitCoreContract impl mMax w L vCap eCap b G').pre [b, heapInit] mem8 ∧
    BatchBodyAt mem8 (heapStep + 5) st.H (restrictUpdate u st.H) prefWords ∧
    oldHEdges.Nodup ∧ (∀ e, e ∈ oldHEdges ↔ e ∈ H_mid.E) ∧ oldHEdges.length = H_mid.m ∧
    ListAt mem8 (heapStep + 5 + len) oldHEdges ∧
    mem8 (b + dsQOff) = q ∧ mem8 (b + dsTOff) = k + 1 ∧ mem8 (b + dsGenOff) = gOld ∧
    (∀ i : Fin (L + 1), 0 < i.1 →
      IsDoublyLinkedList mem8 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
      mem8 (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
      mem8 (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ e < eCap, mem8 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ gOld) ∧
      (∀ v < vCap, mem8 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ gOld)) ∧
    (∀ i : Fin (L + 1), mem8 (dsSGenBase b L vCap eCap + i.1) = 0 ∧
      ∀ v < vCap, mem8 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ gOld) ∧
    (∀ v < vCap, mem8 (dsSBitBase b L vCap eCap + v) = 0) ∧
    (∀ e < eCap, mem8 (dsEStampBase b L vCap eCap + e) ≤ gOld ∧
      (mem8 (dsEStampBase b L vCap eCap + e) = gOld ↔ e ∈ H_mid.E) ∧
      mem8 (dsKeptStampBase b L vCap eCap + e) ≤ gOld) ∧
    (∀ a < heapStep, ¬ metaFoot b x a → mem8 a = mem0 a) := by
  intro st G' H_mid gOld heapInit
  have hk_inv := hPref k le_rfl
  obtain ⟨_, _, hU_k⟩ := batchIsValid_take us G₀ k hBV hds
  obtain ⟨hu_val, hdu⟩ := hU_k u hu_some
  rcases hState with ⟨hxV, hxE, _, hb1, hGval, _, _, _, _, hGV_cap, hGE_cap,
    hmQ0, _, hmL0, hmV0, hmE0, _, _, _, hAux0, _, _, hDom0, hS0, hSBit0, hES0⟩
  obtain ⟨hgo, hgh, hha, ham, hmn, hnh, hhd, hdd, hde, her, hrs, hsv, hvs, hsb, hve, hek, hkf,
    _, _, _⟩ := stepZero_clear_bounds b L vCap eCap
  have hto_lt : b + dsTOff < dsGPtr b := by simp [dsTOff, dsGPtr, dsHdrSize]
  have hG'val : G'.IsValid := isValid_applyUpdate_of_delOrSplit hGval (hk_inv.G_eq ▸ hu_val) hdu
  have hG'E_sub : G'.E ⊆ st.G.E := E_applyUpdate_subset hdu
  have hGE'_cap : ∀ e ∈ G'.E, e < eCap := fun e he => hGE_cap e (hG'E_sub he)
  have hGV'_cap : ∀ v ∈ G'.V, v < vCap := by
    intro v hv; cases u with
    | insert _ _ _ => exact hdu.elim
    | delete _ => exact hGV_cap v hv
    | split _ v' _ _ =>
      simp only [G', MGraph.applyUpdate, Finset.mem_insert] at hv
      rcases hv with rfl | hv; exact hupd_cap; exact hGV_cap v hv
  have hG'm_le : G'.m ≤ mMax := by
    have h1 : G'.E ⊆ G₀.E := Finset.Subset.trans hG'E_sub (by
      rw [hk_inv.G_eq]
      obtain ⟨hBV_k, hds_k, _⟩ := batchIsValid_take us G₀ k hBV hds
      exact (batch_delOrSplit_invariants (us.take k) G₀ hVG₀ hBV_k hds_k).2.1)
    exact le_trans (Finset.card_le_card h1) hGm₀
  have hfr_b_ltG : ∀ a < dsGPtr b, a ≠ b + dsGenOff → mem7 a = mem0 a := fun a ha hne =>
    (hfr7 a (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((hfr6 a (Or.inl (by omega))).trans ((hfr5 a (Or.inl (by omega))).trans
        ((hfr4 a hne fun e he => by have := hold_ec e he; omega).trans
          ((hfr2 a (Or.inl (by omega))).trans (hfr1 a (Or.inl (by omega)) (Or.inl ha))))))
  have hag8_ge : ∀ a, heapStep + 5 ≤ a → a < heapStep + 5 + len → mem8 a = mem1 a := fun a h1 h2 =>
    (hfr8 a (by omega)).trans ((hfr7 a (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hfr6 a (Or.inr (by omega))).trans ((hfr5 a (Or.inr (by omega))).trans
        ((hfr4 a (by omega) fun e he => by have := hold_ec e he; omega).trans (hfr2 a (Or.inl (by omega)))))))
  have hag8_old : ∀ a, heapStep + 5 + len ≤ a → a < heapInit → mem8 a = mem2 a := fun a h1 h2 =>
    (hfr8 a (by omega)).trans ((hfr7 a (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hfr6 a (Or.inr (by omega))).trans ((hfr5 a (Or.inr (by omega))).trans
        (hfr4 a (by omega) fun e he => by have := hold_ec e he; omega))))
  have hag8_z : ZeroFrom mem8 heapInit := fun a ha => by
    rw [hfr8 a (by omega), hfr7 a (Or.inr (by omega)) (Or.inr (by omega)),
      hfr6 a (Or.inr (by omega)), hfr5 a (Or.inr (by omega)),
      hfr4 a (by omega) (fun e he => by have := hold_ec e he; omega),
      hfr2 a (Or.inr (by dsimp only [heapInit] at ha; omega)),
      hfr1 a (Or.inr (by dsimp only [heapInit] at ha; omega)) (Or.inr (Or.inr (by dsimp only [heapInit] at ha; omega)))]
    exact hz0 a (by dsimp only [heapInit] at ha; omega)
  have hgen8 : mem8 (b + dsGenOff) = mem0 (b + dsGenOff) + 1 := by
    rw [hfr8 _ (by simp [dsGenOff, dsTOff]), hfr7 _ (Or.inl (by omega)) (Or.inl (by omega)),
      hfr6 _ (Or.inl (by omega)), hfr5 _ (Or.inl (by omega))]
    exact hgen4
  have hag8_geDom : ∀ a, dsDomGenBase b L vCap eCap ≤ a → a < heapStep →
      (a < dsDomGenBase b L vCap eCap + 1 ∨ dsDomGenBase b L vCap eCap + (L + 1) ≤ a) →
      (a < dsSGenBase b L vCap eCap ∨ dsSGenBase b L vCap eCap + (L + 1) ≤ a) →
      (a < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ a) →
      mem8 a = mem0 a := fun a h1 h2 hd hs he =>
    (hfr8 a (by omega)).trans ((hfr7 a hd hs).trans ((hfr6 a (Or.inr h1)).trans
      ((hfr5 a (Or.inr (by omega))).trans
        ((hfr4 a (by omega) fun e he' => by have := hold_ec e he'; omega).trans
          ((hfr2 a (Or.inl (by omega))).trans (hfr1 a (Or.inl (by omega)) (Or.inr (Or.inr h1))))))))
  have hG8 : DynGraphAt mem8 (dsGPtr b) vCap eCap G' :=
    dynGraphAt_of_agree hG1 fun a h1 h2 =>
      (hfr8 a (by omega)).trans ((hfr7 a (Or.inl (by omega)) (Or.inl (by omega))).trans
        ((hfr6 a (Or.inl (by omega))).trans ((hfr5 a (Or.inl (by omega))).trans
          ((hfr4 a (by omega) fun e he => by have := hold_ec e he; omega).trans
            (hfr2 a (Or.inl (by omega)))))))
  have hH8 : DynGraphAt mem8 (dsHPtr b vCap eCap) vCap eCap emptyMGraph :=
    dynGraphAt_of_agree hH5 fun a h1 h2 =>
      (hfr8 a (by omega)).trans ((hfr7 a (Or.inl (by omega)) (Or.inl (by omega))).trans
        (hfr6 a (Or.inl (by omega))))
  have hAux8 : DynGraphAt mem8 (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph :=
    dynGraphAt_of_agree hAux0 fun a h1 h2 =>
      (hfr8 a (by omega)).trans ((hfr7 a (Or.inl (by omega)) (Or.inl (by omega))).trans
        ((hfr6 a (Or.inl (by omega))).trans ((hfr5 a (Or.inr (by omega))).trans
          ((hfr4 a (by omega) fun e he => by have := hold_ec e he; omega).trans
            ((hfr2 a (Or.inl (by omega))).trans (hfr1 a (Or.inl (by omega)) (Or.inr (Or.inl ⟨h1, h2⟩))))))))
  have hag8_buck : ∀ a, dsMinHBase b vCap eCap ≤ a → a < dsDomGenBase b L vCap eCap →
      mem8 a = mem6 a := fun a h1 h2 =>
    (hfr8 a (by omega)).trans (hfr7 a (Or.inl (by omega)) (Or.inl (by omega)))
  have hes8 : ∀ e < eCap, mem8 (dsEStampBase b L vCap eCap + e) = mem4 (dsEStampBase b L vCap eCap + e) :=
    fun e he => (hfr8 _ (by omega)).trans ((hfr7 _ (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((hfr6 _ (Or.inr (by omega))).trans (hfr5 _ (Or.inr (by omega)))))
  have hfr4_es : ∀ e < eCap, e ∉ oldHEdges →
      mem4 (dsEStampBase b L vCap eCap + e) = mem0 (dsEStampBase b L vCap eCap + e) :=
    fun e he hne =>
      (hfr4 _ (by omega) fun e' he' hEq => hne (by have h := Nat.add_left_cancel hEq; rwa [h])).trans
        ((hfr2 _ (Or.inl (by omega))).trans (hfr1 _ (Or.inl (by omega)) (Or.inr (Or.inr (by omega)))))
  have hfr_out : ∀ a < heapStep, ¬ metaFoot b x a → mem8 a = mem0 a := by
    intro a ha hnf
    simp only [metaFoot, hxV, hxE, not_or, not_and, not_lt] at hnf
    by_cases hlt : a < b
    · exact (hfr8 a (by omega)).trans (hfr_b_ltG a (by omega) (by omega))
    · have hge : b + dsFixedSize L vCap eCap ≤ a := hnf.1 (Nat.le_of_not_lt hlt)
      exact (hfr8 a (by omega)).trans ((hfr7 a (Or.inr (by omega)) (Or.inr (by omega))).trans
        ((hfr6 a (Or.inr (by omega))).trans ((hfr5 a (Or.inr (by omega))).trans
          ((hfr4 a (by omega) fun e he => by have := hold_ec e he; omega).trans
            ((hfr2 a (Or.inl (by omega))).trans (hfr1 a (Or.inl (by omega)) (Or.inr (Or.inr (by omega)))))))))
  refine ⟨?_, hPrefBat1.of_agree fun i hi => hag8_ge _ (by omega) (by omega),
    hold_nd, hold_mem, hold_len,
    hold_at2.congr fun a h1 h2 => hag8_old a h1 (by dsimp only [heapInit]; rw [← hold_len]; exact h2),
    (hfr8 _ (by simp [dsQOff, dsTOff])).trans ((hfr_b_ltG _ (by simp [dsQOff, dsGPtr, dsHdrSize])
      (by simp [dsQOff, dsGenOff])).trans (hmQ0.trans hk_inv.q_eq)),
    hT8, hgen8, ?_, ?_, ?_, ?_, hfr_out⟩
  · refine ⟨heapInit, rfl, hw16, hb1, by dsimp only [heapInit]; omega, hsp_lt, hag8_z, hw'_le,
      (hfr8 _ (by simp [dsLOff, dsTOff])).trans ((hfr_b_ltG _ (by simp [dsLOff, dsGPtr, dsHdrSize])
        (by simp [dsLOff, dsGenOff])).trans hmL0),
      (hfr8 _ (by simp [dsVCapOff, dsTOff])).trans ((hfr_b_ltG _ (by simp [dsVCapOff, dsGPtr, dsHdrSize])
        (by simp [dsVCapOff, dsGenOff])).trans hmV0),
      (hfr8 _ (by simp [dsECapOff, dsTOff])).trans ((hfr_b_ltG _ (by simp [dsECapOff, dsGPtr, dsHdrSize])
        (by simp [dsECapOff, dsGenOff])).trans hmE0),
      by rw [hgen8]; have hg' : mem0 (b + dsGenOff) + 2 + G'.m < 2 ^ w := hgen_w; omega,
      fun e he => (hag8_buck _ (by omega) (by omega)).trans (hmin6 e he),
      IsDoublyLinkedList.nil ((hag8_buck _ (by omega) (by omega)).trans
        (hbuck6 ⟨0, Nat.zero_lt_succ L⟩).1.2.2.1),
      (hag8_buck _ (by omega) (by omega)).trans (hbuck6 ⟨0, Nat.zero_lt_succ L⟩).2,
      ?_, ?_, ?_, ?_, hG8, hH8, hAux8, hG'val, hG'm_le, hGV'_cap, hGE'_cap⟩
    · rw [hag8_geDom _ le_rfl (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), hgen8]
      have := (hDom0 ⟨0, Nat.zero_lt_succ L⟩).1
      simp only [Nat.add_zero] at this; omega
    · intro e he
      have hmul : e < (L + 1) * eCap := by simpa using idx_lt_mul_cp (Nat.zero_lt_succ L) he
      rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), hgen8]
      have := ((hDom0 ⟨0, Nat.zero_lt_succ L⟩).2.1 e he).1
      simp only [Nat.zero_mul, Nat.add_zero] at this; omega
    · intro v hv
      have hmul : v < (L + 1) * vCap := by simpa using idx_lt_mul_cp (Nat.zero_lt_succ L) hv
      rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), hgen8]
      have := ((hDom0 ⟨0, Nat.zero_lt_succ L⟩).2.2.2.2.2 v hv).1
      simp only [Nat.zero_mul, Nat.add_zero] at this; omega
    · intro v hv
      rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)), hgen8]
      have := (hSBit0 v hv).2; omega
  · intro i hi
    have hbi := hbuck6 i
    refine ⟨IsDoublyLinkedList.nil ((hag8_buck _ (by omega) (by have := i.2; omega)).trans hbi.1.2.2.1),
      (hag8_buck _ (by omega) (by have := i.2; omega)).trans hbi.2,
      (hfr8 _ (by omega)).trans (hzD7 i.1 hi i.2), fun e he => ?_, fun v hv => ?_⟩
    · have hmul := idx_lt_mul_cp i.2 he
      rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      have := ((hDom0 i).2.1 e he).1; dsimp only [gOld]; omega
    · have hmul := idx_lt_mul_cp i.2 hv
      rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      have := ((hDom0 i).2.2.2.2.2 v hv).1; dsimp only [gOld]; omega
  · intro i
    refine ⟨(hfr8 _ (by omega)).trans (hzS7 i.1 (Nat.zero_le _) i.2), fun v hv => ?_⟩
    have hmul := idx_lt_mul_cp i.2 hv
    rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    have := ((hS0 i).2.2.1 v hv).1; dsimp only [gOld]; omega
  · intro v hv
    rw [hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    exact (hSBit0 v hv).1
  · intro e he
    have hkept8 : mem8 (dsKeptStampBase b L vCap eCap + e) = mem0 (dsKeptStampBase b L vCap eCap + e) :=
      hag8_geDom _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
    refine ⟨?_, ?_, by rw [hkept8]; have := (hES0 e he).2; dsimp only [gOld]; omega⟩
    · rw [hes8 e he]
      by_cases heH : e ∈ H_mid.E
      · rw [hst4 e ((hold_mem e).mpr heH)]
      · rw [hfr4_es e he (fun hm => heH ((hold_mem e).mp hm))]
        have := (hES0 e he).1; dsimp only [gOld]; omega
    · rw [hes8 e he]
      by_cases heH : e ∈ H_mid.E
      · simp [heH, hst4 e ((hold_mem e).mpr heH), gOld]
      · rw [hfr4_es e he (fun hm => heH ((hold_mem e).mp hm))]
        have := (hES0 e he).1; simp only [heH, iff_false]; dsimp only [gOld]; omega

/-- Compact ordering of the fixed-block boundaries touched by `dsInitCoreFrameCond`. -/
theorem stepZero_initCore_bounds (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsPiPtrBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + eCap ≤ dsRevGenBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap = dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + vCap ≤ dsRevHeadBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + vCap ≤ dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap + (L + 1) = dsVSGenBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap + (L + 1) * vCap ≤ dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap = dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  obtain ⟨hgo, hgh, hha, ham, hmn, hnp, hph, hhd, hdd, hde, hep, hpr, hrr, hrs, hsv, hvs, hsh, hsb,
    hve, hek, hkm, hmf⟩ := stepZero_fixed_order b L vCap eCap
  have he_mul : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left eCap (Nat.succ_pos L)
  have hv_mul : vCap ≤ (L + 1) * vCap := Nat.le_mul_of_pos_left vCap (Nat.succ_pos L)
  exact ⟨hgo, hgh, hha, ham, hmn, hnp, hph, hhd, hdd, hde,
    hep ▸ Nat.add_le_add_left he_mul _, hep,
    hpr ▸ Nat.add_le_add_left he_mul _, hpr,
    hrr ▸ Nat.add_le_add_left hv_mul _, hrr,
    hrs ▸ Nat.add_le_add_left hv_mul _, hsv,
    hvs.symm ▸ (hsh ▸ Nat.le_add_right _ _), hsb, hve, hek, hkm, hmf⟩

/-- Frame transfer helper: addresses in a sub-interval strictly above `dsHHeadBase` (and outside
level 0's arrays and `vStamp`) satisfy `dsInitCoreFrameCond`. -/
lemma initCore_frame_of_fixed_range {L vCap eCap b heapInit retInit addr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapInit)
    (h1 : (dsHHeadBase b vCap eCap < addr ∧ addr < dsHDegDummyBase b L vCap eCap) ∨
      (dsHDegDummyBase b L vCap eCap < addr ∧ addr < dsDomGenBase b L vCap eCap) ∨
      (dsDomGenBase b L vCap eCap < addr ∧ addr < dsEdgeDomGenBase b L vCap eCap) ∨
      (dsEdgeDomGenBase b L vCap eCap + eCap ≤ addr ∧ addr < dsPiPtrBase b L vCap eCap) ∨
      (dsRevGenBase b L vCap eCap + vCap ≤ addr ∧ addr < dsRevHeadBase b L vCap eCap) ∨
      (dsSGenBase b L vCap eCap ≤ addr ∧ addr < dsVStampBase b L vCap eCap) ∨
      (dsEStampBase b L vCap eCap ≤ addr ∧ addr < dsMEmbTempBase b L vCap eCap)) :
    dsInitCoreFrameCond L vCap eCap b heapInit retInit addr := by
  obtain ⟨hgo, hgh, hha, ham, hmn, hnp, hph, hhd, hdd, hde, he1, hep, hp1, hpr, hr1, hrr, hr2,
    hsv, hvs, hsb, hve, hek, hkm, hmf⟩ := stepZero_initCore_bounds b L vCap eCap
  have hA : b + dsGenOff < dsHHeadBase b vCap eCap := by omega
  have hC : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsHHeadBase b vCap eCap := by omega
  have hD : dsMinHBase b vCap eCap + eCap ≤ dsHHeadBase b vCap eCap := by omega
  have hE : dsHNextBase b vCap eCap + eCap ≤ dsHHeadBase b vCap eCap := by omega
  have hF : dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap := hph
  have h_le1 : dsHDegDummyBase b L vCap eCap ≤ dsDomGenBase b L vCap eCap := hdd ▸ Nat.le_add_right _ _
  have h_le2 : dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap := hde ▸ Nat.le_add_right _ _
  have h_le3 : dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsPiPtrBase b L vCap eCap := he1
  have h_le4 : dsPiPtrBase b L vCap eCap + eCap ≤ dsRevGenBase b L vCap eCap := hp1
  have h_le5 : dsRevGenBase b L vCap eCap + vCap ≤ dsRevHeadBase b L vCap eCap := hr1
  have h_le6 : dsRevHeadBase b L vCap eCap + vCap ≤ dsSGenBase b L vCap eCap := hr2
  have h_le7 : dsSGenBase b L vCap eCap ≤ dsVStampBase b L vCap eCap :=
    ((hsv ▸ Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hvs)).trans (hsb ▸ Nat.le_add_right _ _)
  have h_le8 : dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap := hve
  have h_le9 : dsEStampBase b L vCap eCap ≤ dsMEmbTempBase b L vCap eCap :=
    (hek ▸ Nat.le_add_right _ _).trans (hkm ▸ Nat.le_add_right _ _)
  have h_le10 : dsMEmbTempBase b L vCap eCap ≤ heapInit := (hmf ▸ Nat.le_add_right _ _).trans hfix
  have h_gt_head : dsHHeadBase b vCap eCap < addr := by
    have h0 : dsHHeadBase b vCap eCap < dsHDegDummyBase b L vCap eCap := by rw [← hhd]; omega
    rcases h1 with ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ha
    · exact lt_trans h0 ha
    · exact lt_of_lt_of_le h0 (h_le1.trans (le_of_lt ha))
    · exact lt_of_lt_of_le h0 (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans ha)))
    · exact lt_of_lt_of_le h0 (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans
        (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans ha)))))))
    · exact lt_of_lt_of_le h0 (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans
        (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans
          (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans ha))))))))))
    · exact lt_of_lt_of_le h0 (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans
        (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans
          (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans
            (h_le7.trans ((h_le8 ▸ Nat.le_add_right _ _).trans ha))))))))))))
  have h_lt_mt : addr < dsMEmbTempBase b L vCap eCap := by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩
    · exact lt_of_lt_of_le hb (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans
        (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans
          (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans
            (h_le7.trans ((h_le8 ▸ Nat.le_add_right _ _).trans h_le9))))))))))))
    · exact lt_of_lt_of_le hb (h_le2.trans ((Nat.le_add_right _ _).trans
        (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans
          (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans
            (h_le7.trans ((h_le8 ▸ Nat.le_add_right _ _).trans h_le9)))))))))))
    · exact lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans
        (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans
          (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans
            (h_le7.trans ((h_le8 ▸ Nat.le_add_right _ _).trans h_le9))))))))))
    · exact lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans
        (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans
          (h_le6.trans (h_le7.trans ((h_le8 ▸ Nat.le_add_right _ _).trans h_le9))))))))
    · exact lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans
        (h_le6.trans (h_le7.trans ((h_le8 ▸ Nat.le_add_right _ _).trans h_le9))))
    · exact lt_of_lt_of_le hb ((h_le8 ▸ Nat.le_add_right _ _).trans h_le9)
    · exact hb
  have h_le_s_e : dsSGenBase b L vCap eCap ≤ dsEStampBase b L vCap eCap :=
    h_le7.trans (h_le8 ▸ Nat.le_add_right _ _)
  have h_not_ed : ∀ e < eCap, addr ≠ dsEdgeDomGenBase b L vCap eCap + e := fun e he => by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le1.trans (h_le2.trans (Nat.le_add_right _ _))))
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le2.trans (Nat.le_add_right _ _)))
    · exact ne_of_lt (lt_of_lt_of_le hb (Nat.le_add_right _ _))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) ha)
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans ha)))))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans ha))))))))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le_s_e.trans ha)))))))))
  have h_not_pi : ∀ e < eCap, addr ≠ dsPiPtrBase b L vCap eCap + e := fun e he => by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans (Nat.le_add_right _ _))))))
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans (Nat.le_add_right _ _)))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le3.trans (Nat.le_add_right _ _))))
    · exact ne_of_lt (lt_of_lt_of_le hb (Nat.le_add_right _ _))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) (h_le4.trans ((Nat.le_add_right _ _).trans ha)))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans ha))))))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left he _) (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le_s_e.trans ha)))))))
  have h_not_rg : ∀ v < vCap, addr ≠ dsRevGenBase b L vCap eCap + v := fun v hv => by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans (Nat.le_add_right _ _))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans (Nat.le_add_right _ _)))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans (Nat.le_add_right _ _))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le4.trans (Nat.le_add_right _ _))))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left hv _) ha)
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left hv _) (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans ha))))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left hv _) (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le_s_e.trans ha)))))
  have h_not_rh : ∀ v < vCap, addr ≠ dsRevHeadBase b L vCap eCap + v := fun v hv => by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans (Nat.le_add_right _ _))))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans (Nat.le_add_right _ _)))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans (Nat.le_add_right _ _))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans (Nat.le_add_right _ _))))))
    · exact ne_of_lt (lt_of_lt_of_le hb (Nat.le_add_right _ _))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left hv _) (h_le6.trans ha))
    · exact ne_of_gt (lt_of_lt_of_le (Nat.add_lt_add_left hv _) (h_le6.trans (h_le_s_e.trans ha)))
  have h_not_vs : ∀ v < vCap, addr ≠ dsVStampBase b L vCap eCap + v := fun v hv => by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨ha, _⟩
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le1.trans (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le7.trans (Nat.le_add_right _ _)))))))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb (h_le2.trans ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le7.trans (Nat.le_add_right _ _))))))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le7.trans (Nat.le_add_right _ _)))))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le7.trans (Nat.le_add_right _ _)))))))))
    · exact ne_of_lt (lt_of_lt_of_le hb ((Nat.le_add_right _ _).trans (h_le6.trans (h_le7.trans (Nat.le_add_right _ _)))))
    · exact ne_of_lt (lt_of_lt_of_le hb (Nat.le_add_right _ _))
    · exact ne_of_gt (lt_of_lt_of_le (h_le8 ▸ Nat.add_lt_add_left hv _) ha)
  have h_deg_lt_ed : dsHDegDummyBase b L vCap eCap < dsEdgeDomGenBase b L vCap eCap := by
    rw [← hde, ← hdd]; omega
  have h_dom_lt_ed : dsDomGenBase b L vCap eCap < dsEdgeDomGenBase b L vCap eCap := by
    rw [← hde]; omega
  have h_ne_deg : addr ≠ dsHDegDummyBase b L vCap eCap := by
    rcases h1 with ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ne_of_lt hb
    · exact ne_of_gt ha
    · exact ne_of_gt (lt_of_le_of_lt h_le1 ha)
    · exact ne_of_gt (lt_of_lt_of_le h_deg_lt_ed ((Nat.le_add_right _ _).trans ha))
    · exact ne_of_gt (lt_of_lt_of_le h_deg_lt_ed ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans ha))))))
    · exact ne_of_gt (lt_of_lt_of_le h_deg_lt_ed ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans ha)))))))))
    · exact ne_of_gt (lt_of_lt_of_le h_deg_lt_ed ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le_s_e.trans ha))))))))))
  have h_ne_dom : addr ≠ dsDomGenBase b L vCap eCap := by
    rcases h1 with ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ne_of_lt (lt_of_lt_of_le hb h_le1)
    · exact ne_of_lt hb
    · exact ne_of_gt ha
    · exact ne_of_gt (lt_of_lt_of_le h_dom_lt_ed ((Nat.le_add_right _ _).trans ha))
    · exact ne_of_gt (lt_of_lt_of_le h_dom_lt_ed ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans ha))))))
    · exact ne_of_gt (lt_of_lt_of_le h_dom_lt_ed ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans ha)))))))))
    · exact ne_of_gt (lt_of_lt_of_le h_dom_lt_ed ((Nat.le_add_right _ _).trans (h_le3.trans ((Nat.le_add_right _ _).trans (h_le4.trans ((Nat.le_add_right _ _).trans (h_le5.trans ((Nat.le_add_right _ _).trans (h_le6.trans (h_le_s_e.trans ha))))))))))
  refine ⟨ne_of_gt (lt_trans hA h_gt_head), Or.inr (le_of_lt (lt_of_le_of_lt hC h_gt_head)),
    fun e he => ne_of_gt (lt_trans (lt_of_lt_of_le (Nat.add_lt_add_left he _) hD) h_gt_head),
    ne_of_gt h_gt_head, h_ne_deg,
    fun e he => ne_of_gt (lt_trans (hF ▸ Nat.add_lt_add_left he _) h_gt_head),
    fun e he => ne_of_gt (lt_trans (lt_of_lt_of_le (Nat.add_lt_add_left he _) hE) h_gt_head),
    h_ne_dom, h_not_ed, h_not_pi, h_not_rg, h_not_rh, h_not_vs,
    fun e _ => ne_of_lt (lt_of_lt_of_le h_lt_mt (Nat.le_add_right _ _)),
    Or.inl (lt_of_lt_of_le h_lt_mt h_le10)⟩

/-- Addresses in `[b + dsFixedSize, heapInit)` satisfy `dsInitCoreFrameCond`. -/
lemma initCore_frame_of_heap_lt {L vCap eCap b heapInit retInit addr : ℕ}
    (h1 : b + dsFixedSize L vCap eCap ≤ addr) (h2 : addr < heapInit) :
    dsInitCoreFrameCond L vCap eCap b heapInit retInit addr := by
  have hlt := stepZero_fixed_lt b L vCap eCap
  have h0lt : 0 < L + 1 := Nat.zero_lt_succ L
  have hmt_eq : dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap :=
    (stepZero_fixed_order b L vCap eCap).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨ne_of_gt (lt_of_lt_of_le (hlt.1 dsGenOff (by decide)).2 h1),
    Or.inr (le_trans hlt.2.2.2.1.2 h1),
    fun e he => ne_of_gt (lt_of_lt_of_le (hlt.2.2.2.2.1 e he).2 h1),
    ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.1 0 h0lt).2) h1),
    ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.2.1 0 h0lt).2) h1),
    fun e he => ne_of_gt (lt_of_lt_of_le (hlt.2.2.2.2.2.1 e he).2 h1),
    fun e he => ne_of_gt (lt_of_lt_of_le (hlt.2.2.2.2.2.2.1 e he).2 h1),
    ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.2.2.1 0 h0lt).2) h1),
    fun e he => ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.2.2.2.1 0 h0lt e he).2) h1),
    fun e he => ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.2.2.2.2.1 0 h0lt e he).2) h1),
    fun v hv => ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.2.2.2.2.2.1 0 h0lt v hv).2) h1),
    fun v hv => ne_of_gt (lt_of_lt_of_le (by simpa using (hlt.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 h0lt v hv).2) h1),
    fun v hv => ne_of_gt (lt_of_lt_of_le (hlt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v hv).2 h1),
    fun e he => ne_of_gt (lt_of_lt_of_le (hmt_eq ▸ Nat.add_lt_add_left he _) h1),
    Or.inl h2⟩

/-- Transfer fixed-array invariants, `G'`, header fields, `eStamp` membership, and caller-memory
frame across `dsInitCoreStmt` for `dsStepZero_meetsContract`. -/
theorem stepZero_core_transfer {L q vCap eCap b k heapStep heapInit retInit gOld : ℕ}
    {G' H_mid : MGraph} {x : DynSpannerMeta L} {mem0 mem1 memCore : ℕ → ℕ}
    (hxV : x.vCap = vCap) (hxE : x.eCap = eCap)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapStep) (hstep_le_init : heapStep ≤ heapInit)
    (hG1 : DynGraphAt mem1 (dsGPtr b) vCap eCap G')
    (hL1 : mem1 (b + dsLOff) = L) (hV1 : mem1 (b + dsVCapOff) = vCap)
    (hE1 : mem1 (b + dsECapOff) = eCap) (hQ1 : mem1 (b + dsQOff) = q)
    (hT1 : mem1 (b + dsTOff) = k + 1)
    (hgenC : memCore (b + dsGenOff) = gOld + 1 + G'.m)
    (hdomC : memCore (dsDomGenBase b L vCap eCap) = gOld + 1)
    (hvstC : ∀ v < vCap, memCore (dsVStampBase b L vCap eCap + v) ≤ memCore (b + dsGenOff))
    (hPos1 : ∀ i : Fin (L + 1), 0 < i.1 →
      IsDoublyLinkedList mem1 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
      mem1 (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
      mem1 (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ e < eCap, mem1 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ gOld) ∧
      (∀ v < vCap, mem1 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ gOld))
    (hS1 : ∀ i : Fin (L + 1), mem1 (dsSGenBase b L vCap eCap + i.1) = 0 ∧
      ∀ v < vCap, mem1 (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ gOld)
    (hSBit1 : ∀ v < vCap, mem1 (dsSBitBase b L vCap eCap + v) = 0)
    (hES1 : ∀ e < eCap, mem1 (dsEStampBase b L vCap eCap + e) ≤ gOld ∧
      (mem1 (dsEStampBase b L vCap eCap + e) = gOld ↔ e ∈ H_mid.E) ∧
      mem1 (dsKeptStampBase b L vCap eCap + e) ≤ gOld)
    (hFr1 : ∀ a < heapStep, ¬ metaFoot b x a → mem1 a = mem0 a)
    (hfrC : ∀ addr, dsInitCoreFrameCond L vCap eCap b heapInit retInit addr →
      memCore addr = mem1 addr) :
    DynGraphAt memCore (dsGPtr b) vCap eCap G' ∧
    (memCore (b + dsQOff) = q ∧ memCore (b + dsTOff) = k + 1 ∧
      memCore (b + dsLOff) = L ∧ memCore (b + dsVCapOff) = vCap ∧ memCore (b + dsECapOff) = eCap ∧
      memCore (b + dsGenOff) = gOld + 1 + G'.m ∧ memCore (dsDomGenBase b L vCap eCap) = gOld + 1) ∧
    (∀ i : Fin (L + 1), 0 < i.1 →
      IsDoublyLinkedList memCore (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
        (dsHHeadBase b vCap eCap + i.1) eCap [] ∧
      memCore (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
      memCore (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ e < eCap, memCore (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) ≤ memCore (b + dsGenOff)) ∧
      (∀ v < vCap, memCore (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ memCore (b + dsGenOff))) ∧
    (∀ i : Fin (L + 1), memCore (dsSGenBase b L vCap eCap + i.1) = 0 ∧
      ∀ v < vCap, memCore (dsVSGenBase b L vCap eCap + i.1 * vCap + v) ≤ memCore (b + dsGenOff)) ∧
    (∀ v < vCap, memCore (dsSBitBase b L vCap eCap + v) = 0 ∧
      memCore (dsVStampBase b L vCap eCap + v) ≤ memCore (b + dsGenOff)) ∧
    (∀ e < eCap, memCore (dsEStampBase b L vCap eCap + e) ≤ memCore (b + dsGenOff) ∧
      memCore (dsKeptStampBase b L vCap eCap + e) ≤ memCore (b + dsGenOff)) ∧
    (∀ e < eCap, memCore (dsEStampBase b L vCap eCap + e) = gOld ↔ e ∈ H_mid.E) ∧
    (∀ a < heapStep, ¬ metaFoot b x a → memCore a = mem0 a) := by
  obtain ⟨hgo, hgh, _, _, _, _, _, hhd, hdd, hde, _, hep, _, hpr, _, hrr, _, hsv, hvs, hsb, hve,
    hek, hkm, _⟩ := stepZero_initCore_bounds b L vCap eCap
  have hb_lt_H : b < dsHPtr b vCap eCap := by have := dsGPtr_ge b; omega
  have hfix_hi : b + dsFixedSize L vCap eCap ≤ heapInit := le_trans hfix hstep_le_init
  have hltH : ∀ a < dsHPtr b vCap eCap, a ≠ b + dsGenOff → memCore a = mem1 a := fun a ha hne =>
    hfrC a (dsInitCoreFrameCond_lt_H hfix_hi ha hne)
  refine ⟨hG1.of_agree fun a h1 h2 => hltH a (hgh ▸ h2) (by omega),
    ⟨(hltH _ (by simp [dsQOff, dsGPtr, dsHdrSize] at hgh ⊢; omega) (by simp [dsQOff, dsGenOff])).trans hQ1,
     (hltH _ (by simp [dsTOff, dsGPtr, dsHdrSize] at hgh ⊢; omega) (by simp [dsTOff, dsGenOff])).trans hT1,
     (hltH _ (by simp [dsLOff, dsGPtr, dsHdrSize] at hgh ⊢; omega) (by simp [dsLOff, dsGenOff])).trans hL1,
     (hltH _ (by simp [dsVCapOff, dsGPtr, dsHdrSize] at hgh ⊢; omega) (by simp [dsVCapOff, dsGenOff])).trans hV1,
     (hltH _ (by simp [dsECapOff, dsGPtr, dsHdrSize] at hgh ⊢; omega) (by simp [dsECapOff, dsGenOff])).trans hE1,
     hgenC, hdomC⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hdllI, hdegI, hdomI, hedI, hrgI⟩ := hPos1 i hi
    have hi_le : i.1 < L + 1 := i.2
    refine ⟨IsDoublyLinkedList.nil ((hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inl ⟨by omega, by omega⟩))).trans hdllI.2.2.1),
      (hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans hdegI,
      (hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans hdomI,
      fun e he => ?_, fun v hv => ?_⟩
    · have hie : eCap ≤ i.1 * eCap := Nat.le_mul_of_pos_left eCap hi
      have hmul := idx_lt_mul_cp hi_le he
      rw [hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))), hgenC]
      have := hedI e he; omega
    · have hiv : vCap ≤ i.1 * vCap := Nat.le_mul_of_pos_left vCap hi
      have hmul := idx_lt_mul_cp hi_le hv
      rw [hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))), hgenC]
      have := hrgI v hv; omega
  · intro i
    obtain ⟨hsgI, hvsI⟩ := hS1 i
    have hi_le : i.1 < L + 1 := i.2
    refine ⟨(hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))).trans hsgI,
      fun v hv => ?_⟩
    have hmul := idx_lt_mul_cp hi_le hv
    rw [hfrC _ (initCore_frame_of_fixed_range hfix_hi
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))), hgenC]
    have := hvsI v hv; omega
  · intro v hv
    exact ⟨(hfrC _ (initCore_frame_of_fixed_range hfix_hi
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))).trans (hSBit1 v hv),
      hvstC v hv⟩
  · intro e he
    refine ⟨?_, ?_⟩
    · rw [hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))), hgenC]
      have := (hES1 e he).1; omega
    · rw [hfrC _ (initCore_frame_of_fixed_range hfix_hi
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))))))), hgenC]
      have := (hES1 e he).2.2; omega
  · intro e he
    rw [hfrC _ (initCore_frame_of_fixed_range hfix_hi
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))]
    exact (hES1 e he).2.1
  · intro a ha hnf
    have hnf' := hnf
    simp only [metaFoot, hxV, hxE, not_or, not_and, not_lt] at hnf'
    by_cases hlt : a < b
    · exact (hltH a (lt_trans hlt hb_lt_H) (by omega)).trans (hFr1 a ha hnf)
    · have hge : b + dsFixedSize L vCap eCap ≤ a := hnf'.1 (Nat.le_of_not_lt hlt)
      exact (hfrC a (initCore_frame_of_heap_lt hge (lt_of_lt_of_le ha hstep_le_init))).trans
        (hFr1 a ha hnf)

end

end MinCostFlow.DynSpanner.Program
