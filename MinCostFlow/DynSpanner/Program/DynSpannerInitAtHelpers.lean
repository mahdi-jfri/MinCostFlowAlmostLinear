module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCore
public import MinCostFlow.DynSpanner.Program.DynGraphInit

import Mathlib.Tactic.Ring

/-!
# Setup and zero-array helpers for `dsInitAtStmt` (`DynSpannerInitAtHelpers`)
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

lemma dsInitAt_stores_cont {w b L q t vCap eCap : ℕ} {mem0 : ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (hzb : ZeroFrom mem0 b) (hb6 : b + dsHdrSize < 2 ^ w)
    (_hq_w : q < 2 ^ w) (_ht_w : t < 2 ^ w) (_hL_w : L < 2 ^ w) (_hv_w : vCap < 2 ^ w) (_he_w : eCap < 2 ^ w)
    (hm : st.mem = mem0) (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = L) (hr2 : st.regs 2 = q)
    (hr3 : st.regs 3 = t) (hr4 : st.regs 4 = vCap) (hr5 : st.regs 5 = eCap)
    (hrest : ∀ st₁ : State,
      st₁.regs 0 = b ∧ st₁.regs 1 = L ∧ st₁.regs 2 = q ∧ st₁.regs 3 = t ∧
      st₁.regs 4 = vCap ∧ st₁.regs 5 = eCap ∧ (∀ r ≥ 6, st₁.regs r = st.regs r) ∧
      st₁.mem (b + dsQOff) = q ∧ st₁.mem (b + dsTOff) = t ∧ st₁.mem (b + dsLOff) = L ∧
      st₁.mem (b + dsVCapOff) = vCap ∧ st₁.mem (b + dsECapOff) = eCap ∧
      st₁.mem (b + dsGenOff) = 0 ∧ ZeroFrom st₁.mem (dsGPtr b) ∧
      (∀ addr, addr < b → st₁.mem addr = mem0 addr) →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ (k + 40) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.store (.bin .add (.reg 0) (.const dsQOff)) (.reg 2) ;;
       .store (.bin .add (.reg 0) (.const dsTOff)) (.reg 3) ;;
       .store (.bin .add (.reg 0) (.const dsLOff)) (.reg 1) ;;
       .store (.bin .add (.reg 0) (.const dsVCapOff)) (.reg 4) ;;
       .store (.bin .add (.reg 0) (.const dsECapOff)) (.reg 5) ;;
       .store (.bin .add (.reg 0) (.const dsGenOff)) (.const 0) ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  subst hm
  have hd : dsQOff = 0 ∧ dsTOff = 1 ∧ dsLOff = 2 ∧ dsVCapOff = 3 ∧ dsECapOff = 4 ∧
      dsGenOff = 5 ∧ dsHdrSize = 6 ∧ dsGPtr b = b + 6 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hc0 : (0 : ℕ) < 2 ^ w := by omega
  have hqOff : dsQOff = 0 := rfl
  have htOff : dsTOff = 1 := rfl
  have hLOff : dsLOff = 2 := rfl
  have hvOff : dsVCapOff = 3 := rfl
  have heOff : dsECapOff = 4 := rfl
  have hgOff : dsGenOff = 5 := rfl
  let wrap {st₁ : State} {k₁ k₂ : ℕ}
      (h : ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k₂ + c ≤ T) (hk : k₁ ≤ k₂) :
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k₁ + c ≤ T :=
    let ⟨o, st', c, hr, hq, hc⟩ := h
    ⟨o, st', c, hr, hq, by omega⟩
  refine runs_seq_store_le (x := b + dsQOff) (v := q)
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by rw [hqOff]; omega))
      (by rw [hqOff]; omega))
    (Expr.eval_reg_of_eq hr2) ?_
  refine runs_seq_store_le (x := b + dsTOff) (v := t)
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by rw [htOff]; omega))
      (by rw [htOff]; omega))
    (Expr.eval_reg_of_eq hr3) ?_
  refine runs_seq_store_le (x := b + dsLOff) (v := L)
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by rw [hLOff]; omega))
      (by rw [hLOff]; omega))
    (Expr.eval_reg_of_eq hr1) ?_
  refine runs_seq_store_le (x := b + dsVCapOff) (v := vCap)
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by rw [hvOff]; omega))
      (by rw [hvOff]; omega))
    (Expr.eval_reg_of_eq hr4) ?_
  refine runs_seq_store_le (x := b + dsECapOff) (v := eCap)
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by rw [heOff]; omega))
      (by rw [heOff]; omega))
    (Expr.eval_reg_of_eq hr5) ?_
  refine runs_seq_store_le (x := b + dsGenOff) (v := 0)
    (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_const (by rw [hgOff]; omega))
      (by rw [hgOff]; omega))
    (Expr.eval_const hc0) ?_
  refine wrap (hrest _ ⟨hr0, hr1, hr2, hr3, hr4, hr5, fun _ _ => rfl,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) (by dsimp only [Expr.size]; omega)
  · simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff]
  · simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff]
  · simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff]
  · simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff]
  · simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff]
  · simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff]
  · intro addr ha
    have hgp : dsGPtr b = b + 6 := rfl
    rw [hgp] at ha
    simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff,
      show addr ≠ b + 5 by omega, show addr ≠ b + 4 by omega,
      show addr ≠ b + 3 by omega, show addr ≠ b + 2 by omega,
      show addr ≠ b + 1 by omega, show addr ≠ b by omega]
    exact hzb addr (by omega)
  · intro addr ha
    simp [hqOff, htOff, hLOff, hvOff, heOff, hgOff,
      show addr ≠ b + 5 by omega, show addr ≠ b + 4 by omega,
      show addr ≠ b + 3 by omega, show addr ≠ b + 2 by omega,
      show addr ≠ b + 1 by omega, show addr ≠ b by omega]

lemma dsInitAt_assigns_cont {w b vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (hw16 : 16 ≤ 2 ^ w) (haux_w : dsAuxPtr b vCap eCap < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr4 : st.regs 4 = vCap) (hr5 : st.regs 5 = eCap)
    (hrest : ∀ st₁ : State,
      st₁.mem = st.mem ∧ (∀ r ≤ 10, st₁.regs r = st.regs r) ∧
      st₁.regs 11 = dynGraphSize vCap eCap ∧ st₁.regs 12 = dsGPtr b ∧
      st₁.regs 13 = dsHPtr b vCap eCap ∧ st₁.regs 14 = dsAuxPtr b vCap eCap →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ (k + 40) + c ≤ T) :
    ∃ o st' c, Runs w p ω
      (.assign 11 (.bin .add (.const 4)
        (.bin .add (.bin .mul (.const 7) (.reg 4)) (.bin .mul (.const 9) (.reg 5)))) ;;
       .assign 12 (.bin .add (.reg 0) (.const dsHdrSize)) ;;
       .assign 13 (.bin .add (.reg 12) (.reg 11)) ;;
       .assign 14 (.bin .add (.reg 13) (.reg 11)) ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  have hd : dsGPtr b + dynGraphSize vCap eCap = dsHPtr b vCap eCap ∧
      dsHPtr b vCap eCap + dynGraphSize vCap eCap = dsAuxPtr b vCap eCap ∧
      dsGPtr b = b + dsHdrSize ∧ dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hHdr : dsHdrSize = 6 := rfl
  have hv_w : vCap < 2 ^ w := by simp only [dsAuxPtr, dsHPtr, dynGraphSize] at haux_w; omega
  have he_w : eCap < 2 ^ w := by simp only [dsAuxPtr, dsHPtr, dynGraphSize] at haux_w; omega
  have h7v : 7 * vCap < 2 ^ w := by simp only [dsAuxPtr, dsHPtr, dynGraphSize] at haux_w; omega
  have h9e : 9 * eCap < 2 ^ w := by simp only [dsAuxPtr, dsHPtr, dynGraphSize] at haux_w; omega
  have h79 : 7 * vCap + 9 * eCap < 2 ^ w := by
    simp only [dsAuxPtr, dsHPtr, dynGraphSize] at haux_w; omega
  have hdg : dynGraphSize vCap eCap < 2 ^ w := by
    simp only [dsAuxPtr, dsHPtr] at haux_w; omega
  have hgp : dsGPtr b < 2 ^ w := by simp only [dsAuxPtr, dsHPtr] at haux_w; omega
  have hhp : dsHPtr b vCap eCap < 2 ^ w := by simp only [dsAuxPtr] at haux_w; omega
  let wrap {st₁ : State} {k₁ k₂ : ℕ}
      (h : ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k₂ + c ≤ T) (hk : k₁ ≤ k₂) :
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ k₁ + c ≤ T :=
    let ⟨o, st', c, hr, hq, hc⟩ := h
    ⟨o, st', c, hr, hq, by omega⟩
  refine runs_seq_assign_le (v := dynGraphSize vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr4) h7v)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr5) h9e) h79)
        (by rw [← Nat.add_assoc, ← hd.2.2.2]; exact hdg))
      (by rw [hd.2.2.2, Nat.add_assoc])) ?_
  refine runs_seq_assign_le (v := dsGPtr b)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr0]))
        (Expr.eval_const (by rw [hHdr]; omega)) (by rw [← hd.2.2.1]; exact hgp))
      hd.2.2.1.symm) ?_
  refine runs_seq_assign_le (v := dsHPtr b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by rw [hd.1]; exact hhp))
      hd.1) ?_
  refine runs_seq_assign_le (v := dsAuxPtr b vCap eCap)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp))
        (by rw [hd.2.1]; exact haux_w))
      hd.2.1) ?_
  refine wrap (hrest _ ⟨rfl, fun r hr => by
      simp [Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 13),
        Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11)],
    by simp, by simp, by simp, by simp⟩) (by dsimp only [Expr.size]; omega)

private lemma dsFixed_mono (b L vCap eCap : ℕ) :
    b + dsGenOff < dsGPtr b ∧
    dsGPtr b ≤ dsHPtr b vCap eCap ∧
    dsHPtr b vCap eCap ≤ dsAuxPtr b vCap eCap ∧
    dsAuxPtr b vCap eCap ≤ dsMinHBase b vCap eCap ∧
    dsMinHBase b vCap eCap + eCap = dsHNextBase b vCap eCap ∧
    dsHNextBase b vCap eCap + eCap = dsHPrevBase b vCap eCap ∧
    dsHPrevBase b vCap eCap + eCap = dsHHeadBase b vCap eCap ∧
    dsHHeadBase b vCap eCap < dsHDegDummyBase b L vCap eCap ∧
    dsHDegDummyBase b L vCap eCap < dsDomGenBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap < dsEdgeDomGenBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsPiPtrBase b L vCap eCap ∧
    dsPiPtrBase b L vCap eCap + eCap ≤ dsRevGenBase b L vCap eCap ∧
    dsRevGenBase b L vCap eCap + vCap ≤ dsRevHeadBase b L vCap eCap ∧
    dsRevHeadBase b L vCap eCap + vCap ≤ dsSGenBase b L vCap eCap ∧
    dsSGenBase b L vCap eCap ≤ dsVSGenBase b L vCap eCap ∧
    dsVSGenBase b L vCap eCap ≤ dsSHeadBase b L vCap eCap ∧
    dsSHeadBase b L vCap eCap ≤ dsSBitBase b L vCap eCap ∧
    dsSBitBase b L vCap eCap + vCap = dsVStampBase b L vCap eCap ∧
    dsVStampBase b L vCap eCap + vCap = dsEStampBase b L vCap eCap ∧
    dsEStampBase b L vCap eCap + eCap = dsKeptStampBase b L vCap eCap ∧
    dsKeptStampBase b L vCap eCap + eCap = dsMEmbTempBase b L vCap eCap ∧
    dsMEmbTempBase b L vCap eCap + eCap = b + dsFixedSize L vCap eCap := by
  have he_mul : eCap ≤ (L + 1) * eCap := Nat.le_mul_of_pos_left eCap (Nat.succ_pos L)
  have hv_mul : vCap ≤ (L + 1) * vCap := Nat.le_mul_of_pos_left vCap (Nat.succ_pos L)
  refine ⟨by simp [dsGenOff, dsGPtr, dsHdrSize], by simp [dsHPtr], by simp [dsAuxPtr],
    by simp [dsMinHBase], rfl, rfl, rfl,
    by simp [dsHDegDummyBase], by simp [dsDomGenBase], by simp [dsEdgeDomGenBase],
    ?_, ?_, ?_, ?_, by simp [dsVSGenBase], by simp [dsSHeadBase], by simp [dsSBitBase],
    rfl, rfl, rfl, rfl, dsFixedSize_add b L vCap eCap⟩
  · change dsEdgeDomGenBase b L vCap eCap + eCap ≤ dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap; omega
  · change dsPiPtrBase b L vCap eCap + eCap ≤ dsPiPtrBase b L vCap eCap + (L + 1) * eCap; omega
  · change dsRevGenBase b L vCap eCap + vCap ≤ dsRevGenBase b L vCap eCap + (L + 1) * vCap; omega
  · change dsRevHeadBase b L vCap eCap + vCap ≤ dsRevHeadBase b L vCap eCap + (L + 1) * vCap; omega

lemma dsInitAt_mem4_zero {L vCap eCap b heapPtr : ℕ} {mem4 : ℕ → ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hz4 : ZeroFrom mem4 (dsMinHBase b vCap eCap))
    (hgen0 : mem4 (b + dsGenOff) = 0) :
    ZeroFrom mem4 heapPtr ∧ (∀ e < eCap, mem4 (dsMinHBase b vCap eCap + e) = 0) ∧
    IsDoublyLinkedList mem4 (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap) eCap [] ∧
    mem4 (dsHDegDummyBase b L vCap eCap) = 0 ∧
    mem4 (dsDomGenBase b L vCap eCap) ≤ mem4 (b + dsGenOff) ∧
    (∀ e < eCap, mem4 (dsEdgeDomGenBase b L vCap eCap + e) ≤ mem4 (b + dsGenOff)) ∧
    (∀ v < vCap, mem4 (dsRevGenBase b L vCap eCap + v) ≤ mem4 (b + dsGenOff)) ∧
    (∀ v < vCap, mem4 (dsVStampBase b L vCap eCap + v) ≤ mem4 (b + dsGenOff)) := by
  obtain ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    dsFixed_mono b L vCap eCap
  rw [hgen0]
  refine ⟨fun a ha => hz4 a (by omega), fun e _ => hz4 _ (by omega),
    IsDoublyLinkedList.nil (hz4 _ (by omega)), hz4 _ (by omega),
    by rw [hz4 _ (by omega)], fun e _ => by rw [hz4 _ (by omega)],
    fun v _ => by rw [hz4 _ (by omega)], fun v _ => by rw [hz4 _ (by omega)]⟩

private lemma dsInitCore_frame_of_bounds {L vCap eCap b heapPtr ret addr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hge : dsHHeadBase b vCap eCap < addr) (hlt : addr < dsMEmbTempBase b L vCap eCap)
    (hne_dg : addr ≠ dsHDegDummyBase b L vCap eCap)
    (hne_dm : addr ≠ dsDomGenBase b L vCap eCap)
    (hne_ed : dsEdgeDomGenBase b L vCap eCap ≤ addr → addr < dsEdgeDomGenBase b L vCap eCap + eCap → False)
    (hne_pi : dsPiPtrBase b L vCap eCap ≤ addr → addr < dsPiPtrBase b L vCap eCap + eCap → False)
    (hne_rg : dsRevGenBase b L vCap eCap ≤ addr → addr < dsRevGenBase b L vCap eCap + vCap → False)
    (hne_rh : dsRevHeadBase b L vCap eCap ≤ addr → addr < dsRevHeadBase b L vCap eCap + vCap → False)
    (hne_vs : dsVStampBase b L vCap eCap ≤ addr → addr < dsVStampBase b L vCap eCap + vCap → False) :
    dsInitCoreFrameCond L vCap eCap b heapPtr ret addr := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18⟩ :=
    dsFixed_mono b L vCap eCap
  have h_aux : dsAuxPtr b vCap eCap + dynGraphSize vCap eCap = dsMinHBase b vCap eCap := rfl
  refine ⟨by omega, Or.inr (by omega), fun _ _ => by omega, by omega, hne_dg,
    fun _ _ => by omega, fun _ _ => by omega, hne_dm,
    fun _ _ => fun h => hne_ed (by omega) (by omega),
    fun _ _ => fun h => hne_pi (by omega) (by omega),
    fun _ _ => fun h => hne_rg (by omega) (by omega),
    fun _ _ => fun h => hne_rh (by omega) (by omega),
    fun _ _ => fun h => hne_vs (by omega) (by omega),
    fun _ _ => by omega, Or.inl (by omega)⟩

private lemma dsBlock_frame_pos_lvl {L vCap eCap b heapPtr ret addr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hge : dsHHeadBase b vCap eCap < addr)
    (hlt : (dsHHeadBase b vCap eCap < addr ∧ addr < dsHDegDummyBase b L vCap eCap) ∨
      (dsHDegDummyBase b L vCap eCap < addr ∧ addr < dsDomGenBase b L vCap eCap) ∨
      (dsDomGenBase b L vCap eCap < addr ∧ addr < dsEdgeDomGenBase b L vCap eCap) ∨
      (dsEdgeDomGenBase b L vCap eCap + eCap ≤ addr ∧ addr < dsPiPtrBase b L vCap eCap) ∨
      (dsRevGenBase b L vCap eCap + vCap ≤ addr ∧ addr < dsRevHeadBase b L vCap eCap)) :
    dsInitCoreFrameCond L vCap eCap b heapPtr ret addr := by
  obtain ⟨_, _, _, _, _, _, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _⟩ :=
    dsFixed_mono b L vCap eCap
  rcases hlt with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    exact dsInitCore_frame_of_bounds hfix hge (by omega) (by omega) (by omega)
      (fun _ _ => by omega) (fun _ _ => by omega) (fun _ _ => by omega)
      (fun _ _ => by omega) (fun _ _ => by omega)

private lemma dsBlock_frame_s_e {L vCap eCap b heapPtr ret addr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hlt : (dsSGenBase b L vCap eCap ≤ addr ∧ addr < dsVStampBase b L vCap eCap) ∨
      (dsEStampBase b L vCap eCap ≤ addr ∧ addr < dsMEmbTempBase b L vCap eCap)) :
    dsInitCoreFrameCond L vCap eCap b heapPtr ret addr := by
  obtain ⟨_, _, _, _, _, _, _, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _⟩ :=
    dsFixed_mono b L vCap eCap
  rcases hlt with ⟨_, _⟩ | ⟨_, _⟩ <;>
    exact dsInitCore_frame_of_bounds hfix (by omega) (by omega) (by omega) (by omega)
      (fun _ _ => by omega) (fun _ _ => by omega) (fun _ _ => by omega)
      (fun _ _ => by omega) (fun _ _ => by omega)

lemma dsInitAt_memFinal_zero {L vCap eCap b heapPtr ret : ℕ} {mem4 memFinal : ℕ → ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hz4 : ZeroFrom mem4 (dsMinHBase b vCap eCap))
    (hfr : ∀ addr, dsInitCoreFrameCond L vCap eCap b heapPtr ret addr → memFinal addr = mem4 addr) :
    (∀ i : Fin (L + 1), 0 < i.1 →
      memFinal (dsHHeadBase b vCap eCap + i.1) = 0 ∧
      memFinal (dsHDegDummyBase b L vCap eCap + i.1) = 0 ∧
      memFinal (dsDomGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ e < eCap, memFinal (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) = 0) ∧
      (∀ v < vCap, memFinal (dsRevGenBase b L vCap eCap + i.1 * vCap + v) = 0)) ∧
    (∀ i : Fin (L + 1),
      memFinal (dsSGenBase b L vCap eCap + i.1) = 0 ∧
      (∀ v < vCap, memFinal (dsVSGenBase b L vCap eCap + i.1 * vCap + v) = 0) ∧
      memFinal (dsSHeadBase b L vCap eCap + i.1) = 0) ∧
    (∀ v < vCap, memFinal (dsSBitBase b L vCap eCap + v) = 0) ∧
    (∀ e < eCap, memFinal (dsEStampBase b L vCap eCap + e) = 0 ∧
      memFinal (dsKeptStampBase b L vCap eCap + e) = 0) := by
  obtain ⟨_, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, _⟩ :=
    dsFixed_mono b L vCap eCap
  have hvs_eq : dsSGenBase b L vCap eCap + (L + 1) = dsVSGenBase b L vCap eCap := rfl
  have hsh_eq : dsVSGenBase b L vCap eCap + (L + 1) * vCap = dsSHeadBase b L vCap eCap := rfl
  have hpi_eq : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap := rfl
  have hrh_eq : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := rfl
  refine ⟨fun i hi0 => ?_, fun i => ?_, fun v hv => ?_, fun e he => ⟨?_, ?_⟩⟩
  · have hi_le : i.1 ≤ L := Nat.lt_succ_iff.mp i.2
    have hhd : dsHHeadBase b vCap eCap + (L + 1) = dsHDegDummyBase b L vCap eCap := rfl
    have hdg : dsHDegDummyBase b L vCap eCap + (L + 1) = dsDomGenBase b L vCap eCap := rfl
    have hdm : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap := rfl
    refine ⟨(hfr _ (dsBlock_frame_pos_lvl hfix (by omega) (Or.inl ⟨by omega, by omega⟩))).trans (hz4 _ (by omega)),
      (hfr _ (dsBlock_frame_pos_lvl hfix (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩)))).trans (hz4 _ (by omega)),
      (hfr _ (dsBlock_frame_pos_lvl hfix (by omega) (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))).trans (hz4 _ (by omega)),
      fun e he => ?_, fun v hv => ?_⟩
    · have hie : eCap ≤ i.1 * eCap := Nat.le_mul_of_pos_left eCap hi0
      have hie2 : i.1 * eCap + e < (L + 1) * eCap := by
        calc i.1 * eCap + e < i.1 * eCap + eCap := Nat.add_lt_add_left he _
          _ = (i.1 + 1) * eCap := by ring
          _ ≤ (L + 1) * eCap := Nat.mul_le_mul_right eCap (by omega)
      exact (hfr _ (dsBlock_frame_pos_lvl hfix (by omega)
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))).trans (hz4 _ (by omega))
    · have hiv : vCap ≤ i.1 * vCap := Nat.le_mul_of_pos_left vCap hi0
      have hiv2 : i.1 * vCap + v < (L + 1) * vCap := by
        calc i.1 * vCap + v < i.1 * vCap + vCap := Nat.add_lt_add_left hv _
          _ = (i.1 + 1) * vCap := by ring
          _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right vCap (by omega)
      exact (hfr _ (dsBlock_frame_pos_lvl hfix (by omega)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))).trans (hz4 _ (by omega))
  · have hi_le : i.1 ≤ L := Nat.lt_succ_iff.mp i.2
    have hsb : dsSHeadBase b L vCap eCap + (L + 1) = dsSBitBase b L vCap eCap := rfl
    refine ⟨(hfr _ (dsBlock_frame_s_e hfix (Or.inl ⟨by omega, by omega⟩))).trans (hz4 _ (by omega)),
      fun v hv => ?_,
      (hfr _ (dsBlock_frame_s_e hfix (Or.inl ⟨by omega, by omega⟩))).trans (hz4 _ (by omega))⟩
    have hiv2 : i.1 * vCap + v < (L + 1) * vCap := by
      calc i.1 * vCap + v < i.1 * vCap + vCap := Nat.add_lt_add_left hv _
        _ = (i.1 + 1) * vCap := by ring
        _ ≤ (L + 1) * vCap := Nat.mul_le_mul_right vCap (by omega)
    exact (hfr _ (dsBlock_frame_s_e hfix (Or.inl ⟨by omega, by omega⟩))).trans (hz4 _ (by omega))
  · exact (hfr _ (dsBlock_frame_s_e hfix (Or.inl ⟨by omega, by omega⟩))).trans (hz4 _ (by omega))
  · exact (hfr _ (dsBlock_frame_s_e hfix (Or.inr ⟨by omega, by omega⟩))).trans (hz4 _ (by omega))
  · exact (hfr _ (dsBlock_frame_s_e hfix (Or.inr ⟨by omega, by omega⟩))).trans (hz4 _ (by omega))

lemma dsInitCoreFrameCond_lt_H {L vCap eCap b heapPtr ret addr : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr) (hlt : addr < dsHPtr b vCap eCap)
    (hne : addr ≠ b + dsGenOff) :
    dsInitCoreFrameCond L vCap eCap b heapPtr ret addr := by
  obtain ⟨_, h0, h0b, h0c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    dsFixed_mono b L vCap eCap
  refine ⟨hne, Or.inl hlt, fun _ _ => by omega, by omega, by omega, fun _ _ => by omega,
    fun _ _ => by omega, by omega, fun _ _ => by omega, fun _ _ => by omega,
    fun _ _ => by omega, fun _ _ => by omega, fun _ _ => by omega, fun _ _ => by omega,
    Or.inl (by omega)⟩

end

end MinCostFlow.DynSpanner.Program
