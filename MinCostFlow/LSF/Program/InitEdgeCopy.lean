module

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import MinCostFlow.LSF.Program.InitTreeCopy

/-!
# LSF Tree Initialization Edge-Copy Emission

Implements and verifies `emitEdgeCopiesProc`, which emits `mj` parallel copies of one original
edge into `copyTail`, `copyHead`, `copyLen`, `copyWt` (first limb `1`), `copyOrigIdx`, and
`copySubIdx`, returning `qCur + mj`.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM

/-! ## Procedure 4: `emitEdgeCopies` -/

/-- Emit `mj` parallel copies starting at `qCur` into `copyTail`, `copyHead`, `copyLen`,
`copyWt` (limb 0 set to `1`), `copyOrigIdx`, and `copySubIdx`, returning `qCur + mj`. -/
def emitEdgeCopiesProc (b : ℕ) : Stmt :=
  forRange 13 (.const 0) (.reg 11)
    (.assign 14 (.bin .add (.reg 12) (.reg 13)) ;;
     .store (.bin .add (.reg 3) (.reg 14)) (.reg 0) ;;
     .store (.bin .add (.reg 4) (.reg 14)) (.reg 1) ;;
     .store (.bin .add (.reg 7) (.reg 14)) (.reg 10) ;;
     .store (.bin .add (.reg 8) (.reg 14)) (.reg 13) ;;
     .assign 15 (.bin .mul (.reg 14) (.reg 9)) ;;
     .assign 16 (.bin .add (.reg 5) (.reg 15)) ;;
     .call 17 (lsfBaseUtils b + idxUtilMemCopy) [.reg 16, .reg 2, .reg 9] ;;
     .store (.bin .add (.reg 6) (.reg 15)) (.const 1)) ;;
  .ret (.bin .add (.reg 12) (.reg 11))

lemma emitEdgeCopiesProc_noRand (b : ℕ) : (emitEdgeCopiesProc b).NoRand := by
  simp [emitEdgeCopiesProc, forRange, forUp, Stmt.NoRand]

def emitEdgeCopiesContract (w : ℕ) : Contract where
  pre args _mem :=
    ∃ uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
        L_in e mj qCur,
      args = [uVal, vVal, lenSrc, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
        copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur] ∧
        16 ≤ 2 ^ w ∧ uVal < 2 ^ w ∧ vVal < 2 ^ w ∧ 1 ≤ L_in ∧ e < 2 ^ w ∧
        lenSrc + L_in ≤ copyTailPtr ∧
        copyTailPtr + (qCur + mj) ≤ copyHeadPtr ∧
        copyHeadPtr + (qCur + mj) ≤ copyLenPtr ∧
        copyLenPtr + (qCur + mj) * L_in ≤ copyWtPtr ∧
        copyWtPtr + (qCur + mj) * L_in ≤ copyOrigIdxPtr ∧
        copyOrigIdxPtr + (qCur + mj) ≤ copySubIdxPtr ∧
        copySubIdxPtr + (qCur + mj) < 2 ^ w
  post args mem ret mem' :=
    ∃ uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
        L_in e mj qCur,
      args = [uVal, vVal, lenSrc, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
        copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur] ∧
        ret = qCur + mj ∧
        (∀ k < mj, mem' (copyTailPtr + (qCur + k)) = uVal) ∧
        (∀ k < mj, mem' (copyHeadPtr + (qCur + k)) = vVal) ∧
        (∀ k < mj, ∀ i < L_in, mem' (copyLenPtr + (qCur + k) * L_in + i) = mem (lenSrc + i)) ∧
        (∀ k < mj, mem' (copyWtPtr + (qCur + k) * L_in) = 1) ∧
        (∀ k < mj, ∀ i, 0 < i → i < L_in →
          mem' (copyWtPtr + (qCur + k) * L_in + i) = mem (copyWtPtr + (qCur + k) * L_in + i)) ∧
        (∀ k < mj, mem' (copyOrigIdxPtr + (qCur + k)) = e) ∧
        (∀ k < mj, mem' (copySubIdxPtr + (qCur + k)) = k) ∧
        ∀ a,
          (a < copyTailPtr + qCur ∨ copyTailPtr + (qCur + mj) ≤ a) →
          (a < copyHeadPtr + qCur ∨ copyHeadPtr + (qCur + mj) ≤ a) →
          (a < copyLenPtr + qCur * L_in ∨ copyLenPtr + (qCur + mj) * L_in ≤ a) →
          (a < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ a) →
          (a < copyOrigIdxPtr + qCur ∨ copyOrigIdxPtr + (qCur + mj) ≤ a) →
          (a < copySubIdxPtr + qCur ∨ copySubIdxPtr + (qCur + mj) ≤ a) →
          mem' a = mem a
  cost args _ :=
    let L_in := args.getD 9 0
    let mj := args.getD 11 0
    mj * (25 * L_in + 80) + 15

private structure EmitBaseRegs
    (uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      L_in e mj qCur : ℕ) (st : State) : Prop where
  r0 : st.regs 0 = uVal
  r1 : st.regs 1 = vVal
  r2 : st.regs 2 = lenSrc
  r3 : st.regs 3 = copyTailPtr
  r4 : st.regs 4 = copyHeadPtr
  r5 : st.regs 5 = copyLenPtr
  r6 : st.regs 6 = copyWtPtr
  r7 : st.regs 7 = copyOrigIdxPtr
  r8 : st.regs 8 = copySubIdxPtr
  r9 : st.regs 9 = L_in
  r10 : st.regs 10 = e
  r11 : st.regs 11 = mj
  r12 : st.regs 12 = qCur

private lemma emitBaseRegs_update_hi
    {uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      L_in e mj qCur r v pos' : ℕ} {mem' : ℕ → ℕ} {st : State}
    (hb : EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
      copyOrigIdxPtr copySubIdxPtr L_in e mj qCur st) (hr : 13 ≤ r) :
    EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
      copyOrigIdxPtr copySubIdxPtr L_in e mj qCur
      { mem := mem', regs := Function.update st.regs r v, pos := pos' } :=
  ⟨by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r0,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r1,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r2,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r3,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r4,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r5,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r6,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r7,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r8,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r9,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r10,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r11,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r12⟩

private lemma emitBaseRegs_update_mem
    {uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr copyOrigIdxPtr copySubIdxPtr
      L_in e mj qCur : ℕ} {mem' : ℕ → ℕ} {st : State}
    (hb : EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
      copyOrigIdxPtr copySubIdxPtr L_in e mj qCur st) :
    EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
      copyOrigIdxPtr copySubIdxPtr L_in e mj qCur { mem := mem', regs := st.regs, pos := st.pos } :=
  ⟨hb.r0, hb.r1, hb.r2, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hb.r9, hb.r10, hb.r11, hb.r12⟩

lemma emitEdgeCopies_meetsContract {w b K_AN h f : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hproc : p.procs[f]? = some (emitEdgeCopiesProc b)) :
    MeetsContract w p f (emitEdgeCopiesContract w) := by
  refine meetsContract_of_triple hproc ?_
  intro args mem0 pos _ hpre
  rcases hpre with ⟨uVal, vVal, lenSrc, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
    copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur, rfl,
    hw16, hu_w, hv_w, hLin1, he_w, hlen_tail, htail_head, hhead_len, hlen_wt, hwt_orig,
    horig_sub, hsub_w⟩
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := hw1
  have hmj_w : mj < 2 ^ w := by omega
  have hLin_w : L_in < 2 ^ w := by omega
  have hret_w : qCur + mj < 2 ^ w := by omega
  have hmc_copy := lsfMemCopy_meetsContract hw1 hp
  let Inv : ℕ → State → Prop := fun t st =>
    t ≤ mj ∧
      EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
        copyOrigIdxPtr copySubIdxPtr L_in e mj qCur st ∧
      st.regs 13 = t ∧
      (∀ k < t, st.mem (copyTailPtr + (qCur + k)) = uVal) ∧
      (∀ k < t, st.mem (copyHeadPtr + (qCur + k)) = vVal) ∧
      (∀ k < t, ∀ i < L_in, st.mem (copyLenPtr + (qCur + k) * L_in + i) = mem0 (lenSrc + i)) ∧
      (∀ k < t, st.mem (copyWtPtr + (qCur + k) * L_in) = 1) ∧
      (∀ k < mj, ∀ i, 0 < i → i < L_in →
        st.mem (copyWtPtr + (qCur + k) * L_in + i) = mem0 (copyWtPtr + (qCur + k) * L_in + i)) ∧
      (∀ k < t, st.mem (copyOrigIdxPtr + (qCur + k)) = e) ∧
      (∀ k < t, st.mem (copySubIdxPtr + (qCur + k)) = k) ∧
      ∀ a,
        (a < copyTailPtr + qCur ∨ copyTailPtr + (qCur + t) ≤ a) →
        (a < copyHeadPtr + qCur ∨ copyHeadPtr + (qCur + t) ≤ a) →
        (a < copyLenPtr + qCur * L_in ∨ copyLenPtr + (qCur + t) * L_in ≤ a) →
        (a < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + t) * L_in ≤ a) →
        (a < copyOrigIdxPtr + qCur ∨ copyOrigIdxPtr + (qCur + t) ≤ a) →
        (a < copySubIdxPtr + qCur ∨ copySubIdxPtr + (qCur + t) ≤ a) →
        st.mem a = mem0 a
  have hloop : Triple w p (fun st => st = startState [uVal, vVal, lenSrc, copyTailPtr,
        copyHeadPtr, copyLenPtr, copyWtPtr, copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur] mem0 pos)
      (forRange 13 (.const 0) (.reg 11)
        (.assign 14 (.bin .add (.reg 12) (.reg 13)) ;;
         .store (.bin .add (.reg 3) (.reg 14)) (.reg 0) ;;
         .store (.bin .add (.reg 4) (.reg 14)) (.reg 1) ;;
         .store (.bin .add (.reg 7) (.reg 14)) (.reg 10) ;;
         .store (.bin .add (.reg 8) (.reg 14)) (.reg 13) ;;
         .assign 15 (.bin .mul (.reg 14) (.reg 9)) ;;
         .assign 16 (.bin .add (.reg 5) (.reg 15)) ;;
         .call 17 (lsfBaseUtils b + idxUtilMemCopy) [.reg 16, .reg 2, .reg 9] ;;
         .store (.bin .add (.reg 6) (.reg 15)) (.const 1)))
      (normalPost (Inv mj))
      fun _ => (mj - 0) * ((25 * L_in + 70) + 1 + 8) + (1 + 1 + 5) := by
    refine Triple.forRange_const (25 * L_in + 70) 0 mj (Nat.zero_le _) hw1 (fun _ => hmj_w)
      (fun st hst => by
        subst hst
        have hb0 : EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
            copyOrigIdxPtr copySubIdxPtr L_in e mj qCur
            (startState [uVal, vVal, lenSrc, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
              copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur] mem0 pos) :=
          ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
           by simp [startState], by simp [startState], by simp [startState], by simp [startState],
           by simp [startState], by simp [startState], by simp [startState], by simp [startState],
           by simp [startState]⟩
        exact ⟨Expr.eval_const h0_w, Nat.zero_le _, emitBaseRegs_update_hi hb0 (by omega),
          by dsimp; rw [Function.update_self],
          fun _ hk => False.elim (Nat.not_lt_zero _ hk),
          fun _ hk => False.elim (Nat.not_lt_zero _ hk),
          fun _ hk => False.elim (Nat.not_lt_zero _ hk),
          fun _ hk => False.elim (Nat.not_lt_zero _ hk),
          fun _ _ _ _ _ => rfl,
          fun _ hk => False.elim (Nat.not_lt_zero _ hk),
          fun _ hk => False.elim (Nat.not_lt_zero _ hk),
          fun _ _ _ _ _ _ _ => rfl⟩)
      (fun _ _ _ _ hi => hi.2.2.1)
      (fun _ _ _ _ hi => Expr.eval_reg_of_eq hi.2.1.r11)
      (fun k _ hk => ?_)
    let q := qCur + k
    have hq_lt : q + 1 ≤ qCur + mj := by omega
    have hqL_le : q * L_in + L_in ≤ (qCur + mj) * L_in := by
      rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in hq_lt
    have hqL_lo : qCur * L_in ≤ q * L_in := Nat.mul_le_mul_right L_in (by omega)
    have hq_w : q < 2 ^ w := by omega
    have hqt_w : copyTailPtr + q < 2 ^ w := by omega
    have hqh_w : copyHeadPtr + q < 2 ^ w := by omega
    have hqo_w : copyOrigIdxPtr + q < 2 ^ w := by omega
    have hqs_w : copySubIdxPtr + q < 2 ^ w := by omega
    have hqL_w : q * L_in < 2 ^ w := by omega
    have hcl_w : copyLenPtr + q * L_in < 2 ^ w := by omega
    have hcl_end_w : copyLenPtr + q * L_in + L_in < 2 ^ w := by omega
    have hcw_w : copyWtPtr + q * L_in < 2 ^ w := by omega
    have hsrc_w : lenSrc + L_in < 2 ^ w := by omega
    let BInv : (ℕ → ℕ) → State → Prop := fun m st =>
      EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
        copyOrigIdxPtr copySubIdxPtr L_in e mj qCur st ∧
      st.regs 13 = k ∧ st.mem = m
    have hb_frame_wt : ∀ {m : ℕ → ℕ} {addr val : ℕ},
        (addr < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ addr) →
        (∀ t < mj, ∀ i, 0 < i → i < L_in → m (copyWtPtr + (qCur + t) * L_in + i) = mem0 (copyWtPtr + (qCur + t) * L_in + i)) →
        ∀ t < mj, ∀ i, 0 < i → i < L_in →
          Function.update m addr val (copyWtPtr + (qCur + t) * L_in + i) = mem0 (copyWtPtr + (qCur + t) * L_in + i) := by
      intro m addr val hdisj hm t ht i hi0 hiL
      have hne : copyWtPtr + (qCur + t) * L_in + i ≠ addr := by
        have h1 : qCur * L_in ≤ (qCur + t) * L_in := Nat.mul_le_mul_right L_in (by omega)
        have h2 : (qCur + t) * L_in + L_in ≤ (qCur + mj) * L_in := by
          rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by omega)
        omega
      rw [Function.update_of_ne hne]; exact hm t ht i hi0 hiL
    let K1 : State → Prop := fun st => Inv k st ∧ st.regs 14 = q
    let K2 : State → Prop := fun st => K1 st
    have hs1 : Triple w p (Inv k) (.assign 14 (.bin .add (.reg 12) (.reg 13))) (normalPost K1) fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.2.1.r12) (Expr.eval_reg_of_eq hst.2.2.1) hq_w)
        fun _ hst => ⟨⟨hst.1, emitBaseRegs_update_hi hst.2.1 (by omega),
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
          hst.2.2.2⟩, by dsimp; rw [Function.update_self]⟩
    -- Combine remaining store/assign sequence directly inside a loop step state
    let MidInv (wT wH wO wS wL wW : Prop) (st : State) : Prop :=
      EmitBaseRegs uVal vVal lenSrc copyTailPtr copyHeadPtr copyLenPtr copyWtPtr
        copyOrigIdxPtr copySubIdxPtr L_in e mj qCur st ∧
      st.regs 13 = k ∧ st.regs 14 = q ∧
      (∀ t < k, st.mem (copyTailPtr + (qCur + t)) = uVal) ∧
      (∀ t < k, st.mem (copyHeadPtr + (qCur + t)) = vVal) ∧
      (∀ t < k, ∀ i < L_in, st.mem (copyLenPtr + (qCur + t) * L_in + i) = mem0 (lenSrc + i)) ∧
      (∀ t < k, st.mem (copyWtPtr + (qCur + t) * L_in) = 1) ∧
      (∀ t < mj, ∀ i, 0 < i → i < L_in →
        st.mem (copyWtPtr + (qCur + t) * L_in + i) = mem0 (copyWtPtr + (qCur + t) * L_in + i)) ∧
      (∀ t < k, st.mem (copyOrigIdxPtr + (qCur + t)) = e) ∧
      (∀ t < k, st.mem (copySubIdxPtr + (qCur + t)) = t) ∧
      wT ∧ wH ∧ wO ∧ wS ∧ wL ∧ wW ∧
      ∀ a,
        (a < copyTailPtr + qCur ∨ copyTailPtr + (qCur + (k + 1)) ≤ a) →
        (a < copyHeadPtr + qCur ∨ copyHeadPtr + (qCur + (k + 1)) ≤ a) →
        (a < copyLenPtr + qCur * L_in ∨ copyLenPtr + (qCur + (k + 1)) * L_in ≤ a) →
        (a < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + (k + 1)) * L_in ≤ a) →
        (a < copyOrigIdxPtr + qCur ∨ copyOrigIdxPtr + (qCur + (k + 1)) ≤ a) →
        (a < copySubIdxPtr + qCur ∨ copySubIdxPtr + (qCur + (k + 1)) ≤ a) →
        st.mem a = mem0 a
    have hK1_mid : ∀ st, K1 st →
        MidInv True True True True True True st := fun st hst => by
      have h0 := hst.1
      refine ⟨h0.2.1, h0.2.2.1, hst.2, h0.2.2.2.1, h0.2.2.2.2.1, h0.2.2.2.2.2.1,
        h0.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.1, h0.2.2.2.2.2.2.2.2.2.1,
        trivial, trivial, trivial, trivial, trivial, trivial, fun a h1 h2 h3 h4 h5 h6 =>
        h0.2.2.2.2.2.2.2.2.2.2 a
          (by rcases h1 with h1 | h1 <;> [exact Or.inl h1; exact Or.inr (by omega)])
          (by rcases h2 with h2 | h2 <;> [exact Or.inl h2; exact Or.inr (by omega)])
          (by rcases h3 with h3 | h3
              · exact Or.inl h3
              · exact Or.inr (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L_in (by omega)) copyLenPtr) h3))
          (by rcases h4 with h4 | h4
              · exact Or.inl h4
              · exact Or.inr (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right L_in (by omega)) copyWtPtr) h4))
          (by rcases h5 with h5 | h5 <;> [exact Or.inl h5; exact Or.inr (by omega)])
          (by rcases h6 with h6 | h6 <;> [exact Or.inl h6; exact Or.inr (by omega)])⟩
    have hs2 : Triple w p (MidInv True True True True True True)
        (.store (.bin .add (.reg 3) (.reg 14)) (.reg 0))
        (normalPost fun st => MidInv (st.mem (copyTailPtr + q) = uVal) True True True True True st)
        fun _ => 5 :=
      Triple.store
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.r3) (Expr.eval_reg_of_eq hst.2.2.1) hqt_w)
        (fun _ hst => Expr.eval_reg_of_eq hst.1.r0)
        fun st hst => by
          have hwt_disj : copyTailPtr + q < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ copyTailPtr + q :=
            Or.inl (by omega)
          refine ⟨emitBaseRegs_update_mem hst.1, hst.2.1, hst.2.2.1,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.1 t ht,
            fun t ht i hi => by
              dsimp
              have hne : copyLenPtr + (qCur + t) * L_in + i ≠ copyTailPtr + q := by omega
              rw [Function.update_of_ne hne]
              exact hst.2.2.2.2.2.1 t ht i hi,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.1 t ht,
            fun t ht i hi0 hiL => by dsimp; exact hb_frame_wt hwt_disj hst.2.2.2.2.2.2.2.1 t ht i hi0 hiL,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.1 t ht,
            by dsimp; rw [Function.update_self], trivial, trivial, trivial, trivial, trivial,
            fun a h1 h2 h3 h4 h5 h6 => by
              dsimp; rw [Function.update_of_ne (by rcases h1 with h1 | h1 <;> omega)]
              exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5 h6⟩
    have hs3 : Triple w p (fun st => MidInv (st.mem (copyTailPtr + q) = uVal) True True True True True st)
        (.store (.bin .add (.reg 4) (.reg 14)) (.reg 1))
        (normalPost fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal) True True True True st)
        fun _ => 5 :=
      Triple.store
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.r4) (Expr.eval_reg_of_eq hst.2.2.1) hqh_w)
        (fun _ hst => Expr.eval_reg_of_eq hst.1.r1)
        fun st hst => by
          have hwt_disj : copyHeadPtr + q < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ copyHeadPtr + q :=
            Or.inl (by omega)
          refine ⟨emitBaseRegs_update_mem hst.1, hst.2.1, hst.2.2.1,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.1 t ht,
            fun t ht i hi => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.1 t ht i hi,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.1 t ht,
            fun t ht i hi0 hiL => by dsimp; exact hb_frame_wt hwt_disj hst.2.2.2.2.2.2.2.1 t ht i hi0 hiL,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.1 t ht,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_self], trivial, trivial, trivial, trivial,
            fun a h1 h2 h3 h4 h5 h6 => by
              dsimp; rw [Function.update_of_ne (by rcases h2 with h2 | h2 <;> omega)]
              exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5 h6⟩
    have hs4 : Triple w p
        (fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal) True True True True st)
        (.store (.bin .add (.reg 7) (.reg 14)) (.reg 10))
        (normalPost fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal)
          (st.mem (copyOrigIdxPtr + q) = e) True True True st)
        fun _ => 5 :=
      Triple.store
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.r7) (Expr.eval_reg_of_eq hst.2.2.1) hqo_w)
        (fun _ hst => Expr.eval_reg_of_eq hst.1.r10)
        fun st hst => by
          have hwt_disj : copyOrigIdxPtr + q < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ copyOrigIdxPtr + q :=
            Or.inr (by omega)
          refine ⟨emitBaseRegs_update_mem hst.1, hst.2.1, hst.2.2.1,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.1 t ht,
            fun t ht i hi => by
              dsimp
              have hne : copyLenPtr + (qCur + t) * L_in + i ≠ copyOrigIdxPtr + q := by
                have h1 : (qCur + t) * L_in + L_in ≤ (qCur + mj) * L_in := by
                  rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by omega)
                omega
              rw [Function.update_of_ne hne]
              exact hst.2.2.2.2.2.1 t ht i hi,
            fun t ht => by
              dsimp
              have hne : copyWtPtr + (qCur + t) * L_in ≠ copyOrigIdxPtr + q := by
                have : (qCur + t) * L_in ≤ (qCur + mj) * L_in := Nat.mul_le_mul_right L_in (by omega)
                omega
              rw [Function.update_of_ne hne]
              exact hst.2.2.2.2.2.2.1 t ht,
            fun t ht i hi0 hiL => by dsimp; exact hb_frame_wt hwt_disj hst.2.2.2.2.2.2.2.1 t ht i hi0 hiL,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.1 t ht,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_self], trivial, trivial, trivial,
            fun a h1 h2 h3 h4 h5 h6 => by
              dsimp; rw [Function.update_of_ne (by rcases h5 with h5 | h5 <;> omega)]
              exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5 h6⟩
    have hs5 : Triple w p
        (fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal)
          (st.mem (copyOrigIdxPtr + q) = e) True True True st)
        (.store (.bin .add (.reg 8) (.reg 14)) (.reg 13))
        (normalPost fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal)
          (st.mem (copyOrigIdxPtr + q) = e) (st.mem (copySubIdxPtr + q) = k) True True st)
        fun _ => 5 :=
      Triple.store
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.r8) (Expr.eval_reg_of_eq hst.2.2.1) hqs_w)
        (fun _ hst => Expr.eval_reg_of_eq hst.2.1)
        fun st hst => by
          have hwt_disj : copySubIdxPtr + q < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ copySubIdxPtr + q :=
            Or.inr (by omega)
          refine ⟨emitBaseRegs_update_mem hst.1, hst.2.1, hst.2.2.1,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.1 t ht,
            fun t ht i hi => by
              dsimp
              have hne : copyLenPtr + (qCur + t) * L_in + i ≠ copySubIdxPtr + q := by
                have h1 : (qCur + t) * L_in + L_in ≤ (qCur + mj) * L_in := by
                  rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by omega)
                omega
              rw [Function.update_of_ne hne]
              exact hst.2.2.2.2.2.1 t ht i hi,
            fun t ht => by
              dsimp
              have hne : copyWtPtr + (qCur + t) * L_in ≠ copySubIdxPtr + q := by
                have : (qCur + t) * L_in ≤ (qCur + mj) * L_in := Nat.mul_le_mul_right L_in (by omega)
                omega
              rw [Function.update_of_ne hne]
              exact hst.2.2.2.2.2.2.1 t ht,
            fun t ht i hi0 hiL => by dsimp; exact hb_frame_wt hwt_disj hst.2.2.2.2.2.2.2.1 t ht i hi0 hiL,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.1 t ht,
            fun t ht => by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.1 t ht,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.2.2.2.2.2.2.2.2.2.1,
            by dsimp; rw [Function.update_self], trivial, trivial,
            fun a h1 h2 h3 h4 h5 h6 => by
              dsimp; rw [Function.update_of_ne (by rcases h6 with h6 | h6 <;> omega)]
              exact hst.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5 h6⟩
    let M4 := fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal)
      (st.mem (copyOrigIdxPtr + q) = e) (st.mem (copySubIdxPtr + q) = k) True True st
    have hs6 : Triple w p M4 (.assign 15 (.bin .mul (.reg 14) (.reg 9)))
        (normalPost fun st => M4 st ∧ st.regs 15 = q * L_in) fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_mul (Expr.eval_reg_of_eq hst.2.2.1) (Expr.eval_reg_of_eq hst.1.r9) hqL_w)
        fun _ hst => ⟨⟨emitBaseRegs_update_hi hst.1 (by omega),
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1, hst.2.2.2⟩,
          by dsimp; rw [Function.update_self]⟩
    have hs7 : Triple w p (fun st => M4 st ∧ st.regs 15 = q * L_in)
        (.assign 16 (.bin .add (.reg 5) (.reg 15)))
        (normalPost fun st => M4 st ∧ st.regs 15 = q * L_in ∧ st.regs 16 = copyLenPtr + q * L_in) fun _ => 4 :=
      Triple.assign
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.1.r5) (Expr.eval_reg_of_eq hst.2) hcl_w)
        fun _ hst => ⟨⟨emitBaseRegs_update_hi hst.1.1 (by omega),
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.2.1, hst.1.2.2.2⟩,
          by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2,
          by dsimp; rw [Function.update_self]⟩
    let M5 := fun st => MidInv (st.mem (copyTailPtr + q) = uVal) (st.mem (copyHeadPtr + q) = vVal)
      (st.mem (copyOrigIdxPtr + q) = e) (st.mem (copySubIdxPtr + q) = k)
      (∀ i < L_in, st.mem (copyLenPtr + q * L_in + i) = mem0 (lenSrc + i)) True st
    have hs8 : Triple w p (fun st => M4 st ∧ st.regs 15 = q * L_in ∧ st.regs 16 = copyLenPtr + q * L_in)
        (.call 17 (lsfBaseUtils b + idxUtilMemCopy) [.reg 16, .reg 2, .reg 9])
        (normalPost fun st => M5 st ∧ st.regs 15 = q * L_in) fun _ => 20 * L_in + 18 := by
      refine Triple.conseq
        (Triple.call (vs := fun _ => [copyLenPtr + q * L_in, lenSrc, L_in]) hmc_copy
          (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.2.2)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r2)
              (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r9) (evalArgs_nil _ _))))
          (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
          (fun _ _ => ⟨copyLenPtr + q * L_in, lenSrc, L_in, rfl, hcl_end_w, hsrc_w, Or.inr (by omega)⟩)
          (fun st _ mem1 _ hst ⟨_, _, _, heq, _, hcp, hfr⟩ => by
            simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
            have hsrc_mem : ∀ i < L_in, st.mem (lenSrc + i) = mem0 (lenSrc + i) := fun i hi =>
              hst.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (lenSrc + i)
                (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
                (Or.inl (by omega)) (Or.inl (by omega))
            have hq1_mul : (q + 1) * L_in = q * L_in + L_in := Nat.add_one_mul q L_in
            have hdisj_t : ∀ a, a < copyLenPtr + q * L_in → mem1 a = st.mem a := fun a ha =>
              hfr a (Or.inl ha)
            have hdisj_hi : ∀ a, copyLenPtr + (q + 1) * L_in ≤ a → mem1 a = st.mem a := fun a ha =>
              hfr a (Or.inr (by omega))
            refine ⟨⟨emitBaseRegs_update_hi hst.1.1 (by omega),
              by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
              by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.2.1,
              fun t ht => by dsimp; rw [hdisj_t _ (by omega)]; exact hst.1.2.2.2.1 t ht,
              fun t ht => by dsimp; rw [hdisj_t _ (by omega)]; exact hst.1.2.2.2.2.1 t ht,
              fun t ht i hi => by
                dsimp
                have hlt_a : copyLenPtr + (qCur + t) * L_in + i < copyLenPtr + q * L_in := by
                  have hle : (qCur + t) * L_in + L_in ≤ q * L_in := by
                    rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by dsimp [q]; omega)
                  omega
                rw [hdisj_t _ hlt_a]
                exact hst.1.2.2.2.2.2.1 t ht i hi,
              fun t ht => by
                dsimp
                have hge_a : copyLenPtr + (q + 1) * L_in ≤ copyWtPtr + (qCur + t) * L_in := by
                  have hle : (q + 1) * L_in ≤ (qCur + mj) * L_in := Nat.mul_le_mul_right L_in hq_lt
                  have hle2 : qCur * L_in ≤ (qCur + t) * L_in := Nat.mul_le_mul_right L_in (by omega)
                  omega
                rw [hdisj_hi _ hge_a]
                exact hst.1.2.2.2.2.2.2.1 t ht,
              fun t ht i hi0 hiL => by
                dsimp
                have hge_a : copyLenPtr + (q + 1) * L_in ≤ copyWtPtr + (qCur + t) * L_in + i := by
                  have hle : (q + 1) * L_in ≤ (qCur + mj) * L_in := Nat.mul_le_mul_right L_in hq_lt
                  have hle2 : qCur * L_in ≤ (qCur + t) * L_in := Nat.mul_le_mul_right L_in (by omega)
                  omega
                rw [hdisj_hi _ hge_a]
                exact hst.1.2.2.2.2.2.2.2.1 t ht i hi0 hiL,
              fun t ht => by dsimp; rw [hdisj_hi _ (by omega)]; exact hst.1.2.2.2.2.2.2.2.2.1 t ht,
              fun t ht => by dsimp; rw [hdisj_hi _ (by omega)]; exact hst.1.2.2.2.2.2.2.2.2.2.1 t ht,
              by dsimp; rw [hdisj_t _ (by omega)]; exact hst.1.2.2.2.2.2.2.2.2.2.2.1,
              by dsimp; rw [hdisj_t _ (by omega)]; exact hst.1.2.2.2.2.2.2.2.2.2.2.2.1,
              by dsimp; rw [hdisj_hi _ (by omega)]; exact hst.1.2.2.2.2.2.2.2.2.2.2.2.2.1,
              by dsimp; rw [hdisj_hi _ (by omega)]; exact hst.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
              fun i hi => by dsimp; rw [hcp i hi, hsrc_mem i hi], trivial,
              fun a h1 h2 h3 h4 h5 h6 => by
                dsimp
                have hfr_disj : a < copyLenPtr + q * L_in ∨ copyLenPtr + q * L_in + L_in ≤ a := by
                  rcases h3 with h3a | h3b
                  · exact Or.inl (by omega)
                  · have h3b' : copyLenPtr + (q + 1) * L_in ≤ a := by
                      rw [show q + 1 = qCur + (k + 1) by dsimp [q]; omega]
                      exact h3b
                    exact Or.inr (by omega)
                rw [hfr a hfr_disj]
                exact hst.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5 h6⟩,
              by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1⟩))
        (fun _ h => h) (fun _ _ h => h)
        (fun _ _ => by
          simp only [argsSize, Expr.size, memCopyContract, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
          omega)
    have hs9 : Triple w p (fun st => M5 st ∧ st.regs 15 = q * L_in)
        (.store (.bin .add (.reg 6) (.reg 15)) (.const 1))
        (normalPost fun st₁ =>
          Inv (k + 1) { st₁ with regs := Function.update st₁.regs 13 (k + 1) } ∧ st₁.regs 13 = k)
        fun _ => 5 :=
      Triple.store
        (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.1.r6) (Expr.eval_reg_of_eq hst.2) hcw_w)
        (fun _ _ => Expr.eval_const h1_w)
        fun st hst => by
          dsimp only
          have hs := hst.1
          have hk_lt : ∀ t < k, copyWtPtr + (qCur + t) * L_in ≠ copyWtPtr + q * L_in := by
            intro t ht
            have hle : (qCur + t) * L_in + L_in ≤ q * L_in := by
              rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by dsimp [q]; omega)
            omega
          have hwt_nz : ∀ t < mj, ∀ i, 0 < i → i < L_in →
              Function.update st.mem (copyWtPtr + q * L_in) 1 (copyWtPtr + (qCur + t) * L_in + i) =
                mem0 (copyWtPtr + (qCur + t) * L_in + i) := by
            intro t ht i hi0 hiL
            have hne : copyWtPtr + (qCur + t) * L_in + i ≠ copyWtPtr + q * L_in := by
              rcases lt_trichotomy t k with hlt | rfl | hgt
              · have : (qCur + t) * L_in + i < q * L_in := by
                  have h1 : (qCur + t) * L_in + L_in ≤ q * L_in := by
                    rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by dsimp [q]; omega)
                  omega
                omega
              · dsimp [q]; omega
              · have : q * L_in < (qCur + t) * L_in := by
                  have h1 : (q + 1) * L_in ≤ (qCur + t) * L_in := Nat.mul_le_mul_right L_in (by dsimp [q]; omega)
                  have h2 : q * L_in + L_in = (q + 1) * L_in := (Nat.add_one_mul q L_in).symm
                  omega
                omega
            rw [Function.update_of_ne hne]; exact hs.2.2.2.2.2.2.2.1 t ht i hi0 hiL
          refine ⟨⟨by omega, emitBaseRegs_update_hi hs.1 (by omega),
            by dsimp; rw [Function.update_self],
            fun t ht => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.1 t ht
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.2.2.2.2.2.2.1,
            fun t ht => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.1 t ht
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.2.2.2.2.2.2.2.1,
            fun t ht i hi => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
              · dsimp
                have hne : copyLenPtr + (qCur + t) * L_in + i ≠ copyWtPtr + q * L_in := by
                  have h1 : (qCur + t) * L_in + L_in ≤ (qCur + mj) * L_in := by
                    rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by omega)
                  omega
                rw [Function.update_of_ne hne]
                exact hs.2.2.2.2.2.1 t ht i hi
              · dsimp
                have hne : copyLenPtr + (qCur + t) * L_in + i ≠ copyWtPtr + q * L_in := by
                  have h1 : (qCur + t) * L_in + L_in ≤ (qCur + mj) * L_in := by
                    rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right L_in (by omega)
                  omega
                rw [Function.update_of_ne hne]
                exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi,
            fun t ht => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
              · dsimp; rw [Function.update_of_ne (hk_lt t ht)]; exact hs.2.2.2.2.2.2.1 t ht
              · dsimp; rw [Function.update_self],
            fun t ht i hi0 hiL => by dsimp; exact hwt_nz t ht i hi0 hiL,
            fun t ht => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.2.2.2.2.1 t ht
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun t ht => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.2.2.2.2.2.1 t ht
              · dsimp; rw [Function.update_of_ne (by omega)]; exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun a h1 h2 h3 h4 h5 h6 => by
              dsimp
              have hne : a ≠ copyWtPtr + q * L_in := by
                rcases h4 with h4a | h4b
                · omega
                · have h4b' : copyWtPtr + (q + 1) * L_in ≤ a := by
                    rw [show q + 1 = qCur + (k + 1) by dsimp [q]; omega]
                    exact h4b
                  have : (q + 1) * L_in = q * L_in + L_in := Nat.add_one_mul q L_in
                  omega
              rw [Function.update_of_ne hne]
              exact hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a h1 h2 h3 h4 h5 h6⟩,
            hs.2.1⟩
    have h2_9 :=
      Triple.conseq
        (Triple.seq_normal_const hs2 (Triple.seq_normal_const hs3 (Triple.seq_normal_const hs4
          (Triple.seq_normal_const hs5 (Triple.seq_normal_const hs6 (Triple.seq_normal_const hs7
            (Triple.seq_normal_const hs8 hs9)))))))
        hK1_mid (fun _ _ h => h) fun _ _ => le_rfl
    exact (Triple.seq_normal_const hs1 h2_9).mono_cost fun _ _ => by omega
  have hret : Triple w p (Inv mj) (.ret (.bin .add (.reg 12) (.reg 11)))
      (retPost fun ret st => ret = qCur + mj ∧
        (∀ k < mj, st.mem (copyTailPtr + (qCur + k)) = uVal) ∧
        (∀ k < mj, st.mem (copyHeadPtr + (qCur + k)) = vVal) ∧
        (∀ k < mj, ∀ i < L_in, st.mem (copyLenPtr + (qCur + k) * L_in + i) = mem0 (lenSrc + i)) ∧
        (∀ k < mj, st.mem (copyWtPtr + (qCur + k) * L_in) = 1) ∧
        (∀ k < mj, ∀ i, 0 < i → i < L_in →
          st.mem (copyWtPtr + (qCur + k) * L_in + i) = mem0 (copyWtPtr + (qCur + k) * L_in + i)) ∧
        (∀ k < mj, st.mem (copyOrigIdxPtr + (qCur + k)) = e) ∧
        (∀ k < mj, st.mem (copySubIdxPtr + (qCur + k)) = k) ∧
        ∀ a,
          (a < copyTailPtr + qCur ∨ copyTailPtr + (qCur + mj) ≤ a) →
          (a < copyHeadPtr + qCur ∨ copyHeadPtr + (qCur + mj) ≤ a) →
          (a < copyLenPtr + qCur * L_in ∨ copyLenPtr + (qCur + mj) * L_in ≤ a) →
          (a < copyWtPtr + qCur * L_in ∨ copyWtPtr + (qCur + mj) * L_in ≤ a) →
          (a < copyOrigIdxPtr + qCur ∨ copyOrigIdxPtr + (qCur + mj) ≤ a) →
          (a < copySubIdxPtr + qCur ∨ copySubIdxPtr + (qCur + mj) ≤ a) →
          st.mem a = mem0 a) fun _ => 4 :=
    Triple.ret
      (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.2.1.r12) (Expr.eval_reg_of_eq hst.2.1.r11) hret_w)
      fun _ hst => ⟨rfl, hst.2.2.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2.1, hst.2.2.2.2.2.2.1,
        hst.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.1, hst.2.2.2.2.2.2.2.2.2.1,
        hst.2.2.2.2.2.2.2.2.2.2⟩
  refine Triple.conseq (Triple.seq_normal_const hloop hret) (fun _ h => h)
    (fun o st hpost => by
      cases o with
      | normal => exact False.elim hpost
      | returned _ =>
        exact ⟨uVal, vVal, lenSrc, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
          copyOrigIdxPtr, copySubIdxPtr, L_in, e, mj, qCur, rfl, hpost.1, hpost.2.1,
          hpost.2.2.1, hpost.2.2.2.1, hpost.2.2.2.2.1, hpost.2.2.2.2.2.1, hpost.2.2.2.2.2.2.1,
          hpost.2.2.2.2.2.2.2.1, hpost.2.2.2.2.2.2.2.2⟩)
    (fun st hst => by
      subst hst
      simp only [emitEdgeCopiesContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Nat.sub_zero]
      nlinarith)

end MinCostFlow.LSF.Program
