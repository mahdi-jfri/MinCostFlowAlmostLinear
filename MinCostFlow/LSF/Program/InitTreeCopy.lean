module

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import MinCostFlow.LSF.Program.InitTreeWeights

/-!
# LSF Tree Initialization Weight Scaling Quotients

Implements and verifies `multQNatStepProc`, which computes `edgeMult` and
`q_nat(e) = ⌊edgeMult * 2^(h*(L_in+4)) / ℓ_int(e)⌋` for one original edge, reusing `[hp, hp_next)`
inside the `lsstSpace` arena.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM

/-! ## Pure Arithmetic Helpers for Multiplicity and Congruence Quotients -/

lemma nat_eq_unsignedVal_of_intVal {mem : ℕ → ℕ} {a h L n : ℕ}
    (hval : Num.Valid mem a h L) (hint : Num.intVal mem a h L = (n : ℤ)) :
    Num.unsignedVal mem a h L = n := by
  have hu_lt := Num.unsignedVal_lt hval
  rw [Num.intVal, Num.signedVal] at hint
  split_ifs at hint with hle
  · omega
  · omega

lemma floorDiv_natCast {a b : ℕ} :
    Num.floorDiv (a : ℤ) (b : ℤ) = ((a / b : ℕ) : ℤ) := by
  rw [Num.floorDiv]
  split_ifs with hneg
  · omega
  · exact (Int.natCast_ediv a b).symm

lemma div_lt_cap_half_of_numer {a b h L : ℕ}
    (_hb : 0 < b) (ha : 2 * a < Num.capacity h L) :
    2 * (a / b) < Num.capacity h L := by
  have hle : a / b ≤ a := Nat.div_le_self a b
  omega

private lemma lsfCapacity_mono {h a b : ℕ} (hle : a ≤ b) :
    Num.capacity h a ≤ Num.capacity h b :=
  Nat.pow_le_pow_right (Num.base_pos h) hle

private lemma intVal_eq_cast_of_uVal {mem : ℕ → ℕ} {a h L n : ℕ}
    (hu : Num.unsignedVal mem a h L = n) (hcap : 2 * n < Num.capacity h L) :
    Num.intVal mem a h L = (n : ℤ) := by
  rw [← hu]
  exact intVal_eq_of_unsignedVal_lt (by rw [hu]; exact hcap)

/-! ## Procedure 3: `multQNatStep` -/

/-- Compute `mj = (m0 * v_int + S_v - 1) / S_v`, store `mj` at `multOut`, and store
`q_nat = (mj * 2^(h*(L_in+4))) / ℓ_int` into `qNatOut` (width `K_w + 6`), returning `hp_next`. -/
def multQNatStepProc (b f_l2w : ℕ) : Stmt :=
  .call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 7, .reg 11, .const 0] ;;
  .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 7, .reg 0, .reg 10] ;;
  .call 14 (lsfBaseMul b) [.reg 6, .reg 7, .reg 11, .reg 12] ;;
  .assign 15 (.bin .add (.reg 12) (.bin .mul (.const 4) (.reg 11))) ;;
  .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 8, .reg 15, .reg 11] ;;
  .call 19 (lsfBaseUtils b + idxUtilAddTo) [.reg 8, .reg 5, .reg 11] ;;
  .call 16 (lsfBaseIntDiv b) [.reg 8, .reg 4, .reg 11, .reg 14] ;;
  .assign 15 (.bin .sub (.reg 16) (.reg 11)) ;;
  .call 17 f_l2w [.reg 15, .reg 11, .reg 13] ;;
  .store (.reg 3) (.reg 17) ;;
  .assign 18 (.bin .add (.reg 11) (.const 6)) ;;
  .assign 20 (.bin .add (.reg 10) (.const 4)) ;;
  .assign 21 (.bin .sub (.reg 18) (.reg 20)) ;;
  .assign 22 (.bin .add (.reg 8) (.reg 20)) ;;
  .call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 8, .reg 20, .const 0] ;;
  .call 19 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 22, .reg 21, .reg 17] ;;
  .call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 9, .reg 18, .const 0] ;;
  .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 9, .reg 1, .reg 10] ;;
  .call 16 (lsfBaseIntDiv b) [.reg 8, .reg 9, .reg 18, .reg 16] ;;
  .assign 15 (.bin .sub (.reg 16) (.reg 18)) ;;
  .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 2, .reg 15, .reg 18] ;;
  .ret (.reg 16)

lemma multQNatStepProc_noRand (b f_l2w : ℕ) : (multQNatStepProc b f_l2w).NoRand := by
  simp [multQNatStepProc, Stmt.NoRand]

def multQNatStepSpace (K_w : ℕ) : ℕ :=
  6 * K_w + Num.integerDivideSpace K_w + Num.integerDivideSpace (K_w + 6)

def multQNatStepContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ wtE lenE qNatOut multOut svPtr svMinusOnePtr m0LimbsPtr edgeLimbsPtr numerPtr lenQPtr
        L_in K_w hp pow2h m0 S_v v_int ℓ_int,
      args = [wtE, lenE, qNatOut, multOut, svPtr, svMinusOnePtr, m0LimbsPtr, edgeLimbsPtr,
        numerPtr, lenQPtr, L_in, K_w, hp, pow2h] ∧
        pow2h = 2 ^ h ∧ 1 ≤ h ∧ 3 * h + 2 ≤ w ∧
        1 ≤ L_in ∧ L_in ≤ K_w ∧
        1 ≤ m0 ∧ 2 * m0 < 2 ^ w ∧ 1 ≤ S_v ∧ 1 ≤ v_int ∧
        1 ≤ ℓ_int ∧ 2 * ℓ_int < Num.capacity h L_in ∧
        2 * v_int < Num.capacity h L_in ∧
        2 * S_v < Num.capacity h K_w ∧
        2 * (m0 * v_int + (S_v - 1)) < Num.capacity h K_w ∧
        (m0 * v_int + S_v - 1) / S_v ≤ 2 * m0 ∧
        4 * m0 + 2 < Num.capacity h (K_w + 6 - (L_in + 4)) ∧
        4 * (2 * m0) * 2 ^ (h * (L_in + 4)) < Num.capacity h (K_w + 6) / 2 ∧
        wtE + L_in ≤ qNatOut ∧ lenE + L_in ≤ qNatOut ∧
        qNatOut + (K_w + 6) ≤ multOut ∧ multOut + 1 ≤ svPtr ∧
        svPtr + K_w ≤ svMinusOnePtr ∧ svMinusOnePtr + K_w ≤ m0LimbsPtr ∧
        m0LimbsPtr + K_w ≤ edgeLimbsPtr ∧ edgeLimbsPtr + K_w ≤ numerPtr ∧
        numerPtr + (K_w + 6) ≤ lenQPtr ∧ lenQPtr + (K_w + 6) ≤ hp ∧
        hp + multQNatStepSpace K_w < 2 ^ w ∧
        Num.Valid mem wtE h L_in ∧ Num.unsignedVal mem wtE h L_in = v_int ∧
        Num.Valid mem lenE h L_in ∧ Num.unsignedVal mem lenE h L_in = ℓ_int ∧
        Num.Valid mem svPtr h K_w ∧ Num.unsignedVal mem svPtr h K_w = S_v ∧
        Num.Valid mem svMinusOnePtr h K_w ∧ Num.unsignedVal mem svMinusOnePtr h K_w = S_v - 1 ∧
        Num.Valid mem m0LimbsPtr h K_w ∧ Num.unsignedVal mem m0LimbsPtr h K_w = m0 ∧
        ZeroFrom mem hp
  post args mem ret mem' :=
    ∃ wtE lenE qNatOut multOut svPtr svMinusOnePtr m0LimbsPtr edgeLimbsPtr numerPtr lenQPtr
        L_in K_w hp pow2h m0 S_v v_int ℓ_int,
      args = [wtE, lenE, qNatOut, multOut, svPtr, svMinusOnePtr, m0LimbsPtr, edgeLimbsPtr,
        numerPtr, lenQPtr, L_in, K_w, hp, pow2h] ∧
        ret = hp + multQNatStepSpace K_w ∧
        Num.unsignedVal mem wtE h L_in = v_int ∧
        Num.unsignedVal mem lenE h L_in = ℓ_int ∧
        Num.unsignedVal mem svPtr h K_w = S_v ∧
        Num.unsignedVal mem m0LimbsPtr h K_w = m0 ∧
        mem' multOut = (m0 * v_int + S_v - 1) / S_v ∧
        Num.Valid mem' qNatOut h (K_w + 6) ∧
        Num.unsignedVal mem' qNatOut h (K_w + 6) =
          (((m0 * v_int + S_v - 1) / S_v) * 2 ^ (h * (L_in + 4))) / ℓ_int ∧
        ZeroFrom mem' ret ∧
        ∀ a < edgeLimbsPtr, (a < qNatOut ∨ qNatOut + (K_w + 6) ≤ a) → a ≠ multOut → mem' a = mem a
  cost args _ :=
    let K_q := args.getD 11 0 + 6
    800 * K_q * K_q + 2500 * K_q + 2000

private structure MultStepCtx where
  (wtE lenE qNatOut multOut svPtr svMinusOnePtr m0LimbsPtr edgeLimbsPtr numerPtr lenQPtr : ℕ)
  (L_in K_w hp h w m0 S_v v_int ℓ_int : ℕ)
  mem0 : ℕ → ℕ
  hh1 : 1 ≤ h
  hw3h : 3 * h + 2 ≤ w
  hLin1 : 1 ≤ L_in
  hLK : L_in ≤ K_w
  hm01 : 1 ≤ m0
  hm02w : 2 * m0 < 2 ^ w
  hSv1 : 1 ≤ S_v
  hv1 : 1 ≤ v_int
  hℓ1 : 1 ≤ ℓ_int
  hℓ_cap : 2 * ℓ_int < Num.capacity h L_in
  hv_cap : 2 * v_int < Num.capacity h L_in
  hSv_cap : 2 * S_v < Num.capacity h K_w
  hnum_cap : 2 * (m0 * v_int + (S_v - 1)) < Num.capacity h K_w
  hmj_bd : (m0 * v_int + S_v - 1) / S_v ≤ 2 * m0
  hmj_rem_cap : 4 * m0 + 2 < Num.capacity h (K_w + 6 - (L_in + 4))
  hq_cap : 4 * (2 * m0) * 2 ^ (h * (L_in + 4)) < Num.capacity h (K_w + 6) / 2
  hwt_q : wtE + L_in ≤ qNatOut
  hlen_q : lenE + L_in ≤ qNatOut
  hq_m : qNatOut + (K_w + 6) ≤ multOut
  hm_sv : multOut + 1 ≤ svPtr
  hsv_m1 : svPtr + K_w ≤ svMinusOnePtr
  hm1_m0 : svMinusOnePtr + K_w ≤ m0LimbsPtr
  hm0_ed : m0LimbsPtr + K_w ≤ edgeLimbsPtr
  hed_num : edgeLimbsPtr + K_w ≤ numerPtr
  hnum_lq : numerPtr + (K_w + 6) ≤ lenQPtr
  hlq_hp : lenQPtr + (K_w + 6) ≤ hp
  hhp_w : hp + multQNatStepSpace K_w < 2 ^ w
  hwt_val : Num.Valid mem0 wtE h L_in
  hwt_u : Num.unsignedVal mem0 wtE h L_in = v_int
  hlen_val : Num.Valid mem0 lenE h L_in
  hlen_u : Num.unsignedVal mem0 lenE h L_in = ℓ_int
  hsv_val : Num.Valid mem0 svPtr h K_w
  hsv_u : Num.unsignedVal mem0 svPtr h K_w = S_v
  hsvm1_val : Num.Valid mem0 svMinusOnePtr h K_w
  hsvm1_u : Num.unsignedVal mem0 svMinusOnePtr h K_w = S_v - 1
  hm0_val : Num.Valid mem0 m0LimbsPtr h K_w
  hm0_u : Num.unsignedVal mem0 m0LimbsPtr h K_w = m0
  hzf0 : ZeroFrom mem0 hp

private def MultStepCtx.baseArgs (C : MultStepCtx) : List ℕ :=
  [C.wtE, C.lenE, C.qNatOut, C.multOut, C.svPtr, C.svMinusOnePtr, C.m0LimbsPtr,
    C.edgeLimbsPtr, C.numerPtr, C.lenQPtr, C.L_in, C.K_w, C.hp, 2 ^ C.h]

private def MultStepCtx.mj (C : MultStepCtx) : ℕ :=
  (C.m0 * C.v_int + C.S_v - 1) / C.S_v

private def MultStepCtx.qnat (C : MultStepCtx) : ℕ :=
  (C.mj * 2 ^ (C.h * (C.L_in + 4))) / C.ℓ_int

private def MultStepCtx.hp1 (C : MultStepCtx) : ℕ := C.hp + 6 * C.K_w
private def MultStepCtx.hp2 (C : MultStepCtx) : ℕ := C.hp1 + Num.integerDivideSpace C.K_w
private def MultStepCtx.q1 (C : MultStepCtx) : ℕ := C.hp1 + 2 * C.K_w + Num.unsignedDivideSpace C.K_w
private def MultStepCtx.q2 (C : MultStepCtx) : ℕ := C.hp2 + 2 * (C.K_w + 6) + Num.unsignedDivideSpace (C.K_w + 6)

private lemma MultStepCtx.order (C : MultStepCtx) :
    C.wtE + C.L_in ≤ C.qNatOut ∧ C.lenE + C.L_in ≤ C.qNatOut ∧
    C.qNatOut + (C.K_w + 6) ≤ C.multOut ∧ C.multOut + 1 ≤ C.svPtr ∧
    C.svPtr + C.K_w ≤ C.svMinusOnePtr ∧ C.svMinusOnePtr + C.K_w ≤ C.m0LimbsPtr ∧
    C.m0LimbsPtr + C.K_w ≤ C.edgeLimbsPtr ∧ C.edgeLimbsPtr + C.K_w ≤ C.numerPtr ∧
    C.numerPtr + (C.K_w + 6) ≤ C.lenQPtr ∧ C.lenQPtr + (C.K_w + 6) ≤ C.hp :=
  ⟨C.hwt_q, C.hlen_q, C.hq_m, C.hm_sv, C.hsv_m1, C.hm1_m0, C.hm0_ed, C.hed_num, C.hnum_lq, C.hlq_hp⟩

private lemma MultStepCtx.hw2h (C : MultStepCtx) : 2 * C.h + 2 ≤ C.w := by have := C.hw3h; omega
private lemma MultStepCtx.hw16 (C : MultStepCtx) : 16 ≤ 2 ^ C.w := by
  have h5 : 5 ≤ C.w := by have := C.hh1; have := C.hw3h; omega
  have : 2 ^ 5 ≤ 2 ^ C.w := Nat.pow_le_pow_right (by omega) h5
  omega
private lemma MultStepCtx.hpow_w (C : MultStepCtx) : 2 ^ C.h < 2 ^ C.w :=
  Nat.pow_lt_pow_right (by omega) (by have := C.hh1; have := C.hw3h; omega)
private lemma MultStepCtx.hKw_pos (C : MultStepCtx) : 1 ≤ C.K_w := by have := C.hLin1; have := C.hLK; omega
private lemma MultStepCtx.hp_w (C : MultStepCtx) : C.hp < 2 ^ C.w := by have := C.hhp_w; omega
private lemma MultStepCtx.hp1_w (C : MultStepCtx) : C.hp1 < 2 ^ C.w := by
  have := C.hhp_w; unfold MultStepCtx.hp1 multQNatStepSpace at *; omega
private lemma MultStepCtx.hp2_w (C : MultStepCtx) : C.hp2 < 2 ^ C.w := by
  have := C.hhp_w; unfold MultStepCtx.hp2 MultStepCtx.hp1 multQNatStepSpace at *; omega
private lemma MultStepCtx.q1_sub (C : MultStepCtx) : C.hp2 - C.K_w = C.q1 := by
  unfold MultStepCtx.q1 MultStepCtx.hp2; rw [Num.integerDivideSpace]; omega
private lemma MultStepCtx.q2_sub (C : MultStepCtx) : C.hp + multQNatStepSpace C.K_w - (C.K_w + 6) = C.q2 := by
  unfold MultStepCtx.q2 MultStepCtx.hp2 MultStepCtx.hp1 multQNatStepSpace
  simp only [Num.integerDivideSpace]
  omega
private lemma MultStepCtx.h2m0_cap (C : MultStepCtx) : 2 * C.m0 < Num.capacity C.h C.K_w := by
  have := C.hv1
  have := C.hnum_cap
  nlinarith
private lemma MultStepCtx.hp_le_hp1 (C : MultStepCtx) : C.hp ≤ C.hp1 := by
  unfold MultStepCtx.hp1; omega
private lemma MultStepCtx.hp_le_hp2 (C : MultStepCtx) : C.hp ≤ C.hp2 := by
  unfold MultStepCtx.hp2 MultStepCtx.hp1; omega
private lemma MultStepCtx.hp2_eq (C : MultStepCtx) :
    C.hp2 + Num.integerDivideSpace (C.K_w + 6) = C.hp + multQNatStepSpace C.K_w := by
  unfold MultStepCtx.hp2 MultStepCtx.hp1 multQNatStepSpace; omega

private structure MBaseRegs (C : MultStepCtx) (st : State) : Prop where
  r0 : st.regs 0 = C.wtE
  r1 : st.regs 1 = C.lenE
  r2 : st.regs 2 = C.qNatOut
  r3 : st.regs 3 = C.multOut
  r4 : st.regs 4 = C.svPtr
  r5 : st.regs 5 = C.svMinusOnePtr
  r6 : st.regs 6 = C.m0LimbsPtr
  r7 : st.regs 7 = C.edgeLimbsPtr
  r8 : st.regs 8 = C.numerPtr
  r9 : st.regs 9 = C.lenQPtr
  r10 : st.regs 10 = C.L_in
  r11 : st.regs 11 = C.K_w
  r12 : st.regs 12 = C.hp
  r13 : st.regs 13 = 2 ^ C.h

private lemma mBaseRegs_update_hi {C : MultStepCtx} {st : State} {mem' : ℕ → ℕ} {pos' r v : ℕ}
    (hb : MBaseRegs C st) (hr : 14 ≤ r) :
    MBaseRegs C { mem := mem', regs := Function.update st.regs r v, pos := pos' } :=
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
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r12,
   by dsimp; rw [Function.update_of_ne (by omega)]; exact hb.r13⟩

private lemma mBaseRegs_update_mem {C : MultStepCtx} {st : State} {mem' : ℕ → ℕ}
    (hb : MBaseRegs C st) :
    MBaseRegs C { mem := mem', regs := st.regs, pos := st.pos } :=
  ⟨hb.r0, hb.r1, hb.r2, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hb.r9, hb.r10, hb.r11, hb.r12, hb.r13⟩

private def MFrameBefore (C : MultStepCtx) (mem : ℕ → ℕ) : Prop :=
  ∀ a < C.edgeLimbsPtr, mem a = C.mem0 a

private def MFrameAfterMult (C : MultStepCtx) (mem : ℕ → ℕ) : Prop :=
  (∀ a < C.edgeLimbsPtr, a ≠ C.multOut → mem a = C.mem0 a) ∧ mem C.multOut = C.mj

private def MFrameFinal (C : MultStepCtx) (mem : ℕ → ℕ) : Prop :=
  (∀ a < C.edgeLimbsPtr, (a < C.qNatOut ∨ C.qNatOut + (C.K_w + 6) ≤ a) → a ≠ C.multOut →
      mem a = C.mem0 a) ∧
    mem C.multOut = C.mj ∧
    Num.Valid mem C.qNatOut C.h (C.K_w + 6) ∧
    Num.unsignedVal mem C.qNatOut C.h (C.K_w + 6) = C.qnat

private lemma mFrameBefore_vals {C : MultStepCtx} {mem : ℕ → ℕ} (hf : MFrameBefore C mem) :
    Num.Valid mem C.svPtr C.h C.K_w ∧ Num.unsignedVal mem C.svPtr C.h C.K_w = C.S_v ∧
      Num.Valid mem C.svMinusOnePtr C.h C.K_w ∧ Num.unsignedVal mem C.svMinusOnePtr C.h C.K_w = C.S_v - 1 ∧
      Num.Valid mem C.m0LimbsPtr C.h C.K_w ∧ Num.unsignedVal mem C.m0LimbsPtr C.h C.K_w = C.m0 ∧
      Num.Valid mem C.wtE C.h C.L_in ∧ Num.unsignedVal mem C.wtE C.h C.L_in = C.v_int := by
  have hord := C.order
  have hsv : ∀ i < C.K_w, mem (C.svPtr + i) = C.mem0 (C.svPtr + i) := fun i hi => hf _ (by omega)
  have hm1 : ∀ i < C.K_w, mem (C.svMinusOnePtr + i) = C.mem0 (C.svMinusOnePtr + i) := fun i hi => hf _ (by omega)
  have hm0 : ∀ i < C.K_w, mem (C.m0LimbsPtr + i) = C.mem0 (C.m0LimbsPtr + i) := fun i hi => hf _ (by omega)
  have hwt : ∀ i < C.L_in, mem (C.wtE + i) = C.mem0 (C.wtE + i) := fun i hi => hf _ (by omega)
  exact ⟨fun i hi => by rw [hsv i hi]; exact C.hsv_val i hi, by rw [Num.unsignedVal_congr hsv, C.hsv_u],
    fun i hi => by rw [hm1 i hi]; exact C.hsvm1_val i hi, by rw [Num.unsignedVal_congr hm1, C.hsvm1_u],
    fun i hi => by rw [hm0 i hi]; exact C.hm0_val i hi, by rw [Num.unsignedVal_congr hm0, C.hm0_u],
    fun i hi => by rw [hwt i hi]; exact C.hwt_val i hi, by rw [Num.unsignedVal_congr hwt, C.hwt_u]⟩

private lemma multQNat_part1 {w b K_AN h pos : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (C : MultStepCtx) (hCw : C.w = w) (hCh : C.h = h)
    (tail : Stmt) (Q : Outcome → State → Prop) (T_tail : ℕ)
    (htail : Triple w p (fun st => MBaseRegs C st ∧ st.regs 14 = C.hp1 ∧
      ZeroFrom st.mem C.hp1 ∧ MFrameBefore C st.mem ∧
      Num.Valid st.mem (C.hp + 4 * C.K_w) h C.K_w ∧
      Num.unsignedVal st.mem (C.hp + 4 * C.K_w) h C.K_w = C.m0 * C.v_int) tail Q fun _ => T_tail) :
    Triple w p (fun st => st = startState C.baseArgs C.mem0 pos)
      (.call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 7, .reg 11, .const 0] ;;
       .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 7, .reg 0, .reg 10] ;;
       .call 14 (lsfBaseMul b) [.reg 6, .reg 7, .reg 11, .reg 12] ;; tail)
      Q fun _ => (16 * C.K_w + 18) + (20 * C.L_in + 18) +
        (152 * C.K_w * C.K_w + 190 * C.K_w + 110) + T_tail + 3 := by
  subst hCw hCh
  have hord := C.order
  have hhp := C.hp_w; have hhp1 := C.hp1_w; have hLK := C.hLK
  have hw1 : 1 < 2 ^ C.w := by have := C.hw16; omega
  have h0_w : 0 < 2 ^ C.w := by omega
  have hmc_fill := lsfMemFill_meetsContract hw1 hp
  have hmc_copy := lsfMemCopy_meetsContract hw1 hp
  have hmc_mul := Num.multiply_meetsContract C.hh1 C.hw2h (lsfHasAt_mul hp)
  let S0 : State → Prop := fun st => st = startState C.baseArgs C.mem0 pos
  let S1 : State → Prop := fun st => MBaseRegs C st ∧ ZeroFrom st.mem C.hp ∧
    MFrameBefore C st.mem ∧ ∀ i < C.K_w, st.mem (C.edgeLimbsPtr + i) = 0
  let S2 : State → Prop := fun st => MBaseRegs C st ∧ ZeroFrom st.mem C.hp ∧
    MFrameBefore C st.mem ∧ Num.Valid st.mem C.edgeLimbsPtr C.h C.K_w ∧
    Num.unsignedVal st.mem C.edgeLimbsPtr C.h C.K_w = C.v_int
  have hs1 : Triple C.w p S0 (.call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 7, .reg 11, .const 0])
      (normalPost S1) fun _ => 16 * C.K_w + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.edgeLimbsPtr, C.K_w, 0]) hmc_fill
        (fun st hst => by
          subst hst
          exact evalArgs_cons (Expr.eval_reg_of_eq (by simp [MultStepCtx.baseArgs, startState]))
            (evalArgs_cons (Expr.eval_reg_of_eq (by simp [MultStepCtx.baseArgs, startState]))
              (evalArgs_cons (Expr.eval_const h0_w) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.edgeLimbsPtr, C.K_w, 0, rfl, by omega⟩)
        (fun st _ mem1 _ hst ⟨_, _, _, heq, _, hfill, hfr⟩ => by
          subst hst; simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hb0 : MBaseRegs C (startState C.baseArgs C.mem0 pos) := by
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [MultStepCtx.baseArgs, startState]
          refine ⟨mBaseRegs_update_hi hb0 (by omega), ?_, ?_, hfill⟩
          · intro a ha; dsimp; rw [hfr a (by right; omega)]; exact C.hzf0 a ha
          · intro a ha; dsimp; exact hfr a (Or.inl ha)))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memFillContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have hs2 : Triple C.w p S1 (.call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 7, .reg 0, .reg 10])
      (normalPost S2) fun _ => 20 * C.L_in + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.edgeLimbsPtr, C.wtE, C.L_in]) hmc_copy
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r7)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r0) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r10) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.edgeLimbsPtr, C.wtE, C.L_in, rfl, by omega, by omega, Or.inr (by omega)⟩)
        (fun st _ mem2 _ hst ⟨_, _, _, heq, _, hcp, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hsrc_st : ∀ i < C.L_in, st.mem (C.wtE + i) = C.mem0 (C.wtE + i) := fun i hi => hst.2.2.1 _ (by omega)
          have hval_e : Num.Valid mem2 C.edgeLimbsPtr C.h C.K_w := by
            refine valid_pad_zero (L := C.L_in) ?_ ?_
            · intro i hi; rw [hcp i hi, hsrc_st i hi]; exact C.hwt_val i hi
            · intro i hi1 hi2; rw [hfr _ (Or.inr (by omega))]; exact hst.2.2.2 i hi2
          have hu_e : Num.unsignedVal mem2 C.edgeLimbsPtr C.h C.K_w = C.v_int := by
            rw [unsignedVal_pad_zero hLK (fun i hi1 hi2 => by rw [hfr _ (Or.inr (by omega))]; exact hst.2.2.2 i hi2)]
            rw [Num.unsignedVal_congr fun i hi => by rw [hcp i hi, hsrc_st i hi], C.hwt_u]
          refine ⟨mBaseRegs_update_hi hst.1 (by omega), ?_, ?_, hval_e, hu_e⟩
          · intro a ha; dsimp; rw [hfr a (by right; omega)]; exact hst.2.1 a ha
          · intro a ha; dsimp; rw [hfr a (Or.inl ha)]; exact hst.2.2.1 a ha))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memCopyContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have hs3 : Triple C.w p S2 (.call 14 (lsfBaseMul b) [.reg 6, .reg 7, .reg 11, .reg 12])
      (normalPost fun st => MBaseRegs C st ∧ st.regs 14 = C.hp1 ∧
        ZeroFrom st.mem C.hp1 ∧ MFrameBefore C st.mem ∧
        Num.Valid st.mem (C.hp + 4 * C.K_w) C.h C.K_w ∧
        Num.unsignedVal st.mem (C.hp + 4 * C.K_w) C.h C.K_w = C.m0 * C.v_int)
      fun _ => 152 * C.K_w * C.K_w + 190 * C.K_w + 110 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.m0LimbsPtr, C.edgeLimbsPtr, C.K_w, C.hp]) hmc_mul
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r6)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r7)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r11)
              (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r12) (evalArgs_nil _ _)))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        (fun _ hst => ⟨⟨C.m0LimbsPtr, C.edgeLimbsPtr, C.K_w, C.hp, rfl, by omega, by omega,
          (mFrameBefore_vals hst.2.2.1).2.2.2.2.1, hst.2.2.2.1⟩, hst.2.1, by simp [heapArg]; exact hhp1⟩)
        (fun st _ mem3 _ hst ⟨hvret, _, _, hpres, hzf3, hval2, hint2⟩ => by
          simp [heapArg, List.getD_eq_getElem?_getD] at hvret hpres hval2 hint2
          have hm0v := mFrameBefore_vals hst.2.2.1
          have hm0_int := intVal_eq_cast_of_uVal hm0v.2.2.2.2.2.1 C.h2m0_cap
          have hed_int := intVal_eq_cast_of_uVal hst.2.2.2.2
            (by have := C.hv_cap; have := lsfCapacity_mono (h := C.h) hLK; omega)
          have hmul_int : Num.intVal mem3 (C.hp + 4 * C.K_w) C.h (2 * C.K_w) = ((C.m0 * C.v_int : ℕ) : ℤ) := by
            rw [hint2, hm0_int, hed_int]; push_cast; ring
          have hlow := low_limbs_of_mul_lt hval2 hmul_int (by have := C.hnum_cap; omega)
          rw [hvret] at hzf3
          refine ⟨mBaseRegs_update_hi hst.1 (by omega), by dsimp; rw [Function.update_self]; exact hvret,
            by change ZeroFrom mem3 C.hp1; unfold MultStepCtx.hp1; exact hzf3,
            fun a ha => by dsimp; rw [hpres a (by omega)]; exact hst.2.2.1 a ha,
            hlow.1, hlow.2.1⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, Num.multiplyContract, heapContract,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; nlinarith)
  exact (Triple.seq_normal_const hs1 (Triple.seq_normal_const hs2 (Triple.seq_normal_const hs3 htail))).mono_cost
    fun _ _ => by omega

private lemma multQNat_part2 {w b K_AN h f_l2w : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hproc_l2w : p.procs[f_l2w]? = some limbsToWordProc)
    (C : MultStepCtx) (hCw : C.w = w) (hCh : C.h = h)
    (tail : Stmt) (Q : Outcome → State → Prop) (T_tail : ℕ)
    (htail : Triple w p (fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
      st.regs 17 = C.mj ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem) tail Q fun _ => T_tail) :
    Triple w p
      (fun st => MBaseRegs C st ∧ st.regs 14 = C.hp1 ∧
        ZeroFrom st.mem C.hp1 ∧ MFrameBefore C st.mem ∧
        Num.Valid st.mem (C.hp + 4 * C.K_w) h C.K_w ∧
        Num.unsignedVal st.mem (C.hp + 4 * C.K_w) h C.K_w = C.m0 * C.v_int)
      (.assign 15 (.bin .add (.reg 12) (.bin .mul (.const 4) (.reg 11))) ;;
       .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 8, .reg 15, .reg 11] ;;
       .call 19 (lsfBaseUtils b + idxUtilAddTo) [.reg 8, .reg 5, .reg 11] ;;
       .call 16 (lsfBaseIntDiv b) [.reg 8, .reg 4, .reg 11, .reg 14] ;;
       .assign 15 (.bin .sub (.reg 16) (.reg 11)) ;;
       .call 17 f_l2w [.reg 15, .reg 11, .reg 13] ;;
       .store (.reg 3) (.reg 17) ;; tail)
      Q fun _ => 300 * C.K_w * C.K_w + 950 * C.K_w + 500 + T_tail := by
  subst hCw hCh
  have hord := C.order
  have hhp1 := C.hp1_w; have hhp2 := C.hp2_w
  have hw1 : 1 < 2 ^ C.w := by have := C.hw16; omega
  have h4_w : 4 < 2 ^ C.w := by have := C.hw16; omega
  have h4Kw_w : 4 * C.K_w < 2 ^ C.w := by unfold MultStepCtx.hp1 at hhp1; omega
  have hp4Kw_w : C.hp + 4 * C.K_w < 2 ^ C.w := by unfold MultStepCtx.hp1 at hhp1; omega
  have hKw_w : C.K_w < 2 ^ C.w := by omega
  have hpow_w : 2 ^ C.h < 2 ^ C.w := C.hpow_w
  have hmc_copy := lsfMemCopy_meetsContract hw1 hp
  have hmc_addTo := lsfAddTo_meetsContract (w := C.w) hp
  have hmc_div := Num.integerDivide_meetsContract C.hh1 C.hw3h (lsfHasAt_intDiv hp)
  have hmc_l2w := limbsToWord_meetsContract (w := C.w) (h := C.h) hproc_l2w
  let S3 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 14 = C.hp1 ∧
    ZeroFrom st.mem C.hp1 ∧ MFrameBefore C st.mem ∧
    Num.Valid st.mem (C.hp + 4 * C.K_w) C.h C.K_w ∧
    Num.unsignedVal st.mem (C.hp + 4 * C.K_w) C.h C.K_w = C.m0 * C.v_int
  let S4 : State → Prop := fun st => S3 st ∧ st.regs 15 = C.hp + 4 * C.K_w
  let S5 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 14 = C.hp1 ∧
    ZeroFrom st.mem C.hp1 ∧ MFrameBefore C st.mem ∧
    Num.Valid st.mem C.numerPtr C.h C.K_w ∧
    Num.unsignedVal st.mem C.numerPtr C.h C.K_w = C.m0 * C.v_int
  let S6 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 14 = C.hp1 ∧
    ZeroFrom st.mem C.hp1 ∧ MFrameBefore C st.mem ∧
    Num.Valid st.mem C.numerPtr C.h C.K_w ∧
    Num.unsignedVal st.mem C.numerPtr C.h C.K_w = C.m0 * C.v_int + (C.S_v - 1)
  let S7 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
    ZeroFrom st.mem C.hp2 ∧ MFrameBefore C st.mem ∧
    Num.Valid st.mem C.q1 C.h C.K_w ∧ Num.unsignedVal st.mem C.q1 C.h C.K_w = C.mj
  let S8 : State → Prop := fun st => S7 st ∧ st.regs 15 = C.q1
  let S9 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
    st.regs 17 = C.mj ∧ ZeroFrom st.mem C.hp2 ∧ MFrameBefore C st.mem
  have hs4 : Triple C.w p S3 (.assign 15 (.bin .add (.reg 12) (.bin .mul (.const 4) (.reg 11))))
      (normalPost S4) fun _ => 6 :=
    Triple.assign
      (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.r12)
        (Expr.eval_mul (Expr.eval_const h4_w) (Expr.eval_reg_of_eq hst.1.r11) h4Kw_w) hp4Kw_w)
      fun _ hst => ⟨⟨mBaseRegs_update_hi hst.1 (by omega), by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
        hst.2.2⟩, by dsimp; rw [Function.update_self]⟩
  have hs5 : Triple C.w p S4 (.call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 8, .reg 15, .reg 11])
      (normalPost S5) fun _ => 20 * C.K_w + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.numerPtr, C.hp + 4 * C.K_w, C.K_w]) hmc_copy
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r8)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.2) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r11) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.numerPtr, C.hp + 4 * C.K_w, C.K_w, rfl, by omega, by unfold MultStepCtx.hp1 at hhp1; omega, Or.inl (by omega)⟩)
        (fun _ _ mem4 _ hst ⟨_, _, _, heq, _, hcp, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          refine ⟨mBaseRegs_update_hi hst.1.1 (by omega), by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
            fun a ha => by dsimp; have hle := C.hp_le_hp1; rw [hfr a (Or.inr (by omega))]; exact hst.1.2.2.1 a ha,
            fun a ha => by dsimp; rw [hfr a (Or.inl (by omega))]; exact hst.1.2.2.2.1 a ha,
            fun i hi => by dsimp; rw [hcp i hi]; exact hst.1.2.2.2.2.1 i hi,
            by dsimp; rw [Num.unsignedVal_congr hcp]; exact hst.1.2.2.2.2.2⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memCopyContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have hs6 : Triple C.w p S5 (.call 19 (lsfBaseUtils b + idxUtilAddTo) [.reg 8, .reg 5, .reg 11])
      (normalPost S6) fun _ => 55 * C.K_w + 25 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.numerPtr, C.svMinusOnePtr, C.K_w]) hmc_addTo
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r8)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r5) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r11) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ hst => ⟨C.numerPtr, C.svMinusOnePtr, C.K_w, rfl, C.hh1, C.hw2h, by omega, by omega,
          Or.inr (by omega), hst.2.2.2.2.1, (mFrameBefore_vals hst.2.2.2.1).2.2.1⟩)
        (fun _ _ mem5 _ hst ⟨_, _, _, heq, _, hval5, hu5, _, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hm1u := (mFrameBefore_vals hst.2.2.2.1).2.2.2.1
          have hmod : (C.m0 * C.v_int + (C.S_v - 1)) % Num.capacity C.h C.K_w = C.m0 * C.v_int + (C.S_v - 1) :=
            Nat.mod_eq_of_lt (by have := C.hnum_cap; omega)
          refine ⟨mBaseRegs_update_hi hst.1 (by omega), by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
            fun a ha => by dsimp; have hle := C.hp_le_hp1; rw [hfr a (Or.inr (by omega))]; exact hst.2.2.1 a ha,
            fun a ha => by dsimp; rw [hfr a (Or.inl (by omega))]; exact hst.2.2.2.1 a ha,
            hval5, by rw [hu5, hst.2.2.2.2.2, hm1u, hmod]⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, addToContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have hs7 : Triple C.w p S6 (.call 16 (lsfBaseIntDiv b) [.reg 8, .reg 4, .reg 11, .reg 14])
      (normalPost S7) fun _ => 300 * C.K_w * C.K_w + 824 * C.K_w + 410 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.numerPtr, C.svPtr, C.K_w, C.hp1]) hmc_div
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r8)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r4)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.r11) (evalArgs_cons (Expr.eval_reg_of_eq hst.2.1) (evalArgs_nil _ _)))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        (fun st hst => by
          have hsv := mFrameBefore_vals hst.2.2.2.1
          have hsv_int := intVal_eq_cast_of_uVal hsv.2.1 C.hSv_cap
          have hne0 : Num.intVal st.mem C.svPtr C.h C.K_w ≠ 0 := by rw [hsv_int]; have := C.hSv1; omega
          exact ⟨⟨C.numerPtr, C.svPtr, C.K_w, C.hp1, rfl, by unfold MultStepCtx.hp1; omega,
            by unfold MultStepCtx.hp1; omega, hst.2.2.2.2.1, hsv.1, hne0⟩, hst.2.2.1,
            by simp [heapArg]; change C.hp2 < 2 ^ C.w; exact hhp2⟩)
        (fun st _ mem6 _ hst ⟨hvret, _, _, hpres, hzf6, hq_val, hq_int⟩ => by
          simp [heapArg, List.getD_eq_getElem?_getD] at hvret hpres hq_val hq_int
          have hsv := mFrameBefore_vals hst.2.2.2.1
          have hsv_int := intVal_eq_cast_of_uVal hsv.2.1 C.hSv_cap
          have hnum_int := intVal_eq_cast_of_uVal hst.2.2.2.2.2 C.hnum_cap
          have hadd_eq : C.m0 * C.v_int + (C.S_v - 1) = C.m0 * C.v_int + C.S_v - 1 := by have := C.hSv1; omega
          have hfl : Num.floorDiv (Num.intVal st.mem C.numerPtr C.h C.K_w) (Num.intVal st.mem C.svPtr C.h C.K_w) = (C.mj : ℤ) := by
            rw [hnum_int, hsv_int, floorDiv_natCast, hadd_eq]; rfl
          have hmj_cap : 2 * C.mj < Num.capacity C.h C.K_w := by
            rw [show C.mj = (C.m0 * C.v_int + (C.S_v - 1)) / C.S_v by rw [MultStepCtx.mj, hadd_eq]]
            exact div_lt_cap_half_of_numer C.hSv1 C.hnum_cap
          have hmj_u : Num.unsignedVal mem6 C.q1 C.h C.K_w = C.mj := by
            change Num.unsignedVal mem6 (C.hp1 + 2 * C.K_w + Num.unsignedDivideSpace C.K_w) C.h C.K_w = C.mj
            exact nat_eq_unsignedVal_of_intVal hq_val (by rw [hq_int, hfl, wrap_of_nat_lt hmj_cap])
          rw [hvret] at hzf6
          refine ⟨mBaseRegs_update_hi hst.1 (by omega), by dsimp; rw [Function.update_self]; exact hvret,
            by change ZeroFrom mem6 C.hp2; unfold MultStepCtx.hp2; exact hzf6,
            fun a ha => by dsimp; rw [hpres a (by unfold MultStepCtx.hp1; omega)]; exact hst.2.2.2.1 a ha,
            hq_val, hmj_u⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, Num.integerDivideContract, heapContract,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; nlinarith)
  have hs8 : Triple C.w p S7 (.assign 15 (.bin .sub (.reg 16) (.reg 11))) (normalPost S8) fun _ => 4 :=
    Triple.assign
      (fun _ hst => Expr.eval_sub (Expr.eval_reg_of_eq hst.2.1) (Expr.eval_reg_of_eq hst.1.r11) hhp2)
      fun _ hst => ⟨⟨mBaseRegs_update_hi hst.1 (by omega),
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1, hst.2.2⟩,
        by dsimp; rw [Function.update_self, C.q1_sub]⟩
  have hq1_end_w : C.q1 + C.K_w < 2 ^ C.w := by rw [← C.q1_sub]; omega
  have hs9 : Triple C.w p S8 (.call 17 f_l2w [.reg 15, .reg 11, .reg 13]) (normalPost S9) fun _ => 45 * C.K_w + 25 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.q1, C.K_w, 2 ^ C.h]) hmc_l2w
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.2)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r11) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r13) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ hst => ⟨C.q1, C.K_w, 2 ^ C.h, rfl, rfl, C.hh1, C.hKw_pos, C.hw16, hq1_end_w, hKw_w, hpow_w,
          hst.1.2.2.2.2.1, by rw [hst.1.2.2.2.2.2]; exact lt_of_le_of_lt C.hmj_bd C.hm02w⟩)
        (fun st _ mem7 _ hst ⟨_, _, _, heq, hmem7, hret⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩; subst hmem7
          refine ⟨mBaseRegs_update_hi hst.1.1 (by omega),
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
            by dsimp; rw [Function.update_self, hret, hst.1.2.2.2.2.2],
            hst.1.2.2.1, hst.1.2.2.2.1⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, limbsToWordContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have hs10 : Triple C.w p S9 (.store (.reg 3) (.reg 17))
      (normalPost fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
        st.regs 17 = C.mj ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem) fun _ => 3 :=
    Triple.store (fun _ hst => Expr.eval_reg_of_eq hst.1.r3) (fun _ hst => Expr.eval_reg_of_eq hst.2.2.1)
      fun _ hst => ⟨mBaseRegs_update_mem hst.1, hst.2.1, hst.2.2.1,
        fun a ha => by
          dsimp; have hle := C.hp_le_hp2
          rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1 a ha,
        ⟨fun a ha hne => by dsimp; rw [Function.update_of_ne hne]; exact hst.2.2.2.2 a ha,
         by dsimp; rw [Function.update_self]⟩⟩
  have hcomp :=
    Triple.seq_normal_const hs4 (Triple.seq_normal_const hs5 (Triple.seq_normal_const hs6
      (Triple.seq_normal_const hs7 (Triple.seq_normal_const hs8 (Triple.seq_normal_const hs9
        (Triple.seq_normal_const hs10 htail))))))
  exact hcomp.mono_cost fun _ _ => by nlinarith

private lemma multQNat_part3 {w b K_AN h : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (C : MultStepCtx) (hCw : C.w = w) (hCh : C.h = h)
    (tail : Stmt) (Q : Outcome → State → Prop) (T_tail : ℕ)
    (htail : Triple w p (fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
      st.regs 18 = C.K_w + 6 ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem ∧
      Num.Valid st.mem C.numerPtr h (C.K_w + 6) ∧
      Num.unsignedVal st.mem C.numerPtr h (C.K_w + 6) = C.mj * 2 ^ (h * (C.L_in + 4))) tail Q fun _ => T_tail) :
    Triple w p
      (fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
        st.regs 17 = C.mj ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem)
      (.assign 18 (.bin .add (.reg 11) (.const 6)) ;;
       .assign 20 (.bin .add (.reg 10) (.const 4)) ;;
       .assign 21 (.bin .sub (.reg 18) (.reg 20)) ;;
       .assign 22 (.bin .add (.reg 8) (.reg 20)) ;;
       .call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 8, .reg 20, .const 0] ;;
       .call 19 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 22, .reg 21, .reg 17] ;; tail)
      Q fun _ => 50 * (C.K_w + 6) + 80 + T_tail := by
  subst hCw hCh
  have hord := C.order
  have hhp := C.hp_w; have hLK := C.hLK; have hLin := C.hLin1
  have hw1 : 1 < 2 ^ C.w := by have := C.hw16; omega
  have h0_w : 0 < 2 ^ C.w := by omega
  have h4_w : 4 < 2 ^ C.w := by have := C.hw16; omega
  have h6_w : 6 < 2 ^ C.w := by have := C.hw16; omega
  have hKq_w : C.K_w + 6 < 2 ^ C.w := by omega
  have hL4_w : C.L_in + 4 < 2 ^ C.w := by omega
  have hnumL4_w : C.numerPtr + (C.L_in + 4) < 2 ^ C.w := by omega
  have hmc_fill := lsfMemFill_meetsContract hw1 hp
  have hmc_w2l := lsfWordToLimbs_meetsContract (w := C.w) (K_AN := K_AN) hp
  let T0 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
    st.regs 17 = C.mj ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem
  let T1 : State → Prop := fun st => T0 st ∧ st.regs 18 = C.K_w + 6
  let T2 : State → Prop := fun st => T1 st ∧ st.regs 20 = C.L_in + 4
  let T3 : State → Prop := fun st => T2 st ∧ st.regs 21 = C.K_w + 6 - (C.L_in + 4)
  let T4 : State → Prop := fun st => T3 st ∧ st.regs 22 = C.numerPtr + (C.L_in + 4)
  let T5 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
    st.regs 17 = C.mj ∧ st.regs 18 = C.K_w + 6 ∧ st.regs 20 = C.L_in + 4 ∧
    st.regs 21 = C.K_w + 6 - (C.L_in + 4) ∧ st.regs 22 = C.numerPtr + (C.L_in + 4) ∧
    ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem ∧ ∀ i < C.L_in + 4, st.mem (C.numerPtr + i) = 0
  have ht1 : Triple C.w p T0 (.assign 18 (.bin .add (.reg 11) (.const 6))) (normalPost T1) fun _ => 4 :=
    Triple.assign (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.r11) (Expr.eval_const h6_w) hKq_w)
      fun _ hst => ⟨⟨mBaseRegs_update_hi hst.1 (by omega),
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1, hst.2.2.2⟩,
        by dsimp; rw [Function.update_self]⟩
  have ht2 : Triple C.w p T1 (.assign 20 (.bin .add (.reg 10) (.const 4))) (normalPost T2) fun _ => 4 :=
    Triple.assign (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.1.r10) (Expr.eval_const h4_w) hL4_w)
      fun _ hst => ⟨⟨⟨mBaseRegs_update_hi hst.1.1 (by omega),
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.2.1, hst.1.2.2.2⟩,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2⟩, by dsimp; rw [Function.update_self]⟩
  have ht3 : Triple C.w p T2 (.assign 21 (.bin .sub (.reg 18) (.reg 20))) (normalPost T3) fun _ => 4 :=
    Triple.assign (fun _ hst => Expr.eval_sub (Expr.eval_reg_of_eq hst.1.2) (Expr.eval_reg_of_eq hst.2) hKq_w)
      fun _ hst => ⟨⟨⟨⟨mBaseRegs_update_hi hst.1.1.1 (by omega),
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.2.1,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.2.2.1, hst.1.1.2.2.2⟩,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2⟩,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2⟩, by dsimp; rw [Function.update_self]⟩
  have ht4 : Triple C.w p T3 (.assign 22 (.bin .add (.reg 8) (.reg 20))) (normalPost T4) fun _ => 4 :=
    Triple.assign (fun _ hst => Expr.eval_add (Expr.eval_reg_of_eq hst.1.1.1.1.r8) (Expr.eval_reg_of_eq hst.1.2) hnumL4_w)
      fun _ hst => ⟨⟨⟨⟨⟨mBaseRegs_update_hi hst.1.1.1.1 (by omega),
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.1.2.1,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.1.2.2.1, hst.1.1.1.2.2.2⟩,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.2⟩,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2⟩,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2⟩, by dsimp; rw [Function.update_self]⟩
  have ht5 : Triple C.w p T4 (.call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 8, .reg 20, .const 0])
      (normalPost T5) fun _ => 16 * (C.K_w + 6) + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.numerPtr, C.L_in + 4, 0]) hmc_fill
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.1.1.1.r8)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.2) (evalArgs_cons (Expr.eval_const h0_w) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.numerPtr, C.L_in + 4, 0, rfl, by omega⟩)
        (fun _ _ mem1 _ hst ⟨_, _, _, heq, _, hfill, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          refine ⟨mBaseRegs_update_hi hst.1.1.1.1.1 (by omega),
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.1.1.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.1.1.2.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.1.2,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.1.2,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2,
            fun a ha => by dsimp; have hle := C.hp_le_hp2; rw [hfr a (Or.inr (by omega))]; exact hst.1.1.1.1.2.2.2.1 a ha,
            ⟨fun a ha hne => by dsimp; rw [hfr a (Or.inl (by omega))]; exact hst.1.1.1.1.2.2.2.2.1 a ha hne,
             by dsimp; rw [hfr _ (Or.inl (by omega))]; exact hst.1.1.1.1.2.2.2.2.2⟩,
            hfill⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memFillContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have ht6 : Triple C.w p T5 (.call 19 (lsfBaseUtils b + idxUtilWordToLimbs) [.reg 22, .reg 21, .reg 17])
      (normalPost fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
        st.regs 18 = C.K_w + 6 ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem ∧
        Num.Valid st.mem C.numerPtr C.h (C.K_w + 6) ∧
        Num.unsignedVal st.mem C.numerPtr C.h (C.K_w + 6) = C.mj * 2 ^ (C.h * (C.L_in + 4)))
      fun _ => 25 * (C.K_w + 6) + 28 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.numerPtr + (C.L_in + 4), C.K_w + 6 - (C.L_in + 4), C.mj]) hmc_w2l
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.2.2.2.1)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.2.2.2.1) (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.1) (evalArgs_nil _ _))))
        (fun _ _ v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> [exact hnumL4_w; omega; exact lt_of_le_of_lt C.hmj_bd C.hm02w])
        (fun _ _ => ⟨C.numerPtr + (C.L_in + 4), C.K_w + 6 - (C.L_in + 4), C.mj, rfl, C.hh1,
          by simpa [Num.base] using C.hpow_w, by omega⟩)
        (fun _ _ mem2 _ hst ⟨_, _, _, heq, _, hval_hi, hu_hi, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hlo : ∀ i < C.L_in + 4, mem2 (C.numerPtr + i) = 0 := fun i hi => by
            rw [hfr _ (Or.inl (by omega))]; exact hst.2.2.2.2.2.2.2.2.2 i hi
          have hval_full : Num.Valid mem2 C.numerPtr C.h (C.K_w + 6) := by
            intro i hi
            by_cases hlt : i < C.L_in + 4
            · rw [hlo i hlt]; exact Num.base_pos C.h
            · rw [show C.numerPtr + i = C.numerPtr + (C.L_in + 4) + (i - (C.L_in + 4)) by omega]
              exact hval_hi (i - (C.L_in + 4)) (by omega)
          have hmj_lt_cap : C.mj < Num.capacity C.h (C.K_w + 6 - (C.L_in + 4)) := by
            have : C.mj ≤ 2 * C.m0 := C.hmj_bd
            have := C.hmj_rem_cap
            omega
          have hu_full : Num.unsignedVal mem2 C.numerPtr C.h (C.K_w + 6) = C.mj * 2 ^ (C.h * (C.L_in + 4)) := by
            rw [unsignedVal_zero_lo_hi (by omega) hlo]
            rw [hu_hi, Nat.mod_eq_of_lt hmj_lt_cap, Num.capacity, Num.base, ← pow_mul]
            ring
          refine ⟨mBaseRegs_update_hi hst.1 (by omega),
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.2.1,
            fun a ha => by dsimp; have hle := C.hp_le_hp2; rw [hfr a (Or.inr (by omega))]; exact hst.2.2.2.2.2.2.2.1 a ha,
            ⟨fun a ha hne => by dsimp; rw [hfr a (Or.inl (by omega))]; exact hst.2.2.2.2.2.2.2.2.1.1 a ha hne,
             by dsimp; rw [hfr _ (Or.inl (by omega))]; exact hst.2.2.2.2.2.2.2.2.1.2⟩,
            hval_full, hu_full⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, wordToLimbsContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  exact (Triple.seq_normal_const ht1 (Triple.seq_normal_const ht2 (Triple.seq_normal_const ht3
    (Triple.seq_normal_const ht4 (Triple.seq_normal_const ht5 (Triple.seq_normal_const ht6 htail)))))).mono_cost
    fun _ _ => by omega

private lemma multQNat_part4 {w b K_AN h : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (C : MultStepCtx) (hCw : C.w = w) (hCh : C.h = h) :
    Triple w p
      (fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
        st.regs 18 = C.K_w + 6 ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem ∧
        Num.Valid st.mem C.numerPtr h (C.K_w + 6) ∧
        Num.unsignedVal st.mem C.numerPtr h (C.K_w + 6) = C.mj * 2 ^ (h * (C.L_in + 4)))
      (.call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 9, .reg 18, .const 0] ;;
       .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 9, .reg 1, .reg 10] ;;
       .call 16 (lsfBaseIntDiv b) [.reg 8, .reg 9, .reg 18, .reg 16] ;;
       .assign 15 (.bin .sub (.reg 16) (.reg 18)) ;;
       .call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 2, .reg 15, .reg 18] ;;
       .ret (.reg 16))
      (retPost fun ret st => ret = C.hp + multQNatStepSpace C.K_w ∧ ZeroFrom st.mem ret ∧ MFrameFinal C st.mem)
      fun _ => 300 * (C.K_w + 6) * (C.K_w + 6) + 920 * (C.K_w + 6) + 500 := by
  subst hCw hCh
  have hord := C.order
  have hhp := C.hp_w; have hLK := C.hLK; have hhp2 := C.hp2_w; have hhp3 := C.hhp_w
  have hw1 : 1 < 2 ^ C.w := by have := C.hw16; omega
  have h0_w : 0 < 2 ^ C.w := by omega
  have hmc_fill := lsfMemFill_meetsContract hw1 hp
  have hmc_copy := lsfMemCopy_meetsContract hw1 hp
  have hmc_div := Num.integerDivide_meetsContract C.hh1 C.hw3h (lsfHasAt_intDiv hp)
  let T6 : State → Prop := fun st => MBaseRegs C st ∧ st.regs 16 = C.hp2 ∧
    st.regs 18 = C.K_w + 6 ∧ ZeroFrom st.mem C.hp2 ∧ MFrameAfterMult C st.mem ∧
    Num.Valid st.mem C.numerPtr C.h (C.K_w + 6) ∧
    Num.unsignedVal st.mem C.numerPtr C.h (C.K_w + 6) = C.mj * 2 ^ (C.h * (C.L_in + 4))
  let T7 : State → Prop := fun st => T6 st ∧ ∀ i < C.K_w + 6, st.mem (C.lenQPtr + i) = 0
  let T8 : State → Prop := fun st => T6 st ∧ Num.Valid st.mem C.lenQPtr C.h (C.K_w + 6) ∧
    Num.unsignedVal st.mem C.lenQPtr C.h (C.K_w + 6) = C.ℓ_int
  let T9 : State → Prop := fun st => MBaseRegs C st ∧
    st.regs 16 = C.hp + multQNatStepSpace C.K_w ∧ st.regs 18 = C.K_w + 6 ∧
    ZeroFrom st.mem (C.hp + multQNatStepSpace C.K_w) ∧ MFrameAfterMult C st.mem ∧
    Num.Valid st.mem C.q2 C.h (C.K_w + 6) ∧ Num.unsignedVal st.mem C.q2 C.h (C.K_w + 6) = C.qnat
  let T10 : State → Prop := fun st => T9 st ∧ st.regs 15 = C.q2
  have ht7 : Triple C.w p T6 (.call 19 (lsfBaseUtils b + idxUtilMemFill) [.reg 9, .reg 18, .const 0])
      (normalPost T7) fun _ => 16 * (C.K_w + 6) + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.lenQPtr, C.K_w + 6, 0]) hmc_fill
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.r9)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.2.2.1) (evalArgs_cons (Expr.eval_const h0_w) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.lenQPtr, C.K_w + 6, 0, rfl, by omega⟩)
        (fun _ _ mem3 _ hst ⟨_, _, _, heq, _, hfill, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          refine ⟨⟨mBaseRegs_update_hi hst.1 (by omega),
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1,
            fun a ha => by dsimp; have hle := C.hp_le_hp2; rw [hfr a (Or.inr (by omega))]; exact hst.2.2.2.1 a ha,
            ⟨fun a ha hne => by dsimp; rw [hfr a (Or.inl (by omega))]; exact hst.2.2.2.2.1.1 a ha hne,
             by dsimp; rw [hfr _ (Or.inl (by omega))]; exact hst.2.2.2.2.1.2⟩,
            fun i hi => by dsimp; rw [hfr _ (Or.inl (by omega))]; exact hst.2.2.2.2.2.1 i hi,
            by dsimp; rw [Num.unsignedVal_congr fun i hi => hfr _ (Or.inl (by omega))]; exact hst.2.2.2.2.2.2⟩, hfill⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memFillContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have ht8 : Triple C.w p T7 (.call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 9, .reg 1, .reg 10])
      (normalPost T8) fun _ => 20 * C.L_in + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.lenQPtr, C.lenE, C.L_in]) hmc_copy
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r9)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r1) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r10) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.lenQPtr, C.lenE, C.L_in, rfl, by omega, by omega, Or.inr (by omega)⟩)
        (fun st _ mem4 _ hst ⟨_, _, _, heq, _, hcp, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          have hlen_mem : ∀ i < C.L_in, st.mem (C.lenE + i) = C.mem0 (C.lenE + i) := fun i hi =>
            hst.1.2.2.2.2.1.1 _ (by omega) (by omega)
          have hval_lq : Num.Valid mem4 C.lenQPtr C.h (C.K_w + 6) := by
            refine valid_pad_zero (L := C.L_in) ?_ ?_
            · intro i hi; rw [hcp i hi, hlen_mem i hi]; exact C.hlen_val i hi
            · intro i hi1 hi2; rw [hfr _ (Or.inr (by omega))]; exact hst.2 i hi2
          have hu_lq : Num.unsignedVal mem4 C.lenQPtr C.h (C.K_w + 6) = C.ℓ_int := by
            rw [unsignedVal_pad_zero (L := C.L_in) (K := C.K_w + 6) (by omega)
              (fun i hi1 hi2 => by rw [hfr _ (Or.inr (by omega))]; exact hst.2 i hi2)]
            rw [Num.unsignedVal_congr fun i hi => by rw [hcp i hi, hlen_mem i hi]]
            exact C.hlen_u
          refine ⟨⟨mBaseRegs_update_hi hst.1.1 (by omega),
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.2.1,
            fun a ha => by dsimp; have hle := C.hp_le_hp2; rw [hfr a (Or.inr (by omega))]; exact hst.1.2.2.2.1 a ha,
            ⟨fun a ha hne => by dsimp; rw [hfr a (Or.inl (by omega))]; exact hst.1.2.2.2.2.1.1 a ha hne,
             by dsimp; rw [hfr _ (Or.inl (by omega))]; exact hst.1.2.2.2.2.1.2⟩,
            fun i hi => by dsimp; rw [hfr _ (Or.inl (by omega))]; exact hst.1.2.2.2.2.2.1 i hi,
            by dsimp; rw [Num.unsignedVal_congr fun i hi => hfr _ (Or.inl (by omega))]; exact hst.1.2.2.2.2.2.2⟩,
            hval_lq, hu_lq⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memCopyContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have ht9 : Triple C.w p T8 (.call 16 (lsfBaseIntDiv b) [.reg 8, .reg 9, .reg 18, .reg 16])
      (normalPost T9) fun _ => 300 * (C.K_w + 6) * (C.K_w + 6) + 824 * (C.K_w + 6) + 410 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.numerPtr, C.lenQPtr, C.K_w + 6, C.hp2]) hmc_div
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r8)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r9)
            (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.1) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.1) (evalArgs_nil _ _)))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        (fun st hst => by
          have hlq_int := intVal_eq_cast_of_uVal hst.2.2
            (by have := C.hℓ_cap; have := lsfCapacity_mono (h := C.h) (show C.L_in ≤ C.K_w + 6 by omega); omega)
          have hne0 : Num.intVal st.mem C.lenQPtr C.h (C.K_w + 6) ≠ 0 := by rw [hlq_int]; have := C.hℓ1; omega
          exact ⟨⟨C.numerPtr, C.lenQPtr, C.K_w + 6, C.hp2, rfl, by unfold MultStepCtx.hp2 MultStepCtx.hp1; omega,
            by unfold MultStepCtx.hp2 MultStepCtx.hp1; omega, hst.1.2.2.2.2.2.1, hst.2.1, hne0⟩,
            hst.1.2.2.2.1, by simp [heapArg]; rw [C.hp2_eq]; exact hhp3⟩)
        (fun st _ mem5 _ hst ⟨hvret, _, _, hpres, hzf5, hq_val, hq_int⟩ => by
          simp [heapArg, List.getD_eq_getElem?_getD] at hvret hpres hq_val hq_int
          have hlq_int := intVal_eq_cast_of_uVal hst.2.2
            (by have := C.hℓ_cap; have := lsfCapacity_mono (h := C.h) (show C.L_in ≤ C.K_w + 6 by omega); omega)
          have hnum2_cap : 2 * (C.mj * 2 ^ (C.h * (C.L_in + 4))) < Num.capacity C.h (C.K_w + 6) := by
            have hle : 2 * (C.mj * 2 ^ (C.h * (C.L_in + 4))) ≤ 4 * (2 * C.m0) * 2 ^ (C.h * (C.L_in + 4)) := by
              calc 2 * (C.mj * 2 ^ (C.h * (C.L_in + 4)))
                  ≤ 2 * ((2 * C.m0) * 2 ^ (C.h * (C.L_in + 4))) := by gcongr; exact C.hmj_bd
                _ ≤ 4 * (2 * C.m0) * 2 ^ (C.h * (C.L_in + 4)) := by
                  rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
            have := C.hq_cap; omega
          have hnum2_int := intVal_eq_cast_of_uVal hst.1.2.2.2.2.2.2 hnum2_cap
          have hfl : Num.floorDiv (Num.intVal st.mem C.numerPtr C.h (C.K_w + 6))
              (Num.intVal st.mem C.lenQPtr C.h (C.K_w + 6)) = (C.qnat : ℤ) := by
            rw [hnum2_int, hlq_int, floorDiv_natCast]; rfl
          have hqnat_cap : 2 * C.qnat < Num.capacity C.h (C.K_w + 6) :=
            div_lt_cap_half_of_numer C.hℓ1 hnum2_cap
          have hq_u : Num.unsignedVal mem5 C.q2 C.h (C.K_w + 6) = C.qnat := by
            change Num.unsignedVal mem5 (C.hp2 + 2 * (C.K_w + 6) + Num.unsignedDivideSpace (C.K_w + 6)) C.h (C.K_w + 6) = C.qnat
            exact nat_eq_unsignedVal_of_intVal hq_val (by rw [hq_int, hfl, wrap_of_nat_lt hqnat_cap])
          rw [hvret, C.hp2_eq] at hzf5
          refine ⟨mBaseRegs_update_hi hst.1.1 (by omega), by dsimp; rw [Function.update_self, hvret, C.hp2_eq],
            by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.2.1,
            hzf5,
            ⟨fun a ha hne => by dsimp; rw [hpres a (by unfold MultStepCtx.hp2 MultStepCtx.hp1; omega)]; exact hst.1.2.2.2.2.1.1 a ha hne,
             by dsimp; rw [hpres _ (by unfold MultStepCtx.hp2 MultStepCtx.hp1; omega)]; exact hst.1.2.2.2.2.1.2⟩,
            hq_val, hq_u⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, Num.integerDivideContract, heapContract,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; nlinarith)
  have ht10 : Triple C.w p T9 (.assign 15 (.bin .sub (.reg 16) (.reg 18))) (normalPost T10) fun _ => 4 :=
    Triple.assign
      (fun _ hst => Expr.eval_sub (Expr.eval_reg_of_eq hst.2.1) (Expr.eval_reg_of_eq hst.2.2.1) hhp3)
      fun _ hst => ⟨⟨mBaseRegs_update_hi hst.1 (by omega),
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.1,
        by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.2.2.1, hst.2.2.2⟩,
        by dsimp; rw [Function.update_self, C.q2_sub]⟩
  have hq2_end_w : C.q2 + (C.K_w + 6) < 2 ^ C.w := by rw [← C.q2_sub]; omega
  have hq2_gt_qout : C.qNatOut + (C.K_w + 6) ≤ C.q2 := by
    have : C.hp ≤ C.q2 := by unfold MultStepCtx.q2 MultStepCtx.hp2 MultStepCtx.hp1; omega
    omega
  have ht11 : Triple C.w p T10 (.call 19 (lsfBaseUtils b + idxUtilMemCopy) [.reg 2, .reg 15, .reg 18])
      (normalPost fun st => st.regs 16 = C.hp + multQNatStepSpace C.K_w ∧
        ZeroFrom st.mem (C.hp + multQNatStepSpace C.K_w) ∧ MFrameFinal C st.mem) fun _ => 20 * (C.K_w + 6) + 18 :=
    Triple.conseq
      (Triple.call (vs := fun _ => [C.qNatOut, C.q2, C.K_w + 6]) hmc_copy
        (fun _ hst => evalArgs_cons (Expr.eval_reg_of_eq hst.1.1.r2)
          (evalArgs_cons (Expr.eval_reg_of_eq hst.2) (evalArgs_cons (Expr.eval_reg_of_eq hst.1.2.2.1) (evalArgs_nil _ _))))
        (fun _ _ v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl <;> omega)
        (fun _ _ => ⟨C.qNatOut, C.q2, C.K_w + 6, rfl, by omega, hq2_end_w, Or.inl hq2_gt_qout⟩)
        (fun _ _ mem6 _ hst ⟨_, _, _, heq, _, hcp, hfr⟩ => by
          simp only [List.cons.injEq, and_true] at heq; rcases heq with ⟨rfl, rfl, rfl⟩
          refine ⟨by dsimp; rw [Function.update_of_ne (by omega)]; exact hst.1.2.1,
            fun a ha => by dsimp; rw [hfr a (Or.inr (by omega))]; exact hst.1.2.2.2.1 a ha,
            ⟨fun a ha hout hne => by dsimp; rw [hfr a (by rcases hout with h1 | h2 <;> [exact Or.inl h1; exact Or.inr h2])]; exact hst.1.2.2.2.2.1.1 a ha hne,
             by dsimp; rw [hfr _ (Or.inr C.hq_m)]; exact hst.1.2.2.2.2.1.2,
             fun i hi => by dsimp; rw [hcp i hi]; exact hst.1.2.2.2.2.2.1 i hi,
             by dsimp; rw [Num.unsignedVal_congr hcp]; exact hst.1.2.2.2.2.2.2⟩⟩))
      (fun _ h => h) (fun _ _ h => h)
      (fun _ _ => by simp only [argsSize, Expr.size, memCopyContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]; omega)
  have ht12 : Triple C.w p
      (fun st => st.regs 16 = C.hp + multQNatStepSpace C.K_w ∧
        ZeroFrom st.mem (C.hp + multQNatStepSpace C.K_w) ∧ MFrameFinal C st.mem)
      (.ret (.reg 16))
      (retPost fun ret st => ret = C.hp + multQNatStepSpace C.K_w ∧ ZeroFrom st.mem ret ∧ MFrameFinal C st.mem) fun _ => 2 :=
    Triple.ret (fun _ hst => Expr.eval_reg_of_eq hst.1) fun _ hst => ⟨rfl, hst.2.1, hst.2.2⟩
  exact (Triple.seq_normal_const ht7 (Triple.seq_normal_const ht8 (Triple.seq_normal_const ht9
    (Triple.seq_normal_const ht10 (Triple.seq_normal_const ht11 ht12))))).mono_cost fun _ _ => by nlinarith

lemma multQNatStep_meetsContract {w b K_AN h f_l2w f : ℕ} {p : Program}
    (hp : p.HasAt (b + 2) (lsfSharedProcs b K_AN h))
    (hproc_l2w : p.procs[f_l2w]? = some limbsToWordProc)
    (hproc : p.procs[f]? = some (multQNatStepProc b f_l2w)) :
    MeetsContract w p f (multQNatStepContract w h) := by
  refine meetsContract_of_triple hproc ?_
  intro args mem0 pos _ hpre
  rcases hpre with ⟨wtE, lenE, qNatOut, multOut, svPtr, svMinusOnePtr, m0LimbsPtr,
    edgeLimbsPtr, numerPtr, lenQPtr, L_in, K_w, hp0, pow2h, m0, S_v, v_int, ℓ_int,
    rfl, rfl, hh1, hw3h, hLin1, hLK, hm01, hm02w, hSv1, hv1, hℓ1, hℓ_cap, hv_cap, hSv_cap,
    hnum_cap, hmj_bd, hmj_rem_cap, hq_cap, hwt_q, hlen_q, hq_m, hm_sv, hsv_m1, hm1_m0,
    hm0_ed, hed_num, hnum_lq, hlq_hp, hhp_w, hwt_val, hwt_u, hlen_val, hlen_u, hsv_val,
    hsv_u, hsvm1_val, hsvm1_u, hm0_val, hm0_u, hzf0⟩
  let C : MultStepCtx := {
    wtE, lenE, qNatOut, multOut, svPtr, svMinusOnePtr, m0LimbsPtr, edgeLimbsPtr,
    numerPtr, lenQPtr, L_in, K_w, hp := hp0, h, w, m0, S_v, v_int, ℓ_int, mem0,
    hh1, hw3h, hLin1, hLK, hm01, hm02w, hSv1, hv1, hℓ1, hℓ_cap, hv_cap, hSv_cap, hnum_cap,
    hmj_bd, hmj_rem_cap, hq_cap, hwt_q, hlen_q, hq_m, hm_sv, hsv_m1, hm1_m0, hm0_ed,
    hed_num, hnum_lq, hlq_hp, hhp_w, hwt_val, hwt_u, hlen_val, hlen_u, hsv_val, hsv_u,
    hsvm1_val, hsvm1_u, hm0_val, hm0_u, hzf0 }
  have h4 := multQNat_part4 hp C rfl rfl
  have h3 := multQNat_part3 hp C rfl rfl _ _ _ h4
  have h2 := multQNat_part2 hp hproc_l2w C rfl rfl _ _ _ h3
  have h1 := multQNat_part1 (pos := pos) hp C rfl rfl _ _ _ h2
  refine Triple.conseq h1 (fun _ h => h)
    (fun o st hpost => by
      cases o with
      | normal => exact False.elim hpost
      | returned _ =>
        exact ⟨wtE, lenE, qNatOut, multOut, svPtr, svMinusOnePtr, m0LimbsPtr, edgeLimbsPtr,
          numerPtr, lenQPtr, L_in, K_w, hp0, 2 ^ h, m0, S_v, v_int, ℓ_int,
          rfl, hpost.1, hwt_u, hlen_u, hsv_u, hm0_u, hpost.2.2.2.1, hpost.2.2.2.2.1,
          hpost.2.2.2.2.2, hpost.2.1, hpost.2.2.1⟩)
    (fun st hst => by
      subst hst
      simp only [multQNatStepContract, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      nlinarith)

end MinCostFlow.LSF.Program
