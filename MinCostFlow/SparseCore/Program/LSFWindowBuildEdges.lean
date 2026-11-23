module

public import MinCostFlow.SparseCore.Program.LSFWindowBuildVerts
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of Canonical Guest Builder Edge & Incidence Procedures (`LSFWindowBuildEdges`)

Proves `buildCanonEdgesProc_runs` and `buildCanonIncProc_runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

/-! ## 4. `buildCanonEdgesProc` -/

private lemma buildCanonEdges_loop {w h bCopy g0Ptr vCap0 eCap0 lenArr L_in P_fp guestBase : ℕ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {p : Program} {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hLin1 : 1 ≤ L_in)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hℓ₀ : ∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) h L_in ∧
      fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ guestBase)
    (hlen_le : lenArr + eCap0 * L_in ≤ guestBase)
    (hsp_lt : guestBase + canonHandlesOut G₀ L_in < 2 ^ w)
    (heL : ListAt mem (dgEListBase guestBase (canonVCap G₀) (canonECap G₀)) (canonEList G₀))
    (hCopy : MeetsContract w p bCopy (memCopyContract w)) :
    Triple w p
      (fun st => st.regs 1 = lenArr ∧ st.regs 2 = L_in ∧ st.regs 6 = G₀.m ∧
        st.regs 7 = guestBase + canonLenArr G₀ ∧
        st.regs 10 = dgIntToExtBase g0Ptr vCap0 ∧ st.regs 11 = dgETailSlotBase g0Ptr vCap0 eCap0 ∧
        st.regs 12 = dgEHeadSlotBase g0Ptr vCap0 eCap0 ∧
        st.regs 13 = dgEPresBase guestBase (canonVCap G₀) ∧
        st.regs 14 = dgEListBase guestBase (canonVCap G₀) (canonECap G₀) ∧
        st.regs 15 = dgEPosBase guestBase (canonVCap G₀) (canonECap G₀) ∧
        st.regs 16 = dgETailSlotBase guestBase (canonVCap G₀) (canonECap G₀) ∧
        st.regs 17 = dgEHeadSlotBase guestBase (canonVCap G₀) (canonECap G₀) ∧ st.mem = mem)
      (forRange 18 (.const 0) (.reg 6)
        (.assign 19 (.load (.bin .add (.reg 14) (.reg 18))) ;;
         .assign 20 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 11) (.reg 19))))) ;;
         .assign 21 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 19))))) ;;
         .store (.bin .add (.reg 13) (.reg 19)) (.const 1) ;;
         .store (.bin .add (.reg 15) (.reg 19)) (.reg 18) ;;
         .store (.bin .add (.reg 16) (.reg 19)) (.reg 20) ;;
         .store (.bin .add (.reg 17) (.reg 19)) (.reg 21) ;;
         .call 22 bCopy
           [.bin .add (.reg 7) (.bin .mul (.reg 19) (.reg 2)),
            .bin .add (.reg 1) (.bin .mul (.reg 19) (.reg 2)),
            .reg 2]))
      (normalPost fun st =>
        (∀ j (_hj : j < G₀.m), ∀ (hjL : j < (canonEList G₀).length),
          let e := (canonEList G₀)[j]'hjL
          st.mem (dgEPresBase guestBase (canonVCap G₀) + e) = 1 ∧
          st.mem (dgEPosBase guestBase (canonVCap G₀) (canonECap G₀) + e) = j ∧
          st.mem (dgETailSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e) = G₀.tail e ∧
          st.mem (dgEHeadSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e) = G₀.head e ∧
          ∀ t < L_in, st.mem (guestBase + canonLenArr G₀ + e * L_in + t) =
            natLimb (canonLenInt ℓ₀ P_fp e) h t) ∧
        (∀ addr,
          (∀ e ∈ G₀.E,
            addr ≠ dgEPresBase guestBase (canonVCap G₀) + e ∧
            addr ≠ dgEPosBase guestBase (canonVCap G₀) (canonECap G₀) + e ∧
            addr ≠ dgETailSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e ∧
            addr ≠ dgEHeadSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e ∧
            (addr < guestBase + canonLenArr G₀ + e * L_in ∨
              guestBase + canonLenArr G₀ + e * L_in + L_in ≤ addr)) →
          st.mem addr = mem addr))
      (fun _ => G₀.m * (20 * L_in + 100) + 15) := by
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  set eL := canonEList G₀
  set dstLen := guestBase + canonLenArr G₀
  have heL_len : eL.length = G₀.m := G₀.E.length_sort (· ≤ ·)
  have heL_nd : eL.Nodup := G₀.E.sort_nodup (· ≤ ·)
  have heL_mem : ∀ e, e ∈ eL ↔ e ∈ G₀.E := fun e => G₀.E.mem_sort (· ≤ ·)
  have hsz_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hdst_eq : dstLen = guestBase + (4 + 7 * vCap + 9 * eCap) := rfl
  have hsz0_eq : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  have hcanonH_eq : canonHandlesOut G₀ L_in = dynGraphSize vCap eCap + eCap * L_in := rfl
  have hm_le : G₀.m ≤ eCap := by
    have hsub : G₀.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (canonECap_gt he)
    calc G₀.m = G₀.E.card := rfl
      _ ≤ (Finset.range eCap).card := Finset.card_le_card hsub
      _ = eCap := Finset.card_range eCap
  have hLin_lt : L_in < 2 ^ w := by
    have : 1 * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in (canonECap_pos G₀)
    omega
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 1 = lenArr ∧ st.regs 2 = L_in ∧ st.regs 6 = G₀.m ∧ st.regs 7 = dstLen ∧
    st.regs 10 = dgIntToExtBase g0Ptr vCap0 ∧ st.regs 11 = dgETailSlotBase g0Ptr vCap0 eCap0 ∧
    st.regs 12 = dgEHeadSlotBase g0Ptr vCap0 eCap0 ∧ st.regs 13 = dgEPresBase guestBase vCap ∧
    st.regs 14 = dgEListBase guestBase vCap eCap ∧ st.regs 15 = dgEPosBase guestBase vCap eCap ∧
    st.regs 16 = dgETailSlotBase guestBase vCap eCap ∧ st.regs 17 = dgEHeadSlotBase guestBase vCap eCap ∧
    st.regs 18 = i ∧
    (∀ j (_hj : j < i), ∀ (hjL : j < eL.length),
      let e := eL[j]'hjL
      st.mem (dgEPresBase guestBase vCap + e) = 1 ∧
      st.mem (dgEPosBase guestBase vCap eCap + e) = j ∧
      st.mem (dgETailSlotBase guestBase vCap eCap + e) = G₀.tail e ∧
      st.mem (dgEHeadSlotBase guestBase vCap eCap + e) = G₀.head e ∧
      ∀ t < L_in, st.mem (dstLen + e * L_in + t) = natLimb (canonLenInt ℓ₀ P_fp e) h t) ∧
    (∀ addr,
      (∀ e ∈ G₀.E,
        addr ≠ dgEPresBase guestBase vCap + e ∧
        addr ≠ dgEPosBase guestBase vCap eCap + e ∧
        addr ≠ dgETailSlotBase guestBase vCap eCap + e ∧
        addr ≠ dgEHeadSlotBase guestBase vCap eCap + e ∧
        (addr < dstLen + e * L_in ∨ dstLen + e * L_in + L_in ≤ addr)) →
      st.mem addr = mem addr)
  have hloop : Triple w p
      (fun st => st.regs 1 = lenArr ∧ st.regs 2 = L_in ∧ st.regs 6 = G₀.m ∧
        st.regs 7 = dstLen ∧
        st.regs 10 = dgIntToExtBase g0Ptr vCap0 ∧ st.regs 11 = dgETailSlotBase g0Ptr vCap0 eCap0 ∧
        st.regs 12 = dgEHeadSlotBase g0Ptr vCap0 eCap0 ∧
        st.regs 13 = dgEPresBase guestBase vCap ∧
        st.regs 14 = dgEListBase guestBase vCap eCap ∧
        st.regs 15 = dgEPosBase guestBase vCap eCap ∧
        st.regs 16 = dgETailSlotBase guestBase vCap eCap ∧
        st.regs 17 = dgEHeadSlotBase guestBase vCap eCap ∧ st.mem = mem)
      (forRange 18 (.const 0) (.reg 6)
        (.assign 19 (.load (.bin .add (.reg 14) (.reg 18))) ;;
         .assign 20 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 11) (.reg 19))))) ;;
         .assign 21 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 19))))) ;;
         .store (.bin .add (.reg 13) (.reg 19)) (.const 1) ;;
         .store (.bin .add (.reg 15) (.reg 19)) (.reg 18) ;;
         .store (.bin .add (.reg 16) (.reg 19)) (.reg 20) ;;
         .store (.bin .add (.reg 17) (.reg 19)) (.reg 21) ;;
         .call 22 bCopy
           [.bin .add (.reg 7) (.bin .mul (.reg 19) (.reg 2)),
            .bin .add (.reg 1) (.bin .mul (.reg 19) (.reg 2)),
            .reg 2]))
      (normalPost (Inv G₀.m))
      (fun _ => (G₀.m - 0) * (20 * L_in + 82 + (Expr.reg 6).size + 8) +
        ((Expr.const 0).size + (Expr.reg 6).size + 5)) := by
    refine Triple.forRange_const (Inv := Inv) (20 * L_in + 82) 0 G₀.m (Nat.zero_le _) (by omega)
      (fun _ => by omega) ?_ ?_ ?_ ?_
    · intro st hst
      rcases hst with ⟨q1, q2, q6, q7, q10, q11, q12, q13, q14, q15, q16, q17, hmeq⟩
      exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], by simp [q1], by simp [q2],
        by simp [q6], by simp [q7], by simp [q10], by simp [q11], by simp [q12], by simp [q13],
        by simp [q14], by simp [q15], by simp [q16], by simp [q17], by simp,
        fun _ hj _ => absurd hj (Nat.not_lt_zero _), fun _ _ => congrFun hmeq _⟩
    · intro _ _ _ _ hi; exact hi.2.2.2.2.2.2.2.2.2.2.2.2.1
    · intro _ st _ _ hi; simp [Expr.eval, hi.2.2.1]
    · intro i _ hi st ω' hinv
      rcases hinv with ⟨hr1, hr2, hr6, hr7, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18,
        hset, hfr⟩
      have hiL : i < eL.length := by omega
      set e := eL[i]'hiL
      have he_mem : e ∈ G₀.E := (heL_mem e).mp (List.getElem_mem hiL)
      have he_lt : e < eCap := canonECap_gt he_mem
      have he_lt0 : e < eCap0 := hdg0.2.2.1 e he_mem
      have he_mul : (e + 1) * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in (by omega)
      have he_mul0 : (e + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
      have he_add : e * L_in + L_in = (e + 1) * L_in := by ring
      have hlt_g0 : ∀ a, g0Ptr ≤ a → a < g0Ptr + dynGraphSize vCap0 eCap0 → st.mem a = mem a := fun a ha1 ha2 =>
        hfr a fun f hf => by
          have := canonECap_gt hf
          dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]
          omega
      have he_read : st.mem (dgEListBase guestBase vCap eCap + i) = e := by
        rw [hfr _ (fun f hf => by
          have := canonECap_gt hf
          dsimp [dgEListBase, dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr, dynGraphSize]
          omega)]
        exact heL i hiL
      set tSlot := mem (dgETailSlotBase g0Ptr vCap0 eCap0 + e)
      set hSlot := mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + e)
      have ht_eq : tSlot = mem (dgExtToIntBase g0Ptr vCap0 + G₀.tail e) :=
        (hdg0.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he_mem).1
      have hh_eq : hSlot = mem (dgExtToIntBase g0Ptr vCap0 + G₀.head e) :=
        (hdg0.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he_mem).2
      have htSlot_mem : tSlot ∈ G₀.V := ht_eq ▸ (hdg0.2.2.2.2.2.2.2.2.2.1 _ (hdg0.1 e he_mem).1).1
      have hhSlot_mem : hSlot ∈ G₀.V := hh_eq ▸ (hdg0.2.2.2.2.2.2.2.2.2.1 _ (hdg0.1 e he_mem).2).1
      have htSlot_lt : tSlot < vCap0 := hdg0.2.1 tSlot htSlot_mem
      have hhSlot_lt : hSlot < vCap0 := hdg0.2.1 hSlot hhSlot_mem
      have hu_val : mem (dgIntToExtBase g0Ptr vCap0 + tSlot) = G₀.tail e := by
        rw [ht_eq]; exact (hdg0.2.2.2.2.2.2.2.2.2.1 _ (hdg0.1 e he_mem).1).2
      have hv_val : mem (dgIntToExtBase g0Ptr vCap0 + hSlot) = G₀.head e := by
        rw [hh_eq]; exact (hdg0.2.2.2.2.2.2.2.2.2.1 _ (hdg0.1 e he_mem).2).2
      have ht_read : st.mem (dgETailSlotBase g0Ptr vCap0 eCap0 + e) = tSlot :=
        hlt_g0 _ (by dsimp [dgETailSlotBase]; omega) (by dsimp [dgETailSlotBase]; omega)
      have hh_read : st.mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + e) = hSlot :=
        hlt_g0 _ (by dsimp [dgEHeadSlotBase]; omega) (by dsimp [dgEHeadSlotBase]; omega)
      have hu_read : st.mem (dgIntToExtBase g0Ptr vCap0 + tSlot) = G₀.tail e :=
        (hlt_g0 _ (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase]; omega)).trans hu_val
      have hv_read : st.mem (dgIntToExtBase g0Ptr vCap0 + hSlot) = G₀.head e :=
        (hlt_g0 _ (by dsimp [dgIntToExtBase]; omega) (by dsimp [dgIntToExtBase]; omega)).trans hv_val
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := e)
        (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr14, hr18,
          show dgEListBase guestBase vCap eCap + i < 2 ^ w by dsimp [dgEListBase]; omega]) he_read) ?_
      refine runs_seq_assign_le (v := G₀.tail e)
        (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr10, hr11,
          show dgETailSlotBase g0Ptr vCap0 eCap0 + e < 2 ^ w by dsimp [dgETailSlotBase]; omega,
          ht_read, show dgIntToExtBase g0Ptr vCap0 + tSlot < 2 ^ w by dsimp [dgIntToExtBase]; omega]) hu_read) ?_
      refine runs_seq_assign_le (v := G₀.head e)
        (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr10, hr12,
          show dgEHeadSlotBase g0Ptr vCap0 eCap0 + e < 2 ^ w by dsimp [dgEHeadSlotBase]; omega,
          hh_read, show dgIntToExtBase g0Ptr vCap0 + hSlot < 2 ^ w by dsimp [dgIntToExtBase]; omega]) hv_read) ?_
      refine runs_seq_store_le (x := dgEPresBase guestBase vCap + e) (v := 1)
        (by simp [Expr.eval, BinOp.eval, hr13, show dgEPresBase guestBase vCap + e < 2 ^ w by dsimp [dgEPresBase]; omega])
        (by simp [Expr.eval, show 1 < 2 ^ w by omega]) ?_
      refine runs_seq_store_le (x := dgEPosBase guestBase vCap eCap + e) (v := i)
        (by simp [Expr.eval, BinOp.eval, hr15, show dgEPosBase guestBase vCap eCap + e < 2 ^ w by dsimp [dgEPosBase]; omega])
        (by simp [Expr.eval, hr18]) ?_
      refine runs_seq_store_le (x := dgETailSlotBase guestBase vCap eCap + e) (v := G₀.tail e)
        (by simp [Expr.eval, BinOp.eval, hr16, show dgETailSlotBase guestBase vCap eCap + e < 2 ^ w by dsimp [dgETailSlotBase]; omega])
        (by simp [Expr.eval]) ?_
      refine runs_seq_store_le (x := dgEHeadSlotBase guestBase vCap eCap + e) (v := G₀.head e)
        (by simp [Expr.eval, BinOp.eval, hr17, show dgEHeadSlotBase guestBase vCap eCap + e < 2 ^ w by dsimp [dgEHeadSlotBase]; omega])
        (by simp [Expr.eval]) ?_
      have hdst_e_lt : dstLen + e * L_in + L_in < 2 ^ w := by
        dsimp [dstLen, canonLenArr, dynGraphSize]
        dsimp [dynGraphSize] at hcanonH_eq
        omega
      have hlen_e_lt : lenArr + e * L_in + L_in ≤ guestBase := by omega
      refine runs_call_le hCopy
        (vs := [dstLen + e * L_in, lenArr + e * L_in, L_in])
        (by simp [evalArgs, Expr.eval, BinOp.eval, hr7, hr1, hr2,
          show e * L_in < 2 ^ w by omega, show dstLen + e * L_in < 2 ^ w by omega,
          show lenArr + e * L_in < 2 ^ w by omega])
        (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl <;> omega)
        ⟨dstLen + e * L_in, lenArr + e * L_in, L_in, rfl, hdst_e_lt, by omega,
          Or.inr (by dsimp [dstLen, canonLenArr]; omega)⟩
        (fun _ mem' _ hpost => ?_)
      rcases hpost with ⟨_, _, _, hEq, rfl, hcp, hfr_cp⟩
      cases hEq
      dsimp only at hcp hfr_cp
      have hlen_src : ∀ t < L_in, mem (lenArr + e * L_in + t) = natLimb (canonLenInt ℓ₀ P_fp e) h t :=
        valid_limbs_eq_natLimb (hℓ₀ e he_mem).1 (hℓ₀ e he_mem).2.1 (hℓ₀ e he_mem).2.2
      have hsrc_ag : ∀ t < L_in,
          (Function.update (Function.update (Function.update (Function.update st.mem
            (dgEPresBase guestBase vCap + e) 1)
            (dgEPosBase guestBase vCap eCap + e) i)
            (dgETailSlotBase guestBase vCap eCap + e) (G₀.tail e))
            (dgEHeadSlotBase guestBase vCap eCap + e) (G₀.head e)) (lenArr + e * L_in + t) =
          mem (lenArr + e * L_in + t) := fun t ht => by
        have hlt_gb : lenArr + e * L_in + t < guestBase := by omega
        rw [Function.update_of_ne (by dsimp [dgEHeadSlotBase]; omega),
            Function.update_of_ne (by dsimp [dgETailSlotBase]; omega),
            Function.update_of_ne (by dsimp [dgEPosBase]; omega),
            Function.update_of_ne (by dsimp [dgEPresBase]; omega)]
        exact hfr _ fun f hf => by
          have := canonECap_gt hf
          dsimp [dgEPresBase, dgEPosBase, dgETailSlotBase, dgEHeadSlotBase, dstLen, canonLenArr]
          omega
      refine ⟨⟨⟨by simp [hr1], by simp [hr2], by simp [hr6], by simp [hr7], by simp [hr10],
        by simp [hr11], by simp [hr12], by simp [hr13], by simp [hr14], by simp [hr15],
        by simp [hr16], by simp [hr17], by simp, ?_, ?_⟩, by simp [hr18]⟩,
        by simp only [memCopyContract, argsSize, Expr.size, List.getD_eq_getElem?_getD]; norm_num; omega⟩
      · intro j hj hjL
        set f := eL[j]'hjL
        have hf_lt : f < eCap := canonECap_gt ((heL_mem f).mp (List.getElem_mem hjL))
        have hEP : dgEPresBase guestBase vCap = guestBase + 4 + 7 * vCap := rfl
        have hEPos : dgEPosBase guestBase vCap eCap = guestBase + 4 + 7 * vCap + 2 * eCap := rfl
        have hET : dgETailSlotBase guestBase vCap eCap = guestBase + 4 + 7 * vCap + 3 * eCap := rfl
        have hEH : dgEHeadSlotBase guestBase vCap eCap = guestBase + 4 + 7 * vCap + 4 * eCap := rfl
        clear hdg0 hℓ₀ hCopy heL hlt_g0 he_read ht_eq hh_eq htSlot_mem hhSlot_mem htSlot_lt hhSlot_lt
          hu_val hv_val ht_read hh_read hu_read hv_read hfr
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
        · have hne : f ≠ e := fun hEq => by have := (List.Nodup.getElem_inj heL_nd).mp hEq; omega
          obtain ⟨h1, h2, h3, h4, h5⟩ := hset j hj' hjL
          have hdisj_len : ∀ t < L_in,
              dstLen + f * L_in + t < dstLen + e * L_in ∨ dstLen + e * L_in + L_in ≤ dstLen + f * L_in + t := by
            intro t ht
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
            · left
              have : (f + 1) * L_in ≤ e * L_in := Nat.mul_le_mul_right L_in hlt
              have : f * L_in + L_in = (f + 1) * L_in := by ring
              omega
            · right
              have : (e + 1) * L_in ≤ f * L_in := Nat.mul_le_mul_right L_in hgt
              omega
          refine ⟨?_, ?_, ?_, ?_, fun t ht => ?_⟩
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; exact h1
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; exact h2
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; exact h3
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]; exact h4
          · dsimp only
            rw [hfr_cp _ (hdisj_len t ht), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
            exact h5 t ht
        · refine ⟨?_, ?_, ?_, ?_, fun t ht => ?_⟩
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_self]
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_self]
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_of_ne (by omega),
                Function.update_self]
          · dsimp only
            rw [hfr_cp _ (Or.inl (by omega)), Function.update_self]
          · dsimp only
            rw [hcp t ht, hsrc_ag t ht, hlen_src t ht]
      · intro addr haddr
        obtain ⟨h1, h2, h3, h4, h5⟩ := haddr e he_mem
        dsimp only
        rw [hfr_cp addr h5, Function.update_of_ne h4, Function.update_of_ne h3,
            Function.update_of_ne h2, Function.update_of_ne h1]
        exact hfr addr haddr
  exact Triple.conseq hloop (fun _ h => h) (fun o st h => by
    cases o with
    | normal =>
      rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2⟩
      exact ⟨h1, h2⟩
    | returned _ => exact h.elim) (fun _ => by
      simp only [Nat.sub_zero, Expr.size]
      have hmul : G₀.m * (20 * L_in + 82 + 1 + 8) ≤ G₀.m * (20 * L_in + 100) :=
        Nat.mul_le_mul_left G₀.m (by omega)
      omega)

lemma buildCanonEdgesProc_runs {w h bCopy g0Ptr vCap0 eCap0 lenArr L_in P_fp guestBase : ℕ}
    {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hLin1 : 1 ≤ L_in)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hℓ₀ : ∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) h L_in ∧
      fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ guestBase)
    (hlen_le : lenArr + eCap0 * L_in ≤ guestBase)
    (hsp_lt : guestBase + canonHandlesOut G₀ L_in < 2 ^ w)
    (heL : ListAt mem (dgEListBase guestBase (canonVCap G₀) (canonECap G₀)) (canonEList G₀))
    (hCopy : MeetsContract w p bCopy (memCopyContract w)) :
    ∃ st' c,
      Runs w p ω (buildCanonEdgesProc bCopy)
        (startState [g0Ptr, lenArr, L_in, guestBase, canonVCap G₀, canonECap G₀, G₀.m,
          guestBase + canonLenArr G₀] mem pos)
        (.returned 0) st' c ∧
      (∀ e ∈ G₀.E,
        st'.mem (dgEPresBase guestBase (canonVCap G₀) + e) = 1 ∧
        st'.mem (dgEPosBase guestBase (canonVCap G₀) (canonECap G₀) + e) = (canonEList G₀).idxOf e ∧
        st'.mem (dgETailSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e) = G₀.tail e ∧
        st'.mem (dgEHeadSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e) = G₀.head e ∧
        ∀ t < L_in, st'.mem (guestBase + canonLenArr G₀ + e * L_in + t) =
          natLimb (canonLenInt ℓ₀ P_fp e) h t) ∧
      (∀ addr,
        (∀ e ∈ G₀.E,
          addr ≠ dgEPresBase guestBase (canonVCap G₀) + e ∧
          addr ≠ dgEPosBase guestBase (canonVCap G₀) (canonECap G₀) + e ∧
          addr ≠ dgETailSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e ∧
          addr ≠ dgEHeadSlotBase guestBase (canonVCap G₀) (canonECap G₀) + e ∧
          (addr < guestBase + canonLenArr G₀ + e * L_in ∨
            guestBase + canonLenArr G₀ + e * L_in + L_in ≤ addr)) →
        st'.mem addr = mem addr) ∧
      c ≤ G₀.m * (20 * L_in + 100) + 180 := by
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  set eL := canonEList G₀
  set dstLen := guestBase + canonLenArr G₀
  have heL_len : eL.length = G₀.m := G₀.E.length_sort (· ≤ ·)
  have heL_nd : eL.Nodup := G₀.E.sort_nodup (· ≤ ·)
  have heL_mem : ∀ e, e ∈ eL ↔ e ∈ G₀.E := fun e => G₀.E.mem_sort (· ≤ ·)
  have hsz_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hdst_eq : dstLen = guestBase + (4 + 7 * vCap + 9 * eCap) := rfl
  have hsz0_eq : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  have hcanonH_eq : canonHandlesOut G₀ L_in = dynGraphSize vCap eCap + eCap * L_in := rfl
  suffices hmain : ∃ o st' c,
      Runs w p ω (buildCanonEdgesProc bCopy)
        (startState [g0Ptr, lenArr, L_in, guestBase, vCap, eCap, G₀.m, dstLen] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (∀ e ∈ G₀.E,
          st'.mem (dgEPresBase guestBase vCap + e) = 1 ∧
          st'.mem (dgEPosBase guestBase vCap eCap + e) = eL.idxOf e ∧
          st'.mem (dgETailSlotBase guestBase vCap eCap + e) = G₀.tail e ∧
          st'.mem (dgEHeadSlotBase guestBase vCap eCap + e) = G₀.head e ∧
          ∀ t < L_in, st'.mem (dstLen + e * L_in + t) = natLimb (canonLenInt ℓ₀ P_fp e) h t) ∧
        (∀ addr,
          (∀ e ∈ G₀.E,
            addr ≠ dgEPresBase guestBase vCap + e ∧
            addr ≠ dgEPosBase guestBase vCap eCap + e ∧
            addr ≠ dgETailSlotBase guestBase vCap eCap + e ∧
            addr ≠ dgEHeadSlotBase guestBase vCap eCap + e ∧
            (addr < dstLen + e * L_in ∨ dstLen + e * L_in + L_in ≤ addr)) →
          st'.mem addr = mem addr)) ∧
      0 + c ≤ G₀.m * (20 * L_in + 100) + 180 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, by omega⟩
  unfold buildCanonEdgesProc
  refine runs_seq_assign_le (v := vCap0)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dgVCapOff,
      show g0Ptr < 2 ^ w by omega]) hdg0.2.2.2.1) ?_
  refine runs_seq_assign_le (v := eCap0)
    (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, startState, dgECapOff,
      show 1 < 2 ^ w by omega, show g0Ptr + 1 < 2 ^ w by omega]) hdg0.2.2.2.2.1) ?_
  refine runs_seq_assign_le (v := dgIntToExtBase g0Ptr vCap0)
    (by simp [Expr.eval, BinOp.eval, startState, dgIntToExtBase, show 4 < 2 ^ w by omega,
      show g0Ptr + 4 < 2 ^ w by omega, show 4 * vCap0 < 2 ^ w by omega,
      show g0Ptr + 4 + 4 * vCap0 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgETailSlotBase g0Ptr vCap0 eCap0)
    (by simp [Expr.eval, BinOp.eval, startState, dgETailSlotBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show 3 < 2 ^ w by omega, show g0Ptr + 4 < 2 ^ w by omega,
      show 7 * vCap0 < 2 ^ w by omega, show g0Ptr + 4 + 7 * vCap0 < 2 ^ w by omega,
      show 3 * eCap0 < 2 ^ w by omega, show g0Ptr + 4 + 7 * vCap0 + 3 * eCap0 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgEHeadSlotBase g0Ptr vCap0 eCap0)
    (by simp [Expr.eval, BinOp.eval, startState, dgEHeadSlotBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show g0Ptr + 4 < 2 ^ w by omega, show 7 * vCap0 < 2 ^ w by omega,
      show g0Ptr + 4 + 7 * vCap0 < 2 ^ w by omega, show 4 * eCap0 < 2 ^ w by omega,
      show g0Ptr + 4 + 7 * vCap0 + 4 * eCap0 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgEPresBase guestBase vCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEPresBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgEListBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEListBase, dgEPresBase,
      show guestBase + 4 + 7 * vCap + eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgEPosBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEPosBase, dgEPresBase, show 2 < 2 ^ w by omega,
      show 2 * eCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap + 2 * eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgETailSlotBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgETailSlotBase, dgEPresBase, show 3 < 2 ^ w by omega,
      show 3 * eCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap + 3 * eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgEHeadSlotBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEHeadSlotBase, dgEPresBase, show 4 < 2 ^ w by omega,
      show 4 * eCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap + 4 * eCap < 2 ^ w by omega]) ?_
  refine runs_seq_triple_le (buildCanonEdges_loop hw16 hLin1 hdg0 hℓ₀ hg0_le hlen_le hsp_lt heL hCopy)
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState, dstLen],
      by simp, by simp, by simp, by simp [vCap], by simp [vCap, eCap], by simp [vCap, eCap],
      by simp [vCap, eCap], by simp [vCap, eCap], rfl⟩ fun st₁ hinv => ?_
  rcases hinv with ⟨hset, hfr⟩
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ⟨rfl, ?_, hfr⟩
    (by simp only [Expr.size]; omega)
  intro e he
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((heL_mem e).mpr he)
  have h1 := hset j (by omega) hj
  rwa [List.Nodup.idxOf_getElem heL_nd j hj]

/-! ## 5. `buildCanonIncProc` -/

private lemma pushHalfEdgeMem_congr {vCap eCap s he : ℕ} {f g : ℕ → ℕ}
    (hs : s < vCap) (hfg : ∀ a < dynGraphSize vCap eCap, f a = g a) :
    ∀ a < dynGraphSize vCap eCap,
      pushHalfEdgeMem vCap eCap s he f a = pushHalfEdgeMem vCap eCap s he g a := by
  intro a ha
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have h1 : f (dgIncHeadBase 0 vCap + s) = g (dgIncHeadBase 0 vCap + s) :=
    hfg _ (by dsimp [dgIncHeadBase]; omega)
  have h2 : f (dgSlotDegBase 0 vCap + s) = g (dgSlotDegBase 0 vCap + s) :=
    hfg _ (by dsimp [dgSlotDegBase]; omega)
  unfold pushHalfEdgeMem
  by_cases ha5 : a = dgSlotDegBase 0 vCap + s
  · subst ha5; simp [h2]
  rw [Function.update_of_ne ha5, Function.update_of_ne ha5]
  by_cases ha4 : a = dgIncHeadBase 0 vCap + s
  · subst ha4; simp
  rw [Function.update_of_ne ha4, Function.update_of_ne ha4]
  rw [h1]
  split_ifs with h0
  · by_cases ha2 : a = dgHeNextBase 0 vCap eCap + he
    · subst ha2; simp
    rw [Function.update_of_ne ha2, Function.update_of_ne ha2]
    by_cases ha1 : a = dgHePrevBase 0 vCap eCap + he
    · subst ha1; simp
    rw [Function.update_of_ne ha1, Function.update_of_ne ha1]
    exact hfg a ha
  · by_cases ha3 : a = dgHePrevBase 0 vCap eCap + (g (dgIncHeadBase 0 vCap + s) - 1)
    · subst ha3; simp
    rw [Function.update_of_ne ha3, Function.update_of_ne ha3]
    by_cases ha2 : a = dgHeNextBase 0 vCap eCap + he
    · subst ha2; simp
    rw [Function.update_of_ne ha2, Function.update_of_ne ha2]
    by_cases ha1 : a = dgHePrevBase 0 vCap eCap + he
    · subst ha1; simp
    rw [Function.update_of_ne ha1, Function.update_of_ne ha1]
    exact hfg a ha

set_option maxHeartbeats 600000 in
lemma buildCanonIncProc_runs {w bPush guestBase : ℕ} {G₀ : MGraph} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos : ℕ}
    (hG₀ : G₀.IsValid) (hw16 : 16 ≤ 2 ^ w)
    (hsz_lt : guestBase + dynGraphSize (canonVCap G₀) (canonECap G₀) < 2 ^ w)
    (hbase : ∀ a < dynGraphSize (canonVCap G₀) (canonECap G₀),
      mem (guestBase + a) = canonDGMemBase G₀ a)
    (hpPush : p.procs[bPush]? = some pushHalfEdgeProc) :
    ∃ st' c,
      Runs w p ω (buildCanonIncProc bPush)
        (startState [guestBase, canonVCap G₀, canonECap G₀, G₀.m] mem pos)
        (.returned 0) st' c ∧
      (∀ a < dynGraphSize (canonVCap G₀) (canonECap G₀),
        st'.mem (guestBase + a) = canonDGMem G₀ a) ∧
      (∀ addr, addr < guestBase ∨ guestBase + dynGraphSize (canonVCap G₀) (canonECap G₀) ≤ addr →
        st'.mem addr = mem addr) ∧
      c ≤ 270 * G₀.m + 80 := by
  set vCap := canonVCap G₀
  set eCap := canonECap G₀
  set eL := canonEList G₀
  have heL_len : eL.length = G₀.m := G₀.E.length_sort (· ≤ ·)
  have heL_nd : eL.Nodup := G₀.E.sort_nodup (· ≤ ·)
  have heL_mem : ∀ e, e ∈ eL ↔ e ∈ G₀.E := fun e => G₀.E.mem_sort (· ≤ ·)
  have hsz_eq : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hm_le : G₀.m ≤ eCap := by
    have hsub : G₀.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (canonECap_gt he)
    calc G₀.m = G₀.E.card := rfl
      _ ≤ (Finset.range eCap).card := Finset.card_le_card hsub
      _ = eCap := Finset.card_range eCap
  suffices hmain : ∃ o st' c,
      Runs w p ω (buildCanonIncProc bPush) (startState [guestBase, vCap, eCap, G₀.m] mem pos) o st' c ∧
      (o = .returned 0 ∧
        (∀ a < dynGraphSize vCap eCap, st'.mem (guestBase + a) = canonDGMem G₀ a) ∧
        (∀ addr, addr < guestBase ∨ guestBase + dynGraphSize vCap eCap ≤ addr →
          st'.mem addr = mem addr)) ∧
      0 + c ≤ 270 * G₀.m + 80 by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, h1, h2⟩, hc⟩
    exact ⟨st', c, hrun, h1, h2, by omega⟩
  unfold buildCanonIncProc
  refine runs_seq_assign_le (v := dgEListBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEListBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap + eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgETailSlotBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgETailSlotBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show 3 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega,
      show 7 * vCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap < 2 ^ w by omega,
      show 3 * eCap < 2 ^ w by omega, show guestBase + 4 + 7 * vCap + 3 * eCap < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := dgEHeadSlotBase guestBase vCap eCap)
    (by simp [Expr.eval, BinOp.eval, startState, dgEHeadSlotBase, show 4 < 2 ^ w by omega,
      show 7 < 2 ^ w by omega, show guestBase + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap < 2 ^ w by omega, show 4 * eCap < 2 ^ w by omega,
      show guestBase + 4 + 7 * vCap + 4 * eCap < 2 ^ w by omega]) ?_
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = guestBase ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = G₀.m ∧
    st.regs 4 = dgEListBase guestBase vCap eCap ∧
    st.regs 5 = dgETailSlotBase guestBase vCap eCap ∧
    st.regs 6 = dgEHeadSlotBase guestBase vCap eCap ∧
    st.regs 7 = i ∧
    (∀ a < dynGraphSize vCap eCap,
      st.mem (guestBase + a) = (eL.take i).foldl (pushEdgeIncMem G₀ vCap eCap) (canonDGMemBase G₀) a) ∧
    (∀ addr, addr < guestBase ∨ guestBase + dynGraphSize vCap eCap ≤ addr → st.mem addr = mem addr)
  have hloop : Triple w p
      (fun st => st.regs 0 = guestBase ∧ st.regs 1 = vCap ∧ st.regs 2 = eCap ∧ st.regs 3 = G₀.m ∧
        st.regs 4 = dgEListBase guestBase vCap eCap ∧
        st.regs 5 = dgETailSlotBase guestBase vCap eCap ∧
        st.regs 6 = dgEHeadSlotBase guestBase vCap eCap ∧ st.mem = mem)
      (forRange 7 (.const 0) (.reg 3)
        (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
         .assign 9 (.load (.bin .add (.reg 5) (.reg 8))) ;;
         .assign 10 (.load (.bin .add (.reg 6) (.reg 8))) ;;
         .call 11 bPush [.reg 0, .reg 1, .reg 2, .reg 9, .bin .mul (.const 2) (.reg 8)] ;;
         .call 11 bPush [.reg 0, .reg 1, .reg 2, .reg 10, .bin .add (.bin .mul (.const 2) (.reg 8)) (.const 1)]))
      (normalPost (Inv G₀.m)) (fun _ => 270 * G₀.m + 15) := by
    refine (Triple.forRange_const 260 0 G₀.m (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q0, q1, q2, q3, q4, q5, q6, hmeq⟩
        exact ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], by simp [q0], by simp [q1],
          by simp [q2], by simp [q3], by simp [q4], by simp [q5], by simp [q6], by simp,
          fun a ha => by rw [hmeq]; simpa using hbase a ha, fun _ _ => congrFun hmeq _⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by simp [Expr.eval, hi.2.2.2.1])
      (fun i _ hi st ω' hinv => by
        rcases hinv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hmem_i, hfr_i⟩
        have hiL : i < eL.length := by omega
        set e := eL[i]'hiL
        have he_mem : e ∈ G₀.E := (heL_mem e).mp (List.getElem_mem hiL)
        have he_lt : e < eCap := canonECap_gt he_mem
        have ht_lt : G₀.tail e < vCap := canonVCap_gt (hG₀ e he_mem).1
        have hh_lt : G₀.head e < vCap := canonVCap_gt (hG₀ e he_mem).2
        set es := eL.take i
        have hes_nd : es.Nodup := heL_nd.sublist (List.take_sublist i eL)
        have hes_sub : ∀ e' ∈ es, e' ∈ G₀.E := fun e' he' =>
          (heL_mem e').mp ((List.take_sublist i eL).subset he')
        obtain ⟨hfr_es, ⟨incL, hincL, _⟩, hlt_es⟩ := canonDGMem_fold_props hG₀ es hes_nd hes_sub
        set m0 := es.foldl (pushEdgeIncMem G₀ vCap eCap) (canonDGMemBase G₀)
        have he_val : st.mem (dgEListBase guestBase vCap eCap + i) = e := by
          have h1 := hmem_i (dgEListBase 0 vCap eCap + i) (by dsimp [dgEListBase]; omega)
          rw [show guestBase + (dgEListBase 0 vCap eCap + i) = dgEListBase guestBase vCap eCap + i by
            dsimp [dgEListBase]; omega] at h1
          rw [h1, hfr_es _ (Or.inr (by dsimp [dgEListBase, dgEPresBase]; omega))
              (Or.inl (by dsimp [dgEListBase, dgHePrevBase]; omega)),
              canonDGMemBase_eList (by omega), List.getD_eq_getElem _ _ hiL]
        have hu_val : st.mem (dgETailSlotBase guestBase vCap eCap + e) = G₀.tail e := by
          have h1 := hmem_i (dgETailSlotBase 0 vCap eCap + e) (by dsimp [dgETailSlotBase]; omega)
          rw [show guestBase + (dgETailSlotBase 0 vCap eCap + e) = dgETailSlotBase guestBase vCap eCap + e by
            dsimp [dgETailSlotBase]; omega] at h1
          rw [h1, hfr_es _ (Or.inr (by dsimp [dgETailSlotBase, dgEPresBase]; omega))
              (Or.inl (by dsimp [dgETailSlotBase, dgHePrevBase]; omega)),
              canonDGMemBase_eTailSlot he_lt, ite_eq_left he_mem]
        have hv_val : st.mem (dgEHeadSlotBase guestBase vCap eCap + e) = G₀.head e := by
          have h1 := hmem_i (dgEHeadSlotBase 0 vCap eCap + e) (by dsimp [dgEHeadSlotBase]; omega)
          rw [show guestBase + (dgEHeadSlotBase 0 vCap eCap + e) = dgEHeadSlotBase guestBase vCap eCap + e by
            dsimp [dgEHeadSlotBase]; omega] at h1
          rw [h1, hfr_es _ (Or.inr (by dsimp [dgEHeadSlotBase, dgEPresBase]; omega))
              (Or.inl (by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega)),
              canonDGMemBase_eHeadSlot he_lt, ite_eq_left he_mem]
        -- Push 1: 2 * e onto G₀.tail e
        have hold1 : st.mem (dgIncHeadBase guestBase vCap + G₀.tail e) = 0 ∨
            st.mem (dgIncHeadBase guestBase vCap + G₀.tail e) - 1 < 2 * eCap := by
          have h1 := hmem_i (dgIncHeadBase 0 vCap + G₀.tail e) (by dsimp [dgIncHeadBase]; omega)
          rw [show guestBase + (dgIncHeadBase 0 vCap + G₀.tail e) = dgIncHeadBase guestBase vCap + G₀.tail e by
            dsimp [dgIncHeadBase]; omega] at h1
          rw [h1]
          have hhd := (hincL (G₀.tail e) ht_lt).1.2.2.1
          cases hL : incL (G₀.tail e) with
          | nil => left; rw [hhd, hL]
          | cons a l =>
            right; have ha := (hincL (G₀.tail e) ht_lt).1.2.1 a (by rw [hL]; exact List.mem_cons_self)
            have hhd' : m0 (dgIncHeadBase 0 vCap + G₀.tail e) = a + 1 := by
              simpa [m0, hL] using hhd
            omega
        have hinc_len : ∀ s < vCap, (incL s).length ≤ 2 * eCap := fun s hs => by
          have hnd := (hincL s hs).1.1
          have hsub : (incL s).toFinset ⊆ Finset.range (2 * eCap) := fun x hx =>
            Finset.mem_range.mpr ((hincL s hs).1.2.1 x (List.mem_toFinset.mp hx))
          calc (incL s).length = (incL s).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
            _ ≤ (Finset.range (2 * eCap)).card := Finset.card_le_card hsub
            _ = 2 * eCap := Finset.card_range _
        have hdeg1 : st.mem (dgSlotDegBase guestBase vCap + G₀.tail e) + 1 < 2 ^ w := by
          have h1 := hmem_i (dgSlotDegBase 0 vCap + G₀.tail e) (by dsimp [dgSlotDegBase]; omega)
          rw [show guestBase + (dgSlotDegBase 0 vCap + G₀.tail e) = dgSlotDegBase guestBase vCap + G₀.tail e by
            dsimp [dgSlotDegBase]; omega] at h1
          rw [h1]; have hlt1 : m0 (dgSlotDegBase 0 vCap + G₀.tail e) < dynGraphSize vCap eCap :=
            hlt_es (dgSlotDegBase 0 vCap + G₀.tail e)
          omega
        obtain ⟨stP1, cP1, hrunP1, hmP1, hfrP1, hcP1⟩ :=
          pushHalfEdgeProc_runs (p := p) (ω := ω') (mem := st.mem) (pos := st.pos)
            hw16 ht_lt (by omega : 2 * e < 2 * eCap) hsz_lt hold1 hdeg1
        have hmP1_eq : ∀ a < dynGraphSize vCap eCap,
            stP1.mem (guestBase + a) = pushHalfEdgeMem vCap eCap (G₀.tail e) (2 * e) m0 a := fun a ha =>
          (hmP1 a ha).trans (pushHalfEdgeMem_congr ht_lt hmem_i a ha)
        -- Push 2: 2 * e + 1 onto G₀.head e
        set m1 := pushHalfEdgeMem vCap eCap (G₀.tail e) (2 * e) m0
        have hold2 : stP1.mem (dgIncHeadBase guestBase vCap + G₀.head e) = 0 ∨
            stP1.mem (dgIncHeadBase guestBase vCap + G₀.head e) - 1 < 2 * eCap := by
          have h1 := hmP1_eq (dgIncHeadBase 0 vCap + G₀.head e) (by dsimp [dgIncHeadBase]; omega)
          rw [show guestBase + (dgIncHeadBase 0 vCap + G₀.head e) = dgIncHeadBase guestBase vCap + G₀.head e by
            dsimp [dgIncHeadBase]; omega] at h1
          rw [h1]
          by_cases hth : G₀.head e = G₀.tail e
          · right
            unfold m1 pushHalfEdgeMem
            rw [hth, Function.update_of_ne (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega),
                Function.update_self]; omega
          · have heq_inc : m1 (dgIncHeadBase 0 vCap + G₀.head e) = m0 (dgIncHeadBase 0 vCap + G₀.head e) := by
              unfold m1 pushHalfEdgeMem
              rw [Function.update_of_ne (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega),
                  Function.update_of_ne (by omega)]
              split_ifs with h0
              · rw [Function.update_of_ne (by dsimp [dgIncHeadBase, dgHeNextBase]; omega),
                    Function.update_of_ne (by dsimp [dgIncHeadBase, dgHePrevBase]; omega)]
              · rw [Function.update_of_ne (by dsimp [dgIncHeadBase, dgHePrevBase]; omega),
                    Function.update_of_ne (by dsimp [dgIncHeadBase, dgHeNextBase]; omega),
                    Function.update_of_ne (by dsimp [dgIncHeadBase, dgHePrevBase]; omega)]
            rw [heq_inc]
            have hhd := (hincL (G₀.head e) hh_lt).1.2.2.1
            cases hL : incL (G₀.head e) with
            | nil => left; rw [hhd, hL]
            | cons a l =>
              right; have ha := (hincL (G₀.head e) hh_lt).1.2.1 a (by rw [hL]; exact List.mem_cons_self)
              have hhd' : m0 (dgIncHeadBase 0 vCap + G₀.head e) = a + 1 := by
                simpa [m0, hL] using hhd
              omega
        have hdeg2 : stP1.mem (dgSlotDegBase guestBase vCap + G₀.head e) + 1 < 2 ^ w := by
          have h1 := hmP1_eq (dgSlotDegBase 0 vCap + G₀.head e) (by dsimp [dgSlotDegBase]; omega)
          rw [show guestBase + (dgSlotDegBase 0 vCap + G₀.head e) = dgSlotDegBase guestBase vCap + G₀.head e by
            dsimp [dgSlotDegBase]; omega] at h1
          rw [h1]
          have hdeg0 : m0 (dgSlotDegBase 0 vCap + G₀.head e) ≤ 2 * eCap :=
            calc m0 (dgSlotDegBase 0 vCap + G₀.head e) = (incL (G₀.head e)).length := (hincL _ hh_lt).2.1
              _ ≤ 2 * eCap := hinc_len _ hh_lt
          have hdeg0t : m0 (dgSlotDegBase 0 vCap + G₀.tail e) ≤ 2 * eCap :=
            calc m0 (dgSlotDegBase 0 vCap + G₀.tail e) = (incL (G₀.tail e)).length := (hincL _ ht_lt).2.1
              _ ≤ 2 * eCap := hinc_len _ ht_lt
          unfold m1 pushHalfEdgeMem
          by_cases hth : G₀.head e = G₀.tail e
          · rw [hth, Function.update_self]; omega
          · rw [Function.update_of_ne (by omega),
                Function.update_of_ne (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)]
            split_ifs
            · rw [Function.update_of_ne (by dsimp [dgSlotDegBase, dgHeNextBase]; omega),
                  Function.update_of_ne (by dsimp [dgSlotDegBase, dgHePrevBase]; omega)]; omega
            · rw [Function.update_of_ne (by dsimp [dgSlotDegBase, dgHePrevBase]; omega),
                  Function.update_of_ne (by dsimp [dgSlotDegBase, dgHeNextBase]; omega),
                  Function.update_of_ne (by dsimp [dgSlotDegBase, dgHePrevBase]; omega)]; omega
        obtain ⟨stP2, cP2, hrunP2, hmP2, hfrP2, hcP2⟩ :=
          pushHalfEdgeProc_runs (p := p) (ω := ω') (mem := stP1.mem) (pos := stP1.pos)
            hw16 hh_lt (by omega : 2 * e + 1 < 2 * eCap) hsz_lt hold2 hdeg2
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := e)
          (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr4, hr7,
            show dgEListBase guestBase vCap eCap + i < 2 ^ w by dsimp [dgEListBase]; omega]) he_val) ?_
        refine runs_seq_assign_le (v := G₀.tail e)
          (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr5,
            show dgETailSlotBase guestBase vCap eCap + e < 2 ^ w by dsimp [dgETailSlotBase]; omega]) hu_val) ?_
        refine runs_seq_assign_le (v := G₀.head e)
          (Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hr6,
            show dgEHeadSlotBase guestBase vCap eCap + e < 2 ^ w by dsimp [dgEHeadSlotBase]; omega]) hv_val) ?_
        have hcall1 : Runs w p ω'
            (.call 11 bPush [.reg 0, .reg 1, .reg 2, .reg 9, .bin .mul (.const 2) (.reg 8)])
            ⟨st.mem, Function.update (Function.update (Function.update st.regs 8 e) 9 (G₀.tail e)) 10 (G₀.head e), st.pos⟩
            .normal
            ⟨stP1.mem, Function.update (Function.update (Function.update (Function.update st.regs 8 e)
              9 (G₀.tail e)) 10 (G₀.head e)) 11 0, stP1.pos⟩
            (argsSize [.reg 0, .reg 1, .reg 2, .reg 9, .bin .mul (.const 2) (.reg 8)] + cP1 + 1) := by
          rw [runs_call_iff]
          exact ⟨[guestBase, vCap, eCap, G₀.tail e, 2 * e], pushHalfEdgeProc, .returned 0, stP1, cP1,
            by simp [evalArgs, Expr.eval, BinOp.eval, hr0, hr1, hr2, show 2 < 2 ^ w by omega,
              show 2 * e < 2 ^ w by omega],
            hpPush, hrunP1, rfl, rfl, rfl⟩
        refine runs_seq_of_runs' hcall1 ?_
        have hcall2 : Runs w p ω'
            (.call 11 bPush [.reg 0, .reg 1, .reg 2, .reg 10, .bin .add (.bin .mul (.const 2) (.reg 8)) (.const 1)])
            ⟨stP1.mem, Function.update (Function.update (Function.update (Function.update st.regs 8 e)
              9 (G₀.tail e)) 10 (G₀.head e)) 11 0, stP1.pos⟩
            .normal
            ⟨stP2.mem, Function.update (Function.update (Function.update (Function.update
              (Function.update st.regs 8 e) 9 (G₀.tail e)) 10 (G₀.head e)) 11 0) 11 0, stP2.pos⟩
            (argsSize [.reg 0, .reg 1, .reg 2, .reg 10, .bin .add (.bin .mul (.const 2) (.reg 8)) (.const 1)] + cP2 + 1) := by
          rw [runs_call_iff]
          exact ⟨[guestBase, vCap, eCap, G₀.head e, 2 * e + 1], pushHalfEdgeProc, .returned 0, stP2, cP2,
            by simp [evalArgs, Expr.eval, BinOp.eval, hr0, hr1, hr2, show 2 < 2 ^ w by omega,
              show 1 < 2 ^ w by omega, show 2 * e < 2 ^ w by omega, show 2 * e + 1 < 2 ^ w by omega],
            hpPush, hrunP2, rfl, rfl, rfl⟩
        refine ⟨.normal, _, _, hcall2, ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3],
          by simp [hr4], by simp [hr5], by simp [hr6], by simp, ?_, ?_⟩, by simp [hr7]⟩, ?_⟩
        · intro a ha
          rw [List.take_succ_eq_append_getElem hiL, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact (hmP2 a ha).trans (pushHalfEdgeMem_congr hh_lt hmP1_eq a ha)
        · intro addr haddr
          exact (hfrP2 addr haddr).trans ((hfrP1 addr haddr).trans (hfr_i addr haddr))
        · simp only [argsSize, Expr.size]; omega)).mono_cost (fun _ _ => by dsimp [Expr.size]; omega)
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp, by simp, by simp, rfl⟩ fun st₁ hinv => ?_
  rcases hinv with ⟨_, _, _, _, _, _, _, _, hmem_fin, hfr_fin⟩
  refine runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ⟨rfl, ?_, hfr_fin⟩
    (by simp only [Expr.size]; omega)
  intro a ha
  have h1 := hmem_fin a ha
  rwa [← heL_len, List.take_length] at h1

end MinCostFlow.SparseCore.Program
