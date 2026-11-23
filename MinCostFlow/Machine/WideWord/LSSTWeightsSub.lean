module

public import MinCostFlow.Machine.WideWord.LSSTWeightsBase
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Sub-procedure contracts for Theorem 2.2 weight computation

This module verifies the weight helper procedures in `weightsModule`
(`bitWidthProc`, `findMinLenProc`, `sumWeightsProc`, and `copyLimbsProc`).
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM MinCostFlow

/-! ### Sub-procedure contracts and verification -/

def bitWidthContract (w : ℕ) : Contract where
  pre args _ := ∃ nlCnt, args = [nlCnt] ∧ 4 < 2 ^ w ∧ 4 * nlCnt + 2 < 2 ^ w
  post args mem v mem' := mem' = mem ∧ v = Nat.log 2 (4 * args.getD 0 0 + 2) + 1
  cost args _ := 25 * args.getD 0 0 + 80

theorem bitWidth_meetsContract {w b h : ℕ} {p : Program}
    (hp : p.HasAt b (weightsModule b h)) :
    MeetsContract w p (b + idxBitWidth) (bitWidthContract w) := by
  have hentry : p.procs[b + idxBitWidth]? = some bitWidthProc := by
    have := hp 1 (by rw [weightsModule_length]; omega)
    simpa [weightsModule, idxBitWidth] using this
  refine meetsContract_of_runs hentry ?_
  rintro args mem pos ω _ ⟨nlCnt, rfl, hw4, hbd⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hlim_w : nlCnt + 2 < 2 ^ w := by omega
  let d0 := 4 * nlCnt + 2
  have hd0_pos : 2 ≤ d0 := by dsimp only [d0]; omega
  have hlog_bound : Nat.log 2 d0 + 1 ≤ nlCnt + 2 := by
    have hl : Nat.log 2 d0 < nlCnt + 2 :=
      (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) (by omega)).mpr (bitWidth_two_pow_bound nlCnt)
    omega
  refine runs_start_le ?_
  unfold bitWidthProc
  have hmul_bd : 4 * (startState [nlCnt] mem pos).regs 0 < 2 ^ w := by
    change 4 * nlCnt < 2 ^ w; omega
  have hadd_bd : 4 * (startState [nlCnt] mem pos).regs 0 + 2 < 2 ^ w := hbd
  refine runs_seq_assign_le (Expr.eval_add (Expr.eval_mul (Expr.eval_const hw4)
    (Expr.eval_reg_of_eq rfl) hmul_bd) (Expr.eval_const (by omega)) hadd_bd) ?_
  refine runs_seq_assign_le (Expr.eval_const (by omega : 0 < 2 ^ w)) ?_
  refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (v := nlCnt) (by
      dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl))
    (Expr.eval_const (by omega)) hlim_w) ?_
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 4)
    (P := fun s => s.mem = mem ∧ s.regs 1 = d0 ∧ s.regs 2 = 0 ∧ s.regs 3 = nlCnt + 2)
    (lo := .const 0) (hi := .reg 3)
    (body := .cond (.bin .lt (.const 0) (.reg 1))
      (.assign 1 (.bin .div (.reg 1) (.const 2)) ;; .assign 2 (.bin .add (.reg 2) (.const 1)))
      .nop)
    (Inv := fun i s => s.regs 4 = i ∧ s.mem = mem ∧ s.regs 3 = nlCnt + 2 ∧
      s.regs 1 = d0 / 2 ^ i ∧ s.regs 2 = min i (Nat.log 2 d0 + 1))
    14 0 (nlCnt + 2) (by omega) hw1 (fun _ => hlim_w)
    (fun s ⟨hm, r1, r2, r3⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      dsimp only
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), r3, r1, r2]
      exact ⟨rfl, hm, rfl, (Nat.div_one d0).symm, rfl⟩)
    (fun _ _ _ _ hi => hi.1)
    (fun _ s _ _ hi => Expr.eval_reg_of_eq hi.2.2.1)
    (fun i _ hi_le s _ ⟨r4, hm, r3, r1, r2⟩ => by
      have hd_le : s.regs 1 ≤ d0 := by rw [r1]; exact Nat.div_le_self _ _
      have hcnt_le : s.regs 2 ≤ nlCnt + 2 := by rw [r2]; omega
      have hcond : (Expr.bin .lt (.const 0) (.reg 1)).eval w s =
          some (if 0 < s.regs 1 then 1 else 0) :=
        Expr.eval_lt_op (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq rfl) hw1
      refine runs_start_le (runs_cond_le hcond ?_ ?_)
      · intro hT
        have hpos : 0 < s.regs 1 := by by_contra h0; simp [h0] at hT
        rw [r1, Nat.div_pos_iff] at hpos
        have hilog : i ≤ Nat.log 2 d0 := Nat.le_log_of_pow_le (by norm_num) hpos.2
        refine runs_seq_assign_le
          (Expr.eval_div (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega)) ?_
        refine runs_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq (v := min i (Nat.log 2 d0 + 1)) (by
              dsimp only; rw [Function.update_of_ne (by omega), r2]))
            (Expr.eval_const (by omega)) (by omega))
          ?_ (by dsimp only [argsSize, Expr.size]; omega)
        dsimp only
        refine ⟨⟨Function.update_self _ _ _,
          hm,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact r3,
          ?_, ?_⟩, by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact r4⟩
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self, r1,
            Nat.div_div_eq_div_mul, ← pow_succ]
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]; omega
      · intro hF
        have hzero : s.regs 1 = 0 := by
          by_contra hnz
          have hpos : 0 < s.regs 1 := Nat.pos_of_ne_zero hnz
          simp [hpos] at hF
        have hlt_pow : d0 < 2 ^ i := (Nat.div_eq_zero_iff.mp (r1 ▸ hzero)).resolve_left (by positivity)
        have hlog_lt : Nat.log 2 d0 < i := (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hlt_pow
        refine runs_nop_le ?_ (by dsimp only [argsSize, Expr.size]; omega)
        dsimp only
        refine ⟨⟨Function.update_self _ _ _, hm,
          by rw [Function.update_of_ne (by omega)]; exact r3, ?_, ?_⟩, r4⟩
        · rw [Function.update_of_ne (by omega), hzero]
          exact (Nat.div_eq_of_lt (lt_of_lt_of_le hlt_pow (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ i)))).symm
        · rw [Function.update_of_ne (by omega), r2]; omega)
  refine runs_seq_triple_le hloop ⟨rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_self]⟩ ?_
  rintro s ⟨_, hm, _, _, r2⟩
  have hmin : s.regs 2 = Nat.log 2 d0 + 1 := by rw [r2]; omega
  refine runs_ret_le (Expr.eval_reg_of_eq hmin) ⟨hm, rfl⟩ ?_
  have hget : ([nlCnt] : List ℕ).getD 0 0 = nlCnt := rfl
  have hcost : (bitWidthContract w).cost [nlCnt] mem = 25 * nlCnt + 80 := by
    simp only [bitWidthContract, hget]
  dsimp only [argsSize, Expr.size]
  rw [hcost]; omega

def findMinLenContract (w h : ℕ) : Contract where
  pre args mem := ∃ nlCnt nlPtr lenPtr L,
    args = [nlCnt, nlPtr, lenPtr, L] ∧
    1 ≤ nlCnt ∧ 1 ≤ L ∧ 0 < h ∧ 1 < 2 ^ w ∧ Num.base h < 2 ^ w ∧
    nlPtr + nlCnt < 2 ^ w ∧
    ∀ j < nlCnt, lenPtr + mem (nlPtr + j) * L + L < 2 ^ w ∧
      Num.Valid mem (lenPtr + mem (nlPtr + j) * L) h L
  post args mem v mem' := ∃ nlCnt nlPtr lenPtr L,
    args = [nlCnt, nlPtr, lenPtr, L] ∧
    mem' = mem ∧ ∃ minIdx < nlCnt, v = minIdx ∧
      ∀ j < nlCnt,
        Num.intVal mem (lenPtr + mem (nlPtr + minIdx) * L) h L ≤
          Num.intVal mem (lenPtr + mem (nlPtr + j) * L) h L
  cost args _ := args.getD 0 0 * (41 * args.getD 3 0 + 100) + 50

theorem findMinLen_meetsContract {w b h : ℕ} {p : Program}
    (hp : p.HasAt b (weightsModule b h)) :
    MeetsContract w p (b + idxFindMinLen) (findMinLenContract w h) := by
  have hsub := weights_hasAt_sub hp
  have hentry : p.procs[b + idxFindMinLen]? = some (findMinLenProc (b + idxWLess)) := by
    have := hp 2 (by rw [weightsModule_length]; omega)
    simpa [weightsModule, idxFindMinLen] using this
  refine meetsContract_of_runs hentry ?_
  rintro args mem pos ω _ ⟨nlCnt, nlPtr, lenPtr, L, rfl, hne, hL1, hh, hw1, hbh, hnl_w, hlen⟩
  have hless_mc := Num.less_meetsContract hh hw1 hbh hsub.2.2.1
  have h0_bd := (hlen 0 hne).1
  have hL_w : L < 2 ^ w := by omega
  have hnl_gt : nlCnt < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold findMinLenProc
  refine runs_seq_assign_le (Expr.eval_const (by omega : 0 < 2 ^ w)) ?_
  have hload0 : (Expr.load (.reg 1)).eval w
      ⟨mem, Function.update (startState [nlCnt, nlPtr, lenPtr, L] mem pos).regs 4 0, pos⟩ =
      some (mem nlPtr) :=
    Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by
      dsimp only; rw [Function.update_of_ne (by omega)]; rfl)) rfl
  have hmul0_lt : mem (nlPtr + 0) * L < 2 ^ w := by
    have h1 : mem (nlPtr + 0) * L ≤ lenPtr + mem (nlPtr + 0) * L + L := Nat.le_add_left _ _ |>.trans (Nat.le_add_right _ _)
    omega
  refine runs_seq_assign_le
    (Expr.eval_add (Expr.eval_reg_of_eq (v := lenPtr) (by dsimp only; rw [Function.update_of_ne (by omega)]; rfl))
      (Expr.eval_mul hload0 (Expr.eval_reg_of_eq (v := L) (by dsimp only; rw [Function.update_of_ne (by omega)]; rfl))
        hmul0_lt)
      (by have hnl0 : mem nlPtr = mem (nlPtr + 0) := rfl; rw [hnl0]; omega)) ?_
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6)
    (P := fun s => s.mem = mem ∧ s.regs 0 = nlCnt ∧ s.regs 1 = nlPtr ∧
      s.regs 2 = lenPtr ∧ s.regs 3 = L ∧ s.regs 4 = 0 ∧ s.regs 5 = lenPtr + mem (nlPtr + 0) * L)
    (lo := .const 1) (hi := .reg 0)
    (body := .assign 7 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 6))) (.reg 3))) ;;
      .call 8 (b + idxWLess) [.reg 7, .reg 5, .reg 3] ;;
      .cond (.bin .eq (.reg 8) (.const 1)) (.assign 4 (.reg 6) ;; .assign 5 (.reg 7)) .nop)
    (Inv := fun j s => s.regs 6 = j ∧ s.mem = mem ∧ s.regs 0 = nlCnt ∧ s.regs 1 = nlPtr ∧
      s.regs 2 = lenPtr ∧ s.regs 3 = L ∧
      ∃ mIdx, mIdx < j ∧ mIdx < nlCnt ∧ s.regs 4 = mIdx ∧
        s.regs 5 = lenPtr + mem (nlPtr + mIdx) * L ∧
        ∀ t < j, t < nlCnt →
          Num.intVal mem (lenPtr + mem (nlPtr + mIdx) * L) h L ≤
            Num.intVal mem (lenPtr + mem (nlPtr + t) * L) h L)
    (41 * L + 75) 1 nlCnt hne hw1 (fun _ => hnl_gt)
    (fun s ⟨hm, r0, r1, r2, r3, r4, r5⟩ => by
      refine ⟨Expr.eval_const hw1, ?_⟩
      dsimp only
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), r0, r1, r2, r3, r4, r5]
      refine ⟨rfl, hm, rfl, rfl, rfl, rfl, 0, by omega, hne, rfl, rfl, fun t ht _ => by
        have : t = 0 := by omega
        subst this; omega⟩)
    (fun _ _ _ _ hi => hi.1)
    (fun _ s _ _ hi => Expr.eval_reg_of_eq hi.2.2.1)
    (fun j _ hj_lt s _ ⟨r6, hm, r0, r1, r2, r3, mIdx, _, hm_nl, r4, r5, hmin⟩ => by
      have hpj_bd := (hlen j hj_lt).1
      have hpm_bd := (hlen mIdx hm_nl).1
      have hpj_w : lenPtr + mem (nlPtr + j) * L < 2 ^ w := by omega
      have hpm_w : lenPtr + mem (nlPtr + mIdx) * L < 2 ^ w := by omega
      have hload_j : (Expr.load (.bin .add (.reg 1) (.reg 6))).eval w s = some (mem (nlPtr + j)) := by
        refine Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1)
          (Expr.eval_reg_of_eq r6) (by omega)) (by rw [hm])
      refine runs_start_le (runs_seq_assign_le
        (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_mul hload_j (Expr.eval_reg_of_eq r3)
          (by omega)) hpj_w) ?_)
      let s₁ : State := ⟨s.mem, Function.update s.regs 7 (lenPtr + mem (nlPtr + j) * L), s.pos⟩
      have hargs : evalArgs w s₁ [.reg 7, .reg 5, .reg 3] =
          some [lenPtr + mem (nlPtr + j) * L, lenPtr + mem (nlPtr + mIdx) * L, L] := by
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_self])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r5])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r3]))
          (evalArgs_nil _ _)
      have hpre_l : (Num.lessContract w h).pre
          [lenPtr + mem (nlPtr + j) * L, lenPtr + mem (nlPtr + mIdx) * L, L] s₁.mem := by
        refine ⟨lenPtr + mem (nlPtr + j) * L, lenPtr + mem (nlPtr + mIdx) * L, L, rfl,
          hpj_bd, hpm_bd, ?_, ?_⟩
        · dsimp only [s₁]; rw [hm]; exact (hlen j hj_lt).2
        · dsimp only [s₁]; rw [hm]; exact (hlen mIdx hm_nl).2
      refine runs_seq_call_le hless_mc hargs
        (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> omega) hpre_l ?_
      intro ret _ pos' hpost
      obtain ⟨rfl, hret_eq⟩ := hpost
      dsimp only [List.getD_cons_zero, List.getD_cons_succ] at hret_eq
      change ret = if Num.intVal s₁.mem (lenPtr + mem (nlPtr + j) * L) h L <
          Num.intVal s₁.mem (lenPtr + mem (nlPtr + mIdx) * L) h L then 1 else 0 at hret_eq
      have hm1 : s₁.mem = mem := hm
      rw [hm1] at hret_eq
      let s₂ : State := ⟨s₁.mem, Function.update s₁.regs 8 ret, pos'⟩
      have hs2_r6 : s₂.regs 6 = j := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r6]
      have hs2_r0 : s₂.regs 0 = nlCnt := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r0]
      have hs2_r1 : s₂.regs 1 = nlPtr := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r1]
      have hs2_r2 : s₂.regs 2 = lenPtr := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r2]
      have hs2_r3 : s₂.regs 3 = L := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r3]
      have hs2_r4 : s₂.regs 4 = mIdx := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r4]
      have hs2_r5 : s₂.regs 5 = lenPtr + mem (nlPtr + mIdx) * L := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r5]
      have hs2_r7 : s₂.regs 7 = lenPtr + mem (nlPtr + j) * L := by
        dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_self]
      have hcond : (Expr.bin .eq (.reg 8) (.const 1)).eval w s₂ =
          some (if ret = 1 then 1 else 0) :=
        Expr.eval_eq_op (Expr.eval_reg_of_eq (by dsimp only [s₂]; rw [Function.update_self]))
          (Expr.eval_const hw1) hw1
      refine runs_cond_le hcond ?_ ?_
      · intro hT
        have hlt1 : ret = 1 := by by_contra hne1; simp [hne1] at hT
        have hjlt : Num.intVal mem (lenPtr + mem (nlPtr + j) * L) h L <
            Num.intVal mem (lenPtr + mem (nlPtr + mIdx) * L) h L := by
          split_ifs at hret_eq with hlt
          · exact hlt
          · omega
        refine runs_seq_assign_le (Expr.eval_reg_of_eq hs2_r6) ?_
        refine runs_assign_le (Expr.eval_reg_of_eq (v := lenPtr + mem (nlPtr + j) * L) (by
            dsimp only; rw [Function.update_of_ne (by omega)]; exact hs2_r7)) ?_
          (by
            have hc : (Num.lessContract w h).cost [lenPtr + mem (nlPtr + j) * L, lenPtr + mem (nlPtr + mIdx) * L, L] s₁.mem =
                41 * L + 51 := rfl
            dsimp only [argsSize, Expr.size] at *
            rw [hc]; omega)
        refine ⟨⟨by dsimp only [s₂, s₁]; exact Function.update_self _ _ _,
          hm1,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r0,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r1,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r2,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r3,
          j, by omega, hj_lt,
          by dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
          by dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_self],
          fun t ht htnl => ?_⟩,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r6⟩
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ ht) with rfl | ht_j
        · omega
        · exact le_trans hjlt.le (hmin t ht_j htnl)
      · intro hF
        have hnot1 : ret ≠ 1 := by intro heq; simp [heq] at hF
        have hle_j : Num.intVal mem (lenPtr + mem (nlPtr + mIdx) * L) h L ≤
            Num.intVal mem (lenPtr + mem (nlPtr + j) * L) h L := by
          split_ifs at hret_eq with hlt
          · omega
          · exact not_lt.mp hlt
        refine runs_nop_le ?_
          (by
            have hc : (Num.lessContract w h).cost [lenPtr + mem (nlPtr + j) * L, lenPtr + mem (nlPtr + mIdx) * L, L] s₁.mem =
                41 * L + 51 := rfl
            dsimp only [argsSize, Expr.size] at *
            rw [hc]; omega)
        refine ⟨⟨by dsimp only [s₂, s₁]; exact Function.update_self _ _ _,
          hm1,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r0,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r1,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r2,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r3,
          mIdx, by omega, hm_nl,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r4,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r5,
          fun t ht htnl => ?_⟩,
          by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r6⟩
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ ht) with rfl | ht_j
        · exact hle_j
        · exact hmin t ht_j htnl)
  refine runs_seq_triple_le hloop ⟨rfl, by
      dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_self]; simp only [Nat.add_zero]⟩ ?_
  rintro s ⟨_, hm, _, _, _, _, mIdx, _, hm_nl, r4, _, hmin⟩
  have hm_w : mIdx < 2 ^ w := lt_trans hm_nl hnl_gt
  refine runs_ret_le (Expr.eval_reg_of_eq r4) ⟨nlCnt, nlPtr, lenPtr, L, rfl, hm, mIdx, hm_nl,
    rfl, fun j hj => hmin j hj hj⟩ ?_
  have hget0 : ([nlCnt, nlPtr, lenPtr, L] : List ℕ).getD 0 0 = nlCnt := rfl
  have hget3 : ([nlCnt, nlPtr, lenPtr, L] : List ℕ).getD 3 0 = L := rfl
  have hcost : (findMinLenContract w h).cost [nlCnt, nlPtr, lenPtr, L] mem =
      nlCnt * (41 * L + 100) + 50 := by
    simp only [findMinLenContract, hget0, hget3]
  have hloop_le : (nlCnt - 1) * (41 * L + 75 + 1 + 8) ≤ nlCnt * (41 * L + 100) :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  dsimp only [argsSize, Expr.size]
  rw [hcost]; omega

def sumWeightsContract (w h : ℕ) : Contract where
  pre args mem := ∃ nlCnt nlPtr wtPtr L K heap,
    args = [nlCnt, nlPtr, wtPtr, L, K, heap] ∧
    1 ≤ nlCnt ∧ 1 ≤ L ∧ 0 < h ∧ 2 * h + 2 ≤ w ∧ K = kWidthOf nlCnt L ∧
    nlPtr + nlCnt ≤ heap ∧
    (∀ j < nlCnt, wtPtr + mem (nlPtr + j) * L + L ≤ heap ∧
      Num.Valid mem (wtPtr + mem (nlPtr + j) * L) h L ∧
      0 < Num.intVal mem (wtPtr + mem (nlPtr + j) * L) h L) ∧
    ZeroFrom mem heap ∧ heap + K + nlCnt * (2 * K) < 2 ^ w
  post args mem v mem' := ∃ nlCnt nlPtr wtPtr L K heap,
    args = [nlCnt, nlPtr, wtPtr, L, K, heap] ∧
    v = heap + K + nlCnt * (2 * K) ∧
    ZeroFrom mem' v ∧
    (∀ a < heap, mem' a = mem a) ∧
    Num.Valid mem' (v - K) h K ∧
    Num.intVal mem' (v - K) h K =
      (((List.range nlCnt).map fun j => Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L).sum : ℤ) ∧
    Num.unsignedVal mem' (v - K) h K =
      ((List.range nlCnt).map fun j => Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L).sum ∧
    2 * ((List.range nlCnt).map fun j => Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L).sum < Num.capacity h K
  cost args _ := args.getD 0 0 * (70 * args.getD 4 0 + 120) + 25 * args.getD 4 0 + 50

theorem sumWeights_meetsContract {w b h : ℕ} {p : Program}
    (hp : p.HasAt b (weightsModule b h)) :
    MeetsContract w p (b + idxSumWeights) (sumWeightsContract w h) := by
  have hsub := weights_hasAt_sub hp
  have hentry : p.procs[b + idxSumWeights]? =
      some (sumWeightsProc (b + idxWLoadSmall) (b + idxWSignExtend) (b + idxWAdd)) := by
    have := hp 3 (by rw [weightsModule_length]; omega)
    simpa [weightsModule, idxSumWeights] using this
  refine meetsContract_of_runs hentry ?_
  rintro args mem pos ω _ ⟨nlCnt, nlPtr, wtPtr, L, K, heap, rfl, hne, hL1, hh, hw2,
    rfl, hnl_h, hwt_val, hz0, hbound⟩
  let K := kWidthOf nlCnt L
  change heap + K + nlCnt * (2 * K) < 2 ^ w at hbound
  have hkb := kWidth_capacity_bounds (h := h) hh hL1 hne
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have hls_mc := Num.loadSmall_meetsContract hw1 hbh hsub.1
  have hse_mc := Num.signExtend_meetsContract hh hw1 hbh hsub.2.2.2.1
  have had_mc := Num.add_meetsContract hh hw2 hsub.2.2.2.2.1
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hnlK_bd : K + nlCnt * (2 * K) < 2 ^ w := by omega
  have h2K_mul : 2 * K ≤ nlCnt * (2 * K) := Nat.le_mul_of_pos_left (2 * K) hne
  have hK_w : K < 2 ^ w := by omega
  have h2K_w : 2 * K < 2 ^ w := by omega
  have hheap_w : heap < 2 ^ w := by omega
  have hnl_w : nlCnt < 2 ^ w := by
    have : nlCnt ≤ nlCnt * (2 * K) := Nat.le_mul_of_pos_right nlCnt (by omega)
    omega
  have hv_nat : ∀ j < nlCnt, 2 * Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L < Num.capacity h L ∧
      Num.intVal mem (wtPtr + mem (nlPtr + j) * L) h L =
        (Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L : ℤ) := by
    intro j hj
    have h1 := intVal_eq_nat_of_pos (hwt_val j hj).2.1 (hwt_val j hj).2.2
    exact ⟨h1.2.1, h1.1⟩
  have hsum_ub : ∀ j ≤ nlCnt,
      2 * ((List.range j).map fun t => Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum <
        Num.capacity h K := by
    intro j hj
    have h1 : ((List.range j).map fun t => Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum ≤
        j * Num.capacity h L := by
      have hm_le : ∀ x ∈ (List.range j).map fun t =>
          Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L, x ≤ Num.capacity h L := by
        rintro x hx
        obtain ⟨t, ht_r, rfl⟩ := List.mem_map.mp hx
        have ht_lt : t < j := List.mem_range.mp ht_r
        exact le_of_lt (Num.unsignedVal_lt (hwt_val t (by omega)).2.1)
      have hsum_le := List.sum_le_length_nsmul
        ((List.range j).map fun t => Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L)
        (Num.capacity h L) hm_le
      simpa [smul_eq_mul] using hsum_le
    calc 2 * ((List.range j).map fun t => Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum
        ≤ 2 * (j * Num.capacity h L) := Nat.mul_le_mul_left 2 h1
      _ ≤ 2 * (nlCnt * Num.capacity h L) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hj)
      _ = 2 * nlCnt * Num.capacity h L := by ring
      _ < Num.capacity h K := hkb.2.2.2.2.2.1
  refine runs_start_le ?_
  unfold sumWeightsProc
  refine runs_seq_assign_le (Expr.eval_reg_of_eq (by rfl : _ = heap)) ?_
  refine runs_seq_call_le hls_mc (vs := [0, K, heap]) (by
      refine evalArgs_cons (Expr.eval_const (by omega)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega)]; rfl)) ?_
      refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by omega)]; rfl))
        (evalArgs_nil _ _))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> omega)
    ⟨⟨0, K, heap, rfl⟩, hz0, by show heap + K < 2 ^ w; omega⟩ ?_
  intro hp1 mem1 pos1 hp1_post
  obtain ⟨rfl, _, _, hfr1, hz1, hdig0⟩ := hp1_post
  have hz1' : ZeroFrom mem1 (heap + K) := by
    change ZeroFrom mem1 (heapArg [0, K, heap] + K)
    exact hz1
  have hfr1' : ∀ x < heap, mem1 x = mem x := by
    change ∀ x < heapArg [0, K, heap], mem1 x = (startState [nlCnt, nlPtr, wtPtr, L, K, heap] mem pos).mem x at hfr1
    exact hfr1
  have hdig0' : ListAt mem1 heap (Num.digits h K 0) := by
    change ListAt mem1 (heapArg [0, K, heap]) (Num.digits h ([0, K, heap].getD 1 0) ([0, K, heap].getD 0 0)) at hdig0
    exact hdig0
  have hval0 : Num.Valid mem1 heap h K ∧ Num.unsignedVal mem1 heap h K = 0 ∧
      Num.intVal mem1 heap h K = 0 := by
    have hv := Num.loadSmall_value hdig0'
    refine ⟨hv.1, ?_, ?_⟩
    · rw [hv.2.1, Nat.zero_mod]
    · rw [hv.2.2, Nat.zero_mod]; simp [Num.signedVal, Num.capacity, Num.base]
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 8)
    (P := fun s => s.mem = mem1 ∧ s.regs 0 = nlCnt ∧ s.regs 1 = nlPtr ∧
      s.regs 2 = wtPtr ∧ s.regs 3 = L ∧ s.regs 4 = K ∧ s.regs 5 = heap + K ∧ s.regs 6 = heap)
    (lo := .const 0) (hi := .reg 0)
    (body := .assign 9 (.bin .add (.reg 2) (.bin .mul (.load (.bin .add (.reg 1) (.reg 8))) (.reg 3))) ;;
      .call 7 (b + idxWSignExtend) [.reg 9, .reg 3, .reg 4, .reg 5] ;;
      .call 9 (b + idxWAdd) [.reg 6, .reg 5, .reg 4, .reg 7] ;;
      .assign 6 (.reg 7) ;;
      .assign 5 (.reg 9))
    (Inv := fun j s => s.regs 8 = j ∧ s.regs 0 = nlCnt ∧ s.regs 1 = nlPtr ∧
      s.regs 2 = wtPtr ∧ s.regs 3 = L ∧ s.regs 4 = K ∧
      s.regs 5 = heap + K + j * (2 * K) ∧ s.regs 6 = heap + j * (2 * K) ∧
      ZeroFrom s.mem (heap + K + j * (2 * K)) ∧
      (∀ a < heap, s.mem a = mem a) ∧
      Num.Valid s.mem (heap + j * (2 * K)) h K ∧
      Num.intVal s.mem (heap + j * (2 * K)) h K =
        (((List.range j).map fun t => Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum : ℤ))
    (70 * K + 105) 0 nlCnt (by omega) hw1 (fun _ => hnl_w)
    (fun s ⟨hm, r0, r1, r2, r3, r4, r5, r6⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      dsimp only
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), r0, r1, r2, r3, r4, r5, r6]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by omega, by omega,
        by simpa [hm] using hz1', fun a ha => by rw [hm, hfr1' a ha],
        by simpa [hm] using hval0.1, by simpa [hm] using hval0.2.2⟩)
    (fun _ _ _ _ hi => hi.1)
    (fun _ s _ _ hi => Expr.eval_reg_of_eq hi.2.1)
    (fun j _ hj_lt s _ ⟨r8, r0, r1, r2, r3, r4, r5, r6, hz_s, hfr_s, hvs, hints⟩ => by
      have hwt_bd := (hwt_val j hj_lt).1
      have hj_mul : j * (2 * K) + 2 * K ≤ nlCnt * (2 * K) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right (2 * K) hj_lt
      have hwt_sub_w : wtPtr + mem (nlPtr + j) * L < 2 ^ w := by omega
      have hload_j : (Expr.load (.bin .add (.reg 1) (.reg 8))).eval w s = some (mem (nlPtr + j)) := by
        refine Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1)
          (Expr.eval_reg_of_eq r8) (by omega)) (hfr_s _ (by omega))
      refine runs_start_le (runs_seq_assign_le
        (Expr.eval_add (Expr.eval_reg_of_eq r2) (Expr.eval_mul hload_j (Expr.eval_reg_of_eq r3)
          (by omega)) hwt_sub_w) ?_)
      let s₁ : State := ⟨s.mem, Function.update s.regs 9 (wtPtr + mem (nlPtr + j) * L), s.pos⟩
      have hargs_se : evalArgs w s₁ [.reg 9, .reg 3, .reg 4, .reg 5] =
          some [wtPtr + mem (nlPtr + j) * L, L, K, heap + K + j * (2 * K)] := by
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_self])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r3])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r4])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₁]; rw [Function.update_of_ne (by omega), r5]))
          (evalArgs_nil _ _)
      have hpre_se : (Num.signExtendContract w h).pre
          [wtPtr + mem (nlPtr + j) * L, L, K, heap + K + j * (2 * K)] s₁.mem := by
        have hmem_wt : Num.Valid s₁.mem (wtPtr + mem (nlPtr + j) * L) h L :=
          numValid_congr (fun i hi => (hfr_s _ (by omega)).symm) (hwt_val j hj_lt).2.1
        refine ⟨⟨wtPtr + mem (nlPtr + j) * L, L, K, heap + K + j * (2 * K), rfl, hkb.1, by omega, hmem_wt⟩,
          hz_s, by show heap + K + j * (2 * K) + K < 2 ^ w; omega⟩
      refine runs_seq_call_le hse_mc hargs_se (fun x hx => by
        simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> omega) hpre_se ?_
      intro hp_mid mem2 pos2 hse_post
      obtain ⟨rfl, _, _, hfr2, hz2, hv_ext, hint_ext⟩ := hse_post
      have hz2' : ZeroFrom mem2 (heap + K + j * (2 * K) + K) := by
        change ZeroFrom mem2 (heapArg [wtPtr + mem (nlPtr + j) * L, L, K, heap + K + j * (2 * K)] +
          [wtPtr + mem (nlPtr + j) * L, L, K, heap + K + j * (2 * K)].getD 2 0) at hz2
        exact hz2
      have hfr2' : ∀ x < heap + K + j * (2 * K), mem2 x = s₁.mem x := hfr2
      have hv_ext' : Num.Valid mem2 (heap + K + j * (2 * K)) h K := hv_ext
      have hint_ext' : Num.intVal mem2 (heap + K + j * (2 * K)) h K =
          Num.intVal s₁.mem (wtPtr + mem (nlPtr + j) * L) h L := hint_ext
      let s₂ : State := ⟨mem2, Function.update s₁.regs 7 (heap + K + j * (2 * K) + K), pos2⟩
      have hargs_add : evalArgs w s₂ [.reg 6, .reg 5, .reg 4, .reg 7] =
          some [heap + j * (2 * K), heap + K + j * (2 * K), K, heap + K + j * (2 * K) + K] := by
        refine evalArgs_cons (Expr.eval_reg_of_eq (by
          dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r6])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by
          dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r5])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by
          dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), r4])) ?_
        refine evalArgs_cons (Expr.eval_reg_of_eq (by dsimp only [s₂]; rw [Function.update_self])) (evalArgs_nil _ _)
      have hS_pres : Num.Valid mem2 (heap + j * (2 * K)) h K ∧
          Num.intVal mem2 (heap + j * (2 * K)) h K = Num.intVal s.mem (heap + j * (2 * K)) h K := by
        have heq : ∀ i < K, mem2 (heap + j * (2 * K) + i) = s.mem (heap + j * (2 * K) + i) :=
          fun i hi => hfr2' _ (by omega)
        exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hvs, intVal_congr_range heq⟩
      have hpre_add : (Num.addContract w h).pre
          [heap + j * (2 * K), heap + K + j * (2 * K), K, heap + K + j * (2 * K) + K] s₂.mem := by
        refine ⟨heap + j * (2 * K), heap + K + j * (2 * K), K, heap + K + j * (2 * K) + K, rfl,
          ⟨heap + j * (2 * K), heap + K + j * (2 * K), K, 0, heap + K + j * (2 * K) + K, rfl,
            by omega, by omega, by omega, hS_pres.1, hv_ext'⟩,
          hz2', by show heap + K + j * (2 * K) + K + K < 2 ^ w; omega⟩
      refine runs_seq_call_le had_mc hargs_add (fun x hx => by
        simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> omega) hpre_add ?_
      intro hp_next mem3 pos3 hadd_post
      obtain ⟨rfl, _, _, hfr3, hz3, hdig_sum⟩ := hadd_post
      have hz3' : ZeroFrom mem3 (heap + K + j * (2 * K) + K + K) := hz3
      have hfr3' : ∀ x < heap + K + j * (2 * K) + K, mem3 x = mem2 x := hfr3
      have hdig_sum' : ListAt mem3 (heap + K + j * (2 * K) + K) (Num.digits h K
          (Num.unsignedVal mem2 (heap + j * (2 * K)) h K +
            Num.unsignedVal mem2 (heap + K + j * (2 * K)) h K + 0)) := hdig_sum
      have hint_ext_nat : Num.intVal mem2 (heap + K + j * (2 * K)) h K =
          (Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L : ℤ) := by
        rw [hint_ext', intVal_congr_range (fun i hi => hfr_s _ (by omega)), (hv_nat j hj_lt).2]
      have hadd_fits : Num.Fits h K
          (Num.intVal mem2 (heap + j * (2 * K)) h K +
            Num.intVal mem2 (heap + K + j * (2 * K)) h K + (0 : ℤ)) := by
        rw [hS_pres.2, hints, hint_ext_nat]
        have hsum_new : ((List.range (j + 1)).map fun t =>
              Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum =
            ((List.range j).map fun t =>
              Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum +
            Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L := by
          rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        have h2lt := hsum_ub (j + 1) hj_lt
        rw [hsum_new] at h2lt
        simpa [Nat.cast_add, add_zero] using fits_of_lt_half_cap h2lt
      have hadd_val := Num.addCarry_value hdig_sum'
      have hadd_exact := Num.addCarry_value_of_fits hdig_sum' hadd_fits
      have hsum_final : Num.intVal mem3 (heap + (j + 1) * (2 * K)) h K =
          (((List.range (j + 1)).map fun t =>
            Num.unsignedVal mem (wtPtr + mem (nlPtr + t) * L) h L).sum : ℤ) := by
        have haddr : heap + K + j * (2 * K) + K = heap + (j + 1) * (2 * K) := by ring
        rw [← haddr, hadd_exact, hS_pres.2, hints, hint_ext_nat, List.range_succ,
          List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        omega
      refine runs_seq_assign_le (Expr.eval_reg_of_eq (v := heap + K + j * (2 * K) + K) (by
          dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]; rfl)) ?_
      refine runs_assign_le (Expr.eval_reg_of_eq (v := heap + K + j * (2 * K) + K + K) (by
          dsimp only; rw [Function.update_of_ne (by omega), Function.update_self]; rfl)) ?_
        (by
          have hc1 : (Num.signExtendContract w h).cost
              [wtPtr + mem (nlPtr + j) * L, L, K, heap + K + j * (2 * K)] s₁.mem = 30 * K + 42 := rfl
          have hc2 : (Num.addContract w h).cost
              [heap + j * (2 * K), heap + K + j * (2 * K), K, heap + K + j * (2 * K) + K] s₂.mem = 38 * K + 15 := rfl
          dsimp only [argsSize, Expr.size] at *
          rw [hc1, hc2]; omega)
      have hhp_eq : heap + K + j * (2 * K) + K + K = heap + K + (j + 1) * (2 * K) := by ring
      refine ⟨⟨by dsimp only [s₂, s₁]; exact Function.update_self _ _ _,
        by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r0,
        by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r1,
        by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r2,
        by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r3,
        by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r4,
        by dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_self]; ring,
        by dsimp only [s₂, s₁]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]; ring,
        ?_, ?_, ?_, hsum_final⟩,
        by dsimp only [s₂, s₁]; repeat' rw [Function.update_of_ne (by omega)]; exact r8⟩
      · simpa [hhp_eq] using hz3'
      · intro a ha
        dsimp only [s₂, s₁]
        rw [hfr3' a (by omega), hfr2' a (by omega), hfr_s a ha]
      · have haddr : heap + K + j * (2 * K) + K = heap + (j + 1) * (2 * K) := by ring
        simpa [haddr] using hadd_val.1)
  refine runs_seq_triple_le hloop ⟨rfl, by
      dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl,
    by dsimp only [heapArg, List.getLastD, List.getD]; rw [Function.update_self]; rfl,
    by dsimp only [heapArg, List.getLastD, List.getD]; rw [Function.update_of_ne (by omega), Function.update_self]⟩ ?_
  rintro s ⟨_, _, _, _, _, _, r5, _, hz_f, hfr_f, hv_f, hint_f⟩
  have hsub_eq : s.regs 5 - K = heap + nlCnt * (2 * K) := by rw [r5]; omega
  have hval_sub : (Outcome.returned (heap + K + nlCnt * (2 * K))).value - K =
      heap + nlCnt * (2 * K) := by
    dsimp only [Outcome.value]; omega
  have hu_eq : Num.unsignedVal s.mem (heap + nlCnt * (2 * K)) h K =
      ((List.range nlCnt).map fun j => Num.unsignedVal mem (wtPtr + mem (nlPtr + j) * L) h L).sum := by
    dsimp only [Num.intVal, Num.signedVal] at hint_f
    split_ifs at hint_f with hlt
    · have hu_lt := Num.unsignedVal_lt hv_f
      omega
    · exact Int.ofNat.inj hint_f
  refine runs_ret_le (Expr.eval_reg_of_eq r5)
    ⟨nlCnt, nlPtr, wtPtr, L, K, heap, rfl, rfl, hz_f, hfr_f,
      by rw [hval_sub]; exact hv_f, by rw [hval_sub]; exact hint_f, by rw [hval_sub]; exact hu_eq,
      hsum_ub nlCnt (le_refl _)⟩ ?_
  have hcost_val : (sumWeightsContract w h).cost [nlCnt, nlPtr, wtPtr, L, K, heap] mem =
      nlCnt * (70 * K + 120) + 25 * K + 50 := rfl
  have hc0 : (Num.loadSmallContract w h).cost [0, K, heap]
      (startState [nlCnt, nlPtr, wtPtr, L, kWidthOf nlCnt L, heap] mem pos).mem = 23 * K + 6 := rfl
  have hloop_le : (nlCnt - 0) * (70 * K + 105 + 1 + 8) ≤ nlCnt * (70 * K + 120) := by
    simp only [Nat.sub_zero]
    exact Nat.mul_le_mul_left nlCnt (by omega)
  clear hval_sub hsub_eq
  dsimp only [argsSize, Expr.size]
  rw [hcost_val, hc0]
  omega

def copyLimbsContract (w : ℕ) : Contract where
  pre args _ := ∃ src K dst, args = [src, K, dst] ∧ 1 < 2 ^ w ∧
    src + K < 2 ^ w ∧ dst + K < 2 ^ w ∧ DisjointRanges src K dst K
  post args mem v mem' := ∃ src K dst, args = [src, K, dst] ∧ v = 0 ∧
    (∀ i < K, mem' (dst + i) = mem (src + i)) ∧
    (∀ a, a < dst ∨ dst + K ≤ a → mem' a = mem a)
  cost args _ := 25 * args.getD 1 0 + 15

theorem copyLimbs_meetsContract {w b h : ℕ} {p : Program}
    (hp : p.HasAt b (weightsModule b h)) :
    MeetsContract w p (b + idxCopyLimbs) (copyLimbsContract w) := by
  have hentry : p.procs[b + idxCopyLimbs]? = some copyLimbsProc := by
    have := hp 5 (by rw [weightsModule_length]; omega)
    simpa [weightsModule, idxCopyLimbs] using this
  refine meetsContract_of_runs hentry ?_
  rintro args mem pos ω _ ⟨src, K, dst, rfl, hw1, hsrc_w, hdst_w, hdisj⟩
  refine runs_start_le ?_
  unfold copyLimbsProc
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3)
    (P := fun s => s.mem = mem ∧ s.regs 0 = src ∧ s.regs 1 = K ∧ s.regs 2 = dst)
    (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (Inv := fun j s => s.regs 3 = j ∧ s.regs 0 = src ∧ s.regs 1 = K ∧ s.regs 2 = dst ∧
      (∀ i < j, s.mem (dst + i) = mem (src + i)) ∧
      (∀ a, a < dst ∨ dst + K ≤ a → s.mem a = mem a) ∧
      (∀ i, j ≤ i → i < K → s.mem (dst + i) = mem (dst + i)))
    15 0 K (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s ⟨hm, r0, r1, r2⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      dsimp only
      rw [Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), r0, r1, r2]
      exact ⟨rfl, rfl, rfl, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _),
        fun _ _ => by rw [hm], fun _ _ _ => by rw [hm]⟩)
    (fun _ _ _ _ hi => hi.1)
    (fun _ s _ _ hi => Expr.eval_reg_of_eq hi.2.2.1)
    (fun j _ hj_lt s _ ⟨r3, r0, r1, r2, hpref, hfr, hrem⟩ => by
      have hsrc_mem : s.mem (src + j) = mem (src + j) := by
        rcases hdisj with h | h
        · exact hfr (src + j) (Or.inl (by omega))
        · exact hfr (src + j) (Or.inr (by omega))
      refine runs_start_le (runs_store_le
        (Expr.eval_add (w := w) (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r3) (by omega))
        (@Expr.eval_load_of_eq w s (.bin .add (.reg 0) (.reg 3)) (src + j) (mem (src + j))
          (Expr.eval_add (w := w) (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3) (by omega)) hsrc_mem)
        ?_ (by
          have hsz : (Expr.bin .add (.reg 2) (.reg 3)).size +
              (Expr.load (.bin .add (.reg 0) (.reg 3))).size + 1 = 8 := rfl
          dsimp only; rw [hsz]; omega))
      dsimp only
      refine ⟨⟨Function.update_self _ _ _,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact r0,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact r1,
        by dsimp only; rw [Function.update_of_ne (by omega)]; exact r2,
        fun i hi => ?_, fun a ha => ?_, fun i hji hiK => ?_⟩, r3⟩
      · dsimp only
        rcases eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hij
        · rw [Function.update_self]
        · rw [Function.update_of_ne (by omega)]; exact hpref i hij
      · dsimp only
        rw [Function.update_of_ne (by omega)]; exact hfr a ha
      · dsimp only
        rw [Function.update_of_ne (by omega)]; exact hrem i (by omega) hiK)
  refine runs_seq_triple_le hloop ⟨rfl, rfl, rfl, rfl⟩ ?_
  rintro s ⟨_, _, _, _, hpref, hfr, _⟩
  refine runs_ret_le (Expr.eval_const (by omega)) ⟨src, K, dst, rfl, rfl, hpref, hfr⟩ ?_
  have hc : (copyLimbsContract w).cost [src, K, dst] mem = 25 * K + 15 := rfl
  dsimp only [argsSize, Expr.size]
  rw [hc]; omega

end MinCostFlow.WideWord
