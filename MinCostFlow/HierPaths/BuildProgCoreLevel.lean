module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OuterCorePlayer

/-!
# Computing the core recursion level in Word RAM

Given `(M, r, s)` with `1 ≤ r` and `1 < s`, compute `coreLevel M r s = Nat.clog (NOf M r) s`
without touching memory. Division by `2` yields `ell M = Nat.clog 2 (2 * M + 2)` without
overflowing `2 * M + 2`, `(ell M - 1) / r + 1` computes `ceilDiv (ell M) r` without adding `r`,
repeated doubling computes `NOf M r`, and repeated ceiling division computes `coreLevel M r s`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Compute `coreLevel M r s` from `[M, r, s]` without touching memory. -/
def buildCoreLevelProc : Stmt :=
  .assign 3 (.reg 0) ;;
  .assign 4 (.const 1) ;;
  .loop (.reg 3)
    (.assign 3 (.bin .div (.reg 3) (.const 2)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  .assign 5 (.bin .add (.bin .div (.bin .sub (.reg 4) (.const 1)) (.reg 1)) (.const 1)) ;;
  .cond (.bin .lt (.reg 5) (.const 2)) (.assign 5 (.const 2)) .nop ;;
  .assign 6 (.const 1) ;;
  forRange 7 (.const 0) (.reg 5) (.assign 6 (.bin .add (.reg 6) (.reg 6))) ;;
  .assign 8 (.const 0) ;;
  .assign 9 (.reg 2) ;;
  .loop (.bin .lt (.const 1) (.reg 9))
    (.assign 9 (.bin .add (.bin .div (.bin .sub (.reg 9) (.const 1)) (.reg 6)) (.const 1)) ;;
     .assign 8 (.bin .add (.reg 8) (.const 1))) ;;
  .ret (.reg 8)

theorem buildCoreLevelProc_noRand : buildCoreLevelProc.NoRand := by
  simp [buildCoreLevelProc, forRange, forUp, Stmt.NoRand]

/-- Contract for computing `coreLevel M r s` in `O(ell M + s)` steps with no memory writes. -/
def buildCoreLevelContract (w : ℕ) : Contract where
  pre args _ := ∃ M r s, args = [M, r, s] ∧ 1 ≤ r ∧ 1 < s ∧ NOf M r < 2 ^ w ∧ 2 < 2 ^ w
  post args mem v mem' := ∃ M r s, args = [M, r, s] ∧ v = coreLevel M r s ∧ mem' = mem
  cost args _ := 32 * ell (args.getD 0 0) + 24 * args.getD 2 0 + 120

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private theorem ell_zero : ell 0 = 1 := by
  unfold ell; decide

private theorem ell_pos (M : ℕ) : 1 ≤ ell M := by
  unfold ell
  exact Nat.clog_pos (by decide) (by omega)

private theorem ell_succ_div2 {x : ℕ} (hx : 0 < x) : ell x = ell (x / 2) + 1 := by
  unfold ell
  have h1 : Nat.clog 2 (2 * x + 2) = Nat.clog 2 (x + 1) + 1 := by
    rw [Nat.clog_of_one_lt (by decide) (by omega)]
    rw [show (2 * x + 2 + 2 - 1) / 2 = x + 1 by omega]
  have h2 : Nat.clog 2 (x + 1) = Nat.clog 2 (x / 2 + 1) + 1 := by
    rw [Nat.clog_of_one_lt (by decide) (by omega)]
    rw [show (x + 1 + 2 - 1) / 2 = x / 2 + 1 by omega]
  have h3 : Nat.clog 2 (2 * (x / 2) + 2) = Nat.clog 2 (x / 2 + 1) + 1 := by
    rw [Nat.clog_of_one_lt (by decide) (by omega)]
    rw [show (2 * (x / 2) + 2 + 2 - 1) / 2 = x / 2 + 1 by omega]
  omega

private theorem add_one_lt_two_pow {w : ℕ} (hw : 2 < 2 ^ w) : w + 1 < 2 ^ w := by
  have hw2 : 2 ≤ w := by
    by_contra h
    have : w ≤ 1 := by omega
    interval_cases w <;> simp at hw
  induction w with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hw2 with heq | hlt
    · have hk : k = 1 := by omega
      subst hk; decide
    · have hk2 : 2 < 2 ^ k := by
        have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have := ih hk2 (by omega)
      rw [Nat.pow_succ]
      omega

private theorem ell_lt_two_pow {w M : ℕ} (hM : M < 2 ^ w) (hw : 2 < 2 ^ w) : ell M < 2 ^ w := by
  have hclog : Nat.clog 2 (M + 1) ≤ w := Nat.clog_le_of_le_pow (by omega)
  have he : ell M = Nat.clog 2 (M + 1) + 1 := by
    unfold ell
    rw [Nat.clog_of_one_lt (by decide) (by omega)]
    rw [show (2 * M + 2 + 2 - 1) / 2 = M + 1 by omega]
  have hwl := add_one_lt_two_pow hw
  omega

private theorem ceilDiv_eq_sub_div_add {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ceilDiv a b = (a - 1) / b + 1 := by
  unfold ceilDiv
  have : a + b - 1 = (a - 1) + b := by omega
  rw [this, Nat.add_div_right _ hb]

private theorem clog_le_self {b n : ℕ} (hb : 1 < b) : Nat.clog b n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n ≤ 1
    · rw [Nat.clog_of_right_le_one h1]; omega
    · rw [Nat.clog_of_one_lt hb (by omega)]
      have hlt : (n + b - 1) / b < n := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        have : n + b ≤ n * b := by nlinarith
        omega
      have := ih _ hlt
      omega

/-- `buildCoreLevelProc` computes `coreLevel M r s` in linear time in `ell M + s`. -/
theorem buildCoreLevelProc_meetsContract {w f : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildCoreLevelProc) :
    MeetsContract w p f (buildCoreLevelContract w) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨M, r, s, rfl, hr1, hs1, hNw, hw2⟩ := hPre
  have hM : M < 2 ^ w := hWords M (by simp)
  have hr : r < 2 ^ w := hWords r (by simp)
  have hs : s < 2 ^ w := hWords s (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hEllW : ell M < 2 ^ w := ell_lt_two_pow hM hw2
  have hEll1 : 1 ≤ ell M := ell_pos M
  set e := max 2 (ceilDiv (ell M) r)
  set N := NOf M r
  have hN4 : 4 ≤ N := four_le_NOf M r
  have hNdef : N = 2 ^ e := rfl
  have heLe : e ≤ ell M + 1 := by
    have hcd : ceilDiv (ell M) r ≤ ell M := by
      rw [ceilDiv_eq_sub_div_add hEll1 hr1]
      have : (ell M - 1) / r ≤ ell M - 1 := Nat.div_le_self _ _
      omega
    dsimp [e]; omega
  have heW : e < 2 ^ w := by
    have : e < 2 ^ e := Nat.lt_two_pow_self
    rw [← hNdef] at this
    exact this.trans hNw
  have hcdW : ceilDiv (ell M) r < 2 ^ w := by
    have : ceilDiv (ell M) r ≤ e := le_max_right _ _
    exact lt_of_le_of_lt this heW
  -- Loop 1: compute ell M
  let Inv1 : State → Prop := fun st =>
    st.mem = mem ∧ st.regs 1 = r ∧ st.regs 2 = s ∧
    st.regs 4 + ell (st.regs 3) = ell M + 1 ∧ 1 ≤ st.regs 4 ∧ st.regs 3 ≤ M
  have hLoop1 : Triple w p Inv1
      (.loop (.reg 3) (.assign 3 (.bin .div (.reg 3) (.const 2)) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1))))
      (normalPost fun st => st.mem = mem ∧ st.regs 1 = r ∧ st.regs 2 = s ∧ st.regs 4 = ell M)
      (fun st => (1 + 10 + 1) * (ell (st.regs 3) - 1) + 1 + 1) := by
    refine Triple.loop_const_normal (m := fun st => ell (st.regs 3) - 1)
      (condVal := fun st => st.regs 3) (bodyBound := 10)
      (fun st _ => Expr.eval_reg_of_eq rfl)
      (fun st ⟨hm, h1, h2, hsum, _, _⟩ hzero => by
        rw [hzero, ell_zero] at hsum
        exact ⟨hm, h1, h2, by omega⟩) ?_
    intro st ⟨hm, h1, h2, hsum, h4ge, h3le⟩ hne
    have h3pos : 0 < st.regs 3 := Nat.pos_of_ne_zero hne
    have h3w : st.regs 3 < 2 ^ w := lt_of_le_of_lt h3le hM
    have hstep := ell_succ_div2 h3pos
    have h4next : st.regs 4 + 1 < 2 ^ w := by
      have := ell_pos (st.regs 3 / 2); omega
    intro s₀ ω' heq; subst s₀
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := st.regs 3 / 2) ?_ ?_
    · exact Expr.eval_div (Expr.eval_reg_of_eq rfl) (Expr.eval_const hw2) h3w
    refine runs_assign_le (v := st.regs 4 + 1) ?_ ?_ ?_
    · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const hw1) h4next
    · refine ⟨⟨hm, by simp [h1], by simp [h2], ?_, by simp, ?_⟩, ?_⟩
      · simp only [Function.update_self, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4)]
        omega
      · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
        exact (Nat.div_le_self _ _).trans h3le
      · simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Function.update_self]
        have := ell_pos (st.regs 3 / 2); omega
    · simp [Expr.size]
  -- Loop 2: compute N = 2^e
  let Inv2 : ℕ → State → Prop := fun i st =>
    st.mem = mem ∧ st.regs 2 = s ∧ st.regs 5 = e ∧ st.regs 6 = 2 ^ i ∧ st.regs 7 = i
  have hLoop2 := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body := .assign 6 (.bin .add (.reg 6) (.reg 6)))
    (P := fun st => st.mem = mem ∧ st.regs 2 = s ∧ st.regs 5 = e ∧ st.regs 6 = 1)
    (Inv := Inv2) 4 0 e (Nat.zero_le _) hw1 (fun _ => heW)
    (fun st ⟨hm, h2, h5, h6⟩ => ⟨Expr.eval_const (Nat.two_pow_pos w), hm,
      by simp [h2], by simp [h5], by simp [h6], by simp⟩)
    (fun _ _ _ _ h => h.2.2.2.2)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1) (fun i _ hilt st ω' ⟨hm, h2, h5, h6, h7⟩ => by
      have hpow : 2 ^ i + 2 ^ i < 2 ^ w := by
        have : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
        rw [this]
        exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hilt) (hNdef ▸ hNw)
      refine runs_start_le ?_
      refine runs_assign_le (v := 2 ^ (i + 1)) ?_ ?_ ?_
      · have heq : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := by rw [Nat.pow_succ]; omega
        rw [← heq]
        exact Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h6) hpow
      · exact ⟨⟨hm, by simp [h2], by simp [h5], by simp, by simp⟩, h7⟩
      · simp [Expr.size])
  -- Loop 3: compute q = Nat.clog N s
  let Inv3 : State → Prop := fun st =>
    st.mem = mem ∧ st.regs 6 = N ∧
    st.regs 8 + Nat.clog N (st.regs 9) = coreLevel M r s ∧ 1 ≤ st.regs 9 ∧ st.regs 9 ≤ s
  have hLoop3 : Triple w p Inv3
      (.loop (.bin .lt (.const 1) (.reg 9))
        (.assign 9 (.bin .add (.bin .div (.bin .sub (.reg 9) (.const 1)) (.reg 6)) (.const 1)) ;;
         .assign 8 (.bin .add (.reg 8) (.const 1))))
      (normalPost fun st => st.mem = mem ∧ st.regs 8 = coreLevel M r s)
      (fun st => (3 + 14 + 1) * Nat.clog N (st.regs 9) + 3 + 1) := by
    refine Triple.loop_const_normal (m := fun st => Nat.clog N (st.regs 9))
      (condVal := fun st => if 1 < st.regs 9 then 1 else 0) (bodyBound := 14)
      (fun st _ => Expr.eval_lt_op (Expr.eval_const hw1) (Expr.eval_reg_of_eq rfl) hw1)
      (fun st ⟨hm, _, hsum, h9ge, _⟩ hzero => by
        have h9le1 : st.regs 9 ≤ 1 := by split_ifs at hzero with h; omega
        have h9eq : st.regs 9 = 1 := by omega
        rw [h9eq, Nat.clog_one_right] at hsum
        exact ⟨hm, by omega⟩) ?_
    intro st ⟨hm, h6, hsum, h9ge, h9le⟩ hne
    have h9gt1 : 1 < st.regs 9 := by split_ifs at hne with h; exact h; omega
    have h9w : st.regs 9 < 2 ^ w := lt_of_le_of_lt h9le hs
    have h9subw : st.regs 9 - 1 < 2 ^ w := by omega
    set next := (st.regs 9 - 1) / N + 1
    have hclog : Nat.clog N (st.regs 9) = Nat.clog N next + 1 := by
      rw [Nat.clog_of_one_lt (by omega) h9gt1]
      congr 1
      have : st.regs 9 + N - 1 = (st.regs 9 - 1) + N := by omega
      rw [this, Nat.add_div_right _ (by omega)]
    have hnextLe : next ≤ st.regs 9 := by
      have : (st.regs 9 - 1) / N ≤ st.regs 9 - 1 := Nat.div_le_self _ _
      dsimp [next]; omega
    have hnextW : next < 2 ^ w := lt_of_le_of_lt (hnextLe.trans h9le) hs
    have hqLe : coreLevel M r s ≤ s := clog_le_self (by omega)
    have h8next : st.regs 8 + 1 < 2 ^ w := by omega
    intro s₀ ω' heq; subst s₀
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := next) ?_ ?_
    · exact Expr.eval_add (Expr.eval_div (Expr.eval_sub (Expr.eval_reg_of_eq rfl)
        (Expr.eval_const hw1) h9w) (Expr.eval_reg_of_eq h6) h9subw)
        (Expr.eval_const hw1) hnextW
    refine runs_assign_le (v := st.regs 8 + 1) ?_ ?_ ?_
    · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const hw1) h8next
    · refine ⟨⟨hm, by simp [h6], ?_, by simp [next], by simp; exact hnextLe.trans h9le⟩, ?_⟩
      · simp only [Function.update_self, Function.update_of_ne (by decide : (9 : ℕ) ≠ 8)]
        omega
      · simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 8), Function.update_self]
        omega
    · simp [Expr.size]
  -- Chain the whole procedure
  refine runs_start_le ?_
  unfold buildCoreLevelProc
  refine runs_seq_assign_le (v := M) (Expr.eval_reg_of_eq (by simp [startState])) ?_
  refine runs_seq_assign_le (v := 1) (Expr.eval_const hw1) ?_
  refine runs_seq_triple_le hLoop1
    ⟨rfl, by simp [startState], by simp [startState], by simp; omega, by simp, by simp⟩ ?_
  intro st₁ ⟨hm₁, hr₁, hs₁, hell₁⟩
  have hcdEq : (ell M - 1) / r + 1 = ceilDiv (ell M) r := (ceilDiv_eq_sub_div_add hEll1 hr1).symm
  refine runs_seq_assign_le (v := ceilDiv (ell M) r) ?_ ?_
  · rw [← hcdEq]
    exact Expr.eval_add (Expr.eval_div (Expr.eval_sub (Expr.eval_reg_of_eq hell₁)
      (Expr.eval_const hw1) hEllW) (Expr.eval_reg_of_eq hr₁) (by omega))
      (Expr.eval_const hw1) (hcdEq.symm ▸ hcdW)
  refine runs_seq_cond_le (v := if ceilDiv (ell M) r < 2 then 1 else 0)
    (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const hw2) hw1) ?_ ?_
  · intro hne
    have hlt : ceilDiv (ell M) r < 2 := by split_ifs at hne with h; exact h; omega
    have he2 : e = 2 := by dsimp [e]; omega
    refine runs_seq_assign_le (v := 2) (Expr.eval_const hw2) ?_
    refine runs_seq_assign_le (v := 1) (Expr.eval_const hw1) ?_
    refine runs_seq_triple_le hLoop2
      ⟨hm₁, by simp [hs₁], by simp [he2], by simp⟩ ?_
    intro st₂ ⟨hm₂, hs₂, _, hN₂, _⟩
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (Nat.two_pow_pos w)) ?_
    refine runs_seq_assign_le (v := s) (Expr.eval_reg_of_eq (by simp [hs₂])) ?_
    refine runs_seq_triple_le hLoop3
      ⟨hm₂, by simp [hN₂, hNdef], by simp [coreLevel, N], by simp; omega, by simp⟩ ?_
    intro st₃ ⟨hm₃, hq₃⟩
    refine runs_ret_le (v := coreLevel M r s) (Expr.eval_reg_of_eq hq₃)
      ⟨M, r, s, rfl, rfl, hm₃⟩ ?_
    have hqLe : Nat.clog N s ≤ s := clog_le_self (by omega)
    simp only [buildCoreLevelContract, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size, Function.update_self, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Nat.sub_zero]
    change _ ≤ 32 * ell M + 24 * s + 120
    omega
  · intro hzero
    have hge : 2 ≤ ceilDiv (ell M) r := by split_ifs at hzero with h; omega
    have heCd : e = ceilDiv (ell M) r := by dsimp [e]; omega
    refine runs_seq_nop_le ?_
    refine runs_seq_assign_le (v := 1) (Expr.eval_const hw1) ?_
    refine runs_seq_triple_le hLoop2
      ⟨hm₁, by simp [hs₁], by simp [heCd], by simp⟩ ?_
    intro st₂ ⟨hm₂, hs₂, _, hN₂, _⟩
    refine runs_seq_assign_le (v := 0) (Expr.eval_const (Nat.two_pow_pos w)) ?_
    refine runs_seq_assign_le (v := s) (Expr.eval_reg_of_eq (by simp [hs₂])) ?_
    refine runs_seq_triple_le hLoop3
      ⟨hm₂, by simp [hN₂, hNdef], by simp [coreLevel, N], by simp; omega, by simp⟩ ?_
    intro st₃ ⟨hm₃, hq₃⟩
    refine runs_ret_le (v := coreLevel M r s) (Expr.eval_reg_of_eq hq₃)
      ⟨M, r, s, rfl, rfl, hm₃⟩ ?_
    have hqLe : Nat.clog N s ≤ s := clog_le_self (by omega)
    simp only [buildCoreLevelContract, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size, Function.update_self, Function.update_of_ne (by decide : (3 : ℕ) ≠ 4), Nat.sub_zero]
    change _ ≤ 32 * ell M + 24 * s + 120
    omega

end MinCostFlow.HierPaths
