module

public import WordRAM.Logic
public import WordRAM.Tactic
import WordRAM.Layout
public import MinCostFlow.Machine.WideWord.ArithAddSub

/-!
# Multiword shifts on the Word-RAM

This file implements and verifies `mwShiftLeft` and `mwShiftRight` modulo `2 ^ (L * h)` in time
`O(L)` when `L * h < 2 ^ w` and `2 * h + 2 ≤ w`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

private theorem shift_lt_prefix_step {x y h i : ℕ} :
    let ax := (x / 2 ^ (i * h)) % 2 ^ h
    let ay := (y / 2 ^ (i * h)) % 2 ^ h
    (if x % 2 ^ ((i + 1) * h) < y % 2 ^ ((i + 1) * h) then 1 else 0) =
      if ax < ay then 1
      else if ay < ax then 0
      else if x % 2 ^ (i * h) < y % 2 ^ (i * h) then 1 else 0 := by
  intro ax ay
  rw [limb_step_prefix x h i, limb_step_prefix y h i]
  have hxm : x % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hym : y % 2 ^ (i * h) < 2 ^ (i * h) := Nat.mod_lt _ (Nat.two_pow_pos _)
  rcases lt_trichotomy ax ay with hlt | heq | hgt
  · have hsum : x % 2 ^ (i * h) + 2 ^ (i * h) * ax < y % 2 ^ (i * h) + 2 ^ (i * h) * ay := by
      have h1 : x % 2 ^ (i * h) + 2 ^ (i * h) * ax < 2 ^ (i * h) * (ax + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have h2 : 2 ^ (i * h) * (ax + 1) ≤ 2 ^ (i * h) * ay := Nat.mul_le_mul_left _ hlt
      omega
    rw [ite_eq_left hsum, ite_eq_left hlt]
  · have hnot1 : ¬ ax < ay := by omega
    have hnot2 : ¬ ay < ax := by omega
    dsimp only [ax, ay] at heq hnot1 hnot2
    rw [heq, ite_eq_right hnot1, ite_eq_right hnot2]
    have hiff : x % 2 ^ (i * h) + 2 ^ (i * h) * ((y / 2 ^ (i * h)) % 2 ^ h) <
        y % 2 ^ (i * h) + 2 ^ (i * h) * ((y / 2 ^ (i * h)) % 2 ^ h) ↔
        x % 2 ^ (i * h) < y % 2 ^ (i * h) := by omega
    simp only [hiff]
  · have hnot1 : ¬ ax < ay := by omega
    have hsum : ¬ x % 2 ^ (i * h) + 2 ^ (i * h) * ax < y % 2 ^ (i * h) + 2 ^ (i * h) * ay := by
      have h1 : y % 2 ^ (i * h) + 2 ^ (i * h) * ay < 2 ^ (i * h) * (ay + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have h2 : 2 ^ (i * h) * (ay + 1) ≤ 2 ^ (i * h) * ax := Nat.mul_le_mul_left _ hgt
      omega
    rw [ite_eq_right hsum, ite_eq_right hnot1, ite_eq_left hgt]

def shiftPrefixStmt : Stmt :=
  .assign 6 (.const 0) ;;
  .assign 7 (.bin .mul (.reg 3) (.reg 4)) ;;
  forRange 8 (.const 0) (.reg 3)
    (.assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
     .assign 10 (.bin .mod (.reg 7) (.reg 5)) ;;
     .cond (.bin .lt (.reg 9) (.reg 10))
       (.assign 6 (.const 1))
       (.cond (.bin .lt (.reg 10) (.reg 9)) (.assign 6 (.const 0)) .nop) ;;
     .assign 7 (.bin .div (.reg 7) (.reg 5)))

def decodeShiftStmt : Stmt :=
  .assign 7 (.const 0) ;;
  forRange 8 (.const 0) (.reg 3)
    (.assign 7 (.bin .add (.bin .mul (.reg 7) (.reg 5))
      (.load (.bin .add (.reg 1) (.bin .sub (.bin .sub (.reg 3) (.const 1)) (.reg 8)))))) ;;
  .assign 8 (.bin .div (.reg 7) (.reg 4)) ;;
  .assign 9 (.bin .mod (.reg 7) (.reg 4)) ;;
  .assign 10 (.bin .sub (.reg 4) (.reg 9))

/-- Multiword logical left shift `(x <<< y) % 2 ^ (L * h)` into `dst`, taking
`[a, b, dst, L, h, 2 ^ h]`. -/
def mwShiftLeft (base : ℕ) : Stmt :=
  shiftPrefixStmt ;;
  .cond (.reg 6)
    (decodeShiftStmt ;;
     forRange 11 (.const 0) (.reg 3)
       (.cond (.bin .lt (.reg 11) (.reg 8))
         (.store (.bin .add (.reg 2) (.reg 11)) (.const 0))
         (.cond (.bin .eq (.reg 11) (.reg 8))
           (.store (.bin .add (.reg 2) (.reg 11))
             (.bin .mod (.bin .shiftLeft (.load (.reg 0)) (.reg 9)) (.reg 5)))
           (.store (.bin .add (.reg 2) (.reg 11))
             (.bin .add
               (.bin .mod (.bin .shiftLeft
                 (.load (.bin .add (.reg 0) (.bin .sub (.reg 11) (.reg 8)))) (.reg 9)) (.reg 5))
               (.bin .shiftRight
                 (.load (.bin .add (.reg 0)
                   (.bin .sub (.bin .sub (.reg 11) (.reg 8)) (.const 1)))) (.reg 10)))))))
    (.call 7 (base + idxZero) [.reg 2, .reg 3]) ;;
  .ret (.const 0)

/-- Multiword logical right shift `x >>> y` into `dst`, taking `[a, b, dst, L, h, 2 ^ h]`. -/
def mwShiftRight (base : ℕ) : Stmt :=
  shiftPrefixStmt ;;
  .cond (.reg 6)
    (decodeShiftStmt ;;
     .assign 13 (.bin .sub (.reg 3) (.reg 8)) ;;
     forRange 11 (.const 0) (.reg 3)
       (.assign 12 (.const 0) ;;
        .cond (.bin .lt (.reg 11) (.reg 13))
          (.assign 12 (.bin .shiftRight
            (.load (.bin .add (.reg 0) (.bin .add (.reg 11) (.reg 8)))) (.reg 9)))
          .nop ;;
        .cond (.bin .lt (.bin .add (.reg 11) (.const 1)) (.reg 13))
          (.assign 12 (.bin .add (.reg 12)
            (.bin .mod (.bin .shiftLeft
              (.load (.bin .add (.reg 0)
                (.bin .add (.bin .add (.reg 11) (.reg 8)) (.const 1)))) (.reg 10)) (.reg 5))))
          .nop ;;
        .store (.bin .add (.reg 2) (.reg 11)) (.reg 12)))
    (.call 7 (base + idxZero) [.reg 2, .reg 3]) ;;
  .ret (.const 0)

theorem mwShiftLeft_noRand (base : ℕ) : (mwShiftLeft base).NoRand := by
  simp [mwShiftLeft, shiftPrefixStmt, decodeShiftStmt, forRange, forUp, Stmt.NoRand]

theorem mwShiftRight_noRand (base : ℕ) : (mwShiftRight base).NoRand := by
  simp [mwShiftRight, shiftPrefixStmt, decodeShiftStmt, forRange, forUp, Stmt.NoRand]

def mwShiftLeftContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L, h, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ L * h < 2 ^ w ∧
      a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L h, args = [a, b, dst, L, h, 2 ^ h] ∧ v = 0 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y →
        LimbsAt mem' dst L h ((x <<< y) % 2 ^ (L * h))) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L, _, _] => 120 * L + 80 | _ => 0

def mwShiftRightContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ a b dst L h x y, args = [a, b, dst, L, h, 2 ^ h] ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ L * h < 2 ^ w ∧
      a + L < 2 ^ w ∧ b + L < 2 ^ w ∧ dst + L < 2 ^ w ∧
      (dst + L ≤ a ∨ a + L ≤ dst) ∧ (dst + L ≤ b ∨ b + L ≤ dst) ∧
      LimbsAt mem a L h x ∧ LimbsAt mem b L h y
  post args mem v mem' :=
    ∃ a b dst L h, args = [a, b, dst, L, h, 2 ^ h] ∧ v = 0 ∧
      (∀ x y, LimbsAt mem a L h x → LimbsAt mem b L h y →
        LimbsAt mem' dst L h (x >>> y)) ∧
      (∀ p, p < dst ∨ dst + L ≤ p → mem' p = mem p)
  cost args _ := match args with | [_, _, _, L, _, _] => 120 * L + 80 | _ => 0

private theorem shiftPrefix_triple {w : ℕ} {p : Program}
    {mem : ℕ → ℕ} {pos a b' dst L h y : ℕ}
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hLh : L * h < 2 ^ w)
    (hb : b' + L < 2 ^ w) (hL : L < 2 ^ w) (hy : LimbsAt mem b' L h y) :
    Triple w p (fun st => st = startState [a, b', dst, L, h, 2 ^ h] mem pos)
      shiftPrefixStmt
      (normalPost fun st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧
        st.regs 2 = dst ∧ st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h ∧
        st.regs 6 = (if y < L * h then 1 else 0))
      (fun _ => 35 * L + 16) := by
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 3)
    (body :=
      .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
      .assign 10 (.bin .mod (.reg 7) (.reg 5)) ;;
      .cond (.bin .lt (.reg 9) (.reg 10))
        (.assign 6 (.const 1))
        (.cond (.bin .lt (.reg 10) (.reg 9)) (.assign 6 (.const 0)) .nop) ;;
      .assign 7 (.bin .div (.reg 7) (.reg 5)))
    (P := fun st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧
      st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h ∧ st.regs 6 = 0 ∧ st.regs 7 = L * h)
    (Inv := fun i st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧
      st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h ∧ st.regs 8 = i ∧
      st.regs 7 = (L * h) / 2 ^ (i * h) ∧
      st.regs 6 = (if y % 2 ^ (i * h) < (L * h) % 2 ^ (i * h) then 1 else 0))
    26 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st ⟨hm, h0, h1, h2, h3, h4, h5, h6, h7⟩ => by
      refine ⟨by eval_expr, hm, h0, h1, h2, h3, h4, h5, by simp, by simp [h7], ?_⟩
      simp [h6, Nat.mod_one])
    (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 := hi.2.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st _ ⟨hmem, h0, h1, h2, h3, h4, h5, h8, h7, h6⟩
      have hb_val : st.mem (b' + i) = (y / 2 ^ (i * h)) % 2 ^ h := by
        rw [hmem]; exact hy.getElem hilt
      have hdiv_step : ((L * h) / 2 ^ (i * h)) / 2 ^ h = (L * h) / 2 ^ ((i + 1) * h) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show i * h + h = (i + 1) * h by ring]
      have h7_lt : st.regs 7 < 2 ^ w := by
        rw [h7]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hLh
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hb_val) ?_
      refine runs_seq_assign_le (Expr.eval_mod (by eval_expr) (by eval_expr) h7_lt) ?_
      refine runs_seq_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1)
        (fun hne => ?_) (fun heq => ?_)
      · have hlt_a : (y / 2 ^ (i * h)) % 2 ^ h < ((L * h) / 2 ^ (i * h)) % 2 ^ h := by
          by_contra hnot; simp [h7, hnot] at hne
        refine runs_seq_assign_le (by eval_expr) ?_
        refine runs_assign_le (Expr.eval_div (by eval_expr) (by eval_expr) h7_lt) ?_
          (by wram_cost)
        refine ⟨⟨hmem, h0, h1, h2, h3, h4, h5, by simp, ?_, ?_⟩, ?_⟩
        · simp [h7, hdiv_step]
        · simp [shift_lt_prefix_step, ite_eq_left hlt_a]
        · simp [h8]
      · have hnot_a : ¬ (y / 2 ^ (i * h)) % 2 ^ h < ((L * h) / 2 ^ (i * h)) % 2 ^ h := by
          intro hnot; simp [h7, hnot] at heq
        refine runs_seq_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1)
          (fun hne2 => ?_) (fun heq2 => ?_)
        · have hgt_a : ((L * h) / 2 ^ (i * h)) % 2 ^ h < (y / 2 ^ (i * h)) % 2 ^ h := by
            by_contra hnot; simp [h7, hnot] at hne2
          refine runs_seq_assign_le (by eval_expr) ?_
          refine runs_assign_le (Expr.eval_div (by eval_expr) (by eval_expr) h7_lt) ?_
            (by wram_cost)
          refine ⟨⟨hmem, h0, h1, h2, h3, h4, h5, by simp, ?_, ?_⟩, ?_⟩
          · simp [h7, hdiv_step]
          · simp [shift_lt_prefix_step, ite_eq_right hnot_a, ite_eq_left hgt_a]
          · simp [h8]
        · have hnot_b : ¬ ((L * h) / 2 ^ (i * h)) % 2 ^ h < (y / 2 ^ (i * h)) % 2 ^ h := by
            intro hnot; simp [h7, hnot] at heq2
          refine runs_seq_nop_le ?_
          refine runs_assign_le (Expr.eval_div (by eval_expr) (by eval_expr) h7_lt) ?_
            (by wram_cost)
          refine ⟨⟨hmem, h0, h1, h2, h3, h4, h5, by simp, ?_, ?_⟩, ?_⟩
          · simp [h7, hdiv_step]
          · simp [shift_lt_prefix_step, ite_eq_right hnot_a, ite_eq_right hnot_b, h6]
          · simp [h8])
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [shiftPrefixStmt]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_assign_le (Expr.eval_mul (by eval_expr) (by eval_expr) hLh) ?_
  refine runs_triple_le hloop ⟨rfl, by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp, by simp⟩ (fun o st₁ hq => ?_) (by wram_cost)
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    rcases hq with ⟨hmem, h0, h1, h2, h3, h4, h5, _, _, h6⟩
    refine ⟨hmem, h0, h1, h2, h3, h4, h5, ?_⟩
    rcases Nat.eq_zero_or_pos L with rfl | hL_pos
    · simpa [Nat.mod_one] using h6
    · have hLh_pos : 1 ≤ L * h := Nat.mul_pos hL_pos hh
      have hLh_pow : L * h < 2 ^ (L * h) := Nat.lt_two_pow_self
      rw [Nat.mod_eq_of_lt hy.lt_pow, Nat.mod_eq_of_lt hLh_pow] at h6
      exact h6

private theorem decodeShift_triple {w : ℕ} {p : Program}
    {mem : ℕ → ℕ} {a b' dst L h y : ℕ}
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hLh : L * h < 2 ^ w)
    (hb : b' + L < 2 ^ w) (hL : L < 2 ^ w) (hy : LimbsAt mem b' L h y)
    (hy_lt : y < L * h) :
    Triple w p (fun st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧
        st.regs 2 = dst ∧ st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h)
      decodeShiftStmt
      (normalPost fun st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧
        st.regs 2 = dst ∧ st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h ∧
        st.regs 7 = y ∧ st.regs 8 = y / h ∧ st.regs 9 = y % h ∧
        st.regs 10 = h - y % h)
      (fun _ => 22 * L + 28) := by
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hh_lt : h < 2 ^ w := lt_trans Nat.lt_two_pow_self (two_pow_h_lt_two_pow_w hw2)
  have hy_w : y < 2 ^ w := lt_trans hy_lt hLh
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 3)
    (body := .assign 7 (.bin .add (.bin .mul (.reg 7) (.reg 5))
      (.load (.bin .add (.reg 1) (.bin .sub (.bin .sub (.reg 3) (.const 1)) (.reg 8))))))
    (P := fun st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧
      st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h ∧ st.regs 7 = 0)
    (Inv := fun cnt st => st.mem = mem ∧ st.regs 0 = a ∧ st.regs 1 = b' ∧ st.regs 2 = dst ∧
      st.regs 3 = L ∧ st.regs 4 = h ∧ st.regs 5 = 2 ^ h ∧ st.regs 8 = cnt ∧
      st.regs 7 = y / 2 ^ ((L - cnt) * h))
    13 0 L (Nat.zero_le L) hw1 (fun _ => hL)
    (fun st ⟨hm, h0, h1, h2, h3, h4, h5, h7⟩ => by
      refine ⟨by eval_expr, hm, h0, h1, h2, h3, h4, h5, by simp, ?_⟩
      simp [h7, Nat.div_eq_of_lt hy.lt_pow])
    (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 := hi.2.2.2.2.1; eval_expr)
    (fun cnt _ hcnt => by
      intro st _ ⟨hmem, h0, h1, h2, h3, h4, h5, h8, h7⟩
      have hidx_eq : L - 1 - cnt = L - (cnt + 1) := by omega
      have hidx_lt : L - 1 - cnt < L := by omega
      have hpow_m : (L - cnt) * h = (L - (cnt + 1)) * h + h := by
        rw [show L - cnt = (L - (cnt + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
      have hdiv_step : (y / 2 ^ ((L - cnt) * h)) * 2 ^ h +
          (y / 2 ^ ((L - 1 - cnt) * h)) % 2 ^ h = y / 2 ^ ((L - (cnt + 1)) * h) := by
        rw [hidx_eq, hpow_m, Nat.pow_add, ← Nat.div_div_eq_div_mul]
        have hdm := Nat.mod_add_div (y / 2 ^ ((L - (cnt + 1)) * h)) (2 ^ h)
        rw [Nat.add_comm, Nat.mul_comm (2 ^ h)] at hdm
        exact hdm
      have hb_val : st.mem (b' + (L - 1 - cnt)) = (y / 2 ^ ((L - 1 - cnt) * h)) % 2 ^ h := by
        rw [hmem]; exact hy.getElem hidx_lt
      have hnext_lt : y / 2 ^ ((L - (cnt + 1)) * h) < 2 ^ w :=
        lt_of_le_of_lt (Nat.div_le_self _ _) hy_w
      have hmul_lt : st.regs 7 * 2 ^ h < 2 ^ w := by
        rw [h7]; exact lt_of_le_of_lt (by rw [← hdiv_step]; exact Nat.le_add_right _ _) hnext_lt
      have hadd_eval : (Expr.bin .add (.bin .mul (.reg 7) (.reg 5))
          (.load (.bin .add (.reg 1)
            (.bin .sub (.bin .sub (.reg 3) (.const 1)) (.reg 8))))).eval w st =
          some (y / 2 ^ ((L - (cnt + 1)) * h)) := by
        rw [← hdiv_step]
        rw [h7] at hmul_lt
        exact Expr.eval_add (Expr.eval_mul (by eval_expr) (by eval_expr) hmul_lt)
          (Expr.eval_load_of_eq (by eval_expr) hb_val) (by rw [hdiv_step]; exact hnext_lt)
      refine runs_start_le ?_
      refine runs_assign_le hadd_eval ?_ (by wram_cost)
      refine ⟨⟨hmem, h0, h1, h2, h3, h4, h5, by simp, ?_⟩, h8⟩
      simp
    )
  intro st ω ⟨hm, h0, h1, h2, h3, h4, h5⟩
  refine runs_start_le ?_
  dsimp only [decodeShiftStmt]
  refine runs_seq_assign_le (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨hm, by simp [h0], by simp [h1], by simp [h2],
      by simp [h3], by simp [h4], by simp [h5], by simp⟩ ?_
  rintro st₁ ⟨hm1, h0', h1', h2', h3', h4', h5', _, h7'⟩
  have h7_y : st₁.regs 7 = y := by simpa using h7'
  refine runs_seq_assign_le (Expr.eval_div (by eval_expr) (by eval_expr) hy_w) ?_
  refine runs_seq_assign_le (Expr.eval_mod (by eval_expr) (by eval_expr) hy_w) ?_
  refine runs_assign_le (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) ?_ (by wram_cost)
  refine ⟨hm1, by simp [h0'], by simp [h1'], by simp [h2'], by simp [h3'], by simp [h4'],
    by simp [h5'], by simp [h7_y], by simp, by simp, by simp⟩

theorem mwShiftLeft_meetsContract {w : ℕ} {p : Program} {f base : ℕ}
    (hZero : MeetsContract w p (base + idxZero) (mwZeroContract w))
    (hShlProc : p.procs[f]? = some (mwShiftLeft base)) :
    MeetsContract w p f (mwShiftLeftContract w) := by
  refine meetsContract_of_runs hShlProc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, hLh, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have h2B : 2 * 2 ^ h < 2 ^ w := two_mul_pow_h_lt_two_pow_w hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hh_w : h < 2 ^ w := hwords h (by simp)
  refine runs_start_le ?_
  dsimp only [mwShiftLeft]
  refine runs_seq_triple_le (shiftPrefix_triple hh hw2 hLh hb hL hy) rfl ?_
  rintro st₁ ⟨hmem1, h0, h1, h2, h3, h4, h5, h6⟩
  wram_step
  · have hy_lt : y < L * h := by by_contra hnot; simp [hnot] at hcond
    have hq_lt : y / h < L := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hr_lt : y % h < h := Nat.mod_lt _ hh
    have hy_decomp : y = (y / h) * h + y % h := by
      have := (Nat.div_add_mod y h).symm
      rw [Nat.mul_comm] at this
      exact this
    refine runs_seq_assoc_le ?_
    refine runs_seq_triple_le (decodeShift_triple hh hw2 hLh hb hL hy hy_lt)
      ⟨hmem1, h0, h1, h2, h3, h4, h5⟩ ?_
    rintro st₂ ⟨hmem2, h0', h1', h2', h3', h4', h5', _, h8', h9', h10'⟩
    set q := y / h
    set r := y % h
    set hmr := h - r
    have hloop := Triple.forRange_const (w := w) (p := p) (r := 11) (lo := .const 0) (hi := .reg 3)
      (body :=
        .cond (.bin .lt (.reg 11) (.reg 8))
          (.store (.bin .add (.reg 2) (.reg 11)) (.const 0))
          (.cond (.bin .eq (.reg 11) (.reg 8))
            (.store (.bin .add (.reg 2) (.reg 11))
              (.bin .mod (.bin .shiftLeft (.load (.reg 0)) (.reg 9)) (.reg 5)))
            (.store (.bin .add (.reg 2) (.reg 11))
              (.bin .add
                (.bin .mod (.bin .shiftLeft
                  (.load (.bin .add (.reg 0) (.bin .sub (.reg 11) (.reg 8)))) (.reg 9)) (.reg 5))
                (.bin .shiftRight
                  (.load (.bin .add (.reg 0)
                    (.bin .sub (.bin .sub (.reg 11) (.reg 8)) (.const 1)))) (.reg 10))))))
      (P := fun st => st = st₂)
      (Inv := fun i st => st.regs 0 = a ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
        st.regs 5 = 2 ^ h ∧ st.regs 8 = q ∧ st.regs 9 = r ∧ st.regs 10 = hmr ∧
        st.regs 11 = i ∧
        (∀ j < i, st.mem (dst + j) = (((x <<< y) % 2 ^ (L * h)) / 2 ^ (j * h)) % 2 ^ h) ∧
        (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
      35 0 L (Nat.zero_le L) hw1 (fun _ => hL)
      (fun st hst => by
        subst hst
        refine ⟨by eval_expr, h0', h2', h3', h5', h8', h9', h10', by simp,
          fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => congrFun hmem2 _⟩)
      (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h3 := hi.2.2.1; eval_expr)
      (fun i _ hilt => by
        intro st _ ⟨hr0, hr2, hr3, hr5, hr8, hr9, hr10, hr11, hlim, hframe⟩
        have hsh_form := shiftLeft_limb_formula (x := x) (L := L) (h := h) (q := q) (r := r) (i := i)
          hr_lt hq_lt hilt
        rw [← hy_decomp] at hsh_form
        have ha_limb : ∀ k < L, st.mem (a + k) = (x / 2 ^ (k * h)) % 2 ^ h := fun k hk => by
          rw [hframe (a + k) (by omega)]; exact hx.getElem hk
        refine runs_start_le ?_
        refine runs_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1)
          (fun hne => ?_) (fun heq => ?_)
        · have hiq : i < q := by by_contra hnot; simp [hnot] at hne
          refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost)
          refine ⟨⟨hr0, hr2, hr3, hr5, hr8, hr9, hr10, by simp, ?_, ?_⟩, hr11⟩
          · intro j hj
            dsimp only
            by_cases hji : j = i
            · subst hji; rw [Function.update_self, hsh_form, ite_eq_left hiq]
            · rw [Function.update_of_ne (by omega)]; exact hlim j (by omega)
          · intro p hp
            dsimp only
            rw [Function.update_of_ne (by omega)]; exact hframe p (by omega)
        · have hnot_lt : ¬ i < q := by intro hnot; simp [hnot] at heq
          refine runs_cond_le (Expr.eval_eq_op (by eval_expr) (by eval_expr) hw1)
            (fun hne2 => ?_) (fun heq2 => ?_)
          · have hiq : i = q := by by_contra hnot; simp [hnot] at hne2
            have ha0 : st.mem a = x % 2 ^ h := by simpa using ha_limb 0 (by omega)
            have ha0_lt : st.mem a < 2 ^ h := by rw [ha0]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
            have hsh_lt : (st.mem a <<< r) < 2 ^ (2 * h) := by
              rw [Nat.shiftLeft_eq]
              have hpow_eq : 2 ^ (2 * h) = 2 ^ h * 2 ^ h := by
                rw [← Nat.pow_add, show h + h = 2 * h by ring]
              rw [hpow_eq]
              exact lt_of_lt_of_le
                (Nat.mul_lt_mul_of_pos_right ha0_lt (Nat.two_pow_pos _))
                (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (le_of_lt hr_lt)))
            have hsh_w : (st.mem a <<< r) < 2 ^ w :=
              lt_trans hsh_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
            have hval_eval : (Expr.bin .mod (.bin .shiftLeft (.load (.reg 0)) (.reg 9)) (.reg 5)).eval w st =
                some (((x % 2 ^ h) <<< r) % 2 ^ h) := by
              rw [← ha0]
              exact Expr.eval_mod (Expr.eval_bin (Expr.eval_load_of_eq (by eval_expr) rfl)
                (by eval_expr) hsh_w) (by eval_expr) hsh_w
            refine runs_store_le (by eval_expr) hval_eval ?_ (by wram_cost)
            refine ⟨⟨hr0, hr2, hr3, hr5, hr8, hr9, hr10, by simp, ?_, ?_⟩, hr11⟩
            · intro j hj
              dsimp only
              by_cases hji : j = i
              · subst hji; rw [Function.update_self, hsh_form, ite_eq_right hnot_lt, ite_eq_left hiq]
              · rw [Function.update_of_ne (by omega)]; exact hlim j (by omega)
            · intro p hp
              dsimp only
              rw [Function.update_of_ne (by omega)]; exact hframe p (by omega)
          · have hne_eq : ¬ i = q := by intro hnot; simp [hnot] at heq2
            have hiq_gt : q < i := by omega
            have ha1_val : st.mem (a + (i - q)) = (x / 2 ^ ((i - q) * h)) % 2 ^ h := ha_limb (i - q) (by omega)
            have ha2_val : st.mem (a + (i - q - 1)) = (x / 2 ^ ((i - q - 1) * h)) % 2 ^ h := ha_limb (i - q - 1) (by omega)
            have ha1_lt : (x / 2 ^ ((i - q) * h)) % 2 ^ h < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
            have hsh_lt : (((x / 2 ^ ((i - q) * h)) % 2 ^ h) <<< r) < 2 ^ (2 * h) := by
              rw [Nat.shiftLeft_eq, show 2 ^ (2 * h) = 2 ^ h * 2 ^ h by rw [← Nat.pow_add, show h + h = 2 * h by ring]]
              exact lt_of_lt_of_le
                (Nat.mul_lt_mul_of_pos_right ha1_lt (Nat.two_pow_pos _))
                (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (le_of_lt hr_lt)))
            have hsh_w : (((x / 2 ^ ((i - q) * h)) % 2 ^ h) <<< r) < 2 ^ w :=
              lt_trans hsh_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
            have hpart2_lt : (((x / 2 ^ ((i - q - 1) * h)) % 2 ^ h) >>> hmr) < 2 ^ h := by
              rw [Nat.shiftRight_eq_div_pow]
              exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
            have hsum_eq : ((((x / 2 ^ ((i - q) * h)) % 2 ^ h) <<< r) % 2 ^ h +
                (((x / 2 ^ ((i - q - 1) * h)) % 2 ^ h) >>> hmr)) =
                (((x <<< y) % 2 ^ (L * h)) / 2 ^ (i * h)) % 2 ^ h := by
              rw [hsh_form, ite_eq_right hnot_lt, ite_eq_right hne_eq]
            have hval_eval : (Expr.bin .add
                (.bin .mod (.bin .shiftLeft
                  (.load (.bin .add (.reg 0) (.bin .sub (.reg 11) (.reg 8)))) (.reg 9)) (.reg 5))
                (.bin .shiftRight
                  (.load (.bin .add (.reg 0)
                    (.bin .sub (.bin .sub (.reg 11) (.reg 8)) (.const 1)))) (.reg 10))).eval w st =
                some ((((x <<< y) % 2 ^ (L * h)) / 2 ^ (i * h)) % 2 ^ h) := by
              rw [← hsum_eq]
              refine Expr.eval_add
                (Expr.eval_mod
                  (Expr.eval_bin
                    (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
                      (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) (by omega)) ha1_val)
                    (by eval_expr) hsh_w)
                  (by eval_expr) hsh_w)
                (Expr.eval_bin
                  (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
                    (Expr.eval_sub (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega))
                      (by eval_expr) (by omega)) (by omega)) ha2_val)
                  (by eval_expr) (lt_trans hpart2_lt hB))
                (by rw [hsum_eq]; exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hB)
            refine runs_store_le (by eval_expr) hval_eval ?_ (by wram_cost)
            refine ⟨⟨hr0, hr2, hr3, hr5, hr8, hr9, hr10, by simp, ?_, ?_⟩, hr11⟩
            · intro j hj
              dsimp only
              by_cases hji : j = i
              · subst hji; rw [Function.update_self]
              · rw [Function.update_of_ne (by omega)]; exact hlim j (by omega)
            · intro p hp
              dsimp only
              rw [Function.update_of_ne (by omega)]; exact hframe p (by omega))
    refine runs_seq_triple_le hloop rfl ?_
    rintro st₃ ⟨_, _, _, _, _, _, _, _, hlim, hframe⟩
    have hlimbs : LimbsAt st₃.mem dst L h ((x <<< y) % 2 ^ (L * h)) :=
      limbsAt_iff_pointwise.mpr ⟨Nat.mod_lt _ (Nat.two_pow_pos _), hlim⟩
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact hlimbs, hframe⟩ ?_
    dsimp only [mwShiftLeftContract]
    wram_cost
  · have hge : L * h ≤ y := by
      by_contra hnot
      have : y < L * h := Nat.not_le.mp hnot
      simp [this] at hcond
    refine runs_seq_call_le hZero (by eval_expr) (by wram_words) ⟨dst, L, rfl, hw1, hdst⟩ ?_
    rintro _ mem₂ pos₂ ⟨dst', L', heq2, _, hlist, hframe⟩
    simp only [List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    have hsh0 : (x <<< y) % 2 ^ (L * h) = 0 := by
      rw [Nat.shiftLeft_eq]
      have hdvd : 2 ^ (L * h) ∣ x * 2 ^ y :=
        dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hge) x
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hlimbs : LimbsAt mem₂ dst L h ((x <<< y) % 2 ^ (L * h)) := by
      rw [hsh0]
      exact limbsAt_zero_iff.mpr hlist
    have hframe' : ∀ p, p < dst ∨ dst + L ≤ p → mem₂ p = mem p := fun p hp => by
      rw [hframe p hp, hmem1]
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact hlimbs, hframe'⟩ ?_
    dsimp only [mwShiftLeftContract, mwZeroContract]
    wram_cost

theorem mwShiftRight_meetsContract {w : ℕ} {p : Program} {f base : ℕ}
    (hZero : MeetsContract w p (base + idxZero) (mwZeroContract w))
    (hShrProc : p.procs[f]? = some (mwShiftRight base)) :
    MeetsContract w p f (mwShiftRightContract w) := by
  refine meetsContract_of_runs hShrProc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨a, b', dst, L, h, x, y, rfl, hh, hw2, hLh, ha, hb, hdst, hnova, hnovb, hx, hy⟩
  have hw1 : 1 < 2 ^ w := one_lt_two_pow_of_le hh hw2
  have hB : 2 ^ h < 2 ^ w := two_pow_h_lt_two_pow_w hw2
  have h2B : 2 * 2 ^ h < 2 ^ w := two_mul_pow_h_lt_two_pow_w hw2
  have hL : L < 2 ^ w := hwords L (by simp)
  have hh_w : h < 2 ^ w := hwords h (by simp)
  refine runs_start_le ?_
  dsimp only [mwShiftRight]
  refine runs_seq_triple_le (shiftPrefix_triple hh hw2 hLh hb hL hy) rfl ?_
  rintro st₁ ⟨hmem1, h0, h1, h2, h3, h4, h5, h6⟩
  wram_step
  · have hy_lt : y < L * h := by by_contra hnot; simp [hnot] at hcond
    have hq_lt : y / h < L := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hr_lt : y % h < h := Nat.mod_lt _ hh
    have hy_decomp : y = (y / h) * h + y % h := by
      have := (Nat.div_add_mod y h).symm
      rw [Nat.mul_comm] at this
      exact this
    refine runs_seq_assoc_le ?_
    refine runs_seq_triple_le (decodeShift_triple hh hw2 hLh hb hL hy hy_lt)
      ⟨hmem1, h0, h1, h2, h3, h4, h5⟩ ?_
    rintro st₂ ⟨hmem2, h0', h1', h2', h3', h4', h5', _, h8', h9', h10'⟩
    set q := y / h
    set r := y % h
    set hmr := h - r
    set lim := L - q
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (Expr.eval_sub (by eval_expr) (by eval_expr) (by omega)) ?_
    have hloop := Triple.forRange_const (w := w) (p := p) (r := 11) (lo := .const 0) (hi := .reg 3)
      (body :=
        .assign 12 (.const 0) ;;
        .cond (.bin .lt (.reg 11) (.reg 13))
          (.assign 12 (.bin .shiftRight
            (.load (.bin .add (.reg 0) (.bin .add (.reg 11) (.reg 8)))) (.reg 9)))
          .nop ;;
        .cond (.bin .lt (.bin .add (.reg 11) (.const 1)) (.reg 13))
          (.assign 12 (.bin .add (.reg 12)
            (.bin .mod (.bin .shiftLeft
              (.load (.bin .add (.reg 0)
                (.bin .add (.bin .add (.reg 11) (.reg 8)) (.const 1)))) (.reg 10)) (.reg 5))))
          .nop ;;
        .store (.bin .add (.reg 2) (.reg 11)) (.reg 12))
      (P := fun st => st = { st₂ with regs := Function.update st₂.regs 13 lim })
      (Inv := fun i st => st.regs 0 = a ∧ st.regs 2 = dst ∧ st.regs 3 = L ∧
        st.regs 5 = 2 ^ h ∧ st.regs 8 = q ∧ st.regs 9 = r ∧ st.regs 10 = hmr ∧
        st.regs 13 = lim ∧ st.regs 11 = i ∧
        (∀ j < i, st.mem (dst + j) = ((x >>> y) / 2 ^ (j * h)) % 2 ^ h) ∧
        (∀ p, p < dst ∨ dst + i ≤ p → st.mem p = mem p))
      45 0 L (Nat.zero_le L) hw1 (fun _ => hL)
      (fun st hst => by
        subst hst
        refine ⟨by eval_expr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          fun _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ => congrFun hmem2 _⟩ <;>
          simp [h0', h2', h3', h5', h8', h9', h10', lim])
      (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h3 := hi.2.2.1; eval_expr)
      (fun i _ hilt => by
        intro st _ ⟨hr0, hr2, hr3, hr5, hr8, hr9, hr10, hr13, hr11, hlim, hframe⟩
        have hshr_form := shiftRight_limb_formula (x := x) (L := L) (h := h) (q := q) (r := r) (i := i)
          hx.lt_pow hr_lt hilt
        rw [← hy_decomp] at hshr_form
        have ha_limb : ∀ k < L, st.mem (a + k) = (x / 2 ^ (k * h)) % 2 ^ h := fun k hk => by
          rw [hframe (a + k) (by omega)]; exact hx.getElem hk
        set t1 := (if i + q < L then (x / 2 ^ ((i + q) * h)) % 2 ^ h else 0) >>> r
        have hpart2 : ∀ (ω' : ℕ → Bool) (st' : State),
            st'.regs 0 = a → st'.regs 2 = dst → st'.regs 3 = L → st'.regs 5 = 2 ^ h →
            st'.regs 8 = q → st'.regs 9 = r → st'.regs 10 = hmr → st'.regs 13 = lim →
            st'.regs 11 = i → st'.regs 12 = t1 →
            (∀ j < i, st'.mem (dst + j) = ((x >>> y) / 2 ^ (j * h)) % 2 ^ h) →
            (∀ p, p < dst ∨ dst + i ≤ p → st'.mem p = mem p) →
            ∃ o st'' c, Runs w p ω'
              (.cond (.bin .lt (.bin .add (.reg 11) (.const 1)) (.reg 13))
                (.assign 12 (.bin .add (.reg 12)
                  (.bin .mod (.bin .shiftLeft
                    (.load (.bin .add (.reg 0)
                      (.bin .add (.bin .add (.reg 11) (.reg 8)) (.const 1)))) (.reg 10)) (.reg 5))))
                .nop ;;
               .store (.bin .add (.reg 2) (.reg 11)) (.reg 12))
              st' o st'' c ∧
              normalPost (fun st₁ =>
                (Function.update st₁.regs 11 (i + 1) 0 = a ∧
                  Function.update st₁.regs 11 (i + 1) 2 = dst ∧
                  Function.update st₁.regs 11 (i + 1) 3 = L ∧
                  Function.update st₁.regs 11 (i + 1) 5 = 2 ^ h ∧
                  Function.update st₁.regs 11 (i + 1) 8 = q ∧
                  Function.update st₁.regs 11 (i + 1) 9 = r ∧
                  Function.update st₁.regs 11 (i + 1) 10 = hmr ∧
                  Function.update st₁.regs 11 (i + 1) 13 = lim ∧
                  Function.update st₁.regs 11 (i + 1) 11 = i + 1 ∧
                  (∀ j < i + 1, st₁.mem (dst + j) = ((x >>> y) / 2 ^ (j * h)) % 2 ^ h) ∧
                  (∀ p, p < dst ∨ dst + (i + 1) ≤ p → st₁.mem p = mem p)) ∧ st₁.regs 11 = i) o st'' ∧
              c ≤ 27 := by
          intro ω' st' r0 r2 r3 r5 r8 r9 r10 r13 r11 r12 hlim' hframe'
          have ha_limb' : ∀ m < L, st'.mem (a + m) = (x / 2 ^ (m * h)) % 2 ^ h := fun m hm => by
            rw [hframe' (a + m) (by omega)]; exact hx.getElem hm
          refine runs_start_le ?_
          refine runs_seq_cond_le
            (Expr.eval_lt_op (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) (by eval_expr) hw1)
            (fun hne2 => ?_) (fun heq2 => ?_)
          · have hi1_lim : i + 1 < lim := by by_contra hnot; simp [hnot] at hne2
            have hiq1_lt : i + q + 1 < L := by omega
            have ha2_val : st'.mem (a + (i + q + 1)) = (x / 2 ^ ((i + q + 1) * h)) % 2 ^ h :=
              ha_limb' (i + q + 1) hiq1_lt
            set next := (x / 2 ^ ((i + q + 1) * h)) % 2 ^ h
            have hnext_lt : next < 2 ^ h := Nat.mod_lt _ (Nat.two_pow_pos _)
            have hsh_lt : next <<< hmr < 2 ^ (2 * h) := by
              rw [Nat.shiftLeft_eq,
                show 2 ^ (2 * h) = 2 ^ h * 2 ^ h by rw [← Nat.pow_add, show h + h = 2 * h by ring]]
              exact lt_of_lt_of_le
                (Nat.mul_lt_mul_of_pos_right hnext_lt (Nat.two_pow_pos _))
                (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le h r)))
            have hsh_w : next <<< hmr < 2 ^ w :=
              lt_trans hsh_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
            have hmod_eq : (next <<< hmr) % 2 ^ h = (next % 2 ^ r) <<< hmr := by
              have hsp := (Nat.mod_add_div next (2 ^ r)).symm
              have hpow_hr : 2 ^ r * 2 ^ hmr = 2 ^ h := by
                rw [← Nat.pow_add, Nat.add_sub_cancel' (le_of_lt hr_lt)]
              rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
              have hexp : next * 2 ^ hmr = (next % 2 ^ r) * 2 ^ hmr + 2 ^ h * (next / 2 ^ r) := by
                calc next * 2 ^ hmr = (next % 2 ^ r + 2 ^ r * (next / 2 ^ r)) * 2 ^ hmr := by
                      conv_lhs => rw [hsp]
                  _ = (next % 2 ^ r) * 2 ^ hmr + (2 ^ r * 2 ^ hmr) * (next / 2 ^ r) := by ring
                  _ = (next % 2 ^ r) * 2 ^ hmr + 2 ^ h * (next / 2 ^ r) := by rw [hpow_hr]
              have hrem_lt : (next % 2 ^ r) * 2 ^ hmr < 2 ^ h := by
                rw [← hpow_hr]
                exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
              rw [hexp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
            have hsum_eq : t1 + (next <<< hmr) % 2 ^ h = ((x >>> y) / 2 ^ (i * h)) % 2 ^ h := by
              rw [hmod_eq, hshr_form]
              simp [t1, hiq1_lt, show i + q < L by omega, next, hmr]
            have hadd2_eval : (Expr.bin .add (.reg 12)
                (.bin .mod (.bin .shiftLeft
                  (.load (.bin .add (.reg 0)
                    (.bin .add (.bin .add (.reg 11) (.reg 8)) (.const 1)))) (.reg 10)) (.reg 5))).eval w st' =
                some (((x >>> y) / 2 ^ (i * h)) % 2 ^ h) := by
              rw [← hsum_eq]
              refine Expr.eval_add (by eval_expr)
                (Expr.eval_mod
                  (Expr.eval_bin
                    (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
                      (Expr.eval_add (Expr.eval_add (by eval_expr) (by eval_expr) (by omega))
                        (by eval_expr) (by omega)) (by omega)) ha2_val)
                    (by eval_expr) hsh_w)
                  (by eval_expr) hsh_w)
                (by rw [hsum_eq]; exact lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _)) hB)
            refine runs_seq_assign_le hadd2_eval ?_
            refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost)
            refine ⟨⟨by simp [r0], by simp [r2], by simp [r3], by simp [r5], by simp [r8],
              by simp [r9], by simp [r10], by simp [r13], by simp, ?_, ?_⟩, by simp [r11]⟩
            · intro j hj
              dsimp only
              by_cases hji : j = i
              · subst hji; rw [Function.update_self]; try exact hshr_form.symm
              · rw [Function.update_of_ne (by omega)]; exact hlim' j (by omega)
            · intro p hp
              dsimp only
              rw [Function.update_of_ne (by omega)]; exact hframe' p (by omega)
          · have hnot_hi1 : ¬ i + q + 1 < L := by
              intro hlt
              have : i + 1 < lim := by omega
              simp [this] at heq2
            have hsum_eq : t1 = ((x >>> y) / 2 ^ (i * h)) % 2 ^ h := by
              rw [hshr_form, ite_eq_right hnot_hi1]
              simp [t1, Nat.zero_mod, Nat.zero_shiftLeft]
            refine runs_seq_nop_le ?_
            refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost)
            refine ⟨⟨by simp [r0], by simp [r2], by simp [r3], by simp [r5], by simp [r8],
              by simp [r9], by simp [r10], by simp [r13], by simp, ?_, ?_⟩, by simp [r11]⟩
            · intro j hj
              dsimp only
              by_cases hji : j = i
              · subst hji; rw [Function.update_self, hsum_eq]
              · rw [Function.update_of_ne (by omega)]; exact hlim' j (by omega)
            · intro p hp
              dsimp only
              rw [Function.update_of_ne (by omega)]; exact hframe' p (by omega)
        refine runs_start_le ?_
        dsimp only
        refine runs_seq_assign_le (by eval_expr) ?_
        refine runs_seq_cond_le (Expr.eval_lt_op (by eval_expr) (by eval_expr) hw1)
          (fun hne1 => ?_) (fun heq1 => ?_)
        · have hi_lim : i < lim := by by_contra hnot; simp [hnot] at hne1
          have hiq_lt : i + q < L := by omega
          have ha1_val : st.mem (a + (i + q)) = (x / 2 ^ ((i + q) * h)) % 2 ^ h := ha_limb (i + q) hiq_lt
          have h1lt : ((x / 2 ^ ((i + q) * h)) % 2 ^ h) >>> r < 2 ^ h := by
            rw [Nat.shiftRight_eq_div_pow]
            exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _))
          have hsh1_eval : (Expr.bin .shiftRight
              (.load (.bin .add (.reg 0) (.bin .add (.reg 11) (.reg 8)))) (.reg 9)).eval w st =
              some t1 := by
            have ht1_eq : t1 = ((x / 2 ^ ((i + q) * h)) % 2 ^ h) >>> r := by simp [t1, hiq_lt]
            rw [ht1_eq]
            exact Expr.eval_bin
              (Expr.eval_load_of_eq (Expr.eval_add (by eval_expr)
                (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) (by omega)) ha1_val)
              (by eval_expr) (lt_trans h1lt hB)
          refine runs_seq_assign_le hsh1_eval ?_
          obtain ⟨o, st'', c, hrun, hpost, hc⟩ :=
            hpart2 _ ⟨st.mem, Function.update (Function.update st.regs 12 0) 12 t1, st.pos⟩
              (by simp [hr0]) (by simp [hr2]) (by simp [hr3]) (by simp [hr5])
              (by simp [hr8]) (by simp [hr9]) (by simp [hr10]) (by simp [hr13])
              (by simp [hr11]) (by simp) hlim hframe
          exact ⟨o, st'', c, hrun, hpost, by wram_cost⟩
        · have hnot_hiq : ¬ i + q < L := by
            intro hlt
            have : i < lim := by omega
            simp [this] at heq1
          have ht1_zero : 0 = t1 := by simp [t1, hnot_hiq]
          refine runs_seq_nop_le ?_
          obtain ⟨o, st'', c, hrun, hpost, hc⟩ :=
            hpart2 _ ⟨st.mem, Function.update st.regs 12 0, st.pos⟩
              (by simp [hr0]) (by simp [hr2]) (by simp [hr3]) (by simp [hr5])
              (by simp [hr8]) (by simp [hr9]) (by simp [hr10]) (by simp [hr13])
              (by simp [hr11]) (by simp [ht1_zero]) hlim hframe
          exact ⟨o, st'', c, hrun, hpost, by wram_cost⟩)
    refine runs_seq_triple_le hloop rfl ?_
    rintro st₃ ⟨_, _, _, _, _, _, _, _, _, hlim, hframe⟩
    have hshr_lt : x >>> y < 2 ^ (L * h) := by
      rw [Nat.shiftRight_eq_div_pow]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hx.lt_pow
    have hlimbs : LimbsAt st₃.mem dst L h (x >>> y) :=
      limbsAt_iff_pointwise.mpr ⟨hshr_lt, hlim⟩
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact hlimbs, hframe⟩ ?_
    dsimp only [mwShiftRightContract]
    wram_cost
  · have hge : L * h ≤ y := by
      by_contra hnot
      have : y < L * h := Nat.not_le.mp hnot
      simp [this] at hcond
    refine runs_seq_call_le hZero (by eval_expr) (by wram_words) ⟨dst, L, rfl, hw1, hdst⟩ ?_
    rintro _ mem₂ pos₂ ⟨dst', L', heq2, _, hlist, hframe⟩
    simp only [List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    have hsh0 : x >>> y = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le hx.lt_pow (Nat.pow_le_pow_right (by norm_num) hge))
    have hlimbs : LimbsAt mem₂ dst L h (x >>> y) := by
      rw [hsh0]
      exact limbsAt_zero_iff.mpr hlist
    have hframe' : ∀ p, p < dst ∨ dst + L ≤ p → mem₂ p = mem p := fun p hp => by
      rw [hframe p hp, hmem1]
    refine runs_ret_le (by eval_expr)
      ⟨a, b', dst, L, h, rfl, rfl, fun x' y' hx' hy' => by
        obtain rfl : x' = x := hx'.ext hx
        obtain rfl : y' = y := hy'.ext hy
        exact hlimbs, hframe'⟩ ?_
    dsimp only [mwShiftRightContract, mwZeroContract]
    wram_cost

end MinCostFlow.WideWord
