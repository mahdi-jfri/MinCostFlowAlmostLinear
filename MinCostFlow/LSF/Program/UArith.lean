module

public import MinCostFlow.Num.Encoding
public import MinCostFlow.Num.ShiftFacts
public import MinCostFlow.Num.SignFacts
public import MinCostFlow.Num.WordBounds
public import WordRAM.Tactic
import Mathlib.Tactic

/-!
# In-place unsigned arithmetic on limb blocks

The stretch program adds many path lengths, all of them nonnegative. This file gives one small
loop for that, `uAccProc`, which works in place and needs no heap. On a block `d` of `L` limbs it
adds `k` times a block `a` (for a limb `k`), or subtracts `a`, modulo the capacity of the block.
The two blocks must not overlap.

Subtraction uses the two's complement: `d - a = d + (capacity - 1 - a) + 1`, and the limbs of
`capacity - 1 - a` are `base - 1 - a_i`. The carry starts at `1` for a subtraction.

* `uAccProc`, `uAcc_meetsContract`: the loop, at cost `70 L + 20`.
* `uacc_step`: the arithmetic of one limb.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

lemma mul_le_self_of_le_one' {c a : ℕ} (hc : c ≤ 1) : c * a ≤ a := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> subst h <;> simp

/-- The value added by `uAccProc`: `capacity - A` for a subtraction, `k A` otherwise. -/
def accTerm (h L k neg A : ℕ) : ℕ := if neg = 1 then capacity h L - A else k * A

/-- One limb of the accumulation. -/
lemma uacc_step {h i k neg U D A c dI aI : ℕ} (hneg : neg ≤ 1) (hA : A ≤ capacity h i)
    (ha : aI < base h)
    (hinv : U + capacity h i * c = D + accTerm h i k neg A) :
    (U + capacity h i * ((dI + (if neg = 1 then base h - 1 - aI else k * aI) + c) % base h)) +
        capacity h (i + 1) * ((dI + (if neg = 1 then base h - 1 - aI else k * aI) + c) / base h) =
      (D + capacity h i * dI) + accTerm h (i + 1) k neg (A + capacity h i * aI) := by
  set s := dI + (if neg = 1 then base h - 1 - aI else k * aI) + c with hs
  have hsplit : capacity h i * (s % base h) + capacity h (i + 1) * (s / base h) =
      capacity h i * s := by
    rw [capacity_succ, mul_comm (base h) (capacity h i), mul_assoc, ← mul_add,
      Nat.mod_add_div]
  rw [add_assoc, hsplit, hs]
  unfold accTerm at hinv ⊢
  split_ifs at hinv ⊢ with hn
  · -- subtraction
    have hB : 1 ≤ base h := base_pos h
    have hcap := capacity_succ h i
    have hle : A + capacity h i * aI ≤ capacity h (i + 1) := by
      rw [hcap]
      have : capacity h i * aI + capacity h i ≤ base h * capacity h i := by
        rw [mul_comm (base h)]
        calc capacity h i * aI + capacity h i = capacity h i * (aI + 1) := by ring
          _ ≤ capacity h i * base h := Nat.mul_le_mul_left _ (by omega)
      omega
    zify [hA, hle, (by omega : aI ≤ base h - 1), (by omega : 1 ≤ base h)] at hinv ⊢
    push_cast [hcap] at hinv ⊢
    linear_combination hinv
  · have : U + capacity h i * c = D + k * A := hinv
    nlinarith [this]

/-- Args: `[d, a, L, k, neg]`. Registers: `5 = i`, `6 = carry`, `7 = limb sum`. -/
def uAccBody (h : ℕ) : Stmt :=
  .assign 7 (.bin .add
    (.bin .add (.load (.bin .add (.reg 0) (.reg 5)))
      (.bin .add
        (.bin .mul (.reg 4) (.bin .sub (.const (base h - 1)) (.load (.bin .add (.reg 1) (.reg 5)))))
        (.bin .mul (.bin .sub (.const 1) (.reg 4))
          (.bin .mul (.reg 3) (.load (.bin .add (.reg 1) (.reg 5)))))))
    (.reg 6)) ;;
  .store (.bin .add (.reg 0) (.reg 5)) (.bin .mod (.reg 7) (.const (base h))) ;;
  .assign 6 (.bin .div (.reg 7) (.const (base h)))

/-- Args: `[d, a, L, k, neg]`. -/
def uAccProc (h : ℕ) : Stmt :=
  .assign 6 (.reg 4) ;;
  forRange 5 (.const 0) (.reg 2) (uAccBody h) ;;
  .ret (.const 0)

lemma uAccProc_noRand (h : ℕ) : (uAccProc h).NoRand := by
  simp [uAccProc, uAccBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `uAccProc`. -/
def uAccContract (w h : ℕ) : Contract where
  pre args mem := ∃ d a L k neg, args = [d, a, L, k, neg] ∧ neg ≤ 1 ∧ k < base h ∧
    Valid mem d h L ∧ Valid mem a h L ∧ (a + L ≤ d ∨ d + L ≤ a) ∧ d + L < 2 ^ w ∧
    a + L < 2 ^ w
  post args mem ret mem' := ∃ d a L k neg, args = [d, a, L, k, neg] ∧ ret = 0 ∧
    (∀ x, x < d ∨ d + L ≤ x → mem' x = mem x) ∧ Valid mem' d h L ∧
    unsignedVal mem' d h L =
      (unsignedVal mem d h L + accTerm h L k neg (unsignedVal mem a h L)) % capacity h L
  cost args _ := 70 * args.getD 2 0 + 20

theorem uAcc_meetsContract {w h : ℕ} {p : Program} {b : ℕ} (hh : 1 ≤ h) (hw : 2 * h + 2 ≤ w)
    (hp : p.procs[b]? = some (uAccProc h)) :
    MeetsContract w p b (uAccContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨d, a, L, k, neg, rfl, hneg, hk, hvd, hva, hdisj, hdw, haw⟩ := hpre
  set B := base h with hBdef
  have hB0 : 0 < B := base_pos h
  have hBw : B < 2 ^ w := base_lt_word hw
  have hw1 : 1 < 2 ^ w := by omega
  have hB4 : B * B * 4 ≤ 2 ^ w := by
    rw [hBdef, base, ← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBB : (B - 1) * (B - 1) ≤ B * B := Nat.mul_le_mul (by omega) (by omega)
  have hB2 : 2 ≤ B := by
    rw [hBdef, base]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hid : (B - 1) * (B - 1) + 2 * (B - 1) + 1 = B * B := by
    obtain ⟨m, hm⟩ : ∃ m, B = m + 1 := ⟨B - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]; ring
  have hB1 : B - 1 ≤ (B - 1) * (B - 1) := Nat.le_mul_of_pos_left _ (by omega)
  set args := [d, a, L, k, neg] with hargs
  have hLw : L < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ j < 5, st.regs j = args.getD j 0) ∧ st.regs 5 = i ∧ st.regs 6 < B ∧
    (∀ x, x < d ∨ d + i ≤ x → st.mem x = mem x) ∧
    (∀ j < i, st.mem (d + j) < B) ∧
    unsignedVal st.mem d h i + capacity h i * st.regs 6 =
      unsignedVal mem d h i + accTerm h i k neg (unsignedVal mem a h i)
  have hR0 : ∀ j < 5, (startState args mem pos).regs j = args.getD j 0 := by
    intro j hj
    interval_cases j <;> simp [startState, hargs]
  have hloop : ∀ st₀ : State, (∀ j < 5, st₀.regs j = args.getD j 0) → st₀.regs 6 = neg →
      st₀.mem = mem → Triple w p (fun st => st = st₀)
      (forRange 5 (.const 0) (.reg 2) (uAccBody h)) (normalPost (Inv L))
      (fun _ => (L - 0) * (60 + (Expr.reg 2).size + 8) +
        ((Expr.const 0).size + (Expr.reg 2).size + 5)) := by
    intro st₀ hr0 h6 hm0
    refine Triple.forRange_const 60 0 L (by omega) hw1 (fun _ => hLw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun j hj => ?_, by simp, ?_, fun x _ => by simp [hm0],
        fun j hj => absurd hj (by omega), ?_⟩
      · simp only [Function.update_of_ne (show j ≠ 5 by omega)]; exact hr0 j hj
      · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 5 by omega)]; rw [h6]; omega
      · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 5 by omega), h6]
        simp [unsignedVal, capacity, accTerm]
        split_ifs with hn <;> omega
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r2 : st.regs 2 = L := hI.1 2 (by omega)
      eval_expr
    · intro i _ hiL st ω' hI
      obtain ⟨hR, h5, hc, hfr, hlow, heq⟩ := hI
      have r0 : st.regs 0 = d := hR 0 (by omega)
      have r1 : st.regs 1 = a := hR 1 (by omega)
      have r3 : st.regs 3 = k := hR 3 (by omega)
      have r4 : st.regs 4 = neg := hR 4 (by omega)
      set c := st.regs 6 with hcdef
      have hdi : st.mem (d + i) = mem (d + i) := hfr _ (Or.inr (by omega))
      have hai : st.mem (a + i) = mem (a + i) :=
        hfr (a + i) (by rcases hdisj with h' | h' <;> omega)
      set dI := mem (d + i) with hdI
      set aI := mem (a + i) with haI
      have hdB : dI < B := hvd i hiL
      have haB : aI < B := hva i hiL
      set t := (if neg = 1 then B - 1 - aI else k * aI) with ht
      have hka : k * aI ≤ (B - 1) * (B - 1) := Nat.mul_le_mul (by omega) (by omega)
      have htsel : neg * (B - 1 - aI) + (1 - neg) * (k * aI) = t := by
        rw [ht]; rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hneg with h0 | h0 <;> simp [h0]
      have ht_le : t ≤ (B - 1) * (B - 1) + B := by rw [ht]; split_ifs <;> omega
      set s := dI + t + c with hs
      have ht_le' : t ≤ (B - 1) * (B - 1) := by rw [ht]; split_ifs <;> omega
      have hs_lt : s < B * B := by
        rw [hs]; omega
      have h1 : neg * (B - 1 - aI) ≤ B := (mul_le_self_of_le_one' hneg).trans (by omega)
      have h2 : (1 - neg) * (k * aI) ≤ (B - 1) * (B - 1) :=
        (mul_le_self_of_le_one' (by omega)).trans hka
      refine runs_start_le ?_
      unfold uAccBody
      refine runs_seq_assign_le (v := s) (by
        rw [hs, ← htsel, ← hdi, ← hai]
        rw [← hdi] at hdB; rw [← hai] at haB hka h1 h2
        eval_expr) ?_
      refine runs_seq_store_le (x := d + i) (v := s % B) (by eval_expr) (by eval_expr) ?_
      refine runs_assign_le (v := s / B) (by eval_expr) ⟨⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?_⟩ ?_
      · simp only [Function.update_of_ne (show j ≠ 5 by omega),
          Function.update_of_ne (show j ≠ 6 by omega), Function.update_of_ne (show j ≠ 7 by omega)]
        exact hR j hj
      · simpa using h5
      · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 5 by omega), Function.update_self]
        exact (Nat.div_lt_iff_lt_mul hB0).mpr hs_lt
      · intro x hx
        dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr x (by omega)
      · intro j hj
        dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by omega)]; exact hlow j hj
        · rw [Function.update_self]; exact Nat.mod_lt _ hB0
      · dsimp only
        simp only [Function.update_of_ne (show (6 : ℕ) ≠ 5 by omega), Function.update_self]
        have hlowU : unsignedVal (Function.update st.mem (d + i) (s % B)) d h i =
            unsignedVal st.mem d h i :=
          unsignedVal_congr fun j hj => Function.update_of_ne (by omega) _ _
        rw [unsignedVal_snoc, hlowU, Function.update_self, unsignedVal_snoc mem d,
          unsignedVal_snoc mem a]
        have hA : unsignedVal mem a h i ≤ capacity h i :=
          (unsignedVal_lt fun j hj => hva j (by omega)).le
        exact uacc_step hneg hA haB heq
      · simpa using h5
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  refine runs_start_le ?_
  unfold uAccProc
  refine runs_seq_assign_le (v := neg) (by have := hR0 4 (by omega); eval_expr) ?_
  refine runs_seq_triple_le (hloop _ (fun j hj => ?_) (by simp) rfl) rfl ?_
  · simp only [Function.update_of_ne (show j ≠ 6 by omega)]; exact hR0 j hj
  rintro st ⟨-, -, hc, hfr, hlow, heq⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨d, a, L, k, neg, rfl, rfl,
    fun x hx => hfr x (by omega), fun j hj => hlow j hj, ?_⟩ ?_
  · have hlt : unsignedVal st.mem d h L < capacity h L := unsignedVal_lt fun j hj => hlow j hj
    rw [← heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · simp only [uAccContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
      Expr.size_reg, Expr.size_bin, Expr.size_load]
    omega

end MinCostFlow.LSF.Program
