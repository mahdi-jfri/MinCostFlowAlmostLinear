module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.DivisionEstimate
import MinCostFlow.Num.LeadingEstimate
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# A machine quotient-digit estimate

A one-limb divisor uses direct word division. Otherwise the procedure divides the
leading numerator triple by the leading divisor pair, and caps the result at the
largest limb. The result is the true quotient digit or one larger. The body is read
only and costs at most 56 steps. Three-limb word slack replaces a normalization scan.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- The three aligned numerator limbs combined into one word. -/
def leadingTripleExpr (h : ℕ) : Expr :=
  let high := Expr.load (.bin .add (.reg 0) (.reg 2))
  let middle := Expr.load (.bin .add (.reg 0) (.bin .sub (.reg 2) (.const 1)))
  let low := Expr.load (.bin .add (.reg 0) (.bin .sub (.reg 2) (.const 2)))
  .bin .add (.bin .mul (.bin .add (.bin .mul high (.const (base h))) middle) (.const (base h))) low

/-- The two leading divisor limbs combined into one word. -/
def leadingPairExpr (h : ℕ) : Expr :=
  let high := Expr.load (.bin .add (.reg 1) (.bin .sub (.reg 2) (.const 1)))
  let low := Expr.load (.bin .add (.reg 1) (.bin .sub (.reg 2) (.const 2)))
  .bin .add (.bin .mul high (.const (base h))) low

/-- Arguments `[numerator, divisor, effectiveDivisorLength]`. -/
def estimateDigitBody (h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 1))
    (.ret (.bin .div
      (.bin .add (.bin .mul (.load (.bin .add (.reg 0) (.const 1))) (.const (base h))) (.load (.reg 0)))
      (.load (.reg 1))))
    (.assign 3 (leadingTripleExpr h) ;;
     .assign 4 (leadingPairExpr h) ;;
     .assign 5 (.bin .div (.reg 3) (.reg 4)) ;;
     .cond (.bin .lt (.reg 5) (.const (base h))) (.ret (.reg 5)) (.ret (.const (base h - 1))))

/-- A read-only quotient estimate at entry `b`. -/
def estimateDigitModule (_b h : ℕ) : List Stmt := [estimateDigitBody h]

/-- The effective length is positive and its highest divisor limb is nonzero.
The numerator is one limb wider and less than the divisor times the base. -/
def estimateDigitContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d n, args = [a, d, n] ∧ 0 < n ∧ a + (n + 1) < 2 ^ w ∧ d + n < 2 ^ w ∧
    Valid mem a h (n + 1) ∧ Valid mem d h n ∧ 0 < mem (d + (n - 1)) ∧
    unsignedVal mem a h (n + 1) < unsignedVal mem d h n * base h
  post args mem v mem' := mem' = mem ∧
    unsignedVal mem (args.getD 0 0) h (args.getD 2 0 + 1) /
      unsignedVal mem (args.getD 1 0) h (args.getD 2 0) ≤ v ∧
    v ≤ unsignedVal mem (args.getD 0 0) h (args.getD 2 0 + 1) /
      unsignedVal mem (args.getD 1 0) h (args.getD 2 0) + 1 ∧ v < base h
  cost _ _ := 56

/-- The quotient estimate has no random statement. -/
theorem estimateDigitBody_noRand (h : ℕ) : (estimateDigitBody h).NoRand := by
  simp [estimateDigitBody, Stmt.NoRand]

/-- The quotient-digit estimate meets its constant-cost read-only contract. -/
theorem estimateDigit_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hp : p.HasAt b (estimateDigitModule b h)) :
    MeetsContract w p b (estimateDigitContract w h) := by
  have hb := base_lt_word (show 2 * h + 2 ≤ w by omega)
  have hw1 : 1 < 2 ^ w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw2 : 2 < 2 ^ w := lt_of_lt_of_le (by decide : 2 < 2 ^ 3)
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨a, d, n, rfl, hn, ha, hd, hva, hvd, htop, hX⟩
  have hVpos : 0 < unsignedVal mem d h n := by
    by_contra he
    have hz : unsignedVal mem d h n = 0 := by omega
    have hh := unsignedVal_eq_zero_iff.mp hz (n - 1) (by omega)
    omega
  have hqB : unsignedVal mem a h (n + 1) / unsignedVal mem d h n < base h :=
    (Nat.div_lt_iff_lt_mul hVpos).mpr (by simpa only [Nat.mul_comm] using hX)
  apply runs_start_le
  unfold estimateDigitBody
  dsimp only [leadingTripleExpr, leadingPairExpr]
  wram_step
  · have he : n = 1 := by simpa [startState] using hcond
    subst n
    have hxa := hva 0 (by omega)
    have hxb := hva 1 (by omega)
    have hdd := hvd 0 (by omega)
    simp only [Nat.add_zero] at hxa hdd
    have hnumw : mem (a + 1) * base h + mem a < 2 ^ w := by
      simpa only [zero_mul, zero_add] using three_limbs_lt_word hw (base_pos h) hxb hxa
    have hdenw : mem d < 2 ^ w := lt_trans hdd hb
    have hnum : unsignedVal mem a h 2 = mem (a + 1) * base h + mem a := by
      simp only [unsignedVal, mul_zero, add_zero]
      ring
    have hden : unsignedVal mem d h 1 = mem d := by simp [unsignedVal]
    refine runs_ret_le (v := unsignedVal mem a h 2 / unsignedVal mem d h 1) ?_ ?_ ?_
    · conv_rhs => rw [hnum, hden]
      eval_expr
    · change mem = mem ∧ unsignedVal mem a h 2 / unsignedVal mem d h 1 ≤ _ ∧ _ ≤
        unsignedVal mem a h 2 / unsignedVal mem d h 1 + 1 ∧ _ < base h
      exact ⟨rfl, le_rfl, Nat.le_succ _, hqB⟩
    · simp only [estimateDigitContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
      omega
  · have hne : n ≠ 1 := by simpa [startState] using hcond
    have hn2 : 2 ≤ n := by omega
    have hbracket := leading_estimate_bounds hh hn2 hva hvd htop hX
    have hxn := hva n (by omega)
    have hxn1 := hva (n - 1) (by omega)
    have hxn2 := hva (n - 2) (by omega)
    have hdn1 := hvd (n - 1) (by omega)
    have hdn2 := hvd (n - 2) (by omega)
    have hTw : leadingTriple mem a h n < 2 ^ w := three_limbs_lt_word hw hxn hxn1 hxn2
    have hTraw := hTw
    change (mem (a + n) * base h + mem (a + (n - 1))) * base h + mem (a + (n - 2)) < 2 ^ w at hTraw
    have hT2w : mem (a + n) * base h + mem (a + (n - 1)) < 2 ^ w := by
      simpa only [zero_mul, zero_add] using three_limbs_lt_word hw (base_pos h) hxn hxn1
    have hT1w : mem (a + n) * base h < 2 ^ w := by omega
    have hT3w : (mem (a + n) * base h + mem (a + (n - 1))) * base h < 2 ^ w := by omega
    have hDw : leadingPair mem d h n < 2 ^ w := by
      simpa only [leadingPair, zero_mul, zero_add] using three_limbs_lt_word hw (base_pos h) hdn1 hdn2
    have hDraw := hDw
    change mem (d + (n - 1)) * base h + mem (d + (n - 2)) < 2 ^ w at hDraw
    have hD1w : mem (d + (n - 1)) * base h < 2 ^ w := by omega
    have hqw : leadingTriple mem a h n / leadingPair mem d h n < 2 ^ w :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hTw
    refine runs_seq_assign_le (v := leadingTriple mem a h n) ?_ ?_
    · conv_rhs => unfold leadingTriple
      eval_expr
    · refine runs_seq_assign_le (v := leadingPair mem d h n) ?_ ?_
      · conv_rhs => unfold leadingPair
        eval_expr
      · refine runs_seq_assign_le (v := leadingTriple mem a h n / leadingPair mem d h n) (by eval_expr) ?_
        wram_step
        · have hsmall : leadingTriple mem a h n / leadingPair mem d h n < base h := by
            simpa [startState] using hcond
          have hmin : min (base h - 1) (leadingTriple mem a h n / leadingPair mem d h n) =
              leadingTriple mem a h n / leadingPair mem d h n := min_eq_right (by omega)
          rw [hmin] at hbracket
          refine runs_ret_le (v := leadingTriple mem a h n / leadingPair mem d h n) (by eval_expr) ?_ ?_
          · exact ⟨rfl, hbracket.1, hbracket.2, hsmall⟩
          · simp only [estimateDigitContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
            omega
        · have hlarge : ¬ leadingTriple mem a h n / leadingPair mem d h n < base h := by
            simpa [startState] using hcond
          have hmin : min (base h - 1) (leadingTriple mem a h n / leadingPair mem d h n) = base h - 1 :=
            min_eq_left (by omega)
          rw [hmin] at hbracket
          have hmaxw : base h - 1 < 2 ^ w := lt_of_le_of_lt (Nat.sub_le _ _) hb
          refine runs_ret_le (by eval_expr) ?_ ?_
          · exact ⟨rfl, hbracket.1, hbracket.2, by change base h - 1 < base h; have hp := base_pos h; omega⟩
          · simp only [estimateDigitContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
            omega

end MinCostFlow.Num
