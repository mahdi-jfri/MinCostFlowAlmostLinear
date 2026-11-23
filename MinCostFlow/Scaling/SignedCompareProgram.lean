module

public import MinCostFlow.Statement.Problem
public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Comparing one-word-magnitude signed integers

The flow reduction rejects lower capacities larger than upper capacities.
This procedure compares the canonical sign/magnitude pairs used by the
statement. Opposite signs decide the order directly. Equal nonnegative signs
compare magnitudes, and equal negative signs reverse that comparison. It
preserves all memory, has no random instructions, and costs at most 40.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem sign_less_implies_reverse_order (x y : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) < if y < 0 then 1 else 0) : y < x := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0 <;>
    simp only [hx, hy, ↓reduceIte] at h <;> omega

private theorem nonnegative_of_zero_sign (x : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) = 0) : 0 ≤ x := by
  by_cases hx : x < 0 <;> simp only [hx, ↓reduceIte] at h <;> omega

private theorem negative_of_nonzero_sign (x : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) ≠ 0) : x < 0 := by
  by_cases hx : x < 0 <;> simp only [hx, ↓reduceIte] at h <;> omega

/-- Arguments `[xSign,xMagnitude,ySign,yMagnitude]`, returning the indicator
of the first integer being at most the second. -/
def signedCompareBody : Stmt :=
  .cond (.bin .lt (.reg 0) (.reg 2)) (.ret (.const 0))
    (.cond (.bin .lt (.reg 2) (.reg 0)) (.ret (.const 1))
      (.cond (.bin .eq (.reg 0) (.const 0))
        (.ret (.bin .sub (.const 1) (.bin .lt (.reg 3) (.reg 1))))
        (.ret (.bin .sub (.const 1) (.bin .lt (.reg 1) (.reg 3))))))

/-- Signed comparison occupies one procedure. -/
def signedCompareModule : List Stmt := [signedCompareBody]

/-- Canonical comparison with no memory changes or allocation. -/
def signedCompareContract (w : ℕ) (x y : ℤ) : Contract where
  pre args _ := args = [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs] ∧ 1 < 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = if x ≤ y then 1 else 0
  cost _ _ := 40

/-- Comparison uses no random instruction. -/
theorem signedCompareBody_noRand : signedCompareBody.NoRand := by
  simp only [signedCompareBody, Stmt.NoRand, and_self]

/-- The comparison procedure computes the integer order for every pair of
canonical inputs, including zero, and costs at most 40 steps. -/
theorem signedCompare_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b signedCompareModule) (x y : ℤ) :
    MeetsContract w p b (signedCompareContract w x y) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hw⟩ := hpre
  have hxword : x.natAbs < 2 ^ w := hwords _ (List.mem_cons_of_mem _ (List.mem_cons_self))
  have hyword : y.natAbs < 2 ^ w :=
    hwords _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  apply runs_start_le
  unfold signedCompareBody
  wram_step
  · have hsign : (if x < 0 then 1 else 0 : ℕ) < if y < 0 then 1 else 0 := by simpa [startState] using hcond
    have hxy : ¬x ≤ y := not_le.mpr (sign_less_implies_reverse_order x y hsign)
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 0 = if x ≤ y then 1 else 0
      simp only [hxy, ↓reduceIte, and_self]
    · simp only [signedCompareContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hnxy : ¬(if x < 0 then 1 else 0 : ℕ) < if y < 0 then 1 else 0 := by simpa [startState] using hcond
    wram_step
    · have hsign : (if y < 0 then 1 else 0 : ℕ) < if x < 0 then 1 else 0 := by simpa [startState] using hcond
      have hxy := (sign_less_implies_reverse_order y x hsign).le
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ 1 = if x ≤ y then 1 else 0
        simp only [hxy, ↓reduceIte, and_self]
      · simp only [signedCompareContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
        omega
    · have hnyx : ¬(if y < 0 then 1 else 0 : ℕ) < if x < 0 then 1 else 0 := by simpa [startState] using hcond
      have heq : (if x < 0 then 1 else 0 : ℕ) = if y < 0 then 1 else 0 := by omega
      wram_step
      · have hzero : (if x < 0 then 1 else 0 : ℕ) = 0 := by simpa [startState] using hcond
        have hx := nonnegative_of_zero_sign x hzero
        have hy := nonnegative_of_zero_sign y (heq.symm.trans hzero)
        refine runs_ret_le (by eval_expr) ?_ ?_
        · change mem = mem ∧ 1 - (if y.natAbs < x.natAbs then 1 else 0) = if x ≤ y then 1 else 0
          refine ⟨rfl, ?_⟩
          by_cases hxy : x ≤ y
          · have hm : ¬y.natAbs < x.natAbs := by omega
            simp only [hxy, hm, ↓reduceIte, Nat.sub_zero]
          · have hm : y.natAbs < x.natAbs := by omega
            simp only [hxy, hm, ↓reduceIte, Nat.sub_self]
        · simp only [signedCompareContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
          omega
      · have hnon : (if x < 0 then 1 else 0 : ℕ) ≠ 0 := by simpa [startState] using hcond
        have hx := negative_of_nonzero_sign x hnon
        have hy := negative_of_nonzero_sign y (fun hz => hnon (heq.trans hz))
        refine runs_ret_le (by eval_expr) ?_ ?_
        · change mem = mem ∧ 1 - (if x.natAbs < y.natAbs then 1 else 0) = if x ≤ y then 1 else 0
          refine ⟨rfl, ?_⟩
          by_cases hxy : x ≤ y
          · have hm : ¬x.natAbs < y.natAbs := by omega
            simp only [hxy, hm, ↓reduceIte, Nat.sub_zero]
          · have hm : x.natAbs < y.natAbs := by omega
            simp only [hxy, hm, ↓reduceIte, Nat.sub_self]
        · simp only [signedCompareContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
          omega

/-- All comparison preconditions can hold for arbitrary integers. -/
theorem exists_signedCompare_pre (x y : ℤ) :
    ∃ w, (∀ a ∈ [if x < 0 then 1 else 0, x.natAbs,
        if y < 0 then 1 else 0, y.natAbs], a < 2 ^ w) ∧
      (signedCompareContract w x y).pre
        [if x < 0 then 1 else 0, x.natAbs, if y < 0 then 1 else 0, y.natAbs] (fun _ => 0) := by
  let w := wordSize 1 [x.natAbs + y.natAbs + 2]
  have hbig : x.natAbs + y.natAbs + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, rfl, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · split <;> omega
  · omega
  · split <;> omega
  · omega

end MinCostFlow.Scaling.Machine
