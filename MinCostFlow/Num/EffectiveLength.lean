module

public import MinCostFlow.Num.Representation
import MinCostFlow.Num.SignFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Locating the highest nonzero limb

Long division uses the leading divisor limbs. This read-only scan drops zero high
limbs until it finds the highest nonzero cell. Its return is the effective limb count,
zero exactly for an all-zero block. It preserves the unsigned value and costs at most
`21*L + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L]`, returning the number of limbs through the highest nonzero one. -/
def effectiveLengthBody (b : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.cond (.bin .eq (.load (.bin .add (.reg 0) (.bin .sub (.reg 1) (.const 1)))) (.const 0))
      (.call 2 b [.reg 0, .bin .sub (.reg 1) (.const 1)] ;; .ret (.reg 2))
      (.ret (.reg 1)))

/-- The highest-nonzero-limb scan. -/
def effectiveLengthModule (b : ℕ) : List Stmt := [effectiveLengthBody b]

/-- Return the effective length and characterize both the last limb and all omitted cells. -/
def effectiveLengthContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L, args = [a, L] ∧ a + L < 2 ^ w ∧ Valid mem a h L
  post args mem v mem' := mem' = mem ∧ v ≤ args.getD 1 0 ∧
    (∀ i, v ≤ i → i < args.getD 1 0 → mem (args.getD 0 0 + i) = 0) ∧
    (0 < v → 0 < mem (args.getD 0 0 + (v - 1))) ∧
    unsignedVal mem (args.getD 0 0) h v = unsignedVal mem (args.getD 0 0) h (args.getD 1 0)
  cost args _ := 21 * args.getD 1 0 + 6

/-- The leading-limb scan is deterministic. -/
theorem effectiveLengthBody_noRand (b : ℕ) : (effectiveLengthBody b).NoRand := by
  simp [effectiveLengthBody, Stmt.NoRand]

/-- The effective-length scan meets its read-only contract with linear cost. -/
theorem effectiveLength_meetsContract {w h b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b (effectiveLengthModule b)) : MeetsContract w p b (effectiveLengthContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨a, L, rfl, ha, hv⟩
  change L = k at hk
  subst k
  apply runs_start_le
  unfold effectiveLengthBody
  wram_step
  · have hz : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change mem = mem ∧ 0 ≤ 0 ∧ (∀ i, 0 ≤ i → i < 0 → mem (a + i) = 0) ∧
        (0 < 0 → 0 < mem (a + (0 - 1))) ∧ unsignedVal mem a h 0 = unsignedVal mem a h 0
      exact ⟨rfl, le_rfl, fun i _ hi => by omega, by omega, rfl⟩
    · simp only [effectiveLengthContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hMv : Valid mem a h M := fun i hi => hv i (by omega)
    wram_step
    · have hz : mem (a + M) = 0 := by simpa [startState] using hcond
      refine runs_seq_call_le ih (vs := [a, M])
        (by eval_expr; simp [Expr.eval, BinOp.eval, startState, hw, show M < 2 ^ w by omega])
        (by wram_words) ?_ ?_
      · change (∃ a' L', [a, M] = [a', L'] ∧ a' + L' < 2 ^ w ∧ Valid mem a' h L') ∧ M < M + 1
        exact ⟨⟨a, M, rfl, by omega, hMv⟩, by omega⟩
      · intro v mem' pos' hpst
        rcases hpst with ⟨hmem, hle, hzero, hlast, hvalue⟩
        subst mem'
        change v ≤ M at hle
        change (∀ i, v ≤ i → i < M → mem (a + i) = 0) at hzero
        change (0 < v → 0 < mem (a + (v - 1))) at hlast
        change unsignedVal mem a h v = unsignedVal mem a h M at hvalue
        have hvw : v < 2 ^ w := by omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change mem = mem ∧ v ≤ M + 1 ∧ (∀ i, v ≤ i → i < M + 1 → mem (a + i) = 0) ∧
            (0 < v → 0 < mem (a + (v - 1))) ∧ unsignedVal mem a h v = unsignedVal mem a h (M + 1)
          refine ⟨rfl, by omega, ?_, hlast, ?_⟩
          · intro i hiv hi
            by_cases he : i = M
            · simpa only [he] using hz
            · exact hzero i hiv (by omega)
          · rw [unsignedVal_snoc, hz, mul_zero, add_zero, hvalue]
        · simp only [effectiveLengthContract, Contract.below, List.getD_cons_zero,
            List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
            argsSize_cons, argsSize_nil]
          omega
    · have hnz : mem (a + M) ≠ 0 := by simpa [startState] using hcond
      refine runs_ret_le (by eval_expr) ?_ ?_
      · change mem = mem ∧ M + 1 ≤ M + 1 ∧ (∀ i, M + 1 ≤ i → i < M + 1 → mem (a + i) = 0) ∧
          (0 < M + 1 → 0 < mem (a + (M + 1 - 1))) ∧
            unsignedVal mem a h (M + 1) = unsignedVal mem a h (M + 1)
        exact ⟨rfl, le_rfl, fun i hi hj => by omega, fun _ => by simpa using Nat.pos_of_ne_zero hnz, rfl⟩
      · simp only [effectiveLengthContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
        omega

end MinCostFlow.Num
