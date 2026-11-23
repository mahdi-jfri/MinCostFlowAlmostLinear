module

public import MinCostFlow.Num.MulAdd
import MinCostFlow.Num.MulRowFacts
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Schoolbook multiplication rows

This procedure adds all remaining shifted one-limb multiples to an accumulator of
`K` limbs. The row at position `i` updates only its high `K-i` limbs. Sources are
below the accumulator, so every later row reads the original source digits. The
cost is at most `(K-i)*(38*K+35)+6`, giving a quadratic bound at entry `i=0`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, K, accumulator, i]`; `row` is the verified one-row procedure. -/
def mulRowsBody (self row : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 4) (.reg 2))
    (.call 5 row [.reg 1, .bin .add (.reg 3) (.reg 4), .bin .sub (.reg 2) (.reg 4),
       .load (.bin .add (.reg 0) (.reg 4)), .const 0] ;;
     .call 6 self [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 4) (.const 1)] ;;
     .ret (.const 0))
    (.ret (.const 0))

/-- The row loop at entry `b`, linked to a row procedure at `row`. -/
def mulRowsModule (b row : ℕ) : List Stmt := [mulRowsBody b row]

/-- Add all remaining schoolbook rows to a valid accumulator. -/
def mulRowsContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d K out i, args = [a, d, K, out, i] ∧ i ≤ K ∧
    a + K ≤ out ∧ d + K ≤ out ∧ out + K < 2 ^ w ∧
    Valid mem a h K ∧ Valid mem d h K ∧ Valid mem out h K
  post args mem v mem' := v = 0 ∧ Valid mem' (args.getD 3 0) h (args.getD 2 0) ∧
    (∀ z, z < args.getD 3 0 ∨ args.getD 3 0 + args.getD 2 0 ≤ z → mem' z = mem z) ∧
    unsignedVal mem' (args.getD 3 0) h (args.getD 2 0) =
      (unsignedVal mem (args.getD 3 0) h (args.getD 2 0) + capacity h (args.getD 4 0) *
        unsignedVal mem (args.getD 0 0 + args.getD 4 0) h (args.getD 2 0 - args.getD 4 0) *
        unsignedVal mem (args.getD 1 0) h (args.getD 2 0)) % capacity h (args.getD 2 0)
  cost args _ := (args.getD 2 0 - args.getD 4 0) * (38 * args.getD 2 0 + 35) + 6

/-- The row loop contains no random statement. -/
theorem mulRowsBody_noRand (self row : ℕ) : (mulRowsBody self row).NoRand := by
  simp [mulRowsBody, Stmt.NoRand]

private theorem mulRows_cost {K i : ℕ} (hi : i < K) :
    38 * (K - i) + 35 + ((K - (i + 1)) * (38 * K + 35) + 6) ≤
      (K - i) * (38 * K + 35) + 6 := by
  have hs : K - i = (K - (i + 1)) + 1 := by omega
  have hm := Nat.mul_le_mul_left 38 (Nat.sub_le K i)
  conv_rhs => rw [hs, Nat.add_mul, one_mul]
  omega

private theorem mod_add_reduced (x y C : ℕ) : (x % C + y) % C = (x + y) % C := by
  simp only [Nat.add_mod, Nat.mod_mod]

/-- The schoolbook row loop meets its contract using the verified one-row procedure. -/
theorem mulRows_meetsContract {w h b row : ℕ} {p : Program} (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (mulRowsModule b row)) (hr : MeetsContract w p row (mulAddContract w h)) :
    MeetsContract w p b (mulRowsContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 2 0 - args.getD 4 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨a, d, K, out, i, rfl, hi, ha, hd, hout, hva, hvd, hvout⟩
  change K - i = t at ht
  subst t
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hKw : K < 2 ^ w := hwords K (by simp)
  have how : out < 2 ^ w := hwords out (by simp)
  have hiw : i < 2 ^ w := hwords i (by simp)
  apply runs_start_le
  unfold mulRowsBody
  wram_step
  · have hlt : i < K := by simpa [startState] using hcond
    have hx : mem (a + i) < base h := hva i hlt
    refine runs_seq_call_le hr
      (vs := [d, out + i, K - i, mem (a + i), 0]) (by eval_expr) ?_ ?_ ?_
    · have hxw : mem (a + i) < 2 ^ w := lt_trans hx hb
      wram_words
    · exact ⟨d, out + i, K - i, mem (a + i), 0, rfl, by omega, by omega, hx, by omega,
        fun j hj => hvd j (by omega), fun j hj => by
          simpa only [Nat.add_assoc, startState] using hvout (i + j) (by omega)⟩
    · intro carry mem₁ pos₁ hpost
      rcases hpost with ⟨hcarry, hvalid, hframe, hmass⟩
      change Valid mem₁ (out + i) h (K - i) at hvalid
      change (∀ z, z < out + i ∨ out + i + (K - i) ≤ z → mem₁ z = mem z) at hframe
      change unsignedVal mem₁ (out + i) h (K - i) + capacity h (K - i) * carry =
        unsignedVal mem (out + i) h (K - i) + mem (a + i) * unsignedVal mem d h (K - i) + 0 at hmass
      simp only [Nat.add_zero] at hmass
      have hrow := mul_row_value hi hvout hvalid hframe hmass
      have hA : ∀ j < K, mem₁ (a + j) = mem (a + j) := by
        intro j hj
        exact hframe _ (Or.inl (by omega))
      have hB : ∀ j < K, mem₁ (d + j) = mem (d + j) := by
        intro j hj
        exact hframe _ (Or.inl (by omega))
      refine runs_seq_call_le ih (vs := [a, d, K, out, i + 1]) (by eval_expr) (by wram_words) ?_ ?_
      · change (∃ a' d' K' out' i', [a, d, K, out, i + 1] = [a', d', K', out', i'] ∧
            i' ≤ K' ∧ a' + K' ≤ out' ∧ d' + K' ≤ out' ∧ out' + K' < 2 ^ w ∧
            Valid mem₁ a' h K' ∧ Valid mem₁ d' h K' ∧ Valid mem₁ out' h K') ∧
            K - (i + 1) < K - i
        refine ⟨⟨a, d, K, out, i + 1, rfl, by omega, ha, hd, hout, ?_, ?_, hrow.1⟩, by omega⟩
        · intro j hj
          rw [hA j hj]
          exact hva j hj
        · intro j hj
          rw [hB j hj]
          exact hvd j hj
      · intro v mem₂ pos₂ hpst
        rcases hpst with ⟨hvzero, hvalid₂, hframe₂, hvalue₂⟩
        change v = 0 at hvzero
        change Valid mem₂ out h K at hvalid₂
        change (∀ z, z < out ∨ out + K ≤ z → mem₂ z = mem₁ z) at hframe₂
        change unsignedVal mem₂ out h K = (unsignedVal mem₁ out h K + capacity h (i + 1) *
          unsignedVal mem₁ (a + (i + 1)) h (K - (i + 1)) * unsignedVal mem₁ d h K) % capacity h K at hvalue₂
        have hAtail : unsignedVal mem₁ (a + (i + 1)) h (K - (i + 1)) =
            unsignedVal mem (a + (i + 1)) h (K - (i + 1)) := by
          apply unsignedVal_congr
          intro j hj
          simpa only [Nat.add_assoc] using hA (i + 1 + j) (by omega)
        have hBfull : unsignedVal mem₁ d h K = unsignedVal mem d h K := unsignedVal_congr hB
        refine runs_ret_le (by eval_expr) ?_ ?_
        · change 0 = 0 ∧ Valid mem₂ out h K ∧ (∀ z, z < out ∨ out + K ≤ z → mem₂ z = mem z) ∧
            unsignedVal mem₂ out h K = (unsignedVal mem out h K + capacity h i *
              unsignedVal mem (a + i) h (K - i) * unsignedVal mem d h K) % capacity h K
          refine ⟨rfl, hvalid₂, ?_, ?_⟩
          · intro z hz
            rw [hframe₂ z hz, hframe z (by omega)]
          · rw [hvalue₂, hAtail, hBfull, hrow.2, mod_add_reduced, Nat.add_assoc,
              mul_rows_split mem a d h K i hlt]
        · simp only [mulRowsContract, Contract.below, mulAddContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_const,
            Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil]
          nlinarith only [mulRows_cost hlt]
  · have hnot : ¬ i < K := by simpa [startState] using hcond
    have he : i = K := by omega
    subst i
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change 0 = 0 ∧ Valid mem out h K ∧ (∀ z, z < out ∨ out + K ≤ z → mem z = mem z) ∧
        unsignedVal mem out h K = (unsignedVal mem out h K + capacity h K * unsignedVal mem (a + K) h (K - K) *
          unsignedVal mem d h K) % capacity h K
      refine ⟨rfl, hvout, fun _ _ => rfl, ?_⟩
      simp only [Nat.sub_self, unsignedVal, mul_zero, zero_mul, add_zero,
        Nat.mod_eq_of_lt (unsignedVal_lt hvout)]
    · simp only [mulRowsContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_reg, Expr.size_const, Expr.size_bin, Nat.sub_self, zero_mul]
      omega

end MinCostFlow.Num
