module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# One schoolbook multiplication row

Multiply a source block by one limb and add it to an existing destination block, with
an incoming carry. The source ends before the destination starts. The procedure updates
only the destination and returns the final carry. The proof keeps the exact equality
between the old value, the new value, and the carried capacity. Its cost is `38*M + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[source, destination, M, factor, carry]`. -/
def mulAddBody (b h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 4))
    (.assign 5 (.bin .add
       (.bin .add (.bin .mul (.load (.reg 0)) (.reg 3)) (.load (.reg 1))) (.reg 4)) ;;
     .store (.reg 1) (.bin .mod (.reg 5) (.const (base h))) ;;
     .call 6 b [.bin .add (.reg 0) (.const 1), .bin .add (.reg 1) (.const 1),
       .bin .sub (.reg 2) (.const 1), .reg 3, .bin .div (.reg 5) (.const (base h))] ;;
     .ret (.reg 6))

/-- The in-place row helper for schoolbook multiplication. -/
def mulAddModule (b h : ℕ) : List Stmt := [mulAddBody b h]

/-- Add a one-limb multiple to a destination, preserving every cell outside that block.
The returned carry gives an exact conservation equation, including overflow. -/
def mulAddContract (w h : ℕ) : Contract where
  pre args mem := ∃ a d M k c, args = [a, d, M, k, c] ∧ a + M ≤ d ∧ d + M < 2 ^ w ∧
    k < base h ∧ c ≤ k ∧ Valid mem a h M ∧ Valid mem d h M
  post args mem v mem' :=
    v ≤ args.getD 3 0 ∧ Valid mem' (args.getD 1 0) h (args.getD 2 0) ∧
    (∀ x, x < args.getD 1 0 ∨ args.getD 1 0 + args.getD 2 0 ≤ x → mem' x = mem x) ∧
    unsignedVal mem' (args.getD 1 0) h (args.getD 2 0) + capacity h (args.getD 2 0) * v =
      unsignedVal mem (args.getD 1 0) h (args.getD 2 0) +
        args.getD 3 0 * unsignedVal mem (args.getD 0 0) h (args.getD 2 0) + args.getD 4 0
  cost args _ := 38 * args.getD 2 0 + 6

/-- A schoolbook row contains no random statement. -/
theorem mulAddBody_noRand (b h : ℕ) : (mulAddBody b h).NoRand := by
  simp [mulAddBody, Stmt.NoRand]

/-- The row carry is never larger than its one-limb factor. -/
theorem mul_add_carry_le {h x y k c : ℕ} (hx : x < base h) (hy : y < base h) (hc : c ≤ k) :
    (x * k + y + c) / base h ≤ k := by
  have hm := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hx)
  have hs : x * k + y + c < (k + 1) * base h := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul (base_pos h)).mpr hs
  omega

/-- One multiplication row meets its exact in-place contract with linear cost. -/
theorem mulAdd_meetsContract {w h b : ℕ} {p : Program}
    (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (mulAddModule b h)) :
    MeetsContract w p b (mulAddContract w h) := by
  have hb := base_lt_word hw
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply meetsContract_of_rec (fun args _ => args.getD 2 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨a, d, M, k, c, rfl, ha, hd, hk, hc, hva, hvd⟩
  change M = t at ht
  subst t
  have hcw : c < 2 ^ w := lt_of_le_of_lt hc (lt_trans hk hb)
  apply runs_start_le
  unfold mulAddBody
  wram_step
  · have hz : M = 0 := by simpa [startState] using hcond
    subst M
    refine runs_ret_le (by eval_expr) ?_ ?_
    · change c ≤ k ∧ Valid mem d h 0 ∧ (∀ x, x < d ∨ d + 0 ≤ x → mem x = mem x) ∧
        unsignedVal mem d h 0 + capacity h 0 * c = unsignedVal mem d h 0 + k * unsignedVal mem a h 0 + c
      exact ⟨hc, fun i hi => by omega, fun _ _ => rfl, by simp [unsignedVal, capacity]⟩
    · simp only [mulAddContract, List.getD_cons_zero, List.getD_cons_succ,
        Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : M ≠ 0 := by simpa [startState] using hcond
    obtain ⟨S, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    obtain ⟨hxa, hta⟩ := valid_succ.mp hva
    obtain ⟨hxd, htd⟩ := valid_succ.mp hvd
    have hcb : c < base h := lt_of_le_of_lt hc hk
    have hsum := limb_mul_add_lt_word hw hxa hk hxd hcb
    have hmul : mem a * k < 2 ^ w := by omega
    have hadd : mem a * k + mem d < 2 ^ w := by omega
    have hcarry := mul_add_carry_le hxa hxd hc
    have hcarryw : (mem a * k + mem d + c) / base h < 2 ^ w := lt_of_le_of_lt hcarry (lt_trans hk hb)
    refine runs_seq_assign_le (v := mem a * k + mem d + c) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_call_le ih (by eval_expr) (by wram_words) ?_ ?_
    · change (∃ a' d' M' k' c',
          [a + 1, d + 1, S + 1 - 1, k, (mem a * k + mem d + c) / base h] = [a', d', M', k', c'] ∧
          a' + M' ≤ d' ∧ d' + M' < 2 ^ w ∧ k' < base h ∧ c' ≤ k' ∧
          Valid (Function.update mem d ((mem a * k + mem d + c) % base h)) a' h M' ∧
          Valid (Function.update mem d ((mem a * k + mem d + c) % base h)) d' h M') ∧ S + 1 - 1 < S + 1
      refine ⟨⟨a + 1, d + 1, S, k, _, by simp, by omega, by omega, hk, hcarry, ?_, ?_⟩, by omega⟩
      · intro i hi
        rw [Function.update_of_ne (by omega)]
        exact hta i hi
      · intro i hi
        rw [Function.update_of_ne (by omega)]
        exact htd i hi
    · intro v mem' pos' hpst
      rcases hpst with ⟨hvk, hvalid, hframe, hmass⟩
      change v ≤ k at hvk
      change Valid mem' (d + 1) h S at hvalid
      change (∀ x, x < d + 1 ∨ d + 1 + S ≤ x →
        mem' x = Function.update mem d ((mem a * k + mem d + c) % base h) x) at hframe
      have hvw : v < 2 ^ w := lt_of_le_of_lt hvk (lt_trans hk hb)
      have hhead : mem' d = (mem a * k + mem d + c) % base h := by
        rw [hframe d (Or.inl (by omega)), Function.update_self]
      have hsource : unsignedVal (Function.update mem d ((mem a * k + mem d + c) % base h))
          (a + 1) h S = unsignedVal mem (a + 1) h S := by
        apply unsignedVal_congr
        intro i hi
        exact Function.update_of_ne (by omega) _ _
      have hdest : unsignedVal (Function.update mem d ((mem a * k + mem d + c) % base h))
          (d + 1) h S = unsignedVal mem (d + 1) h S := by
        apply unsignedVal_congr
        intro i hi
        exact Function.update_of_ne (by omega) _ _
      change unsignedVal mem' (d + 1) h (S + 1 - 1) + capacity h (S + 1 - 1) * v =
        unsignedVal (Function.update mem d ((mem a * k + mem d + c) % base h)) (d + 1) h (S + 1 - 1) +
        k * unsignedVal (Function.update mem d ((mem a * k + mem d + c) % base h)) (a + 1) h (S + 1 - 1) +
          (mem a * k + mem d + c) / base h at hmass
      simp only [Nat.add_sub_cancel, hsource, hdest] at hmass
      refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
      · change v ≤ k ∧ Valid mem' d h (S + 1) ∧
          (∀ x, x < d ∨ d + (S + 1) ≤ x → mem' x = mem x) ∧
          unsignedVal mem' d h (S + 1) + capacity h (S + 1) * v =
            unsignedVal mem d h (S + 1) + k * unsignedVal mem a h (S + 1) + c
        refine ⟨hvk, valid_succ.mpr ⟨by rw [hhead]; exact Nat.mod_lt _ (base_pos h), hvalid⟩, ?_, ?_⟩
        · intro x hx
          have hx' : x < d + 1 ∨ d + 1 + S ≤ x := by omega
          rw [hframe x hx', Function.update_of_ne (by omega)]
        · have hm := congrArg (fun n => base h * n) hmass
          have hr := Nat.mod_add_div (mem a * k + mem d + c) (base h)
          rw [unsignedVal, unsignedVal, unsignedVal, capacity_succ, hhead]
          nlinarith only [hm, hr]
      · simp only [mulAddContract, Contract.below, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.Num
