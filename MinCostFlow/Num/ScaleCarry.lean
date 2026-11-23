module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Scaling limbs by a one-limb factor

The small part of a left bit shift multiplies by a power of two smaller than the limb
base. This helper multiplies by any one-limb factor, propagating a carry. It
stores the low `L` limbs and discards the last carry. Its cost is `35*L + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Splitting off the low limb of a scaled block gives the next carry. -/
theorem digits_unsigned_scale (mem : ℕ → ℕ) (a h L k c : ℕ) :
    digits h (L + 1) (unsignedVal mem a h (L + 1) * k + c) =
      (mem a * k + c) % base h ::
        digits h L (unsignedVal mem (a + 1) h L * k + (mem a * k + c) / base h) := by
  have he : unsignedVal mem a h (L + 1) * k + c =
      (mem a * k + c) + base h * (unsignedVal mem (a + 1) h L * k) := by
    simp only [unsignedVal]
    ring
  rw [he, digits, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (base_pos h)]
  congr 2
  omega

/-- Arguments `[a, L, factor, carry, heap]`. -/
def scaleCarryBody (b h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 4))
    (.assign 5 (.bin .add (.bin .mul (.load (.reg 0)) (.reg 2)) (.reg 3)) ;;
     .store (.reg 4) (.bin .mod (.reg 5) (.const (base h))) ;;
     .call 6 b [.bin .add (.reg 0) (.const 1), .bin .sub (.reg 1) (.const 1), .reg 2,
       .bin .div (.reg 5) (.const (base h)), .bin .add (.reg 4) (.const 1)] ;;
     .ret (.reg 6))

/-- A recursive one-limb scaling helper. -/
def scaleCarryModule (b h : ℕ) : List Stmt := [scaleCarryBody b h]

/-- Scale a valid block by a factor below the base and add a carry at most that factor. -/
def scaleCarryContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L k c heap, args = [a, L, k, c, heap] ∧
      a + L ≤ heap ∧ k < base h ∧ c ≤ k ∧ Valid mem a h L)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (digits h (args.getD 1 0)
        (unsignedVal mem (args.getD 0 0) h (args.getD 1 0) * args.getD 2 0 + args.getD 3 0)))
    (fun args _ => 35 * args.getD 1 0 + 6) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- One-limb scaling contains no random statement. -/
theorem scaleCarryBody_noRand (b h : ℕ) : (scaleCarryBody b h).NoRand := by
  simp [scaleCarryBody, Stmt.NoRand]

/-- The carry remains at most the scaling factor, including factor zero. -/
theorem scale_limb_carry_le {h x k c : ℕ} (hx : x < base h) (hc : c ≤ k) :
    (x * k + c) / base h ≤ k := by
  have hm := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hx)
  apply Nat.div_le_of_le_mul
  nlinarith only [hm, hc]

/-- One-limb scaling meets its contract with a linear cost bound. -/
theorem scaleCarry_meetsContract {w h b : ℕ} {p : Program}
    (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (scaleCarryModule b h)) :
    MeetsContract w p b (scaleCarryContract w h) := by
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := base_lt_word hw
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro t ih args mem pos ω hwords hpre ht
  rcases hpre with ⟨⟨a, L, k, c, heap, rfl, ha, hk, hc, hv⟩, hz, hbound⟩
  change L = t at ht
  subst t
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  apply runs_start_le
  unfold scaleCarryBody
  wram_step
  · have hzero : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨rfl, ?_⟩
      change heap ≤ heap ∧ heap ≤ heap + 0 ∧
        (∀ x < heap, mem x = mem x) ∧ ZeroFrom mem heap ∧ ListAt mem heap []
      exact ⟨le_rfl, le_rfl, fun _ _ => rfl, hz, listAt_nil _ _⟩
    · simp only [scaleCarryContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    obtain ⟨hx, htail⟩ := valid_succ.mp hv
    have hcb : c < base h := lt_of_le_of_lt hc hk
    have hsum : mem a * k + c < 2 ^ w := by
      simpa using limb_mul_add_lt_word hw hx hk hcb (base_pos h)
    have hpartial : mem a * k < 2 ^ w := by omega
    have hcarry := scale_limb_carry_le hx hc
    have hcarryword : (mem a * k + c) / base h < 2 ^ w := lt_of_le_of_lt hcarry (lt_trans hk hb)
    refine runs_seq_assign_le (v := mem a * k + c) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    have hz' := hz.update_head ((mem a * k + c) % base h)
    refine runs_seq_call_le ih (by eval_expr) ?_ ?_ ?_
    · wram_words
    · change ((∃ a' L' k' c' heap',
          [a + 1, M + 1 - 1, k, (mem a * k + c) / base h, heap + 1] =
            [a', L', k', c', heap'] ∧ a' + L' ≤ heap' ∧ k' < base h ∧ c' ≤ k' ∧
          Valid (Function.update mem heap ((mem a * k + c) % base h)) a' h L') ∧
          ZeroFrom (Function.update mem heap ((mem a * k + c) % base h)) (heap + 1) ∧
          heap + 1 + (M + 1 - 1) < 2 ^ w) ∧ M + 1 - 1 < M + 1
      refine ⟨⟨⟨a + 1, M, k, _, heap + 1, by simp, by omega, hk, hcarry, ?_⟩,
        hz', by omega⟩, by omega⟩
      intro i hi
      rw [Function.update_of_ne (by omega)]
      exact htail i hi
    · intro v mem' pos' hpost
      rcases hpost with ⟨he, hlo, hhi, hf, hzero, hlist⟩
      change v = heap + 1 + (M + 1 - 1) at he
      change (∀ x < heap + 1, mem' x = Function.update mem heap ((mem a * k + c) % base h) x) at hf
      have hvword : v < 2 ^ w := by omega
      refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
      · refine ⟨by change v = heap + (M + 1); omega, ?_⟩
        change heap ≤ v ∧ v ≤ heap + (M + 1) ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' v ∧ ListAt mem' heap (digits h (M + 1) (unsignedVal mem a h (M + 1) * k + c))
        refine ⟨by omega, by omega, ?_, hzero, ?_⟩
        · intro x hx
          rw [hf x (by omega), Function.update_of_ne (by omega)]
        · rw [digits_unsigned_scale, listAt_cons]
          refine ⟨by rw [hf heap (by omega), Function.update_self], ?_⟩
          have ht : unsignedVal (Function.update mem heap ((mem a * k + c) % base h)) (a + 1) h M =
              unsignedVal mem (a + 1) h M := by
            apply unsignedVal_congr
            intro i hi
            exact Function.update_of_ne (by omega) _ _
          change ListAt mem' (heap + 1) (digits h (M + 1 - 1)
            (unsignedVal (Function.update mem heap ((mem a * k + c) % base h)) (a + 1) h (M + 1 - 1) * k +
              (mem a * k + c) / base h)) at hlist
          simpa only [Nat.add_sub_cancel, ht] using hlist
      · simp only [scaleCarryContract, Contract.below, heapContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
          Expr.size_load, argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.Num
