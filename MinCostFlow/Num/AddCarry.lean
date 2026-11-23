module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Limb addition with carry

At each step we add the low limbs and the incoming carry. Division by the base gives
the next carry and the remainder gives the output limb. The recursive call works on
the remaining limbs. All outputs are allocated in fresh heap memory, so the sources
are preserved. The final carry is dropped: overflow wraps modulo the block capacity.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Splitting the low limb of a sum leaves the sum of the tails and the new carry. -/
theorem digits_unsigned_add (mem : ℕ → ℕ) (a d h L c : ℕ) :
    digits h (L + 1) (unsignedVal mem a h (L + 1) + unsignedVal mem d h (L + 1) + c) =
      (mem a + mem d + c) % base h ::
        digits h L (unsignedVal mem (a + 1) h L + unsignedVal mem (d + 1) h L +
          (mem a + mem d + c) / base h) := by
  have he : unsignedVal mem a h (L + 1) + unsignedVal mem d h (L + 1) + c =
      (mem a + mem d + c) + base h *
        (unsignedVal mem (a + 1) h L + unsignedVal mem (d + 1) h L) := by
    simp only [unsignedVal]
    ring
  rw [he, digits, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (base_pos h)]
  congr 2
  omega

/-- Arguments `[a, d, L, carry, heap]`. Register 5 holds the sum of the low limbs. -/
def addCarryBody (b h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 4))
    (.assign 5 (.bin .add (.bin .add (.load (.reg 0)) (.load (.reg 1))) (.reg 3)) ;;
     .store (.reg 4) (.bin .mod (.reg 5) (.const (base h))) ;;
     .call 6 b [.bin .add (.reg 0) (.const 1), .bin .add (.reg 1) (.const 1),
       .bin .sub (.reg 2) (.const 1), .bin .div (.reg 5) (.const (base h)),
       .bin .add (.reg 4) (.const 1)] ;;
     .ret (.reg 6))

/-- A recursively linked addition module. -/
def addCarryModule (b h : ℕ) : List Stmt := [addCarryBody b h]

/-- Add two valid blocks and an incoming carry of zero or one.
The output is the low `L` limbs of the unsigned sum. -/
def addCarryContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L c heap, args = [a, d, L, c, heap] ∧
      a + L ≤ heap ∧ d + L ≤ heap ∧ c ≤ 1 ∧ Valid mem a h L ∧ Valid mem d h L)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (digits h (args.getD 2 0)
        (unsignedVal mem (args.getD 0 0) h (args.getD 2 0) +
          unsignedVal mem (args.getD 1 0) h (args.getD 2 0) + args.getD 3 0)))
    (fun args _ => 38 * args.getD 2 0 + 6) (fun args _ => args.getD 2 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 2 0 ∧ C.post args mem v mem' }

/-- Addition contains no random statement. -/
theorem addCarryBody_noRand (b h : ℕ) : (addCarryBody b h).NoRand := by
  simp [addCarryBody, Stmt.NoRand]

/-- The carry stays at most one when adding two limbs. -/
theorem add_limb_carry_le_one {h x y c : ℕ}
    (hx : x < base h) (hy : y < base h) (hc : c ≤ 1) :
    (x + y + c) / base h ≤ 1 := by
  have hh : x + y + c < 2 * base h := by omega
  have ht := (Nat.div_lt_iff_lt_mul (base_pos h)).mpr hh
  omega

/-- Limb addition meets its heap contract with cost at most `38 * L + 6`. -/
theorem addCarry_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
    (hp : p.HasAt b (addCarryModule b h)) :
    MeetsContract w p b (addCarryContract w h) := by
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb := base_lt_word hw
  have hb1 : 1 < base h := Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)
  apply meetsContract_of_rec (fun args _ => args.getD 2 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a, d, L, c, heap, rfl, ha, hd, hc, hva, hvd⟩, hz, hbound⟩
  change L = k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  have hcword : c < 2 ^ w := lt_of_le_of_lt hc hw1
  apply runs_start_le
  unfold addCarryBody
  wram_step
  · have hzero : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨rfl, ?_⟩
      change heap ≤ heap ∧ heap ≤ heap + 0 ∧
        (∀ x < heap, mem x = mem x) ∧ ZeroFrom mem heap ∧ ListAt mem heap []
      exact ⟨le_rfl, le_rfl, fun _ _ => rfl, hz, listAt_nil _ _⟩
    · simp only [addCarryContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hnonzero : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
    obtain ⟨hxa, hta⟩ := valid_succ.mp hva
    obtain ⟨hxd, htd⟩ := valid_succ.mp hvd
    have hsum : mem a + mem d + c < 2 ^ w :=
      limb_add_lt_word hw hxa hxd (lt_of_le_of_lt hc hb1)
    have hpartial : mem a + mem d < 2 ^ w := by omega
    have hcarry := add_limb_carry_le_one hxa hxd hc
    have hcarryword : (mem a + mem d + c) / base h < 2 ^ w := by omega
    refine runs_seq_assign_le (v := mem a + mem d + c) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    have hz' := hz.update_head ((mem a + mem d + c) % base h)
    refine runs_seq_call_le ih (by eval_expr) ?_ ?_ ?_
    · wram_words
    · change ((∃ a' d' L' c' heap',
          [a + 1, d + 1, M + 1 - 1, (mem a + mem d + c) / base h, heap + 1] =
            [a', d', L', c', heap'] ∧
          a' + L' ≤ heap' ∧ d' + L' ≤ heap' ∧ c' ≤ 1 ∧
          Valid (Function.update mem heap ((mem a + mem d + c) % base h)) a' h L' ∧
          Valid (Function.update mem heap ((mem a + mem d + c) % base h)) d' h L') ∧
          ZeroFrom (Function.update mem heap ((mem a + mem d + c) % base h)) (heap + 1) ∧
          heap + 1 + (M + 1 - 1) < 2 ^ w) ∧ M + 1 - 1 < M + 1
      refine ⟨⟨⟨a + 1, d + 1, M, _, heap + 1, by simp, by omega, by omega,
        hcarry, ?_, ?_⟩, hz', by omega⟩, by omega⟩
      · intro i hi
        rw [Function.update_of_ne (by omega)]
        exact hta i hi
      · intro i hi
        rw [Function.update_of_ne (by omega)]
        exact htd i hi
    · intro v mem' pos' hpost
      rcases hpost with ⟨hvexact, hvlo, hvhi, hf, hzero, hlist⟩
      change v = heap + 1 + (M + 1 - 1) at hvexact
      change (∀ x < heap + 1,
        mem' x = Function.update mem heap ((mem a + mem d + c) % base h) x) at hf
      have hvword : v < 2 ^ w := by omega
      refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
      · refine ⟨by change v = heap + (M + 1); omega, ?_⟩
        change heap ≤ v ∧ v ≤ heap + (M + 1) ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' v ∧ ListAt mem' heap
            (digits h (M + 1) (unsignedVal mem a h (M + 1) + unsignedVal mem d h (M + 1) + c))
        refine ⟨by omega, by omega, ?_, hzero, ?_⟩
        · intro x hx
          rw [hf x (by omega), Function.update_of_ne (by omega)]
        · rw [digits_unsigned_add, listAt_cons]
          refine ⟨by rw [hf heap (by omega), Function.update_self], ?_⟩
          have hea : unsignedVal (Function.update mem heap ((mem a + mem d + c) % base h))
              (a + 1) h M = unsignedVal mem (a + 1) h M := by
            apply unsignedVal_congr
            intro i hi
            exact Function.update_of_ne (by omega) _ _
          have hed : unsignedVal (Function.update mem heap ((mem a + mem d + c) % base h))
              (d + 1) h M = unsignedVal mem (d + 1) h M := by
            apply unsignedVal_congr
            intro i hi
            exact Function.update_of_ne (by omega) _ _
          change ListAt mem' (heap + 1)
            (digits h (M + 1 - 1)
              (unsignedVal (Function.update mem heap ((mem a + mem d + c) % base h)) (a + 1) h
                (M + 1 - 1) + unsignedVal (Function.update mem heap ((mem a + mem d + c) % base h))
                (d + 1) h (M + 1 - 1) + (mem a + mem d + c) / base h)) at hlist
          simpa only [Nat.add_sub_cancel, hea, hed] using hlist
      · simp only [addCarryContract, Contract.below, heapContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
          Expr.size_load, argsSize_cons, argsSize_nil]
        omega

/-- The stored output is the wrapped signed sum, including the incoming carry. -/
theorem addCarry_value {mem mem' : ℕ → ℕ} {a d heap h L c : ℕ}
    (hx : ListAt mem' heap (digits h L
      (unsignedVal mem a h L + unsignedVal mem d h L + c))) :
    Valid mem' heap h L ∧ intVal mem' heap h L =
      wrap h L (intVal mem a h L + intVal mem d h L + (c : ℤ)) := by
  have hv := valid_listAt hx (digits_lt h L _)
  have hu := unsignedVal_listAt (h := h) hx
  rw [digits_length, listVal_digits] at hu
  refine ⟨by simpa using hv, ?_⟩
  simp only [intVal, wrap, residue_signedVal_add, hu]

/-- If the signed sum fits, addition returns that exact integer. -/
theorem addCarry_value_of_fits {mem mem' : ℕ → ℕ} {a d heap h L c : ℕ}
    (hx : ListAt mem' heap (digits h L
      (unsignedVal mem a h L + unsignedVal mem d h L + c)))
    (hfit : Fits h L (intVal mem a h L + intVal mem d h L + (c : ℤ))) :
    intVal mem' heap h L = intVal mem a h L + intVal mem d h L + (c : ℤ) := by
  rw [(addCarry_value hx).2, wrap_of_fits hfit]

end MinCostFlow.Num
