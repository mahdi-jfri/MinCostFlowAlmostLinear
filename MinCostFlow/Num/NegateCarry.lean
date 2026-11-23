module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Complementing limbs with carry

Two's-complement negation complements every limb and adds one. This file verifies the
limb routine with an incoming carry of zero or one. Each step stores a remainder and
passes the quotient to the next step. Overflow is discarded at the end of the block.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Complementing a valid block and adding a carry splits at the low limb. -/
theorem digits_complement (mem : ℕ → ℕ) (a h L c : ℕ)
    (hv : Valid mem a h (L + 1)) :
    digits h (L + 1) (capacity h (L + 1) - 1 - unsignedVal mem a h (L + 1) + c) =
      (base h - 1 - mem a + c) % base h ::
        digits h L (capacity h L - 1 - unsignedVal mem (a + 1) h L +
          (base h - 1 - mem a + c) / base h) := by
  have hh := (valid_succ.mp hv).1
  have ht := unsignedVal_lt (valid_succ.mp hv).2
  have hlo : base h - 1 - mem a + mem a + 1 = base h := by omega
  have hhi : capacity h L - 1 - unsignedVal mem (a + 1) h L +
      unsignedVal mem (a + 1) h L + 1 = capacity h L := by omega
  have he : (base h - 1 - mem a) +
      base h * (capacity h L - 1 - unsignedVal mem (a + 1) h L) +
      unsignedVal mem a h (L + 1) + 1 = capacity h (L + 1) := by
    rw [unsignedVal, capacity_succ]
    nlinarith
  have hd : capacity h (L + 1) - 1 - unsignedVal mem a h (L + 1) + c =
      (base h - 1 - mem a + c) +
        base h * (capacity h L - 1 - unsignedVal mem (a + 1) h L) := by omega
  rw [hd, digits, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (base_pos h)]
  congr 2
  omega

/-- Arguments `[a, L, carry, heap]`. Register 4 holds the complemented limb plus carry. -/
def negateCarryBody (b h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 3))
    (.assign 4 (.bin .add
       (.bin .sub (.bin .sub (.const (base h)) (.const 1)) (.load (.reg 0))) (.reg 2)) ;;
     .store (.reg 3) (.bin .mod (.reg 4) (.const (base h))) ;;
     .call 5 b [.bin .add (.reg 0) (.const 1), .bin .sub (.reg 1) (.const 1),
       .bin .div (.reg 4) (.const (base h)), .bin .add (.reg 3) (.const 1)] ;;
     .ret (.reg 5))

/-- The recursive complement-and-carry module. -/
def negateCarryModule (b h : ℕ) : List Stmt := [negateCarryBody b h]

/-- Complement a valid source and add the incoming carry, modulo the block capacity. -/
def negateCarryContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L c heap, args = [a, L, c, heap] ∧
      a + L ≤ heap ∧ c ≤ 1 ∧ Valid mem a h L)
    (fun args mem mem' => ListAt mem' (heapArg args)
      (digits h (args.getD 1 0)
        (capacity h (args.getD 1 0) - 1 -
          unsignedVal mem (args.getD 0 0) h (args.getD 1 0) + args.getD 2 0)))
    (fun args _ => 36 * args.getD 1 0 + 6) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- The complement routine contains no random statement. -/
theorem negateCarryBody_noRand (b h : ℕ) : (negateCarryBody b h).NoRand := by
  simp [negateCarryBody, Stmt.NoRand]

/-- Complementing with carry meets its heap contract in at most `36 * L + 6` steps. -/
theorem negateCarry_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (negateCarryModule b h)) :
    MeetsContract w p b (negateCarryContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a, L, c, heap, rfl, ha, hc, hv⟩, hz, hbound⟩
  change L = k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  apply runs_start_le
  unfold negateCarryBody
  wram_step
  · have hzero : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨rfl, ?_⟩
      change heap ≤ heap ∧ heap ≤ heap + 0 ∧
        (∀ x < heap, mem x = mem x) ∧ ZeroFrom mem heap ∧ ListAt mem heap []
      exact ⟨le_rfl, le_rfl, fun _ _ => rfl, hz, listAt_nil _ _⟩
    · simp only [negateCarryContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hnonzero : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
    obtain ⟨hhead, htail⟩ := valid_succ.mp hv
    have hsumle : base h - 1 - mem a + c ≤ base h := by omega
    have hsum : base h - 1 - mem a + c < 2 ^ w := by omega
    have hcarry : (base h - 1 - mem a + c) / base h ≤ 1 :=
      Nat.div_le_of_le_mul (by omega)
    have hcarryword : (base h - 1 - mem a + c) / base h < 2 ^ w := by omega
    refine runs_seq_assign_le (v := base h - 1 - mem a + c) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    have hz' := hz.update_head ((base h - 1 - mem a + c) % base h)
    refine runs_seq_call_le ih (by eval_expr) ?_ ?_ ?_
    · wram_words
    · change ((∃ a' L' c' heap',
          [a + 1, M + 1 - 1, (base h - 1 - mem a + c) / base h, heap + 1] =
            [a', L', c', heap'] ∧ a' + L' ≤ heap' ∧ c' ≤ 1 ∧
          Valid (Function.update mem heap ((base h - 1 - mem a + c) % base h)) a' h L') ∧
          ZeroFrom (Function.update mem heap ((base h - 1 - mem a + c) % base h)) (heap + 1) ∧
          heap + 1 + (M + 1 - 1) < 2 ^ w) ∧ M + 1 - 1 < M + 1
      refine ⟨⟨⟨a + 1, M, _, heap + 1, by simp, by omega, hcarry, ?_⟩, hz', by omega⟩, by omega⟩
      intro i hi
      rw [Function.update_of_ne (by omega)]
      exact htail i hi
    · intro v mem' pos' hpost
      rcases hpost with ⟨hvexact, hvlo, hvhi, hf, hzero, hlist⟩
      change v = heap + 1 + (M + 1 - 1) at hvexact
      change (∀ x < heap + 1,
        mem' x = Function.update mem heap ((base h - 1 - mem a + c) % base h) x) at hf
      have hvword : v < 2 ^ w := by omega
      refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
      · refine ⟨by change v = heap + (M + 1); omega, ?_⟩
        change heap ≤ v ∧ v ≤ heap + (M + 1) ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' v ∧ ListAt mem' heap
            (digits h (M + 1) (capacity h (M + 1) - 1 - unsignedVal mem a h (M + 1) + c))
        refine ⟨by omega, by omega, ?_, hzero, ?_⟩
        · intro x hx
          rw [hf x (by omega), Function.update_of_ne (by omega)]
        · rw [digits_complement mem a h M c hv, listAt_cons]
          refine ⟨by rw [hf heap (by omega), Function.update_self], ?_⟩
          have he : unsignedVal (Function.update mem heap ((base h - 1 - mem a + c) % base h))
              (a + 1) h M = unsignedVal mem (a + 1) h M := by
            apply unsignedVal_congr
            intro i hi
            exact Function.update_of_ne (by omega) _ _
          change ListAt mem' (heap + 1)
            (digits h (M + 1 - 1) (capacity h (M + 1 - 1) - 1 -
              unsignedVal (Function.update mem heap ((base h - 1 - mem a + c) % base h))
                (a + 1) h (M + 1 - 1) + (base h - 1 - mem a + c) / base h)) at hlist
          simpa only [Nat.add_sub_cancel, he] using hlist
      · simp only [negateCarryContract, Contract.below, heapContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
          Expr.size_load, argsSize_cons, argsSize_nil]
        omega

/-- Initial carry one gives wrapped signed negation. -/
theorem negateCarry_value_one {mem mem' : ℕ → ℕ} {a heap h L : ℕ}
    (hv : Valid mem a h L)
    (hx : ListAt mem' heap
      (digits h L (capacity h L - 1 - unsignedVal mem a h L + 1))) :
    Valid mem' heap h L ∧ intVal mem' heap h L = wrap h L (-intVal mem a h L) := by
  have hu := unsignedVal_lt hv
  have he : capacity h L - 1 - unsignedVal mem a h L + 1 =
      capacity h L - unsignedVal mem a h L := by omega
  have hout := unsignedVal_listAt (h := h) hx
  rw [digits_length, listVal_digits, he] at hout
  refine ⟨by simpa using valid_listAt hx (digits_lt h L _), ?_⟩
  simp only [intVal, wrap, residue_signedVal_neg hu, hout]

end MinCostFlow.Num
