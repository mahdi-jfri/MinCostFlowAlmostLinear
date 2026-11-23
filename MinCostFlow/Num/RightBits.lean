module

public import MinCostFlow.Num.Encoding
import MinCostFlow.Num.RightBitsFacts
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Right shifts within limbs

The input has `L+1` limbs and the output has `L`. The extra source limb provides the
high bits of the last output limb. A positive divisor of the base specifies the bit
shift. Every output limb uses just its current source limb and the next one, so the
routine scans forward and allocates only its result. Its cost is `36*L + 6`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L, divisor, heap]`; the source contains `L+1` valid limbs. -/
def rightBitsBody (b h : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 3))
    (.store (.reg 3)
      (.bin .add (.bin .div (.load (.reg 0)) (.reg 2))
        (.bin .mul (.bin .div (.const (base h)) (.reg 2))
          (.bin .mod (.load (.bin .add (.reg 0) (.const 1))) (.reg 2)))) ;;
     .call 4 b [.bin .add (.reg 0) (.const 1), .bin .sub (.reg 1) (.const 1), .reg 2,
       .bin .add (.reg 3) (.const 1)] ;; .ret (.reg 4))

/-- The adjacent-limb right-shift helper. -/
def rightBitsModule (b h : ℕ) : List Stmt := [rightBitsBody b h]

/-- Divide an unsigned source of `L+1` limbs by a factor of the base and keep `L` limbs. -/
def rightBitsContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L t heap, args = [a, L, t, heap] ∧
      a + (L + 1) ≤ heap ∧ 0 < t ∧ t ∣ base h ∧ Valid mem a h (L + 1))
    (fun args mem mem' => ListAt mem' (heapArg args)
      (digits h (args.getD 1 0)
        (unsignedVal mem (args.getD 0 0) h (args.getD 1 0 + 1) / args.getD 2 0)))
    (fun args _ => 36 * args.getD 1 0 + 6) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- The adjacent-limb shift uses no random bits. -/
theorem rightBitsBody_noRand (b h : ℕ) : (rightBitsBody b h).NoRand := by
  simp [rightBitsBody, Stmt.NoRand]

/-- The right-shift helper meets its heap contract in linear time. -/
theorem rightBits_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (rightBitsModule b h)) :
    MeetsContract w p b (rightBitsContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 1 0) hp.head
  intro k ih args mem pos ω hwords hpre hk
  rcases hpre with ⟨⟨a, L, t, heap, rfl, ha, ht, hd, hv⟩, hz, hbound⟩
  change L = k at hk
  subst k
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  apply runs_start_le
  unfold rightBitsBody
  wram_step
  · have hzero : L = 0 := by simpa [startState] using hcond
    subst L
    refine runs_ret_le (by eval_expr) ?_ ?_
    · refine ⟨rfl, ?_⟩
      change heap ≤ heap ∧ heap ≤ heap + 0 ∧ (∀ x < heap, mem x = mem x) ∧
        ZeroFrom mem heap ∧ ListAt mem heap []
      exact ⟨le_rfl, le_rfl, fun _ _ => rfl, hz, listAt_nil _ _⟩
    · simp only [rightBitsContract, heapContract, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const]
      omega
  · have hn : L ≠ 0 := by simpa [startState] using hcond
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    obtain ⟨hhead, htail⟩ := valid_succ.mp hv
    have htw : t < 2 ^ w := hwords t (by simp)
    have hxw : mem a < 2 ^ w := lt_trans hhead hb
    have hnextw : mem (a + 1) < 2 ^ w := lt_trans (valid_succ.mp htail).1 hb
    have hqnonneg : 0 ≤ mem a / t := Nat.zero_le _
    have hlow := (div_limb_pair (base_pos h) ht hd hhead (V := mem (a + 1))).2.2
    have hprod : (base h / t) * (mem (a + 1) % t) < 2 ^ w := by omega
    have hquot : mem a / t < 2 ^ w := by omega
    have hfactor : base h / t < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hb
    have hrem : mem (a + 1) % t < 2 ^ w :=
      lt_trans (Nat.mod_lt _ ht) (hwords t (by simp))
    have hsum : mem a / t + (base h / t) * (mem (a + 1) % t) < 2 ^ w := lt_trans hlow hb
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    have hz' := hz.update_head (mem a / t + (base h / t) * (mem (a + 1) % t))
    refine runs_seq_call_le ih (by eval_expr) (by wram_words) ?_ ?_
    · change ((∃ a' L' t' heap', [a + 1, M + 1 - 1, t, heap + 1] = [a', L', t', heap'] ∧
          a' + (L' + 1) ≤ heap' ∧ 0 < t' ∧ t' ∣ base h ∧
          Valid (Function.update mem heap (mem a / t + (base h / t) * (mem (a + 1) % t))) a' h (L' + 1)) ∧
        ZeroFrom (Function.update mem heap (mem a / t + (base h / t) * (mem (a + 1) % t))) (heap + 1) ∧
        heap + 1 + (M + 1 - 1) < 2 ^ w) ∧ M + 1 - 1 < M + 1
      refine ⟨⟨⟨a + 1, M, t, heap + 1, by simp, by omega, ht, hd, ?_⟩,
        hz', by omega⟩, by omega⟩
      intro i hi
      rw [Function.update_of_ne (by omega)]
      exact htail i hi
    · intro v mem' pos' hpost
      rcases hpost with ⟨he, hlo, hhi, hf, hzero, hl⟩
      change v = heap + 1 + (M + 1 - 1) at he
      change (∀ x < heap + 1, mem' x = Function.update mem heap
        (mem a / t + (base h / t) * (mem (a + 1) % t)) x) at hf
      have hvw : v < 2 ^ w := by omega
      refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
      · refine ⟨by change v = heap + (M + 1); omega, ?_⟩
        change heap ≤ v ∧ v ≤ heap + (M + 1) ∧ (∀ x < heap, mem' x = mem x) ∧
          ZeroFrom mem' v ∧ ListAt mem' heap (digits h (M + 1) (unsignedVal mem a h (M + 2) / t))
        refine ⟨by omega, by omega, ?_, hzero, ?_⟩
        · intro x hx
          rw [hf x (by omega), Function.update_of_ne (by omega)]
        · rw [digits_unsigned_right_bits ht hd hv, listAt_cons]
          refine ⟨by rw [hf heap (by omega), Function.update_self], ?_⟩
          have hsame : unsignedVal
              (Function.update mem heap (mem a / t + (base h / t) * (mem (a + 1) % t)))
              (a + 1) h (M + 1) = unsignedVal mem (a + 1) h (M + 1) := by
            apply unsignedVal_congr
            intro i hi
            exact Function.update_of_ne (by omega) _ _
          change ListAt mem' (heap + 1) (digits h (M + 1 - 1)
            (unsignedVal (Function.update mem heap (mem a / t + (base h / t) * (mem (a + 1) % t)))
              (a + 1) h (M + 1 - 1 + 1) / t)) at hl
          simpa only [Nat.add_sub_cancel, hsame] using hl
      · simp only [rightBitsContract, Contract.below, heapContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
          argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.Num
