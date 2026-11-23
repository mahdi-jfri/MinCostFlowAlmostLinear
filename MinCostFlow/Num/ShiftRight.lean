module

public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.ExtendCopy
public import MinCostFlow.Num.RightBits
import MinCostFlow.Num.ShiftRightFacts
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Arithmetic right shifts by arbitrary bit counts

Drop the whole shifted limbs, then copy the remaining limbs into a scratch block and
fill its high cells with the sign limb. One extra sign limb makes division by the
remaining-bit factor local to adjacent limbs. The result starts at `heap+L+1`, after
an `L+1`-limb scratch block. Its value is the signed floor quotient by `2^bits`.
The cost is at most `66*L + 106`, independently of the bit count.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L, bits, heap]`. Drop is `L-(L-bits/h)`, which is bounded by `L`. -/
def shiftRightBody (neg extend bits h : ℕ) : Stmt :=
  .call 4 neg [.reg 0, .reg 1] ;;
  .assign 5 (.bin .div (.reg 2) (.const h)) ;;
  .assign 6 (.bin .sub (.reg 1) (.bin .sub (.reg 1) (.reg 5))) ;;
  .assign 7 (.bin .shiftLeft (.const 1) (.bin .mod (.reg 2) (.const h))) ;;
  .assign 8 (.bin .mul (.bin .sub (.const (base h)) (.const 1)) (.reg 4)) ;;
  .call 9 extend [.bin .add (.reg 0) (.reg 6), .bin .sub (.reg 1) (.reg 6),
    .bin .add (.reg 1) (.const 1), .reg 8, .reg 3] ;;
  .call 10 bits [.reg 3, .reg 1, .reg 7, .reg 9] ;;
  .ret (.reg 10)

/-- Arithmetic right shift, sign test, sign-extension copy, and remaining-bit helper. -/
def shiftRightModule (b h : ℕ) : List Stmt :=
  [shiftRightBody (b + 1) (b + 2) (b + 3) h, isNegativeBody h,
    extendCopyBody (b + 2), rightBitsBody (b + 3) h]

/-- Allocate scratch and result blocks and compute the signed floor quotient. -/
def shiftRightContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L s heap, args = [a, L, s, heap] ∧ a + L ≤ heap ∧ Valid mem a h L)
    (fun args mem mem' =>
      Valid mem' (heapArg args + args.getD 1 0 + 1) h (args.getD 1 0) ∧
      intVal mem' (heapArg args + args.getD 1 0 + 1) h (args.getD 1 0) =
        intVal mem (args.getD 0 0) h (args.getD 1 0) /
          (2 : ℤ) ^ args.getD 2 0)
    (fun args _ => 66 * args.getD 1 0 + 106) (fun args _ => 2 * args.getD 1 0 + 1)
  { C with post := fun args mem v mem' =>
      v = heapArg args + (2 * args.getD 1 0 + 1) ∧ C.post args mem v mem' }

/-- Arithmetic right shifting is deterministic. -/
theorem shiftRightModule_noRand (b h : ℕ) : ∀ s ∈ shiftRightModule b h, s.NoRand := by
  simp only [shiftRightModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp [shiftRightBody, Stmt.NoRand], isNegativeBody_noRand _,
    extendCopyBody_noRand _, rightBitsBody_noRand _ _⟩

/-- Arithmetic right shifting meets its heap contract with a linear cost bound. -/
theorem shiftRight_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (shiftRightModule b h)) :
    MeetsContract w p b (shiftRightContract w h) := by
  have hneg : p.HasAt (b + 1) (isNegativeModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [shiftRightModule, isNegativeModule] using hp 1 (by simp [shiftRightModule])
  have hext : p.HasAt (b + 2) (extendCopyModule (b + 2)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [shiftRightModule, extendCopyModule] using hp 2 (by simp [shiftRightModule])
  have hbits : p.HasAt (b + 3) (rightBitsModule (b + 3) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [shiftRightModule, rightBitsModule] using hp 3 (by simp [shiftRightModule])
  have hn := isNegative_meetsContract hh hw hb hneg
  have he := extendCopy_meetsContract (h := h) hw hext
  have hr := rightBits_meetsContract hw hb hbits
  have hhw : h < 2 ^ w := lt_trans (Nat.lt_two_pow_self (n := h)) hb
  have hentry : p.procs[b]? = some (shiftRightBody (b + 1) (b + 2) (b + 3) h) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, L, s, heap, rfl, ha, hv⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + (2 * L + 1) < 2 ^ w at hbound
  have haw : a < 2 ^ w := hwords a (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hsw : s < 2 ^ w := hwords s (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have hqnonneg : 0 ≤ s / h := Nat.zero_le _
  have hqw : s / h < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hsw
  have hdrople : L - (L - s / h) ≤ L := Nat.sub_le _ _
  have htpos : 0 < 2 ^ (s % h) := pow_pos (by decide) _
  have htbase : 2 ^ (s % h) < base h := Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ hh)
  have htw : 2 ^ (s % h) < 2 ^ w := lt_trans htbase hb
  have hshiftw : 1 <<< (s % h) < 2 ^ w := by simpa only [Nat.one_shiftLeft] using htw
  have htdvd : 2 ^ (s % h) ∣ base h := Nat.pow_dvd_pow 2 (Nat.le_of_lt (Nat.mod_lt _ hh))
  apply runs_start_le
  unfold shiftRightBody
  refine runs_seq_call_le hn (vs := [a, L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a, L, rfl, by omega, hv⟩
  · intro sign mem' pos' hpost
    rcases hpost with ⟨hmem, hsign⟩
    subst mem'
    change sign = if intVal mem a h L < 0 then 1 else 0 at hsign
    have hfill : (base h - 1) * sign = if intVal mem a h L < 0 then base h - 1 else 0 := by
      rw [hsign]
      split_ifs <;> simp
    have hfillbase : (base h - 1) * sign < base h := by
      rw [hfill]
      split_ifs <;> have hbpos := base_pos h <;> omega
    have hfillw : (base h - 1) * sign < 2 ^ w := lt_trans hfillbase hb
    refine runs_seq_assign_le (v := s / h) (by eval_expr) ?_
    refine runs_seq_assign_le (v := L - (L - s / h)) (by eval_expr) ?_
    refine runs_seq_assign_le (v := 2 ^ (s % h)) ?_ ?_
    · rw [← Nat.one_shiftLeft]
      eval_expr
    · refine runs_seq_assign_le (v := (base h - 1) * sign) (by eval_expr) ?_
      have hsrc : Valid mem (a + (L - (L - s / h))) h (L - (L - (L - s / h))) := by
        intro i hi
        simpa only [Nat.add_assoc] using hv (L - (L - s / h) + i) (by omega)
      refine runs_seq_call_le he
        (vs := [a + (L - (L - s / h)), L - (L - (L - s / h)), L + 1, (base h - 1) * sign, heap])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨_, _, _, _, _, rfl, by omega, by omega, hfillbase, hsrc⟩, hz,
          by change heap + (L + 1) < 2 ^ w; omega⟩
      · intro v₁ mem₁ pos₁ hpost₁
        rcases hpost₁ with ⟨hv₁, hlo₁, hhi₁, hf₁, hz₁, hl₁⟩
        change v₁ = heap + (L + 1) at hv₁
        change (∀ x < heap, mem₁ x = mem x) at hf₁
        change ListAt mem₁ heap (extendedLimbs mem (a + (L - (L - s / h)))
          ((base h - 1) * sign) (L - (L - (L - s / h))) (L + 1)) at hl₁
        have hvalid := valid_listAt hl₁ (extendedLimbs_lt hsrc hfillbase)
        rw [extendedLimbs_length] at hvalid
        have hv₁w : v₁ < 2 ^ w := by omega
        refine runs_seq_call_le hr (vs := [heap, L, 2 ^ (s % h), v₁]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨heap, L, 2 ^ (s % h), v₁, rfl, by omega, htpos, htdvd, hvalid⟩, hz₁,
            by change v₁ + L < 2 ^ w; omega⟩
        · intro v₂ mem₂ pos₂ hpost₂
          rcases hpost₂ with ⟨hv₂, hlo₂, hhi₂, hf₂, hz₂, hl₂⟩
          change v₂ = v₁ + L at hv₂
          change (∀ x < v₁, mem₂ x = mem₁ x) at hf₂
          change ListAt mem₂ v₁ (digits h L (unsignedVal mem₁ heap h (L + 1) / 2 ^ (s % h))) at hl₂
          have hvalidout := valid_listAt hl₂ (digits_lt h L _)
          rw [digits_length] at hvalidout
          have hout := unsignedVal_listAt (h := h) hl₂
          rw [digits_length, listVal_digits] at hout
          have hvalue : intVal mem₂ v₁ h L =
              wrap h L ((unsignedVal mem₁ heap h (L + 1) : ℤ) / (2 : ℤ) ^ (s % h)) := by
            rw [intVal, hout, ← wrap_natCast, Int.natCast_ediv]
            simp only [Nat.cast_pow, Nat.cast_ofNat]
          have hv₂w : v₂ < 2 ^ w := by omega
          refine runs_ret_le (v := v₂) (by eval_expr) ?_ ?_
          · refine ⟨by change v₂ = heap + (2 * L + 1); omega, ?_⟩
            change heap ≤ v₂ ∧ v₂ ≤ heap + (2 * L + 1) ∧ (∀ x < heap, mem₂ x = mem x) ∧
              ZeroFrom mem₂ v₂ ∧ Valid mem₂ (heap + L + 1) h L ∧
                intVal mem₂ (heap + L + 1) h L = intVal mem a h L / (2 : ℤ) ^ s
            refine ⟨by omega, by omega, ?_, hz₂, ?_, ?_⟩
            · intro x hx
              rw [hf₂ x (by omega), hf₁ x hx]
            · simpa only [hv₁, Nat.add_assoc] using hvalidout
            · rw [show heap + L + 1 = v₁ by omega, hvalue]
              rw [hfill] at hl₁
              have heq := scratch_right_shift_value hh hv hl₁
              rw [wrap_of_fits (fits_ediv (intVal_fits hv) (pow_pos (by decide) s))] at heq
              exact heq
          · simp only [shiftRightContract, isNegativeContract, extendCopyContract,
              rightBitsContract, heapContract, List.getD_cons_zero, List.getD_cons_succ,
              Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
            omega

end MinCostFlow.Num
