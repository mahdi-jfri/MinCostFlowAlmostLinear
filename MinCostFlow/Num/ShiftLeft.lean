module

public import MinCostFlow.Num.ScaleCarry
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Left shifts by arbitrary bit counts

Divide the bit count by the limb width. Whole shifted limbs are already zero in fresh
heap memory. The remaining bits are a one-limb scaling of the source prefix that can
still contribute. If every source limb is shifted out, allocation alone gives zero.
The result wraps modulo capacity and costs at most `35*L + 35`, independently of the
bit count.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L, bits, heap]`. Registers 4 and 5 hold the whole-limb count and factor. -/
def shiftLeftBody (scale h : ℕ) : Stmt :=
  .assign 4 (.bin .div (.reg 2) (.const h)) ;;
  .assign 5 (.bin .shiftLeft (.const 1) (.bin .mod (.reg 2) (.const h))) ;;
  .cond (.bin .lt (.reg 4) (.reg 1))
    (.call 6 scale [.reg 0, .bin .sub (.reg 1) (.reg 4), .reg 5, .const 0,
      .bin .add (.reg 3) (.reg 4)] ;; .ret (.reg 6))
    (.ret (.bin .add (.reg 3) (.reg 1)))

/-- A left-shift entry and its one-limb scaling helper. -/
def shiftLeftModule (b h : ℕ) : List Stmt :=
  [shiftLeftBody (b + 1) h, scaleCarryBody (b + 1) h]

/-- Shift left, allocating exactly `L` limbs at the old heap pointer. -/
def shiftLeftContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L s heap, args = [a, L, s, heap] ∧
      a + L ≤ heap ∧ Valid mem a h L)
    (fun args mem mem' => Valid mem' (heapArg args) h (args.getD 1 0) ∧
      intVal mem' (heapArg args) h (args.getD 1 0) =
        wrap h (args.getD 1 0) (intVal mem (args.getD 0 0) h (args.getD 1 0) *
          (2 : ℤ) ^ args.getD 2 0))
    (fun args _ => 35 * args.getD 1 0 + 35) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- Both bodies of a left shift are deterministic. -/
theorem shiftLeftModule_noRand (b h : ℕ) : ∀ s ∈ shiftLeftModule b h, s.NoRand := by
  simp only [shiftLeftModule, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨by simp [shiftLeftBody, Stmt.NoRand], scaleCarryBody_noRand _ _⟩

private theorem wrap_large_shift (h L s : ℕ) (n : ℤ) (hs : h * L ≤ s) :
    wrap h L (n * (2 : ℤ) ^ s) = 0 := by
  have hd : (capacity h L : ℤ) ∣ (2 : ℤ) ^ s := by
    rw [capacity_eq_two_pow]
    exact_mod_cast Nat.pow_dvd_pow 2 hs
  have hm : (capacity h L : ℤ) ∣ n * (2 : ℤ) ^ s := dvd_mul_of_dvd_right hd n
  have he := Int.emod_eq_zero_of_dvd hm
  simp only [wrap, residue, he, Int.toNat_zero, signedVal_zero]

/-- Left shifts meet their heap contract with a cost linear in the block length. -/
theorem shiftLeft_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (shiftLeftModule b h)) :
    MeetsContract w p b (shiftLeftContract w h) := by
  have hscale : p.HasAt (b + 1) (scaleCarryModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [shiftLeftModule, scaleCarryModule] using hp 1 (by simp [shiftLeftModule])
  have hk := scaleCarry_meetsContract hw hscale
  have hentry : p.procs[b]? = some (shiftLeftBody (b + 1) h) := hp.head
  have hb := base_lt_word hw
  have hw1 : 1 < 2 ^ w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hhw : h < 2 ^ w := lt_trans (Nat.lt_two_pow_self (n := h)) hb
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, L, s, heap, rfl, ha, hv⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  have hsw : s < 2 ^ w := hwords s (by simp)
  have hqnonneg : 0 ≤ s / h := Nat.zero_le _
  have hqw : s / h < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hsw
  have hr : s % h < h := Nat.mod_lt _ hh
  have ht : 2 ^ (s % h) < base h := Nat.pow_lt_pow_right (by decide) hr
  have htw : 2 ^ (s % h) < 2 ^ w := lt_trans ht hb
  have hshiftw : 1 <<< (s % h) < 2 ^ w := by simpa only [Nat.one_shiftLeft] using htw
  have htp : 0 < 2 ^ (s % h) := pow_pos (by decide) _
  apply runs_start_le
  unfold shiftLeftBody
  refine runs_seq_assign_le (v := s / h) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 2 ^ (s % h)) ?_ ?_
  · rw [← Nat.one_shiftLeft]
    eval_expr
  · wram_step
    · have hq : s / h < L := by simpa [startState] using hcond
      refine runs_seq_call_le hk
        (vs := [a, L - s / h, 2 ^ (s % h), 0, heap + s / h]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨a, L - s / h, 2 ^ (s % h), 0, heap + s / h, rfl,
          by omega, ht, Nat.le_of_lt htp, fun i hi => hv i (by omega)⟩,
          hz.mono (by change heap ≤ heap + s / h; omega),
          by change heap + s / h + (L - s / h) < 2 ^ w; omega⟩
      · intro v mem' pos' hpost
        rcases hpost with ⟨he, hlo, hhi, hf, hzero, hl⟩
        change v = heap + s / h + (L - s / h) at he
        clear hlo hhi
        have hvheap : v = heap + L := by omega
        change (∀ x < heap + s / h, mem' x = mem x) at hf
        change ListAt mem' (heap + s / h)
          (digits h (L - s / h) (unsignedVal mem a h (L - s / h) * 2 ^ (s % h) + 0)) at hl
        simp only [Nat.add_zero] at hl
        have hvword : v < 2 ^ w := by omega
        have hlow : ∀ i < s / h, mem' (heap + i) = 0 := by
          intro i hi
          rw [hf (heap + i) (by omega), hz (heap + i) (by omega)]
        have hvalidtail := valid_listAt hl (digits_lt h (L - s / h) _)
        rw [digits_length] at hvalidtail
        have hcalc : unsignedVal mem' heap h L =
            (unsignedVal mem a h L * 2 ^ s) % capacity h L := by
          rw [two_pow_shift_split h s]
          exact unsignedVal_left_shift hv (Nat.le_of_lt hq) hlow hl
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · refine ⟨by change v = heap + L; omega, ?_⟩
          change heap ≤ v ∧ v ≤ heap + L ∧ (∀ x < heap, mem' x = mem x) ∧
            ZeroFrom mem' v ∧ Valid mem' heap h L ∧
              intVal mem' heap h L = wrap h L (intVal mem a h L * (2 : ℤ) ^ s)
          refine ⟨by omega, by omega, fun x hx => hf x (by omega), hzero, ?_, ?_⟩
          · intro i hi
            by_cases hlowi : i < s / h
            · rw [hlow i hlowi]
              exact base_pos h
            · have hv' := hvalidtail (i - s / h) (by omega)
              simpa only [show heap + s / h + (i - s / h) = heap + i by omega] using hv'
          · rw [intVal, hcalc, signedVal_mul_mod]
            simp only [intVal, Int.natCast_pow, Nat.cast_ofNat]
        · simp only [shiftLeftContract, scaleCarryContract, heapContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_const,
            Expr.size_bin, argsSize_cons, argsSize_nil]
          omega
    · have hq : L ≤ s / h := by simpa [startState] using hcond
      have hs : h * L ≤ s := by
        have hm := Nat.mul_le_mul_left h hq
        have he := Nat.mod_add_div s h
        omega
      refine runs_ret_le (by eval_expr) ?_ ?_
      · refine ⟨rfl, ?_⟩
        change heap ≤ heap + L ∧ heap + L ≤ heap + L ∧ (∀ x < heap, mem x = mem x) ∧
          ZeroFrom mem (heap + L) ∧ Valid mem heap h L ∧
            intVal mem heap h L = wrap h L (intVal mem a h L * (2 : ℤ) ^ s)
        exact ⟨by omega, le_rfl, fun _ _ => rfl, hz.mono (by omega),
          zeroFrom_valid hz le_rfl, by rw [intVal_zeroFrom hz le_rfl, wrap_large_shift h L s _ hs]⟩
      · simp only [shiftLeftContract, heapContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_reg, Expr.size_const, Expr.size_bin]
        omega

/-- Left shifting is exact whenever its signed result fits the output block. -/
theorem shiftLeft_value_of_fits {w h a L s heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hp : (shiftLeftContract w h).post [a, L, s, heap] mem v mem')
    (hf : Fits h L (intVal mem a h L * (2 : ℤ) ^ s)) :
    intVal mem' heap h L = intVal mem a h L * (2 : ℤ) ^ s := by
  have he := hp.2.2.2.2.2.2
  change intVal mem' heap h L = wrap h L (intVal mem a h L * (2 : ℤ) ^ s) at he
  rw [he, wrap_of_fits hf]

end MinCostFlow.Num
