module

public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.ExtendCopy
public import MinCostFlow.Num.MulRows
import MinCostFlow.Num.MultiplyFacts
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Exact signed multiplication into twice as many limbs

Sign-extend both inputs from `L` to `2L` limbs, then apply schoolbook rows to a fresh
zero accumulator of `2L` limbs. Unsigned multiplication modulo the larger capacity
has the correct signed residue. The signed product fits that capacity, so the result
is exact. The two extended inputs use `4L` scratch cells and the result uses `2L`.
The cost is at most `152*L^2 + 190*L + 99`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, L, heap]`, with entries for sign, extension, and rows. -/
def multiplyBody (neg extend rows h : ℕ) : Stmt :=
  .call 4 neg [.reg 0, .reg 2] ;;
  .call 5 neg [.reg 1, .reg 2] ;;
  .assign 6 (.bin .mul (.bin .sub (.const (base h)) (.const 1)) (.reg 4)) ;;
  .assign 7 (.bin .mul (.bin .sub (.const (base h)) (.const 1)) (.reg 5)) ;;
  .call 8 extend [.reg 0, .reg 2, .bin .mul (.const 2) (.reg 2), .reg 6, .reg 3] ;;
  .call 9 extend [.reg 1, .reg 2, .bin .mul (.const 2) (.reg 2), .reg 7, .reg 8] ;;
  .call 10 rows [.reg 3, .reg 8, .bin .mul (.const 2) (.reg 2), .reg 9, .const 0] ;;
  .ret (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 2)))

/-- The exact multiplier and its four linked helpers. -/
def multiplyModule (b h : ℕ) : List Stmt :=
  [multiplyBody (b + 1) (b + 2) (b + 3) h, isNegativeBody h,
    extendCopyBody (b + 2), mulRowsBody (b + 3) (b + 4), mulAddBody (b + 4) h]

/-- Exact signed multiplication. Result starts at `heap+4L`; return is `heap+6L`. -/
def multiplyContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L heap, args = [a, d, L, heap] ∧ a + L ≤ heap ∧ d + L ≤ heap ∧
      Valid mem a h L ∧ Valid mem d h L)
    (fun args mem mem' => Valid mem' (heapArg args + 4 * args.getD 2 0) h (2 * args.getD 2 0) ∧
      intVal mem' (heapArg args + 4 * args.getD 2 0) h (2 * args.getD 2 0) =
        intVal mem (args.getD 0 0) h (args.getD 2 0) * intVal mem (args.getD 1 0) h (args.getD 2 0))
    (fun args _ => (2 * args.getD 2 0) * (38 * (2 * args.getD 2 0) + 35) + 120 * args.getD 2 0 + 99)
    (fun args _ => 6 * args.getD 2 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + 6 * args.getD 2 0 ∧ C.post args mem v mem' }

/-- Every linked multiplication body has no random statement. -/
theorem multiplyModule_noRand (b h : ℕ) : ∀ s ∈ multiplyModule b h, s.NoRand := by
  simp only [multiplyModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by simp [multiplyBody, Stmt.NoRand], isNegativeBody_noRand _, extendCopyBody_noRand _,
    mulRowsBody_noRand _ _, mulAddBody_noRand _ _⟩

private theorem fill_sign_bound {B sign : ℕ} {n : ℤ} (hB : 0 < B)
    (hs : sign = if n < 0 then 1 else 0) :
    (B - 1) * sign = (if n < 0 then B - 1 else 0) ∧ (B - 1) * sign < B := by
  rw [hs]
  split_ifs <;> simp <;> omega

/-- The exact multiplier meets its contract with quadratic time and linear space. -/
theorem multiply_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (multiplyModule b h)) :
    MeetsContract w p b (multiplyContract w h) := by
  have hneg : p.HasAt (b + 1) (isNegativeModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [multiplyModule, isNegativeModule] using hp 1 (by simp [multiplyModule])
  have hext : p.HasAt (b + 2) (extendCopyModule (b + 2)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [multiplyModule, extendCopyModule] using hp 2 (by simp [multiplyModule])
  have hrows : p.HasAt (b + 3) (mulRowsModule (b + 3) (b + 4)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [multiplyModule, mulRowsModule] using hp 3 (by simp [multiplyModule])
  have hrow : p.HasAt (b + 4) (mulAddModule (b + 4) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [multiplyModule, mulAddModule] using hp 4 (by simp [multiplyModule])
  have hb := base_lt_word hw
  have hb2 : 1 < base h := Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)
  have hw1 : 1 < 2 ^ w := lt_trans hb2 hb
  have hw2 : 2 < 2 ^ w := lt_of_le_of_lt (Nat.succ_le_of_lt hb2) hb
  have hn := isNegative_meetsContract hh hw1 hb hneg
  have he := extendCopy_meetsContract (h := h) hw1 hext
  have hr := mulRows_meetsContract hw1 hb hrows (mulAdd_meetsContract hw hrow)
  have hentry : p.procs[b]? = some (multiplyBody (b + 1) (b + 2) (b + 3) h) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, d, L, heap, rfl, ha, hd, hva, hvd⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + 6 * L < 2 ^ w at hbound
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have h2Lw : 2 * L < 2 ^ w := by omega
  apply runs_start_le
  unfold multiplyBody
  refine runs_seq_call_le hn (vs := [a, L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a, L, rfl, by omega, hva⟩
  · intro signA mem' pos' hpA
    rcases hpA with ⟨hmem, hsignA⟩
    subst mem'
    change signA = if intVal mem a h L < 0 then 1 else 0 at hsignA
    refine runs_seq_call_le hn (vs := [d, L]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨d, L, rfl, by omega, hvd⟩
    · intro signB mem' pos'' hpB
      rcases hpB with ⟨hmem, hsignB⟩
      subst mem'
      change signB = if intVal mem d h L < 0 then 1 else 0 at hsignB
      have hfA := fill_sign_bound (base_pos h) hsignA
      have hfB := fill_sign_bound (base_pos h) hsignB
      have hfAw : (base h - 1) * signA < 2 ^ w := lt_trans hfA.2 hb
      have hfBw : (base h - 1) * signB < 2 ^ w := lt_trans hfB.2 hb
      refine runs_seq_assign_le (v := (base h - 1) * signA) (by eval_expr) ?_
      refine runs_seq_assign_le (v := (base h - 1) * signB) (by eval_expr) ?_
      refine runs_seq_call_le he (vs := [a, L, 2 * L, (base h - 1) * signA, heap])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨a, L, 2 * L, _, heap, rfl, by omega, ha, hfA.2, hva⟩, hz,
          by change heap + 2 * L < 2 ^ w; omega⟩
      · intro v₁ mem₁ pos₁ hp₁
        rcases hp₁ with ⟨hv₁, hlo₁, hhi₁, hf₁, hz₁, hl₁⟩
        change v₁ = heap + 2 * L at hv₁
        clear hlo₁ hhi₁
        change (∀ x < heap, mem₁ x = mem x) at hf₁
        change ListAt mem₁ heap (extendedLimbs mem a ((base h - 1) * signA) L (2 * L)) at hl₁
        have hva₁ := valid_listAt hl₁ (extendedLimbs_lt hva hfA.2)
        rw [extendedLimbs_length] at hva₁
        have hresA := extended_residue hva (show L ≤ 2 * L by omega) (hfA.1 ▸ hl₁)
        have hvd₁ : Valid mem₁ d h L := by
          intro i hi
          rw [hf₁ (d + i) (by omega)]
          exact hvd i hi
        have hv₁w : v₁ < 2 ^ w := by omega
        refine runs_seq_call_le he (vs := [d, L, 2 * L, (base h - 1) * signB, v₁])
          (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨d, L, 2 * L, _, v₁, rfl, by omega, by omega, hfB.2, hvd₁⟩, hz₁,
            by change v₁ + 2 * L < 2 ^ w; omega⟩
        · intro v₂ mem₂ pos₂ hp₂
          rcases hp₂ with ⟨hv₂, hlo₂, hhi₂, hf₂, hz₂, hl₂⟩
          change v₂ = v₁ + 2 * L at hv₂
          clear hlo₂ hhi₂
          change (∀ x < v₁, mem₂ x = mem₁ x) at hf₂
          change ListAt mem₂ v₁ (extendedLimbs mem₁ d ((base h - 1) * signB) L (2 * L)) at hl₂
          have hstreamB : extendedLimbs mem₁ d ((base h - 1) * signB) L (2 * L) =
              extendedLimbs mem d ((base h - 1) * signB) L (2 * L) := by
            apply extendedLimbs_congr
            intro i hi
            exact hf₁ (d + i) (by omega)
          rw [hstreamB] at hl₂
          have hvd₂ := valid_listAt hl₂ (extendedLimbs_lt hvd hfB.2)
          rw [extendedLimbs_length] at hvd₂
          have hresB := extended_residue hvd (show L ≤ 2 * L by omega) (hfB.1 ▸ hl₂)
          have hsameA : ∀ i < 2 * L, mem₂ (heap + i) = mem₁ (heap + i) := by
            intro i hi
            exact hf₂ (heap + i) (by omega)
          have hva₂ : Valid mem₂ heap h (2 * L) := by
            intro i hi
            rw [hsameA i hi]
            exact hva₁ i hi
          have huA : unsignedVal mem₂ heap h (2 * L) = unsignedVal mem₁ heap h (2 * L) := unsignedVal_congr hsameA
          have hv₂w : v₂ < 2 ^ w := by omega
          have hvzero : unsignedVal mem₂ v₂ h (2 * L) = 0 :=
            unsignedVal_zero (fun i _ => hz₂ (v₂ + i) (by omega))
          refine runs_seq_call_le hr (vs := [heap, v₁, 2 * L, v₂, 0])
            (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨heap, v₁, 2 * L, v₂, 0, rfl, by omega, by omega, by omega, by omega,
              hva₂, hvd₂, zeroFrom_valid hz₂ le_rfl⟩
          · intro v mem₃ pos₃ hp₃
            rcases hp₃ with ⟨hv, hvalid, hframe, hproduct⟩
            change Valid mem₃ v₂ h (2 * L) at hvalid
            change (∀ x, x < v₂ ∨ v₂ + 2 * L ≤ x → mem₃ x = mem₂ x) at hframe
            change unsignedVal mem₃ v₂ h (2 * L) = (unsignedVal mem₂ v₂ h (2 * L) + capacity h 0 *
              unsignedVal mem₂ (heap + 0) h (2 * L - 0) * unsignedVal mem₂ v₁ h (2 * L)) % capacity h (2 * L) at hproduct
            simp only [hvzero, capacity_zero, Nat.add_zero, Nat.sub_zero, one_mul, zero_add] at hproduct
            have hresA₂ : (unsignedVal mem₂ heap h (2 * L) : ℤ) % (capacity h (2 * L) : ℤ) =
                intVal mem a h L % (capacity h (2 * L) : ℤ) := by rwa [huA]
            have hvalue := intVal_product_of_residues hresA₂ hresB hproduct
            rw [wrap_of_fits (fits_mul_double (intVal_fits hva) (intVal_fits hvd))] at hvalue
            have hendw : v₂ + 2 * L < 2 ^ w := by omega
            refine runs_ret_le (v := v₂ + 2 * L) (by eval_expr) ?_ ?_
            · refine ⟨by change v₂ + 2 * L = heap + 6 * L; omega, ?_⟩
              change heap ≤ v₂ + 2 * L ∧ v₂ + 2 * L ≤ heap + 6 * L ∧
                (∀ x < heap, mem₃ x = mem x) ∧ ZeroFrom mem₃ (v₂ + 2 * L) ∧
                Valid mem₃ (heap + 4 * L) h (2 * L) ∧
                  intVal mem₃ (heap + 4 * L) h (2 * L) = intVal mem a h L * intVal mem d h L
              refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
              · intro x hx
                rw [hframe x (Or.inl (by omega)), hf₂ x (by omega), hf₁ x hx]
              · intro x hx
                rw [hframe x (Or.inr hx), hz₂ x (by omega)]
              · simpa only [show v₂ = heap + 4 * L by omega] using hvalid
              · simpa only [show v₂ = heap + 4 * L by omega] using hvalue
            · simp only [multiplyContract, isNegativeContract, extendCopyContract, mulRowsContract,
                heapContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin,
                Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil, Nat.sub_zero]
              omega

end MinCostFlow.Num
