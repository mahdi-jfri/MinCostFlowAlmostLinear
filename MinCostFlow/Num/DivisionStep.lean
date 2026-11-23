module

public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.EstimateDigit
public import MinCostFlow.Num.ScaleCarry
public import MinCostFlow.Num.UnsignedLess
public import MinCostFlow.Num.Subtract
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.DivisionEstimate
import MinCostFlow.Num.DivisionStepFacts
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# One long-division step

Append one digit to a remainder smaller than the divisor. Estimate the next quotient
digit and form the two possible one-limb multiples. One unsigned comparison selects
the correct one. Subtraction leaves the new remainder. The first scratch cell is then
reused to store the quotient digit. The routine allocates `5*(K+1)` cells and costs at
most `300*K+600`. No arithmetic loops flag the bits of a limb are needed.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- The next partial numerator in long division. -/
def stepNumerator (mem : ℕ → ℕ) (r h K digit : ℕ) : ℕ :=
  unsignedVal mem r h (K + 1) * base h + digit

/-- Arguments `[remainder, divisor, effectiveLength, K, digit, heap]`. -/
def divisionStepBody (copy estimate scale less sub : ℕ) : Stmt :=
  .store (.reg 5) (.reg 4) ;;
  .call 6 copy [.reg 0, .reg 3, .bin .add (.reg 5) (.const 1)] ;;
  .call 7 estimate [.reg 5, .reg 1, .reg 2] ;;
  .call 8 scale [.reg 1, .bin .add (.reg 3) (.const 1), .reg 7, .const 0, .reg 6] ;;
  .call 9 scale [.reg 1, .bin .add (.reg 3) (.const 1), .bin .sub (.reg 7) (.const 1), .const 0, .reg 8] ;;
  .call 10 less [.reg 5, .reg 6, .bin .add (.reg 3) (.const 1)] ;;
  .assign 11 (.bin .sub (.reg 7) (.reg 10)) ;;
  .assign 12 (.bin .add (.reg 6) (.bin .mul (.reg 10) (.bin .add (.reg 3) (.const 1)))) ;;
  .call 13 sub [.reg 5, .reg 12, .bin .add (.reg 3) (.const 1), .reg 9] ;;
  .store (.reg 5) (.reg 11) ;;
  .ret (.reg 13)

/-- The division step and its five closed dependencies. -/
def divisionStepModule (b h : ℕ) : List Stmt :=
  [divisionStepBody (b + 1) (b + 2) (b + 3) (b + 4) (b + 5)] ++
    (copyModule (b + 1) ++ (estimateDigitModule (b + 2) h ++
      (scaleCarryModule (b + 3) h ++ (unsignedLessModule (b + 4) ++ subtractModule (b + 5) h))))

/-- The first scratch word holds the next quotient digit. The remainder occupies
`K+1` limbs at `heap+4*(K+1)`, and the return is `heap+5*(K+1)`. -/
def divisionStepContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ r d n K digit heap, args = [r, d, n, K, digit, heap] ∧
      0 < n ∧ n ≤ K ∧ r + (K + 1) ≤ heap ∧ d + (K + 1) ≤ heap ∧
      Valid mem r h (K + 1) ∧ Valid mem d h (K + 1) ∧ 0 < mem (d + (n - 1)) ∧
      (∀ i, n ≤ i → i < K + 1 → mem (d + i) = 0) ∧
      unsignedVal mem r h (K + 1) < unsignedVal mem d h (K + 1) ∧ digit < base h)
    (fun args mem mem' =>
      mem' (heapArg args) = stepNumerator mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0) /
        unsignedVal mem (args.getD 1 0) h (args.getD 3 0 + 1) ∧
      Valid mem' (heapArg args + 4 * (args.getD 3 0 + 1)) h (args.getD 3 0 + 1) ∧
      unsignedVal mem' (heapArg args + 4 * (args.getD 3 0 + 1)) h (args.getD 3 0 + 1) =
        stepNumerator mem (args.getD 0 0) h (args.getD 3 0) (args.getD 4 0) %
          unsignedVal mem (args.getD 1 0) h (args.getD 3 0 + 1))
    (fun args _ => 300 * args.getD 3 0 + 600) (fun args _ => 5 * (args.getD 3 0 + 1))
  { C with post := fun args mem v mem' =>
      v = heapArg args + 5 * (args.getD 3 0 + 1) ∧ C.post args mem v mem' }

/-- The step and all of its dependencies contain no random statements. -/
theorem divisionStepModule_noRand (b h : ℕ) : ∀ s ∈ divisionStepModule b h, s.NoRand := by
  intro s hs
  simp only [divisionStepModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with rfl | hc | he | hm | hl | hs
  · simp [divisionStepBody, Stmt.NoRand]
  · have hx : s = copyBody := by simpa only [copyModule, List.mem_singleton] using hc
    subst s
    exact copyBody_noRand
  · have hx : s = estimateDigitBody h := by simpa only [estimateDigitModule, List.mem_singleton] using he
    subst s
    exact estimateDigitBody_noRand _
  · have hx : s = scaleCarryBody (b + 3) h := by simpa only [scaleCarryModule, List.mem_singleton] using hm
    subst s
    exact scaleCarryBody_noRand _ _
  · have hx : s = unsignedLessBody (b + 4) := by simpa only [unsignedLessModule, List.mem_singleton] using hl
    subst s
    exact unsignedLessBody_noRand _
  · exact subtractModule_noRand _ _ _ hs

/-- One corrected long-division digit meets its linear-cost heap contract. -/
theorem divisionStep_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hp : p.HasAt b (divisionStepModule b h)) :
    MeetsContract w p b (divisionStepContract w h) := by
  have hentry : p.procs[b]? = some (divisionStepBody (b + 1) (b + 2) (b + 3) (b + 4) (b + 5)) := hp.head
  dsimp only [divisionStepModule] at hp
  have h1 := hasAt_append_right hp
  have hc : p.HasAt (b + 1) (copyModule (b + 1)) := by
    simpa only [List.length_singleton] using hasAt_append_left h1
  have h2 := hasAt_append_right h1
  have he : p.HasAt (b + 2) (estimateDigitModule (b + 2) h) := by
    simpa only [copyModule, List.length_singleton, Nat.add_assoc] using hasAt_append_left h2
  have h3 := hasAt_append_right h2
  have hm : p.HasAt (b + 3) (scaleCarryModule (b + 3) h) := by
    simpa only [copyModule, estimateDigitModule, List.length_singleton, Nat.add_assoc] using hasAt_append_left h3
  have h4 := hasAt_append_right h3
  have hl : p.HasAt (b + 4) (unsignedLessModule (b + 4)) := by
    simpa only [copyModule, estimateDigitModule, scaleCarryModule, List.length_singleton, Nat.add_assoc] using hasAt_append_left h4
  have h5 := hasAt_append_right h4
  have hs : p.HasAt (b + 5) (subtractModule (b + 5) h) := by
    simpa only [copyModule, estimateDigitModule, scaleCarryModule, unsignedLessModule,
      List.length_singleton, Nat.add_assoc] using h5
  have hwprod : 2 * h + 2 ≤ w := by omega
  have hb := base_lt_word hwprod
  have hw1 : 1 < 2 ^ w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hcopy := copy_meetsContract (h := h) hw1 hc
  have hest := estimateDigit_meetsContract hh hw he
  have hscale := scaleCarry_meetsContract hwprod hm
  have hless := unsignedLess_meetsContract (h := h) hw1 hl
  have hsub := subtract_meetsContract hh hwprod hs
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨r, d, n, K, digit, heap, rfl, hn, hnK, hr, hd, hvr, hvd, htop, hzeros, hR, hx⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + 5 * (K + 1) < 2 ^ w at hbound
  have hrw : r < 2 ^ w := hwords r (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hnw : n < 2 ^ w := hwords n (by simp)
  have hKw : K < 2 ^ w := hwords K (by simp)
  have hxw : digit < 2 ^ w := hwords digit (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have hMw : K + 1 < 2 ^ w := by omega
  have hDprefix : unsignedVal mem d h (K + 1) = unsignedVal mem d h n :=
    unsignedVal_eq_prefix_of_zeros (by omega) hzeros
  have hVn : unsignedVal mem d h (K + 1) < capacity h n := by
    rw [hDprefix]
    exact unsignedVal_lt (fun i hi => hvd i (by omega))
  have hVcap : unsignedVal mem d h (K + 1) < capacity h K :=
    lt_of_lt_of_le hVn (Nat.pow_le_pow_right (base_pos h) hnK)
  have hVpos : 0 < unsignedVal mem d h (K + 1) := by omega
  have hRprefix := unsignedVal_prefix_of_lt hvr (Nat.le_succ K) (lt_trans hR hVcap)
  have hXbound : stepNumerator mem r h K digit < unsignedVal mem d h (K + 1) * base h :=
    remainder_append_lt hR hx
  have hXcap : stepNumerator mem r h K digit < capacity h (n + 1) := by
    have hm := Nat.mul_le_mul_right (base h) (Nat.le_of_lt hVn)
    rw [capacity_succ]
    nlinarith only [hm, hXbound]
  apply runs_start_le
  unfold divisionStepBody
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  have hsourceR : Valid (Function.update mem heap digit) r h K := by
    intro i hi
    rw [Function.update_of_ne (by omega)]
    exact hvr i (by omega)
  refine runs_seq_call_le hcopy (vs := [r, K, heap + 1]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨r, K, heap + 1, rfl, by omega, hsourceR⟩, hz.update_head digit,
      by change heap + 1 + K < 2 ^ w; omega⟩
  · intro vX mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hvX, hlo₁, hhi₁, hf₁, hz₁, hlimbs, hvalidTail, hcopyval⟩
    change vX = heap + 1 + K at hvX
    clear hlo₁ hhi₁ hcopyval
    change (∀ z < heap + 1, mem₁ z = Function.update mem heap digit z) at hf₁
    change (∀ i < K, mem₁ (heap + 1 + i) = Function.update mem heap digit (r + i)) at hlimbs
    change Valid mem₁ (heap + 1) h K at hvalidTail
    have hfreeze₁ : ∀ z < heap, mem₁ z = mem z := by
      intro z hz'
      rw [hf₁ z (by omega), Function.update_of_ne (by omega)]
    have hheadX : mem₁ heap = digit := by rw [hf₁ heap (by omega), Function.update_self]
    have htailX : unsignedVal mem₁ (heap + 1) h K = unsignedVal mem r h K := by
      apply unsignedVal_congr
      intro i hi
      rw [hlimbs i hi, Function.update_of_ne (by omega)]
    have hvalidX : Valid mem₁ heap h (K + 1) := valid_succ.mpr ⟨by rw [hheadX]; exact hx, hvalidTail⟩
    have hvalueX : unsignedVal mem₁ heap h (K + 1) = stepNumerator mem r h K digit := by
      rw [unsignedVal, hheadX, htailX, hRprefix]
      unfold stepNumerator
      ring
    have hvalidD₁ : Valid mem₁ d h (K + 1) := by
      intro i hi
      rw [hfreeze₁ (d + i) (by omega)]
      exact hvd i hi
    have hvalueD₁ : unsignedVal mem₁ d h (K + 1) = unsignedVal mem d h (K + 1) :=
      unsignedVal_congr (fun i hi => hfreeze₁ (d + i) (by omega))
    have hnumPrefix : unsignedVal mem₁ heap h (n + 1) = stepNumerator mem r h K digit := by
      rw [unsignedVal_prefix_of_lt hvalidX (by omega) (by rw [hvalueX]; exact hXcap), hvalueX]
    have hdenPrefix : unsignedVal mem₁ d h n = unsignedVal mem d h (K + 1) := by
      have heq : unsignedVal mem₁ d h n = unsignedVal mem d h n :=
        unsignedVal_congr (fun i hi => hfreeze₁ (d + i) (by omega))
      rw [heq, hDprefix]
    have hvXw : vX < 2 ^ w := by omega
    refine runs_seq_call_le hest (vs := [heap, d, n]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨heap, d, n, rfl, hn, by omega, by omega, fun i hi => hvalidX i (by omega),
        fun i hi => hvalidD₁ i (by omega), ?_, ?_⟩
      · change 0 < mem₁ (d + (n - 1))
        rw [hfreeze₁ (d + (n - 1)) (by omega)]
        exact htop
      · change unsignedVal mem₁ heap h (n + 1) < unsignedVal mem₁ d h n * base h
        rw [hnumPrefix, hdenPrefix]
        exact hXbound
    · intro qhat mem' pos' hpest
      rcases hpest with ⟨hmem, hqlo, hqhi, hqB⟩
      subst mem'
      change unsignedVal mem₁ heap h (n + 1) / unsignedVal mem₁ d h n ≤ qhat at hqlo
      change qhat ≤ unsignedVal mem₁ heap h (n + 1) / unsignedVal mem₁ d h n + 1 at hqhi
      change qhat < base h at hqB
      rw [hnumPrefix, hdenPrefix] at hqlo hqhi
      have hqhatw : qhat < 2 ^ w := lt_trans hqB hb
      have hprod0 : qhat * unsignedVal mem d h (K + 1) < capacity h (K + 1) :=
        limb_product_lt_next_capacity hVcap hqB
      refine runs_seq_call_le hscale (vs := [d, K + 1, qhat, 0, vX]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨d, K + 1, qhat, 0, vX, rfl, by omega, hqB, Nat.zero_le _, hvalidD₁⟩, hz₁,
          by change vX + (K + 1) < 2 ^ w; omega⟩
      · intro vP mem₂ pos₂ hp₂
        rcases hp₂ with ⟨hvP, hlo₂, hhi₂, hf₂, hz₂, hl₂⟩
        change vP = vX + (K + 1) at hvP
        clear hlo₂ hhi₂
        change (∀ z < vX, mem₂ z = mem₁ z) at hf₂
        change ListAt mem₂ vX (digits h (K + 1) (unsignedVal mem₁ d h (K + 1) * qhat + 0)) at hl₂
        have hvalidP₀ := valid_listAt hl₂ (digits_lt h (K + 1) _)
        rw [digits_length] at hvalidP₀
        have hvalueP₀ := unsignedVal_listAt (h := h) hl₂
        rw [digits_length, listVal_digits] at hvalueP₀
        simp only [Nat.add_zero] at hvalueP₀
        rw [hvalueD₁, Nat.mul_comm, Nat.mod_eq_of_lt hprod0] at hvalueP₀
        have hfreeze₂ : ∀ z < vX, mem₂ z = mem₁ z := hf₂
        have hvalidD₂ : Valid mem₂ d h (K + 1) := by
          intro i hi
          rw [hf₂ (d + i) (by omega)]
          exact hvalidD₁ i hi
        have hvalueD₂ : unsignedVal mem₂ d h (K + 1) = unsignedVal mem d h (K + 1) := by
          rw [unsignedVal_congr (fun i hi => hf₂ (d + i) (by omega)), hvalueD₁]
        have hqminusB : qhat - 1 < base h := lt_of_le_of_lt (Nat.sub_le _ _) hqB
        have hqminusw : qhat - 1 < 2 ^ w := lt_trans hqminusB hb
        have hprod1 : (qhat - 1) * unsignedVal mem d h (K + 1) < capacity h (K + 1) :=
          limb_product_lt_next_capacity hVcap hqminusB
        have hvPw : vP < 2 ^ w := by omega
        refine runs_seq_call_le hscale (vs := [d, K + 1, qhat - 1, 0, vP]) (by eval_expr) (by wram_words) ?_ ?_
        · exact ⟨⟨d, K + 1, qhat - 1, 0, vP, rfl, by omega, hqminusB, Nat.zero_le _, hvalidD₂⟩,
            hz₂, by change vP + (K + 1) < 2 ^ w; omega⟩
        · intro vS mem₃ pos₃ hp₃
          rcases hp₃ with ⟨hvS, hlo₃, hhi₃, hf₃, hz₃, hl₃⟩
          change vS = vP + (K + 1) at hvS
          clear hlo₃ hhi₃
          change (∀ z < vP, mem₃ z = mem₂ z) at hf₃
          change ListAt mem₃ vP (digits h (K + 1) (unsignedVal mem₂ d h (K + 1) * (qhat - 1) + 0)) at hl₃
          have hvalidP₁ := valid_listAt hl₃ (digits_lt h (K + 1) _)
          rw [digits_length] at hvalidP₁
          have hvalueP₁ := unsignedVal_listAt (h := h) hl₃
          rw [digits_length, listVal_digits] at hvalueP₁
          simp only [Nat.add_zero] at hvalueP₁
          rw [hvalueD₂, Nat.mul_comm, Nat.mod_eq_of_lt hprod1] at hvalueP₁
          have hsameX : ∀ i < K + 1, mem₃ (heap + i) = mem₁ (heap + i) := by
            intro i hi
            rw [hf₃ (heap + i) (by omega), hf₂ (heap + i) (by omega)]
          have hvalidX₃ : Valid mem₃ heap h (K + 1) := by
            intro i hi
            rw [hsameX i hi]
            exact hvalidX i hi
          have hvalueX₃ : unsignedVal mem₃ heap h (K + 1) = stepNumerator mem r h K digit := by
            rw [unsignedVal_congr hsameX, hvalueX]
          have hsameP : ∀ i < K + 1, mem₃ (vX + i) = mem₂ (vX + i) := by
            intro i hi
            exact hf₃ (vX + i) (by omega)
          have hvalidP₀₃ : Valid mem₃ vX h (K + 1) := by
            intro i hi
            rw [hsameP i hi]
            exact hvalidP₀ i hi
          have hvalueP₀₃ : unsignedVal mem₃ vX h (K + 1) = qhat * unsignedVal mem d h (K + 1) := by
            rw [unsignedVal_congr hsameP, hvalueP₀]
          have hvSw : vS < 2 ^ w := by omega
          refine runs_seq_call_le hless (vs := [heap, vX, K + 1]) (by eval_expr) (by wram_words) ?_ ?_
          · exact ⟨heap, vX, K + 1, rfl, by omega, by omega, hvalidX₃, hvalidP₀₃⟩
          · intro flag mem' pos' hpcmp
            rcases hpcmp with ⟨hmem, hover⟩
            subst mem'
            change flag = if unsignedVal mem₃ heap h (K + 1) < unsignedVal mem₃ vX h (K + 1) then 1 else 0 at hover
            rw [hvalueX₃, hvalueP₀₃] at hover
            have hoverle : flag ≤ 1 := by split_ifs at hover <;> omega
            have hqfinal : qhat - flag = stepNumerator mem r h K digit / unsignedVal mem d h (K + 1) := by
              have heq := correct_quotient_digit hVpos hqlo hqhi
              rw [hover]
              split_ifs with ho
              · simpa only [ite_eq_left ho] using heq
              · simpa only [ite_eq_right ho, Nat.sub_zero] using heq
            have hqfinalw : qhat - flag < 2 ^ w := lt_of_le_of_lt (Nat.sub_le _ _) hqhatw
            have hselect : Valid mem₃ (vX + flag * (K + 1)) h (K + 1) ∧
                unsignedVal mem₃ (vX + flag * (K + 1)) h (K + 1) =
                  (qhat - flag) * unsignedVal mem d h (K + 1) := by
              by_cases ho : stepNumerator mem r h K digit < qhat * unsignedVal mem d h (K + 1)
              · have h1 : flag = 1 := by simpa only [ite_eq_left ho] using hover
                rw [h1, one_mul, ← hvP]
                exact ⟨hvalidP₁, hvalueP₁⟩
              · have h0 : flag = 0 := by simpa only [ite_eq_right ho] using hover
                rw [h0, zero_mul, Nat.add_zero, Nat.sub_zero]
                exact ⟨hvalidP₀₃, hvalueP₀₃⟩
            have hovermul : flag * (K + 1) ≤ K + 1 := by nlinarith only [Nat.mul_le_mul_right (K + 1) hoverle]
            have hovermulw : flag * (K + 1) < 2 ^ w := lt_of_le_of_lt hovermul hMw
            have hselectw : vX + flag * (K + 1) < 2 ^ w := by omega
            refine runs_seq_assign_le (v := qhat - flag) (by eval_expr) ?_
            refine runs_seq_assign_le (v := vX + flag * (K + 1)) (by eval_expr) ?_
            refine runs_seq_call_le hsub (vs := [heap, vX + flag * (K + 1), K + 1, vS])
              (by eval_expr) (by wram_words) ?_ ?_
            · exact ⟨⟨heap, _, K + 1, vS, rfl, by omega, by omega, hvalidX₃, hselect.1⟩,
                hz₃, by change vS + 2 * (K + 1) < 2 ^ w; omega⟩
            · intro vend mem₄ pos₄ hp₄
              rcases hp₄ with ⟨hvend, hlo₄, hhi₄, hf₄, hz₄, hvalidR, hvalueR⟩
              change vend = vS + 2 * (K + 1) at hvend
              clear hlo₄ hhi₄
              change (∀ z < vS, mem₄ z = mem₃ z) at hf₄
              change Valid mem₄ (vS + (K + 1)) h (K + 1) at hvalidR
              change intVal mem₄ (vS + (K + 1)) h (K + 1) =
                wrap h (K + 1) (intVal mem₃ heap h (K + 1) -
                  intVal mem₃ (vX + flag * (K + 1)) h (K + 1)) at hvalueR
              have hselected := hselect.2
              rw [hqfinal] at hselected
              have hdiff : stepNumerator mem r h K digit -
                  (stepNumerator mem r h K digit / unsignedVal mem d h (K + 1)) * unsignedVal mem d h (K + 1) =
                    stepNumerator mem r h K digit % unsignedVal mem d h (K + 1) := by
                have heq := Nat.mod_add_div (stepNumerator mem r h K digit) (unsignedVal mem d h (K + 1))
                rw [Nat.mul_comm (unsignedVal mem d h (K + 1))] at heq
                omega
              have hfit : Fits h (K + 1) ((stepNumerator mem r h K digit -
                  (stepNumerator mem r h K digit / unsignedVal mem d h (K + 1)) * unsignedVal mem d h (K + 1) : ℕ) : ℤ) := by
                rw [hdiff]
                exact fits_nat_extra_limb hh (lt_trans (Nat.mod_lt _ hVpos) hVcap)
              conv_rhs at hvalueR =>
                rw [intVal, intVal, hvalueX₃, hselected,
                  wrapped_unsigned_difference (Nat.div_mul_le_self _ _) hfit, hdiff]
              have hnumR := unsignedVal_of_intVal_nonneg hvalidR hvalueR
              have hrowendw : vend < 2 ^ w := by omega
              refine runs_seq_store_le (x := heap) (v := qhat - flag) (by eval_expr) (by eval_expr) ?_
              refine runs_ret_le (v := vend) (by eval_expr) ?_ ?_
              · refine ⟨by change vend = heap + 5 * (K + 1); omega, ?_⟩
                change heap ≤ vend ∧ vend ≤ heap + 5 * (K + 1) ∧
                  (∀ z < heap, Function.update mem₄ heap (qhat - flag) z = mem z) ∧
                  ZeroFrom (Function.update mem₄ heap (qhat - flag)) vend ∧
                  Function.update mem₄ heap (qhat - flag) heap =
                    stepNumerator mem r h K digit / unsignedVal mem d h (K + 1) ∧
                  Valid (Function.update mem₄ heap (qhat - flag)) (heap + 4 * (K + 1)) h (K + 1) ∧
                  unsignedVal (Function.update mem₄ heap (qhat - flag)) (heap + 4 * (K + 1)) h (K + 1) =
                    stepNumerator mem r h K digit % unsignedVal mem d h (K + 1)
                refine ⟨by omega, by omega, ?_, hz₄.update_lt (by omega), by simpa using hqfinal, ?_, ?_⟩
                · intro z hz'
                  rw [Function.update_of_ne (by omega), hf₄ z (by omega), hf₃ z (by omega),
                    hf₂ z (by omega), hfreeze₁ z hz']
                · intro i hi
                  rw [Function.update_of_ne (by omega)]
                  simpa only [show heap + 4 * (K + 1) = vS + (K + 1) by omega] using hvalidR i hi
                · have heq : unsignedVal (Function.update mem₄ heap (qhat - flag)) (heap + 4 * (K + 1)) h (K + 1) =
                      unsignedVal mem₄ (vS + (K + 1)) h (K + 1) := by
                    apply unsignedVal_congr
                    intro i hi
                    rw [Function.update_of_ne (by omega)]
                    congr 1
                    omega
                  rw [heq, hnumR]
              · simp only [divisionStepContract, copyContract, estimateDigitContract, scaleCarryContract,
                  unsignedLessContract, subtractContract, heapContract, List.getD_cons_zero,
                  List.getD_cons_succ, Expr.size_bin, Expr.size_reg, Expr.size_const,
                  argsSize_cons, argsSize_nil]
                omega

end MinCostFlow.Num
