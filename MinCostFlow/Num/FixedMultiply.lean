module

public import MinCostFlow.Num.Multiply
public import MinCostFlow.Num.ShiftRight
public import MinCostFlow.Num.Copy
import MinCostFlow.Num.ShiftFacts
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic

/-!
# Fixed-point multiplication

First compute the exact signed product in twice the width. Arithmetic right shifting
by the precision gives the floor quotient required for the fixed-point numerator.
Copying the low `L` limbs gives wrap-around when that numerator does not fit. The result
starts at `heap+10L+1`, with total allocation `11L+1`. The cost is at most
`152*L^2 + 339*L + 248`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, L, P, heap]`, followed by entries for exact multiplication,
arithmetic right shifting, and prefix copying. -/
def fixedMultiplyBody (mul shift copy : ℕ) : Stmt :=
  .call 5 mul [.reg 0, .reg 1, .reg 2, .reg 4] ;;
  .call 6 shift [.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 2)),
    .bin .mul (.const 2) (.reg 2), .reg 3, .reg 5] ;;
  .call 7 copy [.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 2))) (.const 1),
    .reg 2, .reg 6] ;;
  .ret (.reg 7)

/-- The fixed-point multiplier and the closed modules it calls. -/
def fixedMultiplyModule (b h : ℕ) : List Stmt :=
  [fixedMultiplyBody (b + 1) (b + 6) (b + 10)] ++ multiplyModule (b + 1) h ++
    shiftRightModule (b + 6) h ++ copyModule (b + 10)

/-- Compute the wrapped floor numerator of a product at aligned precision `P`. -/
def fixedMultiplyContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L P heap, args = [a, d, L, P, heap] ∧ h ∣ P ∧
      a + L ≤ heap ∧ d + L ≤ heap ∧ Valid mem a h L ∧ Valid mem d h L)
    (fun args mem mem' => Valid mem' (heapArg args + 10 * args.getD 2 0 + 1) h (args.getD 2 0) ∧
      intVal mem' (heapArg args + 10 * args.getD 2 0 + 1) h (args.getD 2 0) =
        wrap h (args.getD 2 0) ((intVal mem (args.getD 0 0) h (args.getD 2 0) *
          intVal mem (args.getD 1 0) h (args.getD 2 0)) / (2 : ℤ) ^ args.getD 3 0))
    (fun args _ => (2 * args.getD 2 0) * (38 * (2 * args.getD 2 0) + 35) + 269 * args.getD 2 0 + 248)
    (fun args _ => 11 * args.getD 2 0 + 1)
  { C with post := fun args mem v mem' =>
      v = heapArg args + (11 * args.getD 2 0 + 1) ∧ C.post args mem v mem' }

/-- The complete fixed-point multiplication module contains no random statements. -/
theorem fixedMultiplyModule_noRand (b h : ℕ) : ∀ s ∈ fixedMultiplyModule b h, s.NoRand := by
  intro s hs
  simp only [fixedMultiplyModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with ((rfl | hm) | hr) | hc
  · simp [fixedMultiplyBody, Stmt.NoRand]
  · exact multiplyModule_noRand _ _ _ hm
  · exact shiftRightModule_noRand _ _ _ hr
  · have he : s = copyBody := by simpa only [copyModule, List.mem_singleton] using hc
    subst s
    exact copyBody_noRand

/-- The fixed-point multiplier meets its heap contract with a quadratic cost bound. -/
theorem fixedMultiply_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (fixedMultiplyModule b h)) :
    MeetsContract w p b (fixedMultiplyContract w h) := by
  have hm : p.HasAt (b + 1) (multiplyModule (b + 1) h) := by
    intro i hi
    have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by change i < 5 at hi; omega
    rcases he with rfl | rfl | rfl | rfl | rfl
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 1 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 2 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 3 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 4 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 5 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
  have hs : p.HasAt (b + 6) (shiftRightModule (b + 6) h) := by
    intro i hi
    have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
    rcases he with rfl | rfl | rfl | rfl
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 6 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 7 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 8 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
    · simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule, Nat.add_assoc] using
        hp 9 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
  have hc : p.HasAt (b + 10) (copyModule (b + 10)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule] using
      hp 10 (by simp [fixedMultiplyModule, multiplyModule, shiftRightModule, copyModule])
  have hb := base_lt_word hw
  have hw1 : 1 < 2 ^ w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hw4 : 4 < 2 ^ w := lt_of_lt_of_le (by decide : 4 < 2 ^ 4)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hw2 : 2 < 2 ^ w := by omega
  have hmul := multiply_meetsContract hh hw hm
  have hshift := shiftRight_meetsContract hh hw1 hb hs
  have hcopy := copy_meetsContract (h := h) hw1 hc
  have hentry : p.procs[b]? = some (fixedMultiplyBody (b + 1) (b + 6) (b + 10)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, d, L, P, heap, rfl, hP, ha, hd, hva, hvd⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + (11 * L + 1) < 2 ^ w at hbound
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hPw : P < 2 ^ w := hwords P (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have h2Lw : 2 * L < 2 ^ w := by omega
  have h4Lw : 4 * L < 2 ^ w := by omega
  apply runs_start_le
  unfold fixedMultiplyBody
  refine runs_seq_call_le hmul (vs := [a, d, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a, d, L, heap, rfl, ha, hd, hva, hvd⟩, hz, by change heap + 6 * L < 2 ^ w; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hv₁, hlo₁, hhi₁, hf₁, hz₁, hvalid₁, hvalue₁⟩
    change v₁ = heap + 6 * L at hv₁
    clear hlo₁ hhi₁
    change (∀ x < heap, mem₁ x = mem x) at hf₁
    change Valid mem₁ (heap + 4 * L) h (2 * L) at hvalid₁
    change intVal mem₁ (heap + 4 * L) h (2 * L) = intVal mem a h L * intVal mem d h L at hvalue₁
    have hv₁w : v₁ < 2 ^ w := by omega
    refine runs_seq_call_le hshift (vs := [heap + 4 * L, 2 * L, P, v₁])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨heap + 4 * L, 2 * L, P, v₁, rfl, by omega, hvalid₁⟩, hz₁,
        by change v₁ + (2 * (2 * L) + 1) < 2 ^ w; omega⟩
    · intro v₂ mem₂ pos₂ hp₂
      rcases hp₂ with ⟨hv₂, hlo₂, hhi₂, hf₂, hz₂, hvalid₂, hvalue₂⟩
      change v₂ = v₁ + (2 * (2 * L) + 1) at hv₂
      clear hlo₂ hhi₂
      change (∀ x < v₁, mem₂ x = mem₁ x) at hf₂
      change Valid mem₂ (v₁ + 2 * L + 1) h (2 * L) at hvalid₂
      change intVal mem₂ (v₁ + 2 * L + 1) h (2 * L) =
        intVal mem₁ (heap + 4 * L) h (2 * L) / (2 : ℤ) ^ P at hvalue₂
      have hprefix : Valid mem₂ (v₁ + 2 * L + 1) h L :=
        fun i hi => hvalid₂ i (by omega)
      have hv₂w : v₂ < 2 ^ w := by omega
      refine runs_seq_call_le hcopy (vs := [v₁ + 2 * L + 1, L, v₂])
        (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨v₁ + 2 * L + 1, L, v₂, rfl, by omega, hprefix⟩, hz₂,
          by change v₂ + L < 2 ^ w; omega⟩
      · intro v₃ mem₃ pos₃ hp₃
        rcases hp₃ with ⟨hv₃, hlo₃, hhi₃, hf₃, hz₃, hlimbs, hvalid₃, hvalue₃⟩
        change v₃ = v₂ + L at hv₃
        clear hlo₃ hhi₃
        change (∀ x < v₂, mem₃ x = mem₂ x) at hf₃
        change Valid mem₃ v₂ h L at hvalid₃
        change intVal mem₃ v₂ h L = intVal mem₂ (v₁ + 2 * L + 1) h L at hvalue₃
        have hv₃w : v₃ < 2 ^ w := by omega
        refine runs_ret_le (v := v₃) (by eval_expr) ?_ ?_
        · refine ⟨by change v₃ = heap + (11 * L + 1); omega, ?_⟩
          change heap ≤ v₃ ∧ v₃ ≤ heap + (11 * L + 1) ∧ (∀ x < heap, mem₃ x = mem x) ∧
            ZeroFrom mem₃ v₃ ∧ Valid mem₃ (heap + 10 * L + 1) h L ∧
              intVal mem₃ (heap + 10 * L + 1) h L =
                wrap h L ((intVal mem a h L * intVal mem d h L) / (2 : ℤ) ^ P)
          refine ⟨by omega, by omega, ?_, hz₃, ?_, ?_⟩
          · intro x hx
            rw [hf₃ x (by omega), hf₂ x (by omega), hf₁ x hx]
          · simpa only [show v₂ = heap + 10 * L + 1 by omega] using hvalid₃
          · rw [show heap + 10 * L + 1 = v₂ by omega, hvalue₃,
              intVal_prefix_wrap hvalid₂ (show L ≤ 2 * L by omega), hvalue₂, hvalue₁]
        · simp only [fixedMultiplyContract, multiplyContract, shiftRightContract, copyContract,
            heapContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin,
            Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
          omega

/-- When the fixed-point numerator fits, the multiplier returns the exact floor quotient. -/
theorem fixedMultiply_value_of_fits {w h a d L P heap v : ℕ} {mem mem' : ℕ → ℕ}
    (hp : (fixedMultiplyContract w h).post [a, d, L, P, heap] mem v mem')
    (hf : Fits h L ((intVal mem a h L * intVal mem d h L) / (2 : ℤ) ^ P)) :
    intVal mem' (heap + 10 * L + 1) h L =
      (intVal mem a h L * intVal mem d h L) / (2 : ℤ) ^ P := by
  have he := hp.2.2.2.2.2.2
  change intVal mem' (heap + 10 * L + 1) h L =
    wrap h L ((intVal mem a h L * intVal mem d h L) / (2 : ℤ) ^ P) at he
  rw [he, wrap_of_fits hf]

end MinCostFlow.Num
