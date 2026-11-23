module

public import MinCostFlow.Num.Negate
public import MinCostFlow.Num.Add
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Signed subtraction

Subtraction first negates its second operand into a fresh `L`-limb scratch block, then
adds the first operand to that block. The result starts at `heap + L`, and the returned
heap pointer is `heap + 2*L`. Both source blocks are preserved. The signed result wraps
modulo capacity, so subtraction also covers the most negative representable integer.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, d, L, heap]`, with entries for negation and addition. -/
def subtractBody (neg add : ℕ) : Stmt :=
  .call 4 neg [.reg 1, .reg 2, .reg 3] ;;
  .call 5 add [.reg 0, .reg 3, .reg 2, .reg 4] ;;
  .ret (.reg 5)

/-- Subtraction followed by the negation and addition modules it calls. -/
def subtractModule (b h : ℕ) : List Stmt :=
  [subtractBody (b + 1) (b + 3)] ++ negateModule (b + 1) h ++ addModule (b + 3) h

/-- Allocate one scratch block and one result block. The result is at `heap + L`. -/
def subtractContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d L heap, args = [a, d, L, heap] ∧
      a + L ≤ heap ∧ d + L ≤ heap ∧ Valid mem a h L ∧ Valid mem d h L)
    (fun args mem mem' =>
      Valid mem' (heapArg args + args.getD 2 0) h (args.getD 2 0) ∧
      intVal mem' (heapArg args + args.getD 2 0) h (args.getD 2 0) =
        wrap h (args.getD 2 0) (intVal mem (args.getD 0 0) h (args.getD 2 0) -
          intVal mem (args.getD 1 0) h (args.getD 2 0)))
    (fun args _ => 74 * args.getD 2 0 + 42) (fun args _ => 2 * args.getD 2 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + 2 * args.getD 2 0 ∧ C.post args mem v mem' }

/-- No body in the complete subtraction module uses random bits. -/
theorem subtractModule_noRand (b h : ℕ) : ∀ s ∈ subtractModule b h, s.NoRand := by
  intro s hs
  simp only [subtractModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with (rfl | hn) | ha
  · simp [subtractBody, Stmt.NoRand]
  · exact negateModule_noRand _ _ _ hn
  · exact addModule_noRand _ _ _ ha

/-- Subtraction meets its heap contract in at most `74 * L + 42` steps. -/
theorem subtract_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hp : p.HasAt b (subtractModule b h)) :
    MeetsContract w p b (subtractContract w h) := by
  have hneg : p.HasAt (b + 1) (negateModule (b + 1) h) := by
    intro i hi
    have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases he with rfl | rfl
    · simpa [subtractModule, negateModule] using hp 1 (by simp [subtractModule, negateModule, addModule])
    · simpa [subtractModule, negateModule, Nat.add_assoc] using hp 2 (by simp [subtractModule, negateModule, addModule])
  have hadd : p.HasAt (b + 3) (addModule (b + 3) h) := by
    intro i hi
    have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases he with rfl | rfl
    · simpa [subtractModule, negateModule, addModule, Nat.add_assoc] using
        hp 3 (by simp [subtractModule, negateModule, addModule])
    · simpa [subtractModule, negateModule, addModule, Nat.add_assoc] using
        hp 4 (by simp [subtractModule, negateModule, addModule])
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hn := negate_meetsContract hw1 (base_lt_word hw) hneg
  have ha := add_meetsContract hh hw hadd
  have hentry : p.procs[b]? = some (subtractBody (b + 1) (b + 3)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, d, L, heap, rfl, hsa, hsd, hva, hvd⟩, hz, hb⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * L < 2 ^ w at hb
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  apply runs_start_le
  unfold subtractBody
  refine runs_seq_call_le hn (by eval_expr) (by wram_words) ?_ ?_
  · change ∃ a' L' heap', [d, L, heap] = [a', L', heap'] ∧ _
    refine ⟨d, L, heap, rfl, ?_⟩
    exact ⟨⟨d, L, 1, heap, rfl, hsd, le_rfl, hvd⟩, hz, by change heap + L < 2 ^ w; omega⟩
  · intro v₁ mem₁ pos₁ hpost₁
    rcases hpost₁ with ⟨he₁, hlo₁, hhi₁, hf₁, hz₁, hl₁⟩
    change v₁ = heap + L at he₁
    change (∀ x < heap, mem₁ x = mem x) at hf₁
    change ListAt mem₁ heap (digits h L (capacity h L - 1 - unsignedVal mem d h L + 1)) at hl₁
    have hnegval := negateCarry_value_one hvd hl₁
    have hsource : Valid mem₁ a h L := by
      intro i hi
      rw [hf₁ (a + i) (by omega)]
      exact hva i hi
    have hsourceval : intVal mem₁ a h L = intVal mem a h L :=
      intVal_congr fun i hi => hf₁ (a + i) (by omega)
    have hv₁w : v₁ < 2 ^ w := by omega
    refine runs_seq_call_le ha (vs := [a, heap, L, v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · change ∃ a' d' L' heap', [a, heap, L, v₁] = [a', d', L', heap'] ∧ _
      refine ⟨a, heap, L, v₁, rfl, ?_⟩
      exact ⟨⟨a, heap, L, 0, v₁, rfl, by omega, by omega, by decide,
        hsource, hnegval.1⟩, hz₁, by change v₁ + L < 2 ^ w; omega⟩
    · intro v₂ mem₂ pos₂ hpost₂
      rcases hpost₂ with ⟨he₂, hlo₂, hhi₂, hf₂, hz₂, hl₂⟩
      change v₂ = v₁ + L at he₂
      change (∀ x < v₁, mem₂ x = mem₁ x) at hf₂
      change ListAt mem₂ v₁ (digits h L (unsignedVal mem₁ a h L + unsignedVal mem₁ heap h L + 0)) at hl₂
      have haddval := addCarry_value hl₂
      have hv₂w : v₂ < 2 ^ w := by omega
      refine runs_ret_le (v := v₂) (by eval_expr) ?_ ?_
      · refine ⟨by change v₂ = heap + 2 * L; omega, ?_⟩
        change heap ≤ v₂ ∧ v₂ ≤ heap + 2 * L ∧ (∀ x < heap, mem₂ x = mem x) ∧
          ZeroFrom mem₂ v₂ ∧ Valid mem₂ (heap + L) h L ∧
            intVal mem₂ (heap + L) h L = wrap h L (intVal mem a h L - intVal mem d h L)
        refine ⟨by omega, by omega, ?_, hz₂, he₁ ▸ haddval.1, ?_⟩
        · intro x hx
          rw [hf₂ x (by omega), hf₁ x hx]
        · rw [← he₁, haddval.2, hsourceval, hnegval.2]
          simp only [Int.natCast_zero, add_zero, wrap_add_wrap, sub_eq_add_neg]
      · simp only [subtractContract, negateContract, negateCarryContract,
          addContract, addCarryContract, heapContract, List.getD_cons_zero,
          List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.Num
