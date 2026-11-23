module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Writing one circulation edge record

The solver's circulation layout uses five words per edge: tail, head,
capacity, cost sign, and cost magnitude. This helper writes one supplied
record to fresh memory and returns the next heap pointer. It preserves
the old heap frame and the fresh zero tail, uses no random instruction,
and costs at most 40 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[tail,head,capacity,costSign,costMagnitude,heap]`. -/
def wordFiveBody : Stmt :=
  .store (.reg 5) (.reg 0) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.reg 2) ;;
  .store (.bin .add (.reg 5) (.const 3)) (.reg 3) ;;
  .store (.bin .add (.reg 5) (.const 4)) (.reg 4) ;;
  .ret (.bin .add (.reg 5) (.const 5))

/-- A five-word record writer occupies one procedure slot. -/
def wordFiveModule : List Stmt := [wordFiveBody]

/-- The supplied words become one fresh record. -/
def wordFiveContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ a b c d e h, args = [a, b, c, d, e, h])
    (fun args _ mem' => ListAt mem' (heapArg args)
      [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0])
    (fun _ _ => 40) (fun _ _ => 5)
  { C with post := fun args mem out mem' => C.post args mem out mem' ∧ out = heapArg args + 5 }

/-- Writing one edge record uses no random instructions. -/
theorem wordFiveBody_noRand : wordFiveBody.NoRand := by
  simp only [wordFiveBody, Stmt.NoRand, and_self]

/-- The record writer meets its exact allocation, value, frame, and cost
contract for all five input words. -/
theorem wordFive_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b wordFiveModule) : MeetsContract w p b (wordFiveContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, b, c, d, e, heap, rfl⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 5 < 2 ^ w at hspace
  have ha : a < 2 ^ w := hwords _ (by simp)
  have hb : b < 2 ^ w := hwords _ (by simp)
  have hc : c < 2 ^ w := hwords _ (by simp)
  have hd : d < 2 ^ w := hwords _ (by simp)
  have he : e < 2 ^ w := hwords _ (by simp)
  apply runs_start_le
  unfold wordFiveBody
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v := heap + 5) (by eval_expr) ?_ ?_
  · change (heap ≤ heap + 5 ∧ heap + 5 ≤ heap + 5 ∧
      (∀ x < heap, _ = mem x) ∧ ZeroFrom _ (heap + 5) ∧ ListAt _ heap [a, b, c, d, e]) ∧
      heap + 5 = heap + 5
    refine ⟨⟨by omega, le_rfl, ?_, ?_, ?_⟩, rfl⟩
    · intro x hx
      simp only [Function.update_of_ne (by omega : x ≠ heap + 4),
        Function.update_of_ne (by omega : x ≠ heap + 3),
        Function.update_of_ne (by omega : x ≠ heap + 2),
        Function.update_of_ne (by omega : x ≠ heap + 1),
        Function.update_of_ne (by omega : x ≠ heap), startState]
    · intro x hx
      simpa only [Function.update_of_ne (by omega : x ≠ heap + 4),
        Function.update_of_ne (by omega : x ≠ heap + 3),
        Function.update_of_ne (by omega : x ≠ heap + 2),
        Function.update_of_ne (by omega : x ≠ heap + 1),
        Function.update_of_ne (by omega : x ≠ heap), startState] using hzero x (by omega)
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by change i < 5 at hi; omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
        simp only [Nat.add_zero, Function.update_self,
          Function.update_of_ne (by omega : heap ≠ heap + 4),
          Function.update_of_ne (by omega : heap ≠ heap + 3),
          Function.update_of_ne (by omega : heap ≠ heap + 2),
          Function.update_of_ne (by omega : heap ≠ heap + 1),
          Function.update_of_ne (by omega : heap + 1 ≠ heap + 4),
          Function.update_of_ne (by omega : heap + 1 ≠ heap + 3),
          Function.update_of_ne (by omega : heap + 1 ≠ heap + 2),
          Function.update_of_ne (by omega : heap + 2 ≠ heap + 4),
          Function.update_of_ne (by omega : heap + 2 ≠ heap + 3),
          Function.update_of_ne (by omega : heap + 3 ≠ heap + 4),
          List.getElem_cons_zero, List.getElem_cons_succ]
  · simp only [wordFiveContract, heapContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

/-- Arbitrary record words can satisfy the writer's argument and fresh-heap
preconditions together at a sufficiently large width. -/
theorem exists_wordFive_pre (a b c d e : ℕ) :
    ∃ w, (∀ x ∈ [a, b, c, d, e, 0], x < 2 ^ w) ∧
      (wordFiveContract w).pre [a, b, c, d, e, 0] (fun _ => 0) := by
  let w := wordSize 1 [a + b + c + d + e + 7]
  have hlarge : a + b + c + d + e + 7 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, ⟨a, b, c, d, e, 0, rfl⟩, (fun _ _ => rfl), ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · change 0 + 5 < 2 ^ w
    omega

end MinCostFlow.Scaling.Machine
