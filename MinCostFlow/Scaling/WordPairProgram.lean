module

public import WordRAM.Layout
import WordRAM.Tactic

/-!
# Writing a two-word integer representation

The problem statement encodes a signed integer by a sign word and its
magnitude. This small helper allocates and writes two supplied words. Its
callers prove that the two words are the canonical `encodeInt` of their
result. The helper returns exactly `heap+2`, preserves the heap frame, leaves
the fresh tail zero, has no random instructions, and costs 14 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[first,second,heap]`. -/
def wordPairBody : Stmt :=
  .store (.reg 2) (.reg 0) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 1) ;;
  .ret (.bin .add (.reg 2) (.const 2))

/-- The two-word writer occupies one procedure slot. -/
def wordPairModule : List Stmt := [wordPairBody]

/-- The writer stores the supplied pair at the old heap. -/
def wordPairContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ first second h, args = [first, second, h])
    (fun args _ mem' => ListAt mem' (heapArg args) [args.getD 0 0, args.getD 1 0])
    (fun _ _ => 14) (fun _ _ => 2)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args + 2 }

/-- Writing a pair uses no random instructions. -/
theorem wordPairBody_noRand : wordPairBody.NoRand := by
  simp only [wordPairBody, Stmt.NoRand, and_self]

/-- The two-word writer meets its allocation and exact-value contract in
14 steps, uniformly over the random tape. -/
theorem wordPair_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b wordPairModule) : MeetsContract w p b (wordPairContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨first, second, heap, rfl⟩, hzero, hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap + 2 < 2 ^ w at hspace
  have hfirst : first < 2 ^ w := hwords first (by simp)
  have hsecond : second < 2 ^ w := hwords second (by simp)
  have hheap : heap < 2 ^ w := hwords heap (by simp)
  apply runs_start_le
  unfold wordPairBody
  wram_step
  wram_step
  refine runs_ret_le (v := heap + 2) (by eval_expr) ?_ ?_
  · change (heap ≤ heap + 2 ∧ heap + 2 ≤ heap + 2 ∧
      (∀ x < heap, Function.update (Function.update mem heap first) (heap + 1) second x = mem x) ∧
      ZeroFrom (Function.update (Function.update mem heap first) (heap + 1) second) (heap + 2) ∧
      ListAt (Function.update (Function.update mem heap first) (heap + 1) second) heap [first, second]) ∧
      heap + 2 = heap + 2
    refine ⟨⟨by omega, le_rfl, ?_, ?_, ?_⟩, rfl⟩
    · intro x hx
      rw [Function.update_of_ne (by omega : x ≠ heap + 1), Function.update_of_ne (by omega : x ≠ heap)]
    · intro x hx
      rw [Function.update_of_ne (by omega : x ≠ heap + 1), Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · intro i hi
      have hic : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
      rcases hic with rfl | rfl
      · simp only [Nat.add_zero, Function.update_of_ne (by omega : heap ≠ heap + 1),
          Function.update_self, List.getElem_cons_zero]
      · simp only [Function.update_self, List.getElem_cons_succ, List.getElem_cons_zero]
  · simp only [wordPairContract, heapContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

end MinCostFlow.Scaling.Machine
