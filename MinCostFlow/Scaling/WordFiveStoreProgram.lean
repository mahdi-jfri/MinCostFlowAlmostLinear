module

public import MinCostFlow.Scaling.WordFiveProgram
import WordRAM.Tactic

/-!
# Writing a circulation record inside a reserved array

Zero-capacity pruning compacts records into a reserved array while writing
retained indices in a separate reserved block. The five-word writer therefore
needs its direct memory-frame specification as well as its fresh-heap one.
This file proves that same machine body writes the supplied words and changes
only its five destination cells, without requiring the rest of memory to be zero.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The five destination cells fit. This is an in-place record-write contract. -/
def wordFiveStoreContract (w : ℕ) : Contract where
  pre args _ := ∃ a b c d e dst, args = [a, b, c, d, e, dst] ∧ dst + 5 < 2 ^ w
  post args mem out mem' := out = heapArg args + 5 ∧
    ListAt mem' (heapArg args)
      [args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0] ∧
    ∀ x, x < heapArg args ∨ heapArg args + 5 ≤ x → mem' x = mem x
  cost _ _ := 40

/-- The existing five-word body also meets the direct store contract,
with no zero-tail premise and with an exact frame on all other cells. -/
theorem wordFiveStore_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b wordFiveModule) : MeetsContract w p b (wordFiveStoreContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, b, c, d, e, dst, rfl, hspace⟩ := hpre
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
  refine runs_ret_le (v := dst + 5) (by eval_expr) ?_ ?_
  · change dst + 5 = dst + 5 ∧ ListAt _ dst [a, b, c, d, e] ∧
      ∀ x, x < dst ∨ dst + 5 ≤ x → _ = mem x
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by change i < 5 at hi; omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := omega) only [Nat.add_zero, Function.update_of_ne,
          Function.update_self, List.getElem_cons_zero, List.getElem_cons_succ]
    · intro x hx
      rcases hx with hx | hx <;>
        simp (disch := omega) only [Function.update_of_ne, startState]
  · simp only [wordFiveStoreContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

/-- All direct-store preconditions hold together for arbitrary record words. -/
theorem exists_wordFiveStore_pre (a b c d e : ℕ) :
    ∃ w, (∀ x ∈ [a, b, c, d, e, 0], x < 2 ^ w) ∧
      (wordFiveStoreContract w).pre [a, b, c, d, e, 0] (fun _ => 0) := by
  obtain ⟨w, hwords, hpre⟩ := exists_wordFive_pre a b c d e
  exact ⟨w, hwords, a, b, c, d, e, 0, rfl, hpre.2.2⟩

end MinCostFlow.Scaling.Machine
