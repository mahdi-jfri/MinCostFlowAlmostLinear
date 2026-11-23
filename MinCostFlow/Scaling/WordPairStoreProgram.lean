module

public import MinCostFlow.Scaling.WordPairProgram
import WordRAM.Tactic

/-!
# Writing a signed pair inside a reserved table

Restoring removed edge slots writes canonical signed pairs to saved indices.
The pair writer also works inside an existing table. This file proves its
exact two-cell frame without a zero-tail premise.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The two destination cells fit. This is an in-place record-write contract. -/
def wordPairStoreContract (w : ℕ) : Contract where
  pre args _ := ∃ a b dst, args = [a, b, dst] ∧ dst + 2 < 2 ^ w
  post args mem out mem' := out = heapArg args + 2 ∧
    ListAt mem' (heapArg args)
      [args.getD 0 0, args.getD 1 0] ∧
    ∀ x, x < heapArg args ∨ heapArg args + 2 ≤ x → mem' x = mem x
  cost _ _ := 14

/-- The existing two-word body also meets the direct store contract,
with no zero-tail premise and with an exact frame on all other cells. -/
theorem wordPairStore_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b wordPairModule) : MeetsContract w p b (wordPairStoreContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, b, dst, rfl, hspace⟩ := hpre
  have ha : a < 2 ^ w := hwords _ (by simp)
  have hb : b < 2 ^ w := hwords _ (by simp)
  apply runs_start_le
  unfold wordPairBody
  wram_step
  wram_step
  refine runs_ret_le (v := dst + 2) (by eval_expr) ?_ ?_
  · change dst + 2 = dst + 2 ∧ ListAt _ dst [a, b] ∧
      ∀ x, x < dst ∨ dst + 2 ≤ x → _ = mem x
    refine ⟨rfl, ?_, ?_⟩
    · intro i hi
      have hi' : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
      rcases hi' with rfl | rfl <;>
        simp (disch := omega) only [Nat.add_zero, Function.update_of_ne,
          Function.update_self, List.getElem_cons_zero, List.getElem_cons_succ]
    · intro x hx
      rcases hx with hx | hx <;>
        simp (disch := omega) only [Function.update_of_ne, startState]
  · simp only [wordPairStoreContract, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

/-- The direct store premises hold together for every pair of words. -/
theorem exists_wordPairStore_pre (a b : ℕ) :
    ∃ w, (∀ x ∈ [a, b, 0], x < 2 ^ w) ∧
      (wordPairStoreContract w).pre [a, b, 0] (fun _ => 0) := by
  let w := a + b + 3
  have hw : a + b + 3 < 2 ^ w := Nat.lt_two_pow_self
  refine ⟨w, ?_, a, b, 0, rfl, by omega⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
