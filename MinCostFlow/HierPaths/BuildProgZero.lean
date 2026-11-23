module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Zeroing a block of words

The shortcut of a routed walk (`pathProc`) needs the position array to be `0` at the vertices
of the walk, and it leaves the array as it found it. So the builder zeroes the array once, before
the first walk. `zeroProc`, called with `[dst, n]`, writes `0` to `dst, …, dst + n − 1` and
changes no other cell (`zeroProc_meetsContract`). The cost is `15 n + 12`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- `for r3 in [0, n): mem[dst + r3] := 0`; return `0`. -/
def zeroProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1) (.store (.bin .add (.reg 0) (.reg 3)) (.const 0)))
    (.ret (.const 0))

/-- The contract of `zeroProc`. -/
def zeroContract (w : ℕ) : Contract where
  pre args _ := ∃ dst n, args = [dst, n] ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem _ mem' := ∃ dst n, args = [dst, n] ∧ (∀ j < n, mem' (dst + j) = 0) ∧
    ∀ x, (x < dst ∨ dst + n ≤ x) → mem' x = mem x
  cost args _ := 15 * args.getD 1 0 + 12

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The zeroing loop. -/
theorem zero_triple {w n dst : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hdn : dst + n < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = dst ∧ st.regs 1 = n ∧ st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 1) (.store (.bin .add (.reg 0) (.reg 3)) (.const 0)))
      (normalPost fun st' => (∀ j < n, st'.mem (dst + j) = 0) ∧
        ∀ x, (x < dst ∨ dst + n ≤ x) → st'.mem x = mem₀ x)
      (fun _ => 15 * n + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 0) (.reg 3)) (.const 0))
    (P := fun st => st.regs 0 = dst ∧ st.regs 1 = n ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = dst ∧ st.regs 1 = n ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = 0) ∧
      (∀ x, (x < dst ∨ dst + i ≤ x) → st.mem x = mem₀ x))
    5 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      exact ⟨by simp [h0], by simp [h1], by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = n := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h3, hz, hf⟩
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) 0 }, 5, ?_, ?_,
        by simp⟩
      · have hdw : dst + i < 2 ^ w := by omega
        refine runs_store_iff.mpr ⟨dst + i, 0, ?_, by eval_expr, rfl, rfl, by simp⟩
        simp [Expr.eval, h0, h3, hdw]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · rw [hji, Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact hz j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hf x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨_, _, _, hz, hf⟩ := hpost
      exact ⟨hz, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`zeroProc` meets its contract.** -/
theorem zeroProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some zeroProc) :
    MeetsContract w p f (zeroContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨dst, n, rfl, hdn, hw⟩
  refine runs_start_le ?_
  dsimp only [zeroProc]
  refine runs_seq_triple_le (zero_triple p mem hw hdn)
    ⟨by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ ⟨hz, hf⟩
  refine runs_ret_le (v := 0) ?_ ⟨dst, n, rfl, hz, hf⟩ ?_
  · eval_expr
  · simp only [zeroContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const]
    omega

end MinCostFlow.HierPaths
