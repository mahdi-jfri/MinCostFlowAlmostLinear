module

public import WordRAM.Logic
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Copying a block of words

`cpBody` copies `n` words from `src` to `dst`, for two blocks that do not overlap. It changes no
other cell. Its cost is at most `17 n + 12`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- Arguments `[src, n, dst]`. Register `3` is the loop index. -/
def cpBody : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 2) (.reg 3))
      (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.const 0)

theorem cpBody_noRand : cpBody.NoRand := by
  simp [cpBody, forRange, forUp, Stmt.NoRand]

/-- The contract of the copy. -/
def cpC (w : ℕ) : Contract where
  pre args _ := ∃ src n dst, args = [src, n, dst] ∧ (src + n ≤ dst ∨ dst + n ≤ src) ∧
    dst + n < 2 ^ w ∧ src + n < 2 ^ w
  post args mem _ mem' := ∀ src n dst, args = [src, n, dst] →
    (∀ i < n, mem' (dst + i) = mem (src + i)) ∧ ∀ x, (x < dst ∨ dst + n ≤ x) → mem' x = mem x
  cost args _ := 17 * args.getD 1 0 + 12

private theorem cpLoop {w src n dst : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hw : 1 < 2 ^ w) (hb : dst + n < 2 ^ w) (hb' : src + n < 2 ^ w)
    (hs : src + n ≤ dst ∨ dst + n ≤ src) :
    Triple w p (fun st => st = startState [src, n, dst] mem pos)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 3))
          (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st => (∀ i < n, st.mem (dst + i) = mem (src + i)) ∧
        ∀ x, (x < dst ∨ dst + n ≤ x) → st.mem x = mem x)
      (fun _ => 17 * n + 7) := by
  have hl := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.reg 3))
      (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st = startState [src, n, dst] mem pos)
    (Inv := fun i st => st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧
      st.regs 3 = i ∧ (∀ j < i, st.mem (dst + j) = mem (src + j)) ∧
      (∀ x, (x < dst ∨ dst + i ≤ x) → st.mem x = mem x))
    8 0 n (Nat.zero_le n) hw (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      simp [startState])
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 := hi.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω hst
      rcases hst with ⟨h0, h1, h2, h3, hcopy, hframe⟩
      have hread : st.mem (src + i) = mem (src + i) := hframe _ (by omega)
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, h3⟩
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simp
        · intro j hj
          dsimp only
          by_cases he : j = i
          · subst j
            simp [hread]
          · rw [Function.update_of_ne (by omega)]
            exact hcopy j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x (by omega)
      · wram_cost)
  refine hl.conseq (fun _ he => he) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.2.2.2.1, fun x hx => ho.2.2.2.2.2 x hx⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **The copy.** -/
theorem cp_meetsContract {w b : ℕ} {p : Program} (hw : 1 < 2 ^ w)
    (hp : p.HasAt b [cpBody]) : MeetsContract w p b (cpC w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω _ hpre
  rcases hpre with ⟨src, n, dst, rfl, hs, hb, hb'⟩
  apply runs_start_le
  unfold cpBody
  refine runs_seq_triple_le (cpLoop p mem pos hw hb hb' hs) rfl ?_
  intro st ⟨hc, hf⟩
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro src' n' dst' he
    simp only [List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨hc, hf⟩
  · simp only [cpC, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const]
    omega

end MinCostFlow.LowStretch
