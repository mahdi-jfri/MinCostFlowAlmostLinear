module

public import WordRAM.Logic

/-!
# A loop rule that carries a potential

The walk over the input batch pays for a split of the tree from a potential: one step may cost
more than its share of the budget, if the potential drops by the excess. The loop rules of the
library bound the cost by a budget `rem` alone. `runs_loop_pot` adds a potential `pot`: if each
step costs at most the drop of `rem + pot`, the whole loop costs at most `rem + pot` at the start
minus `pot` at the end. `runs_seq_loop_pot_le` is the same rule for a loop followed by more code,
in the form of the `runs_seq_*_le` rules.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM

/-- **Loop rule with a potential.** If the invariant holds, the test evaluates to `condVal`, the
loop ends with `Q` when the test is `0`, and each step keeps the invariant, lowers the measure `m`
and costs at most the drop of `rem + pot`, then the loop ends with `Q`, and its cost plus the
final potential is at most `rem + pot` at the start. -/
theorem runs_loop_pot {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {Inv Q : State → Prop} {m rem pot condVal : State → ℕ}
    (hcond : ∀ st, Inv st → e.eval w st = some (condVal st))
    (hexit : ∀ st, Inv st → condVal st = 0 → Q st ∧ e.size + 1 ≤ rem st)
    (hstep : ∀ st, Inv st → condVal st ≠ 0 → ∃ st' c, Runs w p ω body st .normal st' c ∧
      Inv st' ∧ m st' < m st ∧ e.size + c + rem st' + pot st' + 1 ≤ rem st + pot st) :
    ∀ st, Inv st → ∃ st' c, Runs w p ω (.loop e body) st .normal st' c ∧ Q st' ∧
      c + pot st' ≤ rem st + pot st := by
  suffices h : ∀ k st, m st ≤ k → Inv st → ∃ st' c, Runs w p ω (.loop e body) st .normal st' c ∧
      Q st' ∧ c + pot st' ≤ rem st + pot st from
    fun st hInv => h (m st) st (Nat.le_refl _) hInv
  intro k
  induction k with
  | zero =>
    intro st hm hInv
    by_cases hv : condVal st = 0
    · obtain ⟨hq, hrem⟩ := hexit st hInv hv
      exact ⟨st, e.size + 1, runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond st hInv, rfl, rfl, rfl⟩), hq,
        by omega⟩
    · obtain ⟨st₁, c₁, -, -, hm₁, -⟩ := hstep st hInv hv
      omega
  | succ k ih =>
    intro st hm hInv
    by_cases hv : condVal st = 0
    · obtain ⟨hq, hrem⟩ := hexit st hInv hv
      exact ⟨st, e.size + 1, runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond st hInv, rfl, rfl, rfl⟩), hq,
        by omega⟩
    · obtain ⟨st₁, c₁, hr₁, hInv₁, hm₁, hc₁⟩ := hstep st hInv hv
      obtain ⟨st₂, c₂, hr₂, hq₂, hc₂⟩ := ih st₁ (by omega) hInv₁
      exact ⟨st₂, e.size + c₁ + c₂ + 1, runs_loop_iff.mpr
        (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hcond st hInv, hv, hr₁, hr₂, rfl⟩)), hq₂,
        by omega⟩

/-- **A loop with a potential, then more code.** The rest of the code learns the cost `c₁` of the
loop and its bound `c₁ + pot st₁ ≤ rem st + pot st`. -/
theorem runs_seq_loop_pot_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body s : Stmt}
    {Inv Q : State → Prop} {rem pot : State → ℕ} {st : State} {k T : ℕ}
    {Qf : Outcome → State → Prop}
    (hloop : ∀ st, Inv st → ∃ st' c, Runs w p ω (.loop e body) st .normal st' c ∧ Q st' ∧
      c + pot st' ≤ rem st + pot st)
    (hInv : Inv st)
    (hrest : ∀ st₁ c₁, Q st₁ → c₁ + pot st₁ ≤ rem st + pot st →
      ∃ o st' c₂, Runs w p ω s st₁ o st' c₂ ∧ Qf o st' ∧ (k + c₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.loop e body) s) st o st' c ∧ Qf o st' ∧ k + c ≤ T := by
  obtain ⟨st₁, c₁, hr₁, hq₁, hc₁⟩ := hloop st hInv
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest st₁ c₁ hq₁ hc₁
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq,
    by omega⟩

end MinCostFlow.SparseCore.Program.Read
