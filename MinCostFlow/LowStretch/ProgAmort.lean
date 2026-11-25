module

public import WordRAM.Model
public import WordRAM.Contract
public import WordRAM.Exec
public import WordRAM.Expr
public import WordRAM.Memory
public import WordRAM.Logic
public import WordRAM.Layout
public import WordRAM.CopyWords
public import WordRAM.Entry
public import WordRAM.Tactic
public import WordRAM.DataStructure
public import WordRAM.LinkDefs
public import WordRAM.Link
public import WordRAM.Coins
public import WordRAM.CoinsFresh
public import WordRAM.ProbRuns
public import WordRAM.Prob
public import WordRAM.ProbBridge

/-!
# Loops with an amortized cost

The contracts of `WordRAM` bound the cost of a call by a function of the state where it starts.
A petal search may stop early, and its real cost is the drop of a potential from its start to its
end, which is not known at the start. So we reason about runs for one fixed bit stream `ω`.

`runs_loop_amort` is the loop rule of `Triple.loop_inv` in this form. The ghost value `a` has a
measure `m a` that drops at each step and a budget `rem a`. When the loop stops, the final
predicate `Fin` gives a number `r` (what is left of the budget, such as the final potential), and
the cost of the run plus `r` is at most the budget of the start.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- **The amortized loop rule.** -/
theorem runs_loop_amort {w : ℕ} {p : Program} {ω : ℕ → Bool} {α : Type*} {e : Expr} {body : Stmt}
    {Inv : α → State → Prop} {Fin : Outcome → State → ℕ → Prop}
    (m rem : α → ℕ) {condVal : State → ℕ}
    (hcond : ∀ a st, Inv a st → e.eval w st = some (condVal st))
    (hexit : ∀ a st, Inv a st → condVal st = 0 → ∃ r, Fin .normal st r ∧ e.size + 1 + r ≤ rem a)
    (hstep : ∀ a st, Inv a st → condVal st ≠ 0 →
      ∃ o st₁ c₁, Runs w p ω body st o st₁ c₁ ∧
        match o with
        | .returned u => ∃ r, Fin (.returned u) st₁ r ∧ e.size + c₁ + 1 + r ≤ rem a
        | .normal => ∃ a', Inv a' st₁ ∧ m a' < m a ∧ e.size + c₁ + rem a' + 1 ≤ rem a)
    (a₀ : α) (st : State) (hI : Inv a₀ st) :
    ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ ∃ r, Fin o st' r ∧ c + r ≤ rem a₀ := by
  suffices ∀ k a st, m a ≤ k → Inv a st →
      ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ ∃ r, Fin o st' r ∧ c + r ≤ rem a from
    this (m a₀) a₀ st le_rfl hI
  intro k
  induction k with
  | zero =>
    intro a st hm hInv
    by_cases hv : condVal st = 0
    · obtain ⟨r, hq, hrem⟩ := hexit a st hInv hv
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond a st hInv, rfl, rfl, rfl⟩), r, hq, by omega⟩
    · obtain ⟨o₁, st₁, c₁, hr₁, hq₁⟩ := hstep a st hInv hv
      cases o₁ with
      | returned u =>
        obtain ⟨r, hq, hrem⟩ := hq₁
        exact ⟨.returned u, st₁, e.size + c₁ + 1,
          runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hcond a st hInv, hv, hr₁, rfl,
            rfl⟩)), r, hq, by omega⟩
      | normal =>
        obtain ⟨_, _, hm', _⟩ := hq₁
        omega
  | succ k ih =>
    intro a st hm hInv
    by_cases hv : condVal st = 0
    · obtain ⟨r, hq, hrem⟩ := hexit a st hInv hv
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond a st hInv, rfl, rfl, rfl⟩), r, hq, by omega⟩
    · obtain ⟨o₁, st₁, c₁, hr₁, hq₁⟩ := hstep a st hInv hv
      cases o₁ with
      | returned u =>
        obtain ⟨r, hq, hrem⟩ := hq₁
        exact ⟨.returned u, st₁, e.size + c₁ + 1,
          runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hcond a st hInv, hv, hr₁, rfl,
            rfl⟩)), r, hq, by omega⟩
      | normal =>
        obtain ⟨a', hInv', hm', hrem⟩ := hq₁
        obtain ⟨o₂, st₂, c₂, hr₂, r, hq₂, hc₂⟩ := ih a' st₁ (by omega) hInv'
        exact ⟨o₂, st₂, e.size + c₁ + c₂ + 1,
          runs_loop_iff.mpr
            (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hcond a st hInv, hv, hr₁, hr₂, rfl⟩)),
          r, hq₂, by omega⟩

end MinCostFlow.LowStretch
