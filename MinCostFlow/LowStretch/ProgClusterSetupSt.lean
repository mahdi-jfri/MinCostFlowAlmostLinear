module

public import MinCostFlow.LowStretch.ProgClusterSetupT1

/-!
# The setup of a cluster: the stores of the block

The setup ends with the stores `mem[h + i] := e` of the block at `h` (`suStores`). This file
proves a general run lemma for such a list of stores (`runs_suStores_le`), in the style of
`runs_assigns_le`: when the offsets increase, every expression evaluates to its value on every
memory that agrees with the first one outside the written cells, and these cells are words, the
stores leave each value at its cell and change no other cell.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The cost of the stores `l`. -/
def suStCost (l : List (ℕ × Expr)) : ℕ :=
  (l.map fun q => (Expr.bin .add (.reg 2) (.const q.1)).size + q.2.size + 2).sum

/-- **The stores of the block.** -/
theorem runs_suStores_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {Q : Outcome → State → Prop} {T hh : ℕ} {M : ℕ → ℕ} {regs : ℕ → ℕ} (f : ℕ → ℕ) :
    ∀ (l : List (ℕ × Expr)) (st : State) (k : ℕ),
      l.Pairwise (fun a b => a.1 < b.1) → st.regs = regs → regs 2 = hh →
      (∀ q ∈ l, q.1 < 51) → hh + 51 < 2 ^ w →
      (∀ a, (a < hh ∨ hh + 51 ≤ a) → st.mem a = M a) →
      (∀ q ∈ l, ∀ st' : State, st'.regs = regs → (∀ a, (a < hh ∨ hh + 51 ≤ a) → st'.mem a = M a) →
        q.2.eval w st' = some (f q.1)) →
      (∀ st' : State, st'.regs = regs → (∀ q ∈ l, st'.mem (hh + q.1) = f q.1) →
        (∀ a, (∀ q ∈ l, a ≠ hh + q.1) → st'.mem a = st.mem a) →
        ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ k + suStCost l + c ≤ T) →
      ∃ o st' c, Runs w p ω (suStores l s) st o st' c ∧ Q o st' ∧ k + c ≤ T
  | [], st, k, _, hr, _, _, _, _, _, hrest => by
      obtain ⟨o, st', c, h1, h2, h3⟩ := hrest st hr (by simp) (fun _ _ => rfl)
      exact ⟨o, st', c, h1, h2, by simpa [suStCost] using h3⟩
  | (i, e) :: l, st, k, hp, hr, h2, hl, hw, hM, hev, hrest => by
      rw [List.pairwise_cons] at hp
      have hi : i < 51 := hl (i, e) (by simp)
      have ha : (Expr.bin .add (.reg 2) (.const i)).eval w st = some (hh + i) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by rw [hr, h2])) (Expr.eval_const (by omega))
          (by omega)
      have he : e.eval w st = some (f i) := hev (i, e) (by simp) st hr hM
      refine runs_seq_store_le ha he ?_
      refine runs_suStores_le f l _ _ hp.2 hr h2 (fun q hq => hl q (by simp [hq])) hw
        (fun a ha' => ?_) (fun q hq st' h1 h3 => hev q (by simp [hq]) st' h1 h3)
        (fun st' h1 h3 h4 => ?_)
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hM a ha'
      · have v1 : ∀ q ∈ (i, e) :: l, st'.mem (hh + q.1) = f q.1 := by
          intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · rw [h4 _ (fun q hq' => by have := hp.1 q hq'; dsimp only at this ⊢; omega)]
            simp
          · exact h3 q hq
        have v2 : ∀ a, (∀ q ∈ (i, e) :: l, a ≠ hh + q.1) → st'.mem a = st.mem a := by
          intro a ha'
          rw [h4 a (fun q hq => ha' q (by simp [hq]))]
          dsimp only
          rw [Function.update_of_ne (ha' (i, e) (by simp))]
        obtain ⟨o, st'', c, r1, r2, r3⟩ := hrest st' h1 v1 v2
        refine ⟨o, st'', c, r1, r2, ?_⟩
        simp only [suStCost, List.map_cons, List.sum_cons] at r3 ⊢
        omega

end MinCostFlow.LowStretch
