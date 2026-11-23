module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# The position array: clearing it

The linear shortcut of `BuildProgErase.lean` writes into a position array `P` at the vertices of
the walk and clears these cells before it returns (pass 3, `posClear`). `posClearProc`, called
with `[vs, n, P]`, where the `n` vertices of the walk are the words `vs, …, vs + n − 1`, sets
the cell `P + v` to `0` for each of these vertices `v`, and changes no other cell
(`posClearProc_meetsContract`). The cells `P + v` lie above the list of vertices. The cost is
`17 n + 12`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- `for r3 in [0, n): mem[P + mem[vs + r3]] := 0`; return `0`. -/
def posClearProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1)
      (.store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 3)))) (.const 0)))
    (.ret (.const 0))

/-- The contract of `posClearProc`. -/
def posClearContract (w : ℕ) : Contract where
  pre args mem := ∃ vs n P, args = [vs, n, P] ∧ vs + n < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ j < n, vs + n ≤ P + mem (vs + j) ∧ P + mem (vs + j) < 2 ^ w
  post args mem _ mem' := ∃ vs n P, args = [vs, n, P] ∧
    (∀ j < n, mem' (P + mem (vs + j)) = 0) ∧
    ∀ x, (∀ j < n, x ≠ P + mem (vs + j)) → mem' x = mem x
  cost args _ := 17 * args.getD 1 0 + 12

/-- The clearing loop. -/
theorem posClear_triple {w vs n P : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hvn : vs + n < 2 ^ w)
    (hcell : ∀ j < n, vs + n ≤ P + mem₀ (vs + j) ∧ P + mem₀ (vs + j) < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = vs ∧ st.regs 1 = n ∧ st.regs 2 = P ∧ st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 3)))) (.const 0)))
      (normalPost fun st' => (∀ j < n, st'.mem (P + mem₀ (vs + j)) = 0) ∧
        ∀ x, (∀ j < n, x ≠ P + mem₀ (vs + j)) → st'.mem x = mem₀ x)
      (fun _ => 17 * n + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 3)))) (.const 0))
    (P := fun st => st.regs 0 = vs ∧ st.regs 1 = n ∧ st.regs 2 = P ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = vs ∧ st.regs 1 = n ∧ st.regs 2 = P ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (P + mem₀ (vs + j)) = 0) ∧
      (∀ x, (∀ j < i, x ≠ P + mem₀ (vs + j)) → st.mem x = mem₀ x))
    8 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun x _ => by simp [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = n := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, hz, hf⟩
      have hvsi : st.mem (vs + i) = mem₀ (vs + i) := by
        apply hf
        intro j hj
        have := (hcell j (by omega)).1
        omega
      obtain ⟨hlo, hhi⟩ := hcell i hilt
      refine ⟨.normal, { st with mem := Function.update st.mem (P + mem₀ (vs + i)) 0 },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr ⟨P + mem₀ (vs + i), 0, ?_, by eval_expr, rfl, rfl, by simp⟩
        have hvi : vs + i < 2 ^ w := by omega
        have hmw : mem₀ (vs + i) < 2 ^ w := by omega
        simp [Expr.eval, h0, h2, h3, hvi, hvsi, hhi]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : P + mem₀ (vs + j) = P + mem₀ (vs + i)
          · rw [hji, Function.update_self]
          · rw [Function.update_of_ne hji]
            exact hz j (by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
              · exact h
              · exact absurd (by rw [h]) hji)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (hx i (by omega))]
          exact hf x fun j hj => hx j (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨_, _, _, _, hz, hf⟩ := hpost
      exact ⟨hz, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`posClearProc` meets its contract.** -/
theorem posClearProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some posClearProc) :
    MeetsContract w p f (posClearContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨vs, n, P, rfl, hvn, hw, hcell⟩
  refine runs_start_le ?_
  dsimp only [posClearProc]
  refine runs_seq_triple_le (posClear_triple p mem hw hvn hcell)
    ⟨by simp [startState], by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ ⟨hz, hf⟩
  refine runs_ret_le (v := 0) ?_ ⟨vs, n, P, rfl, hz, hf⟩ ?_
  · eval_expr
  · simp only [posClearContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const]
    omega

/-! ### Pass 1: writing the positions -/

/-- The memory after the first `i` steps of pass 1: cell `P + mem₀ (vs + j)` gets `n − 1 − j`
for `j = 0, …, i − 1` in turn, so a later visit overwrites an earlier one. -/
def fillMem (mem₀ : ℕ → ℕ) (vs n P : ℕ) : ℕ → (ℕ → ℕ)
  | 0 => mem₀
  | i + 1 => Function.update (fillMem mem₀ vs n P i) (P + mem₀ (vs + i)) (n - 1 - i)

/-- Pass 1 does not touch the cells below `vs + n`, where the list of vertices is. -/
theorem fillMem_below {mem₀ : ℕ → ℕ} {vs n P : ℕ}
    (hcell : ∀ j < n, vs + n ≤ P + mem₀ (vs + j)) :
    ∀ i ≤ n, ∀ x < vs + n, fillMem mem₀ vs n P i x = mem₀ x
  | 0, _, _, _ => rfl
  | i + 1, hi, x, hx => by
    simp only [fillMem]
    rw [Function.update_of_ne (by have := hcell i (by omega); omega)]
    exact fillMem_below hcell i (by omega) x hx

/-- `for r3 in [0, n): mem[P + mem[vs + r3]] := n − 1 − r3`; return `0`. -/
def posFillProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 1)
      (.store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 3))))
        (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 3))))
    (.ret (.const 0))

/-- The contract of `posFillProc`. -/
def posFillContract (w : ℕ) : Contract where
  pre := (posClearContract w).pre
  post args mem _ mem' := ∃ vs n P, args = [vs, n, P] ∧ mem' = fillMem mem vs n P n
  cost args _ := 22 * args.getD 1 0 + 12

/-- The writing loop. -/
theorem posFill_triple {w vs n P : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 1 < 2 ^ w) (hvn : vs + n < 2 ^ w)
    (hcell : ∀ j < n, vs + n ≤ P + mem₀ (vs + j) ∧ P + mem₀ (vs + j) < 2 ^ w) :
    Triple w p (fun st => st.regs 0 = vs ∧ st.regs 1 = n ∧ st.regs 2 = P ∧ st.mem = mem₀)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 3))))
          (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 3))))
      (normalPost fun st' => st'.mem = fillMem mem₀ vs n P n)
      (fun _ => 22 * n + 7) := by
  have hbelow := fillMem_below (mem₀ := mem₀) (vs := vs) (n := n) (P := P)
    (fun j hj => (hcell j hj).1)
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 3))))
      (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 3)))
    (P := fun st => st.regs 0 = vs ∧ st.regs 1 = n ∧ st.regs 2 = P ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = vs ∧ st.regs 1 = n ∧ st.regs 2 = P ∧ st.regs 3 = i ∧
      st.mem = fillMem mem₀ vs n P i)
    12 0 n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h2, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      exact ⟨by simp [h0], by simp [h1], by simp [h2], by simp, by simp [hm, fillMem]⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = n := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, hm⟩
      have hvsi : st.mem (vs + i) = mem₀ (vs + i) := by
        rw [hm]; exact hbelow i hilt.le (vs + i) (by omega)
      obtain ⟨_, hhi⟩ := hcell i hilt
      refine ⟨.normal, { st with mem := Function.update st.mem (P + mem₀ (vs + i)) (n - 1 - i) },
        12, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr ⟨P + mem₀ (vs + i), n - 1 - i, ?_, ?_, rfl, rfl, by simp⟩
        · have hvi : vs + i < 2 ^ w := by omega
          have hmw : mem₀ (vs + i) < 2 ^ w := by omega
          simp [Expr.eval, h0, h2, h3, hvi, hvsi, hhi]
        · have hn1 : n - 1 < 2 ^ w := by omega
          have hni : n - 1 - i < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, h1, h3, hn1, hni, hw]
      · refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simp, ?_⟩, h3⟩
        dsimp only
        rw [hm]
        rfl)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal => exact hpost.2.2.2.2
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`posFillProc` meets its contract.** -/
theorem posFillProc_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some posFillProc) :
    MeetsContract w p f (posFillContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨vs, n, P, rfl, hvn, hw, hcell⟩
  refine runs_start_le ?_
  dsimp only [posFillProc]
  refine runs_seq_triple_le (posFill_triple p mem hw hvn hcell)
    ⟨by simp [startState], by simp [startState], by simp [startState], rfl⟩ ?_
  intro st₁ hm
  refine runs_ret_le (v := 0) ?_ ⟨vs, n, P, rfl, hm⟩ ?_
  · eval_expr
  · simp only [posFillContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const]
    omega

end MinCostFlow.HierPaths
