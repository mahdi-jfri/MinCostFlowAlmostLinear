module

public import MinCostFlow.HierPaths.InitProgFlatEdge

/-!
# Following an edge of a host walk

A substitution pass keeps the current terminal in a register. After appending
an embedding, it moves to the other end of the corresponding host edge.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the host address, the host edge number and the current terminal. -/
def initFlatEnd : Stmt :=
  .assign 3 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 1))) ;;
  .assign 4 (.load (.reg 3)) ;;
  .cond (.bin .eq (.reg 4) (.reg 2))
    (.ret (.load (.bin .add (.reg 3) (.const 1))))
    (.ret (.reg 4))

theorem initFlatEnd_noRand : initFlatEnd.NoRand := by
  simp [initFlatEnd, Stmt.NoRand]

/-- A single step of the host walk changes the current terminal and preserves memory. -/
def initFlatEndContract (w : ℕ) (G : Graph) (e u : ℕ) : Contract where
  pre args mem := ∃ g, args = [g, e, u] ∧ GraphAt mem g G ∧ e < G.m ∧
    g + G.encode.length < 2 ^ w ∧
    (edgeAt G.edges e).1 < 2 ^ w ∧ (edgeAt G.edges e).2 < 2 ^ w
  post _ mem v mem' := v = otherEnd G.edges e u ∧ mem' = mem
  cost _ _ := 32

theorem initFlatEnd_meetsContract {w f e u : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some initFlatEnd) :
    MeetsContract w p f (initFlatEndContract w G e u) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨g, rfl, hG, he, hroom, hl, hr⟩ := hpre
  let i := g + 2 + 2 * e
  let l := (edgeAt G.edges e).1
  let r := (edgeAt G.edges e).2
  have hlen : G.encode.length = 2 + 2 * G.m := by simp [Graph.encode, Graph.m]; omega
  have hi : i + 1 < 2 ^ w := by dsimp [i]; omega
  have h1 : 1 < 2 ^ w := by dsimp [i] at hi; omega
  have h2 : 2 < 2 ^ w := by dsimp [i] at hi; omega
  have hleft : mem i = l := by
    dsimp only [i, l, edgeAt]
    rw [List.getD_eq_getElem _ _ he]
    exact graphAt_edge_fst hG he
  have hright : mem (i + 1) = r := by
    dsimp only [i, r, edgeAt]
    rw [List.getD_eq_getElem _ _ he]
    convert graphAt_edge_snd hG he using 2 <;> omega
  refine runs_start_le ?_
  unfold initFlatEnd
  refine runs_seq_assign_le (v := i) (Expr.eval_add
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h2) (by dsimp [i] at hi; omega))
    (Expr.eval_mul (Expr.eval_const h2) (Expr.eval_reg_of_eq rfl) (by dsimp [i] at hi; omega))
    (by dsimp [i] at hi ⊢; omega)) ?_
  refine runs_seq_assign_le (v := l) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) hleft) ?_
  refine runs_cond_le (v := if l = u then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h1) ?_ ?_
  · intro hn
    have hu : l = u := by by_contra h; simp [h] at hn
    refine runs_ret_le (v := r) (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hi) hright) ?_ ?_
    · exact ⟨ite_eq_left hu |>.symm, rfl⟩
    · simp [initFlatEndContract, Expr.size]
  · intro hz
    have hu : l ≠ u := by intro h; simp [h] at hz
    refine runs_ret_le (v := l) (Expr.eval_reg_of_eq rfl) ?_ ?_
    · exact ⟨ite_eq_right hu |>.symm, rfl⟩
    · simp [initFlatEndContract, Expr.size]

end MinCostFlow.HierPaths

end
