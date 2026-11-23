module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.HierPaths.InitLayout

/-!
# Storing registers one after the other

A writer that has computed the words of a short section in registers stores them at `r6`,
`r6 + 1`, …. `storeSeq rs i s` stores register `rs[j]` at `r6 + i + j` for each `j`, then runs
`s`. `runs_storeSeq` says what memory it leaves: those words, and memory elsewhere unchanged.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Store register `rs[j]` at `r6 + i + j`, then run `s`. -/
def storeSeq : List ℕ → ℕ → Stmt → Stmt
  | [], _, s => s
  | r :: rs, i, s => .seq (.store (.bin .add (.reg 6) (.const i)) (.reg r)) (storeSeq rs (i + 1) s)

/-- **What `storeSeq` leaves.** With `r6 = c` and `c + i + |rs| < 2^w`, the continuation `s` runs
from a memory that holds `st.regs rs[j]` at `c + i + j` and equals `st.mem` elsewhere, with the
same registers. Each store costs at most 6 steps. -/
theorem runs_storeSeq {w : ℕ} {p : Program} {ω : ℕ → Bool} {Q : Outcome → State → Prop}
    {s : Stmt} {c : ℕ} :
    ∀ (rs : List ℕ) (i : ℕ) (st : State) (k T : ℕ), st.regs 6 = c → c + i + rs.length < 2 ^ w →
      (∀ mem', (∀ j (hj : j < rs.length), mem' (c + i + j) = st.regs rs[j]) →
        (∀ y, (y < c + i ∨ c + i + rs.length ≤ y) → mem' y = st.mem y) →
        ∃ o st' c', Runs w p ω s { st with mem := mem' } o st' c' ∧ Q o st' ∧
          k + 6 * rs.length + c' ≤ T) →
      ∃ o st' c', Runs w p ω (storeSeq rs i s) st o st' c' ∧ Q o st' ∧ k + c' ≤ T := by
  intro rs
  induction rs with
  | nil =>
    intro i st k T _ _ hs
    obtain ⟨o, st', c', hr, hq, hc⟩ := hs st.mem (fun j hj => by simp at hj) (fun _ _ => rfl)
    exact ⟨o, st', c', hr, hq, by simpa using hc⟩
  | cons r rs ih =>
    intro i st k T h6 hb hs
    have hci : c + i < 2 ^ w := by simp at hb; omega
    have hi : i < 2 ^ w := by omega
    unfold storeSeq
    refine runs_seq_store_le (x := c + i) (v := st.regs r)
      (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_const hi) hci)
      (Expr.eval_reg_of_eq rfl) ?_
    refine ih (i + 1) { st with mem := Function.update st.mem (c + i) (st.regs r) } _ T h6
      (by simp at hb; omega) ?_
    intro mem' hm hf
    obtain ⟨o, st', c', hr, hq, hc⟩ := hs mem' (fun j hj => by
        rcases j with _ | j
        · rw [Nat.add_zero, hf (c + i) (Or.inl (by omega))]
          simp
        · have := hm j (by simpa using hj)
          rw [show c + i + (j + 1) = c + (i + 1) + j by omega, this]
          simp)
      (fun y hy => by
        rw [hf y (by simp at hy; omega)]
        simp only
        rw [Function.update_of_ne (by simp at hy; omega)])
    refine ⟨o, st', c', hr, hq, ?_⟩
    simp only [Expr.size, List.length_cons] at hc ⊢
    omega

end MinCostFlow.HierPaths
