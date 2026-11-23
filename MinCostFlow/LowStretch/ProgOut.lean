module

public import MinCostFlow.LowStretch.ProgPreLay
public import WordRAM.CopyWords

/-!
# The output of the tree

The cluster procedure writes the edge numbers of the tree at `OUT` and returns their number,
which the entry keeps in register `7`. The statement wants the tree at address `0`, and the entry
must return its length. `outS` copies the tree to address `0` with `copyWords` and returns
register `7` (`outS_run`). The copy is safe because the tree is shorter than `OUT`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- Copy register `7` words from the value of `e` to address `0`, then return register `7`;
`copyWords` sits at `bCp`. -/
def outS (bCp : ℕ) (e : Expr) : Stmt :=
  .seq (.call 8 bCp [e, .const 0, .reg 7]) (.ret (.reg 7))

theorem outS_run {w : ℕ} {p : Program} {ω : ℕ → Bool} {bCp : ℕ} {e : Expr} {st : State}
    {OUT k T : ℕ} {Tr : List ℕ} {Q : Outcome → State → Prop}
    (hcp : p.HasAt bCp [copyWords]) (he : e.eval w st = some OUT)
    (h7 : st.regs 7 = Tr.length) (hl : ListAt st.mem OUT Tr) (hle : Tr.length ≤ OUT)
    (hb : OUT + Tr.length < 2 ^ w) (hw : 1 < 2 ^ w)
    (hQ : ∀ st' : State, ListAt st'.mem 0 Tr → Q (.returned Tr.length) st')
    (hc : k + e.size + 17 * Tr.length + 20 ≤ T) :
    ∃ o st' c, Runs w p ω (outS bCp e) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  refine runs_seq_call_le (vs := [OUT, 0, Tr.length]) (copyWords_meetsContract hcp) ?_ ?_
    ⟨OUT, 0, Tr.length, rfl, hw, by omega, by omega, Or.inl (by omega)⟩ ?_
  · simp only [evalArgs, he, Expr.eval, h7, show 0 < 2 ^ w by omega, if_true]
  · wram_words
  · intro v mem' pos' hpost
    obtain ⟨src, dst, len, heq, -, hcopy, -⟩ := hpost
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl, -⟩ := heq
    refine runs_ret_le (Expr.eval_reg_of_eq ?_) (hQ _ (copyWords_listAt hl rfl hcopy)) ?_
    · show Function.update st.regs 8 v 7 = _
      rw [Function.update_of_ne (by decide)]
      exact h7
    · simp only [copyWordsContract, argsSize, Expr.size]
      omega

end MinCostFlow.LowStretch
