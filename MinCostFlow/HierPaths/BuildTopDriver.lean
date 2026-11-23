module

public import MinCostFlow.HierPaths.BuildTopAdvance

/-!
# Running the depths in order

Each schedule row contains the fixed words for one depth and the cells
holding its input and output graph directory pointers. The loop passes
the current heap pointer from one depth advance to the next.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

def buildTopDriverWord (offset : ℕ) : Expr :=
  .load (.bin .add (.reg 4) (.const offset))

def buildTopDriverBody (advance : ℕ) : Stmt :=
  .assign 4 (.bin .add (.reg 0) (.bin .mul (.const 13) (.reg 3))) ;;
  .call 2 advance
    [.load (buildTopDriverWord 0), buildTopDriverWord 1, buildTopDriverWord 2,
      buildTopDriverWord 3, buildTopDriverWord 4, buildTopDriverWord 5, buildTopDriverWord 6,
      buildTopDriverWord 7, buildTopDriverWord 8, buildTopDriverWord 9, buildTopDriverWord 10,
      buildTopDriverWord 11, .reg 2, buildTopDriverWord 12]

/-- Arguments are the schedule address, number of depths and initial heap pointer. -/
def buildTopDriver (advance : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 1) (buildTopDriverBody advance) ;;
  .ret (.reg 2)

theorem buildTopDriver_noRand (advance : ℕ) : (buildTopDriver advance).NoRand := by
  simp [buildTopDriver, buildTopDriverBody, forRange, forUp, Stmt.NoRand]

/-- The schedule uses an indirect first word so each stage can read its predecessor's directory. -/
def BuildTopDepthInput.scheduleWords (D : BuildTopDepthInput) (inputCell outputCell : ℕ) : List ℕ :=
  [inputCell, D.replyDir, D.termBase, D.childSize, D.branch, D.count, D.scale, D.rank,
    D.degree, D.pathLog, D.coreLog, D.denominator, outputCell]

/-- A fixed schedule row invokes the certified depth advance and preserves the loop index. -/
theorem buildTopDriverBody_triple {w K advance table i h inputCell outputCell : ℕ}
    {D : BuildTopDepthInput} {st : State} {p : Program}
    {space : Cited.Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (ha : MeetsContract w p advance (D.advanceContract w K space))
    (r0 : st.regs 0 = table) (r2 : st.regs 2 = h) (r3 : st.regs 3 = i)
    (hroom : table + 13 * i + 13 < 2 ^ w)
    (hrow : ListAt st.mem (table + 13 * i) (D.scheduleWords inputCell outputCell))
    (hin : st.mem inputCell = D.graphDir)
    (hw : ∀ v ∈ D.args h ++ [outputCell], v < 2 ^ w)
    (hpre : (D.advanceContract w K space).pre (D.args h ++ [outputCell]) st.mem) :
    Triple w p (fun t => t = st) (buildTopDriverBody advance)
      (normalPost fun t =>
        (∀ j, j ≠ 2 → j ≠ 4 → t.regs j = st.regs j) ∧
        (D.advanceContract w K space).post (D.args h ++ [outputCell]) st.mem (t.regs 2) t.mem)
      (fun _ => (D.advanceContract w K space).cost (D.args h ++ [outputCell]) st.mem + 62) := by
  intro t ω ht
  subst t
  let row := table + 13 * i
  have h13 : 13 < 2 ^ w := by omega
  have hMul : 13 * i < 2 ^ w := by omega
  have hr : row < 2 ^ w := by dsimp [row]; omega
  have hget (j : ℕ) (hj : j < 13) :
      st.mem (row+j) = (D.scheduleWords inputCell outputCell).getD j 0 := by
    rw [List.getD_eq_getElem _ _ (by simpa [BuildTopDepthInput.scheduleWords] using hj)]
    exact hrow j (by simpa [BuildTopDepthInput.scheduleWords] using hj)
  refine runs_start_le ?_
  unfold buildTopDriverBody
  refine runs_seq_assign_le (v := row) (Expr.eval_add (Expr.eval_reg_of_eq r0)
    (Expr.eval_mul (Expr.eval_const h13) (Expr.eval_reg_of_eq r3) hMul) hr) ?_
  refine runs_call_le ha (vs := D.args h ++ [outputCell]) ?_ hw hpre ?_
  · have haddr (j : ℕ) (hj : j < 13) : row + j < 2 ^ w := by dsimp [row]; omega
    have hsmall (j : ℕ) (hj : j < 13) : j < 2 ^ w := hj.trans h13
    have hzero : st.mem row = inputCell := by simpa [BuildTopDepthInput.scheduleWords] using hget 0 (by decide)
    simp (disch := decide) [evalArgs, Expr.eval, buildTopDriverWord, BinOp.eval, BuildTopDepthInput.args,
      hget, haddr, hsmall, BuildTopDepthInput.scheduleWords, hin, hzero, hr, r2, List.getElem?_cons_zero]
  · intro v mem' pos' hpost
    refine ⟨⟨?_, hpost⟩, ?_⟩
    · intro j hj hj'
      simp [Function.update_of_ne hj, Function.update_of_ne hj']
    · simp [Expr.size, argsSize, buildTopDriverWord] <;> omega

end MinCostFlow.HierPaths

end
