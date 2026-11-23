module

public import MinCostFlow.DynSpanner.Program.StateLayout
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# The sum of a range of words

The step for `0 < j` needs the total length of the buckets of the levels `j, …, L` before it
rebuilds them (`oldBucketsSum` in `StepPosCtx`). The layout keeps the length of bucket `i` in the
word `hDeg[i]`, so this total is a sum of consecutive words. `dsWordSumStmt` adds the words
`base + i` for `lo ≤ i < hi` in one loop, with cost `20 · (hi - lo) + 20`, and does not write
memory (`dsWordSum_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- Return `Σ_{lo ≤ i < hi} mem (base + i)` (`args = [base, lo, hi]`). -/
def dsWordSumStmt : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 3 (.reg 1) (.reg 2)
    (.assign 4 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.reg 3))))) ;;
  .ret (.reg 4)

def wordSumProcs : List Stmt := [dsWordSumStmt]

def wordSumIdx : ℕ := 0

lemma wordSumProcs_noRand : ∀ s ∈ wordSumProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsWordSumStmt`: it returns the sum of the words `base + i` for `lo ≤ i < hi`
and keeps memory. The sum must fit in a word. -/
def dsWordSumContract (w base lo hi : ℕ) : Contract where
  pre args mem := args = [base, lo, hi] ∧ lo ≤ hi ∧ base + hi < 2 ^ w ∧ 2 ≤ 2 ^ w ∧
    ∑ i ∈ Finset.Ico lo hi, mem (base + i) < 2 ^ w
  post _ mem ret mem' := mem' = mem ∧ ret = ∑ i ∈ Finset.Ico lo hi, mem (base + i)
  cost _ _ := 20 * (hi - lo) + 20

end

/-- The loop invariant: register `4` holds the sum of the words `base + k` for `lo ≤ k < i`, and
memory is unchanged. -/
private def WSInv (base lo hi : ℕ) (mem0 : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = base ∧ st.regs 2 = hi ∧ st.regs 3 = i ∧
  st.regs 4 = ∑ k ∈ Finset.Ico lo i, mem0 (base + k) ∧ st.mem = mem0

private lemma sum_Ico_le_of_le {f : ℕ → ℕ} {lo i hi : ℕ} (hi' : i ≤ hi) :
    ∑ k ∈ Finset.Ico lo i, f k ≤ ∑ k ∈ Finset.Ico lo hi, f k :=
  Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hi')

public section

/-- `dsWordSumStmt` meets `dsWordSumContract`. -/
theorem dsWordSum_meetsContract {w base lo hi : ℕ} {p : Program} {bW : ℕ}
    (hpW : p.HasAt bW wordSumProcs) :
    MeetsContract w p (bW + wordSumIdx) (dsWordSumContract w base lo hi) := by
  refine meetsContract_of_runs
    (hpW.get (i := wordSumIdx) (by simp [wordSumProcs, wordSumIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hle, hB, hw2, hS⟩
  simp only [wordSumProcs, wordSumIdx, List.getElem_cons_zero]
  dsimp only [dsWordSumStmt]
  let st0 : State :=
    { startState [base, lo, hi] mem pos with
      regs := Function.update (startState [base, lo, hi] mem pos).regs 4 0 }
  have hloop : Triple w p (fun st => st = st0)
      (forRange 3 (.reg 1) (.reg 2)
        (.assign 4 (.bin .add (.reg 4) (.load (.bin .add (.reg 0) (.reg 3))))))
      (normalPost (WSInv base lo hi mem hi))
      (fun _ => (hi - lo) * (8 + (Expr.reg 2).size + 8) +
        ((Expr.reg 1).size + (Expr.reg 2).size + 5)) := by
    refine Triple.forRange_const 8 lo hi hle (by omega) (fun _ => by omega)
      (fun st hst => ?_) (fun i st _ _ h => h.2.2.1) (fun i st _ _ h => Expr.eval_reg_of_eq h.2.1)
      (fun i hli hi' => ?_)
    · subst hst
      refine ⟨Expr.eval_reg_of_eq (by simp [st0, startState]), ?_⟩
      refine ⟨by simp [st0, startState], by simp [st0, startState], by simp, ?_, rfl⟩
      simp [st0]
    · intro st ω' hI
      obtain ⟨r0, r2, r3, r4, hm⟩ := hI
      have hsum_le : ∑ k ∈ Finset.Ico lo (i + 1), mem (base + k) < 2 ^ w :=
        lt_of_le_of_lt (sum_Ico_le_of_le (by omega)) hS
      have hsucc : ∑ k ∈ Finset.Ico lo (i + 1), mem (base + k) =
          ∑ k ∈ Finset.Ico lo i, mem (base + k) + mem (base + i) :=
        Finset.sum_Ico_succ_top hli _
      refine runs_start_le ?_
      refine runs_assign_le (v := ∑ k ∈ Finset.Ico lo (i + 1), mem (base + k))
        (by
          rw [hsucc]
          exact Expr.eval_add (Expr.eval_reg_of_eq r4)
            (Expr.eval_load_of_eq
              (Expr.eval_add (w := w) (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3)
                (by omega))
              (by rw [hm]))
            (by rw [← hsucc]; exact hsum_le))
        ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [r0], by simp [r2], by simp, by simp, hm⟩, ?_⟩
      simp [r3]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop rfl ?_
  intro st hI
  obtain ⟨_, _, _, r4, hm⟩ := hI
  refine runs_ret_le (v := ∑ k ∈ Finset.Ico lo hi, mem (base + k)) (Expr.eval_reg_of_eq r4)
    ⟨hm, rfl⟩ ?_
  simp only [Expr.size, dsWordSumContract]
  omega

end

end MinCostFlow.DynSpanner.Program
