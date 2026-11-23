module

public import MinCostFlow.DynSpanner.Program.StateLayout
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Clearing the levels above `j`

After a rebuild of level `j`, Algorithm 6 empties the levels above `j`: their sets `inDom` and
`S` become empty. In the layout of `StateLayout.lean` a level is empty when its generation word
(`domGen[i]` or `sGen[i]`) is `0`. So the step writes `0` to a range of these words.
`dsZeroRangeStmt` does this for any range `[base + lo, base + hi)`, with cost
`15 · (hi - lo) + 12`. `dsZeroRange_meetsContract` proves its contract.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- Write `0` to `base + i` for `lo ≤ i < hi` (`args = [base, lo, hi]`). -/
def dsZeroRangeStmt : Stmt :=
  forRange 3 (.reg 1) (.reg 2) (.store (.bin .add (.reg 0) (.reg 3)) (.const 0)) ;;
  .ret (.const 0)

def zeroRangeProcs : List Stmt := [dsZeroRangeStmt]

def zeroRangeIdx : ℕ := 0

lemma zeroRangeProcs_noRand : ∀ s ∈ zeroRangeProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsZeroRangeStmt`. -/
def dsZeroRangeContract (w base lo hi : ℕ) : Contract where
  pre args _ := args = [base, lo, hi] ∧ lo ≤ hi ∧ base + hi < 2 ^ w ∧ 2 ≤ 2 ^ w
  post _ mem _ mem' :=
    (∀ i, lo ≤ i → i < hi → mem' (base + i) = 0) ∧
    ∀ addr, (addr < base + lo ∨ base + hi ≤ addr) → mem' addr = mem addr
  cost _ _ := 15 * (hi - lo) + 12

end

/-- The loop invariant: the words of `[base + lo, base + i)` are `0`, and the rest of memory is
unchanged. -/
private def ZRInv (base lo hi : ℕ) (mem0 : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = base ∧ st.regs 2 = hi ∧ st.regs 3 = i ∧
  (∀ k, lo ≤ k → k < i → st.mem (base + k) = 0) ∧
  ∀ addr, (addr < base + lo ∨ base + i ≤ addr) → st.mem addr = mem0 addr

public section

/-- `dsZeroRangeStmt` meets `dsZeroRangeContract`. -/
theorem dsZeroRange_meetsContract {w base lo hi : ℕ} {p : Program} {bZ : ℕ}
    (hpZ : p.HasAt bZ zeroRangeProcs) :
    MeetsContract w p (bZ + zeroRangeIdx) (dsZeroRangeContract w base lo hi) := by
  refine meetsContract_of_runs
    (hpZ.get (i := zeroRangeIdx) (by simp [zeroRangeProcs, zeroRangeIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hle, hB, hw2⟩
  simp only [zeroRangeProcs, zeroRangeIdx, List.getElem_cons_zero]
  dsimp only [dsZeroRangeStmt]
  have hloop : Triple w p (fun st => st = startState [base, lo, hi] mem pos)
      (forRange 3 (.reg 1) (.reg 2) (.store (.bin .add (.reg 0) (.reg 3)) (.const 0)))
      (normalPost (ZRInv base lo hi mem hi))
      (fun _ => (hi - lo) * (6 + (Expr.reg 2).size + 8) +
        ((Expr.reg 1).size + (Expr.reg 2).size + 5)) := by
    refine Triple.forRange_const 6 lo hi hle (by omega) (fun _ => by omega)
      (fun st hst => ?_) (fun i st _ _ h => h.2.2.1) (fun i st _ _ h => Expr.eval_reg_of_eq h.2.1)
      (fun i hli hi' => ?_)
    · subst hst
      refine ⟨Expr.eval_reg_of_eq (by simp [startState]), ?_⟩
      refine ⟨by simp [startState], by simp [startState], by simp, fun k h1 h2 => by omega,
        fun _ _ => rfl⟩
    · intro st ω' hI
      obtain ⟨r0, r2, r3, hz, hfr⟩ := hI
      refine runs_start_le ?_
      refine runs_store_le (x := base + i) (v := 0)
        (Expr.eval_add (w := w) (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r3) (by omega))
        (Expr.eval_const (w := w) (by omega)) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp [r0], by simp [r2], by simp, fun k h1 h2 => ?_, fun addr h => ?_⟩, r3⟩
      · show Function.update st.mem _ _ _ = 0
        by_cases hk : k = i
        · subst hk; simp
        · rw [Function.update_of_ne (by omega)]
          exact hz k h1 (by omega)
      · show Function.update st.mem _ _ _ = _
        rw [Function.update_of_ne (by omega)]
        exact hfr addr (by omega)
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl ?_
  intro st hI
  obtain ⟨_, _, _, hz, hfr⟩ := hI
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ⟨hz, fun addr h => hfr addr h⟩ ?_
  simp only [Expr.size, dsZeroRangeContract]
  omega

end

end MinCostFlow.DynSpanner.Program
