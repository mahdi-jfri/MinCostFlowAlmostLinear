module

public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.DynSpanner.Program.StateLayout
import WordRAM.Tactic

/-!
# Applying the records of `U_H` to `H`

At the end of a step, the step has written the remaining records of `U_H` (the deletions and
insertions of `dsUHTailStmt`) into a buffer. `dsApplyUHStmt` writes the number of records in the
word before them, which makes the buffer a batch (`BatchAt`), and applies the batch to `H` with
`dgApplyBatchStmt` and `allowInsert = 1`. `dsApplyUH_meetsContract` proves that afterwards `H`
has become `H.applyBatch U` (`foldl_dgBatchTarget_one`), with cost `670 · total + 750` for
`total` words of records.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [hPtr, out, n]`: write `n` at `out` and apply the batch at `out` to the graph at
`hPtr`. -/
def dsApplyUHStmt (bBatch : ℕ) : Stmt :=
  .store (.reg 1) (.reg 2) ;;
  .call 3 (bBatch + dgIdxApplyBatch) [.reg 0, .reg 1, .const 1] ;;
  .ret (.const 0)

def applyUHProcs (bBatch : ℕ) : List Stmt := [dsApplyUHStmt bBatch]

def applyUHIdx : ℕ := 0

lemma applyUHProcs_noRand (bBatch : ℕ) : ∀ s ∈ applyUHProcs bBatch, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsApplyUHStmt` for the records `U` of `total` words at `out + 1`. -/
def dsApplyUHContract (w vCap eCap : ℕ) (H : MGraph) (U : List Update)
    (hPtr out total : ℕ) : Contract where
  pre args mem :=
    args = [hPtr, out, U.length] ∧ 16 ≤ 2 ^ w ∧ hPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    out + 1 + total < 2 ^ w ∧
    (out + 1 + total ≤ hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ out) ∧
    (∀ i < total, mem (out + 1 + i) < 2 ^ w) ∧
    BatchBodyAt mem (out + 1) H U total ∧ H.BatchIsValid U ∧ BatchWithinCaps vCap eCap U ∧
    DynGraphAt mem hPtr vCap eCap H
  post _ mem _ mem' :=
    DynGraphAt mem' hPtr vCap eCap (H.applyBatch U) ∧ mem' out = U.length ∧
    ∀ addr, (addr < hPtr ∨ hPtr + dynGraphSize vCap eCap ≤ addr) → addr ≠ out →
      mem' addr = mem addr
  cost _ _ := 670 * total + 750

end

public section

/-- With `allowInsert = 1`, the target graph of a batch is the graph after the batch. -/
theorem foldl_dgBatchTarget_one (U : List Update) (H : MGraph) :
    U.foldl (dgBatchTarget 1) H = H.applyBatch U := by
  induction U generalizing H with
  | nil => rfl
  | cons u U ih =>
    simp only [List.foldl_cons, MGraph.applyBatch] at ih ⊢
    rw [show dgBatchTarget 1 H u = H.applyUpdate u by simp [dgBatchTarget]]
    exact ih _

/-- `dsApplyUHStmt` meets `dsApplyUHContract`. -/
theorem dsApplyUH_meetsContract {w vCap eCap : ℕ} {H : MGraph} {U : List Update}
    {hPtr out total : ℕ} {p : Program} {bA bOps bEdge bSplit bBatch : ℕ}
    (hpB : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpOps : p.HasAt bOps dgOpsProcs) (hpA : p.HasAt bA (applyUHProcs bBatch)) :
    MeetsContract w p (bA + applyUHIdx) (dsApplyUHContract w vCap eCap H U hPtr out total) := by
  refine meetsContract_of_runs
    (hpA.get (i := applyUHIdx) (by simp [applyUHProcs, applyUHIdx])) ?_
  rintro args mem pos ω hW ⟨rfl, hw16, hgB, hoB, hdisj, hwords, hbody, hvalid, hcaps, hH⟩
  simp only [applyUHProcs, applyUHIdx, List.getElem_cons_zero]
  dsimp only [dsApplyUHStmt]
  have hnlt : U.length < 2 ^ w := hW _ (by simp)
  refine runs_start_le ?_
  refine runs_seq_store_le (x := out) (v := U.length)
    (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_reg_of_eq (by simp [startState])) ?_
  set mem₁ := Function.update mem out U.length with hmem₁
  have hag : ∀ i < total, mem₁ (out + 1 + i) = mem (out + 1 + i) := fun i _ =>
    Function.update_of_ne (by omega) _ _
  refine runs_seq_call_le (vs := [hPtr, out, 1])
    (dgApplyBatch_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := H) (H := H)
      (U := U) (totalWords := total + 1) hpB hpEdge hpSplit hpOps)
    (by eval_expr)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl) <;> omega)
    ⟨hPtr, out, 1, rfl, hw16, hgB, by omega, fun i hi => by omega,
      fun i hi => by
        show mem₁ (out + i) < 2 ^ w
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · simp [hmem₁, hnlt]
        · have := hag (i - 1) (by omega)
          rw [show out + i = out + 1 + (i - 1) by omega, this]
          exact hwords _ (by omega),
      ⟨by omega, by simp, by
        show BatchBodyAt mem₁ (out + 1) H U (total + 1 - 1)
        simpa using hbody.of_agree (fun i hi => hag i hi)⟩,
      hvalid, hcaps,
      dynGraphAt_of_agree hH fun addr h1 h2 => Function.update_of_ne (by omega) _ _,
      Or.inl ⟨one_ne_zero, rfl⟩⟩ ?_
  rintro r mem₂ pos₂ ⟨_, _, _, hEq, _, hH₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at hEq
  obtain ⟨h1, h2, h3⟩ := hEq
  subst h1 h2 h3
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨by rw [← foldl_dgBatchTarget_one]; exact hH₂, ?_, fun addr h hne => ?_⟩ ?_
  · show mem₂ out = U.length
    rw [hfr₂ out (by omega)]
    exact Function.update_self _ _ _
  · show mem₂ addr = mem addr
    rw [hfr₂ addr h]
    exact Function.update_of_ne hne _ _
  · simp only [Expr.size, argsSize, dsApplyUHContract, dgApplyBatchContract]
    omega

end

end MinCostFlow.DynSpanner.Program
