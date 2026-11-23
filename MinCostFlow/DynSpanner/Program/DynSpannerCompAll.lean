module

public import MinCostFlow.DynSpanner.Program.DynSpannerCompAllStep
import WordRAM.Tactic

/-!
# Composing the walks of all affected edges: the contract

`dsCompAll_meetsContract` proves that `dsCompAllStmt` meets `dsCompAllContract`. The loop keeps
`CAInv` by `dsCompAll_step_triple`. Before the loop nothing has been written. The cost is the sum
of the step costs, `9` per iteration for the loop test and counter, and a constant.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

private lemma sum_range_getD (es : List ℕ) (g : ℕ → ℕ) :
    ((List.range es.length).map fun i => g (es.getD i 0)).sum = (es.map g).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem]

private lemma sum_step_le (es : List ℕ) (g : ℕ → ℕ) :
    (es.map fun e => g e + 70).sum + 9 * es.length ≤ (es.map fun e => g e + 80).sum := by
  induction es with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

public section

/-- `dsCompAllStmt` meets `dsCompAllContract`, with cost
`Σ_{e ∈ es} (70 · |embMid e| + 120 · |outEmb e| + 80) + 20`. -/
theorem dsCompAll_meetsContract {w eCap : ℕ} {p : Program} {bA bC bOps bEmb : ℕ}
    {T outEmb : Embedding} {es : List ℕ}
    (hpC : p.HasAt bC (compProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpA : p.HasAt bA (compAllProcs bC)) :
    MeetsContract w p (bA + compAllIdx) (dsCompAllContract w eCap T outEmb es) := by
  refine meetsContract_of_runs
    (hpA.get (i := compAllIdx) (by simp [compAllProcs, compAllIdx])) ?_
  rintro args mem pos ω _ ⟨qTab, tab, esPtr, mpPtr, heap, rfl, hw16, hqB, htB, hesB, hmpB, hhB,
    dHQ, dHT, dHE, dHM, dMQ, dMT, dME, hes, hk⟩
  simp only [compAllProcs, compAllIdx, List.getElem_cons_zero]
  let c : CACtx := ⟨w, eCap, T, outEmb, es, qTab, tab, esPtr, mpPtr, heap, mem, hw16, hqB, htB,
    hesB, hmpB, hhB, dHQ, dHT, dHE, dHM, dMQ, dMT, dME, hes, hk⟩
  have hlen_w : es.length < 2 ^ w := by omega
  let g : ℕ → ℕ := fun e =>
    70 * ((outEmb e).flatMap (compPiece T)).length + 120 * (outEmb e).length
  let stepCost : ℕ → ℕ := fun i => g (es.getD i 0) + 70
  have hloop : Triple w p (CAInv c 0) (forUp 6 (.reg 3) (dsCompAllBodyStmt bC))
      (normalPost (CAInv c es.length))
      (fun _ => rangeCost stepCost 0 es.length + (es.length - 0) * ((Expr.reg 3).size + 8) +
        ((Expr.reg 3).size + 3)) :=
    Triple.forUp_le stepCost 0 es.length (Nat.zero_le _) (by omega) (fun _ => hlen_w)
      (fun i st _ _ h => h.2.2.2.2.2.2.1)
      (fun i st _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
      (fun i _ hi => by
        refine (dsCompAll_step_triple c hpC hpEmb hi).conseq (fun _ h => h) (fun _ _ h => h)
          (fun _ _ => ?_)
        show _ ≤ g (es.getD i 0) + 70
        rw [List.getD_eq_getElem _ _ hi])
  dsimp only [dsCompAllStmt, forRange]
  refine runs_start_le ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hinv0 : CAInv c 0 { startState [qTab, tab, esPtr, es.length, mpPtr, heap] mem pos with
      regs := Function.update (startState [qTab, tab, esPtr, es.length, mpPtr, heap] mem
        pos).regs 6 0 } :=
    ⟨rfl, rfl, rfl, rfl, rfl, by simp [compHeapAt, startState, c], rfl,
      fun k _ hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  refine runs_seq_triple_le hloop hinv0 ?_
  intro st2 hI
  obtain ⟨_, _, _, _, _, r5, _, hT, hfr⟩ := hI
  refine runs_ret_le (v := compHeapAt T outEmb es heap es.length)
    (Expr.eval_reg_of_eq r5) ?_ ?_
  · exact ⟨qTab, tab, esPtr, mpPtr, heap, rfl, fun k hk => hT k hk hk, rfl, hfr⟩
  · have hsum := sum_range_getD es (fun e => g e + 70)
    have hle := sum_step_le es g
    simp only [rangeCost_zero_eq_range, Expr.size, dsCompAllContract, compAllCost, stepCost]
    simp only [g] at hsum hle ⊢
    omega

end

end MinCostFlow.DynSpanner.Program
