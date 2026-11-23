module

public import MinCostFlow.DynSpanner.Program.DynSpannerReembedAllStep
import WordRAM.Tactic

/-!
# Re-embedding all affected edges: the contract

`dsReembedAll_meetsContract` proves that `dsReembedAllStmt` meets `dsReembedAllContract`. The
loop runs once per affected edge, and each iteration is `dsReembedAll_step_triple`, which keeps
the invariant `RAInv`. Before the loop the invariant holds because nothing has been written.

The cost is `Σ (800 · (|embLt e| + |embMid e|) + 1090)` for the iterations, plus `9` per
iteration for the loop test and the counter, plus a constant. This is at most
`reembedAllCost embLt embMid es`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

/-- Summing over positions equals summing over the list. -/
private lemma sum_range_getD (es : List ℕ) (g : ℕ → ℕ) :
    ((List.range es.length).map fun i => g (es.getD i 0)).sum = (es.map g).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem]

/-- Each step costs `9` more than `800 · g e + 1090`, still within `1100`. -/
private lemma sum_step_le (es : List ℕ) (g : ℕ → ℕ) :
    (es.map fun e => 800 * g e + 1090).sum + 9 * es.length ≤
      (es.map fun e => 800 * g e + 1100).sum := by
  induction es with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

public section

/-- `dsReembedAllStmt` meets `dsReembedAllContract`, with cost
`Σ_{e ∈ es} (800 · (|embLt e| + |embMid e|) + 1100) + 20`. -/
theorem dsReembedAll_meetsContract {w vCap eCap : ℕ} {p : Program} {bOps bRe bEmb bA : ℕ}
    {G : MGraph} {embLt embMid : Embedding} {S : Finset ℕ} {es : List ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpRe : p.HasAt bRe (reembedProcs bEmb))
    (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpA : p.HasAt bA (reembedAllProcs bOps bRe)) :
    MeetsContract w p (bA + reembedAllIdx)
      (dsReembedAllContract w vCap eCap G embLt embMid S es) := by
  refine meetsContract_of_runs
    (hpA.get (i := reembedAllIdx) (by simp [reembedAllProcs, reembedAllIdx])) ?_
  rintro args mem pos ω _ ⟨gPtr, sBitPtr, esPtr, wpPtr, mpPtr, piTab, heap, rfl, hw16, hgB, hsB,
    hesB, hwpB, hmpB, htB, hhB, dHG, dHS, dHE, dHW, dHM, dHT, dTG, dTS, dTE, dTW, dTM, hwalk, hG,
    hGv, hVc, hEc, hes, hnd, hesG, hPw, hMe, hsBit⟩
  simp only [reembedAllProcs, reembedAllIdx, List.getElem_cons_zero]
  let c : RACtx := ⟨w, vCap, eCap, G, embLt, embMid, S, es, gPtr, sBitPtr, esPtr, wpPtr, mpPtr,
    piTab, heap, mem, hw16, hgB, hsB, hesB, hwpB, hmpB, htB, hhB, dHG, dHS, dHE, dHW, dHM, dHT,
    dTG, dTS, dTE, dTW, dTM, hwalk, hG, hGv, hVc, hEc, hes, hnd, hesG, hPw, hMe, hsBit⟩
  have hlen_w : es.length < 2 ^ w := by omega
  let stepCost : ℕ → ℕ := fun i =>
    800 * ((embLt (es.getD i 0)).length + (embMid (es.getD i 0)).length) + 1090
  have hloop : Triple w p (RAInv c 0) (forUp 8 (.reg 3) (dsReembedAllBodyStmt bOps bRe))
      (normalPost (RAInv c es.length))
      (fun _ => rangeCost stepCost 0 es.length + (es.length - 0) * ((Expr.reg 3).size + 8) +
        ((Expr.reg 3).size + 3)) :=
    Triple.forUp_le stepCost 0 es.length (Nat.zero_le _) (by omega) (fun _ => hlen_w)
      (fun i st _ _ h => h.2.2.2.2.2.2.2.2.1)
      (fun i st _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
      (fun i _ hi => by
        refine (dsReembedAll_step_triple c hpOps hpRe hpEmb hi).conseq
          (fun _ h => h) (fun o st h => ?_) (fun _ _ => ?_)
        · cases o with
          | returned u => exact False.elim h
          | normal => exact h
        · show _ ≤ 800 * ((embLt (es.getD i 0)).length + (embMid (es.getD i 0)).length) + 1090
          rw [List.getD_eq_getElem _ _ hi])
  dsimp only [dsReembedAllStmt, forRange]
  refine runs_start_le ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hinv0 : RAInv c 0 { startState [gPtr, sBitPtr, esPtr, es.length, wpPtr, mpPtr, piTab,
      heap] mem pos with regs := Function.update (startState [gPtr, sBitPtr, esPtr, es.length,
        wpPtr, mpPtr, piTab, heap] mem pos).regs 8 0 } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [reembHeapAt, startState, c], rfl,
      fun k _ hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  refine runs_seq_triple_le hloop hinv0 ?_
  intro st2 hI
  obtain ⟨_, _, _, _, _, _, _, r7, _, hT, hfr⟩ := hI
  refine runs_ret_le (v := reembHeapAt G embLt embMid S es heap es.length)
    (Expr.eval_reg_of_eq r7) ?_ ?_
  · refine ⟨gPtr, sBitPtr, esPtr, wpPtr, mpPtr, piTab, heap, rfl, ?_, rfl, ?_⟩
    · intro e he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
      exact hT k hk hk
    · intro addr h1 h3
      exact hfr addr h1 fun k hk _ => h3 _ (List.getElem_mem hk)
  · have hsum := sum_range_getD es (fun e => 800 * ((embLt e).length + (embMid e).length) + 1090)
    have hle := sum_step_le es (fun e => (embLt e).length + (embMid e).length)
    simp only [rangeCost_zero_eq_range, Expr.size, dsReembedAllContract, reembedAllCost, stepCost]
    omega

end

end MinCostFlow.DynSpanner.Program
