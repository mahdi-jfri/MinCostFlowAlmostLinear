module

public import MinCostFlow.DynSpanner.Program.DynSpannerBuildProjStep
import MinCostFlow.DynSpanner.Program.DynGraphBatch
import WordRAM.Tactic

/-!
# Building the projected graph `J`: the contract

`dsBuildProj_meetsContract` proves that `dsBuildProjStmt` meets `dsBuildProjContract`. The loop
runs once per affected edge. Each iteration is `dsBuildProj_step_triple`, which keeps the
invariant `BPInv`. Before the loop the invariant holds because `J` is empty and nothing has been
written. After the loop it gives the post, since `es.take es.length = es`.

The cost is `Σ (800 · |embLt e| + 1990)` for the iterations, plus `9` per iteration for the loop
test and the counter, plus a constant. This is at most `buildProjCost embLt es`.
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

/-- Each step costs `9` more than `800 · |embLt e| + 1990`, still within `2000`. -/
private lemma sum_step_le (es : List ℕ) (g : ℕ → ℕ) :
    (es.map fun e => 800 * g e + 1990).sum + 9 * es.length ≤
      (es.map fun e => 800 * g e + 2000).sum := by
  induction es with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

public section

/-- `dsBuildProjStmt` meets `dsBuildProjContract`, with cost
`Σ_{e ∈ es} (800 · |embLt e| + 2000) + 20`. -/
theorem dsBuildProj_meetsContract {w vCap eCap : ℕ} {p : Program} {bOps bEdge bProj bEmb bB : ℕ}
    {G : MGraph} {embLt : Embedding} {S : Finset ℕ} {es : List ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpProj : p.HasAt bProj (projProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps))
    (hpB : p.HasAt bB (buildProjProcs bOps bEdge bProj)) :
    MeetsContract w p (bB + buildProjIdx) (dsBuildProjContract w vCap eCap G embLt S es) := by
  refine meetsContract_of_runs
    (hpB.get (i := buildProjIdx) (by simp [buildProjProcs, buildProjIdx])) ?_
  rintro args mem pos ω _ ⟨gPtr, jPtr, sBitPtr, esPtr, wpPtr, embTab, heap, rfl, hw16, hgB, hjB,
    hsB, hesB, hwpB, htB, hhB, dHG, dHJ, dHS, dHE, dHW, dHT, dJG, dJS, dJE, dJW, dJT, dTG, dTS,
    dTE, dTW, hwalk, hG, hGv, hVc, hEc, hJ0, hes, hnd, hesG, hPw, hsBit⟩
  simp only [buildProjProcs, buildProjIdx, List.getElem_cons_zero]
  let c : BPCtx := ⟨w, vCap, eCap, G, embLt, S, es, gPtr, jPtr, sBitPtr, esPtr, wpPtr, embTab,
    heap, mem, hw16, hgB, hjB, hsB, hesB, hwpB, htB, hhB, dHG, dHJ, dHS, dHE, dHW, dHT, dJG, dJS,
    dJE, dJW, dJT, dTG, dTS, dTE, dTW, hwalk, hG, hGv, hVc, hEc, hJ0, hes, hnd, hesG, hPw, hsBit⟩
  have hlen_w : es.length < 2 ^ w := by omega
  let stepCost : ℕ → ℕ := fun i => 800 * (embLt (es.getD i 0)).length + 1990
  have hloop : Triple w p (BPInv c 0) (forUp 8 (.reg 4) (dsBuildProjBodyStmt bOps bEdge bProj))
      (normalPost (BPInv c es.length))
      (fun _ => rangeCost stepCost 0 es.length + (es.length - 0) * ((Expr.reg 4).size + 8) +
        ((Expr.reg 4).size + 3)) :=
    Triple.forUp_le stepCost 0 es.length (Nat.zero_le _) (by omega) (fun _ => hlen_w)
      (fun i st _ _ h => h.2.2.2.2.2.2.2.2.1)
      (fun i st _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.1)
      (fun i _ hi => by
        refine (dsBuildProj_step_triple c hpOps hpEdge hpProj hpEmb hi).conseq
          (fun _ h => h) (fun o st h => ?_) (fun _ _ => ?_)
        · cases o with
          | returned u => exact False.elim h
          | normal => exact h
        · show _ ≤ 800 * (embLt (es.getD i 0)).length + 1990
          rw [List.getD_eq_getElem _ _ hi])
  dsimp only [dsBuildProjStmt, forRange]
  refine runs_start_le ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hinv0 : BPInv c 0 { startState [gPtr, jPtr, sBitPtr, esPtr, es.length, wpPtr, embTab, heap]
      mem pos with regs := Function.update (startState [gPtr, jPtr, sBitPtr, esPtr, es.length,
        wpPtr, embTab, heap] mem pos).regs 8 0 } := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [projHeapAt, startState, c], rfl,
      ?_, fun k _ hk => absurd hk (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩
    obtain ⟨hV0, hE0⟩ := buildProjGraph_take_zero G G embLt S es
    exact DynGraphAt.congr_ends hV0.symm hE0.symm
      (fun e he => by simp [emptyMGraph] at he) hJ0
  refine runs_seq_triple_le hloop hinv0 ?_
  intro st2 hI
  obtain ⟨_, _, _, _, _, _, _, r7, _, hJ, hT, hfr⟩ := hI
  have htake : es.take es.length = es := List.take_of_length_le (Nat.le_refl _)
  refine runs_ret_le (v := projHeapAt G embLt S es heap es.length)
    (Expr.eval_reg_of_eq r7) ?_ ?_
  · refine ⟨gPtr, jPtr, sBitPtr, esPtr, wpPtr, embTab, heap, rfl, ?_, ?_, rfl, ?_⟩
    · have := hJ
      simp only [c, htake] at this
      exact this
    · intro e he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
      exact hT k hk hk
    · intro addr h1 h2 h3
      exact hfr addr h1 h2 fun k hk _ => h3 _ (List.getElem_mem hk)
  · have hsum := sum_range_getD es (fun e => 800 * (embLt e).length + 1990)
    have hle := sum_step_le es (fun e => (embLt e).length)
    simp only [rangeCost_zero_eq_range, Expr.size, dsBuildProjContract, buildProjCost, stepCost]
    omega

end

end MinCostFlow.DynSpanner.Program
