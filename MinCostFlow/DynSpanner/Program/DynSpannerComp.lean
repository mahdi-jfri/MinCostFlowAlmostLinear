module

public import MinCostFlow.DynSpanner.Program.DynSpannerCompStep
import WordRAM.Tactic

/-!
# Composing a walk with an embedding: the contract

`dsCompEdge_meetsContract` proves that `dsCompEdgeStmt` meets `dsCompEdgeContract`. The loop
over the edges of `Q` keeps `CompInv` by `dsComp_step_triple`. After the loop the words after
`out` encode `Q.flatMap (compPiece T)` and the counter is its length, so writing the counter at
`out` gives the walk.

The cost is `Σ_{x ∈ Q} (70 · |T x| + 100)` for the iterations, `9` per iteration for the loop
test and counter, and a constant. Since `|Q.flatMap (compPiece T)| = Σ_{x ∈ Q} |T x|`, this is
at most `70 · |Q.flatMap (compPiece T)| + 120 · |Q| + 40`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

private lemma sum_range_getD' (Q : List (ℕ × Bool)) (g : ℕ × Bool → ℕ) :
    ((List.range Q.length).map fun i => g (Q.getD i (0, false))).sum = (Q.map g).sum := by
  congr 1
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem]

private lemma flatMap_compPiece_length (T : Embedding) (Q : List (ℕ × Bool)) :
    (Q.flatMap (compPiece T)).length = (Q.map fun x => (T x.1).length).sum := by
  induction Q with
  | nil => simp
  | cons x Q ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih,
      compPiece_length]

private lemma sum_mul_add (Q : List (ℕ × Bool)) (g : ℕ × Bool → ℕ) :
    (Q.map fun x => 70 * g x + 100).sum = 70 * (Q.map g).sum + 100 * Q.length := by
  induction Q with
  | nil => simp
  | cons x Q ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

public section

/-- `dsCompEdgeStmt` meets `dsCompEdgeContract`: it writes `Q.flatMap (compPiece T)` at `out`,
in time `70 · |Q.flatMap (compPiece T)| + 120 · |Q| + 40`. -/
theorem dsCompEdge_meetsContract {w eCap : ℕ} {p : Program} {bC bOps bEmb : ℕ}
    {T : Embedding} {Q : List (ℕ × Bool)}
    (hpC : p.HasAt bC (compProcs bEmb)) (hpEmb : p.HasAt bEmb (embOpsProcs bOps)) :
    MeetsContract w p (bC + compIdxEdge) (dsCompEdgeContract w eCap T Q) := by
  refine meetsContract_of_runs
    (hpC.get (i := compIdxEdge) (by simp [compProcs, compIdxEdge])) ?_
  rintro args mem pos ω _ ⟨qPtr, tab, out, rfl, hw16, hqB, htB, hoB, dOQ, dOT, hQ, hx⟩
  simp only [compProcs, compIdxEdge, List.getElem_cons_zero]
  let c : CompCtx := ⟨w, eCap, T, Q, qPtr, tab, out, mem, hw16, hqB, htB, hoB, dOQ, dOT, hQ, hx⟩
  have hR := compAcc_length_le T Q 0
  have hall := compAcc_all T Q
  let stepCost : ℕ → ℕ := fun i => 70 * (T (Q.getD i (0, false)).1).length + 100
  have hloop : Triple w p
      (fun st => st.regs 0 = qPtr ∧ st.regs 1 = tab ∧ st.regs 2 = out ∧
        st.regs 3 = Q.length ∧ st.regs 4 = 0 ∧ st.mem = mem)
      (forRange 5 (.const 0) (.reg 3) (dsCompBodyStmt bEmb)) (normalPost (CompInv c Q.length))
      (fun _ => rangeCost stepCost 0 Q.length + (Q.length - 0) * ((Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) :=
    Triple.forRange_le stepCost 0 Q.length (Nat.zero_le _) (by omega) (fun _ => by omega)
      (fun st ⟨h0, h1, h2, h3, h4, hm⟩ => ⟨Expr.eval_const (by omega),
        by simp [h0, c], by simp [h1, c], by simp [h2, c], by simp [h3, c], by simp [h4, c, compAcc],
        by simp, by simp [c, compAcc, walkWords, listAt_nil], fun addr _ => by simp [hm, c]⟩)
      (fun i st _ _ h => h.2.2.2.2.2.1)
      (fun i st _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
      (fun i _ hi => by
        refine (dsComp_step_triple c hpEmb hi).conseq (fun _ h => h) (fun _ _ h => h)
          (fun _ _ => ?_)
        show _ ≤ 70 * (T (Q.getD i (0, false)).1).length + 100
        rw [List.getD_eq_getElem _ _ hi])
  dsimp only [dsCompEdgeStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := Q.length)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) (MWalkAt_head hQ)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], by simp, by simp, rfl⟩ ?_
  intro st2 hI
  obtain ⟨_, _, r2, _, r4, _, hL, hfr⟩ := hI
  rw [hall] at r4 hL
  have hRw : out + (2 * (Q.flatMap (compPiece T)).length + 1) < 2 ^ w := hoB
  refine runs_seq_store_le (x := out) (v := (Q.flatMap (compPiece T)).length)
    (Expr.eval_reg_of_eq r2) (Expr.eval_reg_of_eq r4) ?_
  refine runs_ret_le (v := out + (2 * (Q.flatMap (compPiece T)).length + 1))
    (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r2))
      (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simpa using r4)) (by omega)) (Expr.eval_const (by omega))
        (by omega)) (by omega)) ?_ ?_
  · refine ⟨qPtr, tab, out, rfl, ?_, rfl, ?_⟩
    · refine (mWalkAt_iff _ _ _).mpr ⟨by simp, hL.update_lt (Nat.lt_succ_self out)⟩
    · intro addr ha
      have hne : addr ≠ out := by omega
      show Function.update st2.mem out _ addr = mem addr
      rw [Function.update_of_ne hne]
      exact hfr addr ha
  · have hsum := sum_range_getD' Q (fun x => 70 * (T x.1).length + 100)
    have hmul := sum_mul_add Q (fun x => (T x.1).length)
    have hlen := flatMap_compPiece_length T Q
    simp only [rangeCost_zero_eq_range, Expr.size_const, Expr.size_reg, Expr.size_load,
      Expr.size_bin, dsCompEdgeContract, stepCost]
    omega

end

end MinCostFlow.DynSpanner.Program
