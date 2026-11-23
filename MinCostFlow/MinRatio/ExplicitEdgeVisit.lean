module

public import MinCostFlow.MinRatio.ExplicitEdgeUpdate
import WordRAM.Tactic

/-!
# Visiting a row of the explicit cycle route

Algorithm 2 (page 29) applies the signed circulation and records its
absolute value. A row triggers its grouped edge update exactly when
its name is absent from the preceding prefix.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Arguments are route base, length, index, edge record, multiplier
address, limb count, and heap. -/
@[expose] def explicitEdgeVisitBody (first update : ℕ) : Stmt :=
  .call 7 first [.reg 0, .reg 2] ;;
  .cond (.reg 7)
    (.call 8 update [.reg 0, .reg 1,
      .load (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 2))),
      .reg 3, .reg 4, .reg 5, .reg 6] ;; .ret (.reg 8))
    (.ret (.reg 6))

/-- On a repeated row preserve the heap and memory. On the first row
apply the grouped update contract with the same record address. -/
@[expose] def explicitEdgeVisitContract (w h : ℕ) (edges : List (ℕ × Bool))
    (i : ℕ) (value : PathEdgeValue) (num : ℤ) : Contract where
  pre args mem := ∃ base edge a L heap, ∃ hi : i < edges.length,
    args = [base, edges.length, i, edge, a, L, heap] ∧
    ExplicitEdgesAt mem base edges ∧ base + 2 * edges.length + 2 < 2 ^ w ∧
    edges[i].1 < 2 ^ w ∧
    (edges[i].1 ∉ (edges.take i).map Prod.fst →
      (explicitEdgeUpdateContract w h edges edges[i].1 value num).pre
        [base, edges.length, edges[i].1, edge, a, L, heap] mem)
  post args mem ret mem' := ∃ hi : i < edges.length,
    if edges[i].1 ∉ (edges.take i).map Prod.fst then
      (explicitEdgeUpdateContract w h edges edges[i].1 value num).post
        [args.getD 0 0, edges.length, edges[i].1, args.getD 3 0,
          args.getD 4 0, args.getD 5 0, heapArg args] mem ret mem'
    else ret = heapArg args ∧ mem' = mem
  cost args _ := 68 * i + 68 * edges.length + 152 * (args.getD 5 0)^2 +
    561 * args.getD 5 0 + 780

/-- A row visit uses only deterministic statements. -/
theorem explicitEdgeVisitBody_noRand (first update : ℕ) :
    (explicitEdgeVisitBody first update).NoRand := by
  simp [explicitEdgeVisitBody, Stmt.NoRand]

/-- The prefix test decides whether to apply the grouped update. -/
theorem explicitEdgeVisit_meetsContract {w h entry first update : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (i : ℕ) (value : PathEdgeValue) (num : ℤ)
    (hp : p.HasAt entry [explicitEdgeVisitBody first update])
    (hf : MeetsContract w p first (explicitEdgeFirstContract w edges i))
    (hu : ∀ e, MeetsContract w p update (explicitEdgeUpdateContract w h edges e value num)) :
    MeetsContract w p entry (explicitEdgeVisitContract w h edges i value num) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, edge, a, L, heap, hi, rfl, hr, hb, hew, hup⟩ := hpre
  have hb' := hwords base (by simp)
  have hiw := hwords i (by simp)
  have hK := hwords edges.length (by simp)
  have he := hwords edge (by simp)
  have ha := hwords a (by simp)
  have hL := hwords L (by simp)
  have hh := hwords heap (by simp)
  have htwo : 2 < 2 ^ w := by omega
  have hmul : 2 * i < 2 ^ w := by omega
  have haddr : base + 2 * i < 2 ^ w := by omega
  have hread := (hr.read hi).1
  apply runs_start_le
  unfold explicitEdgeVisitBody
  refine runs_seq_call_le hf (vs := [base, i]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨base, rfl, hr, by omega, hi, hew⟩
  · intro flag mem₁ pos₁ hflag
    obtain ⟨_, hbflag, rfl⟩ := hflag
    change flag = (if edges[i].1 ∉ (edges.take i).map Prod.fst then 1 else 0) at hbflag
    refine runs_cond_le (v := flag) (by eval_expr) ?_ ?_
    · intro hn
      have hfirst : edges[i].1 ∉ (edges.take i).map Prod.fst := by
        by_contra h
        exact hn (hbflag.trans (ite_eq_right (fun hn => hn h)))
      refine runs_seq_call_le (hu edges[i].1)
        (vs := [base, edges.length, edges[i].1, edge, a, L, heap])
        (by eval_expr) (by wram_words) (hup hfirst) ?_
      intro ret mem₂ pos₂ hpost
      have hret : ret = heap + (17 * L + 3) := hpost.1
      have hroom : heap + (17 * L + 3) < 2 ^ w := by
        obtain ⟨_, _, _, _, _, hargs, _, _, _, hbnd⟩ := hup hfirst
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨_, _, _, _, _, rfl, rfl⟩ := hargs
        exact hbnd
      have hretw : ret < 2 ^ w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · refine ⟨hi, ?_⟩
        rw [ite_eq_left hfirst]
        exact hpost
      · simp [explicitEdgeVisitContract, explicitEdgeFirstContract,
          explicitEdgeUpdateContract, Expr.size, argsSize]
        omega
    · intro hz
      have hnfirst : ¬ (edges[i].1 ∉ (edges.take i).map Prod.fst) := by
        intro h
        have : flag = 1 := hbflag.trans (ite_eq_left h)
        omega
      refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
      · refine ⟨hi, ?_⟩
        rw [ite_eq_right hnfirst]
        exact ⟨rfl, rfl⟩
      · simp [explicitEdgeVisitContract, explicitEdgeFirstContract, Expr.size, argsSize]
        omega

end MinCostFlow.MinRatio
