module

public import MinCostFlow.IPM.Machine.StrictRange
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Checking refreshed coefficients before Update

The machine interface bounds gradients and lengths even on rejected
targets. After refreshing a reported coordinate, compare its gradient
with the signed range endpoints and its length with the positive range
endpoints. The read-only checks cannot change the DS or its caches.
An accepted check gives strict bounds, which imply the interface's
nonstrict bounds. Only reported coordinates need this extra work.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[negativeMaximum,gradient,maximum,minimum,length,L]`.
Return one exactly when both coefficients lie strictly inside their
represented ranges. -/
def coefficientRangeGuardBody (range : ℕ) : Stmt :=
  .call 6 range [.reg 0,.reg 1,.reg 2,.reg 5] ;;
  .call 7 range [.reg 3,.reg 4,.reg 2,.reg 5] ;;
  .ret (.bin .mul (.reg 6) (.reg 7))

/-- A shared signed comparison module serves both range checks. -/
def coefficientRangeGuardModule (b h : ℕ) : List Stmt :=
  [coefficientRangeGuardBody (b+1)] ++ strictRangeModule (b+1) h

/-- The complete input is just five valid blocks and their word bounds.
No coefficient accuracy or hidden stability is needed to run the guard. -/
def coefficientRangeGuardContract (w h : ℕ) : Contract where
  pre args mem := ∃ neg g mx mn l L,args=[neg,g,mx,mn,l,L] ∧
    (strictRangeContract w h).pre [neg,g,mx,L] mem ∧
    (strictRangeContract w h).pre [mn,l,mx,L] mem
  post args mem v mem' := mem'=mem ∧ v=if
    Num.intVal mem (args.getD 0 0) h (args.getD 5 0) < Num.intVal mem (args.getD 1 0) h (args.getD 5 0) ∧
    Num.intVal mem (args.getD 1 0) h (args.getD 5 0) < Num.intVal mem (args.getD 2 0) h (args.getD 5 0) ∧
    Num.intVal mem (args.getD 3 0) h (args.getD 5 0) < Num.intVal mem (args.getD 4 0) h (args.getD 5 0) ∧
    Num.intVal mem (args.getD 4 0) h (args.getD 5 0) < Num.intVal mem (args.getD 2 0) h (args.getD 5 0)
    then 1 else 0
  cost args _ := 164*args.getD 5 0+400

/-- Both comparisons and the caller are deterministic. -/
theorem coefficientRangeGuardModule_noRand (b h : ℕ) :
    ∀ body∈coefficientRangeGuardModule b h,body.NoRand := by
  intro body hb
  simp only [coefficientRangeGuardModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [coefficientRangeGuardBody,Stmt.NoRand]
  · exact strictRangeModule_noRand _ _ _ hb

/-- The actual two range calls preserve all memory and cost linearly in
the scalar width, on both acceptance and rejection. -/
theorem coefficientRangeGuard_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 1<2^w) (hb : Num.base h<2^w)
    (hp : p.HasAt b (coefficientRangeGuardModule b h)) :
    MeetsContract w p b (coefficientRangeGuardContract w h) := by
  have hrange := strictRange_meetsContract hh hw hb (Num.hasAt_append_right hp)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨neg,g,mx,mn,l,L,rfl,hg,hl⟩ := hpre
  have hnW := hwords neg (by simp)
  have hgW := hwords g (by simp)
  have hxW := hwords mx (by simp)
  have hmW := hwords mn (by simp)
  have hlW := hwords l (by simp)
  have hLW := hwords L (by simp)
  apply runs_start_le
  unfold coefficientRangeGuardBody
  refine runs_seq_call_le hrange (vs:=[neg,g,mx,L]) (by eval_expr) (by wram_words) hg ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨hm0,hv0⟩ := hp0
  change mem0=mem at hm0
  subst mem0
  change v0=if Num.intVal mem neg h L<Num.intVal mem g h L ∧
    Num.intVal mem g h L<Num.intVal mem mx h L then 1 else 0 at hv0
  have hv0b : v0≤1 := by split_ifs at hv0 <;> omega
  refine runs_seq_call_le hrange (vs:=[mn,l,mx,L]) (by eval_expr) (by wram_words) hl ?_
  intro v1 mem1 pos1 hp1
  obtain ⟨hm1,hv1⟩ := hp1
  change mem1=mem at hm1
  subst mem1
  change v1=if Num.intVal mem mn h L<Num.intVal mem l h L ∧
    Num.intVal mem l h L<Num.intVal mem mx h L then 1 else 0 at hv1
  have hv1b : v1≤1 := by split_ifs at hv1 <;> omega
  have hprod : v0*v1<2^w := lt_of_le_of_lt
    (by simpa using Nat.mul_le_mul hv0b hv1b) hw
  refine runs_ret_le (v:=v0*v1) (by eval_expr) ?_ ?_
  · change mem=mem ∧ v0*v1=if
      Num.intVal mem neg h L<Num.intVal mem g h L ∧
      Num.intVal mem g h L<Num.intVal mem mx h L ∧
      Num.intVal mem mn h L<Num.intVal mem l h L ∧
      Num.intVal mem l h L<Num.intVal mem mx h L then 1 else 0
    refine ⟨rfl,?_⟩
    rw [hv0,hv1]
    by_cases hg0 : Num.intVal mem neg h L<Num.intVal mem g h L ∧
      Num.intVal mem g h L<Num.intVal mem mx h L <;>
      by_cases hl0 : Num.intVal mem mn h L<Num.intVal mem l h L ∧
        Num.intVal mem l h L<Num.intVal mem mx h L <;>
      simp [hg0,hl0]
  · simp only [coefficientRangeGuardContract,strictRangeContract,List.getD_cons_zero,
      List.getD_cons_succ,Expr.size_bin,Expr.size_reg,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
