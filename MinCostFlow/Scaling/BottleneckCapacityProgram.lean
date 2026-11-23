module

public import WordRAM.Contract
import WordRAM.Logic
import WordRAM.Tactic

/-!
# The scalar capacity test for bottleneck search

Keep an edge at unit capacity exactly when its original capacity is
positive and at least the candidate threshold. Zero-capacity slots stay
inactive even when the threshold is zero. The procedure implements this
test with equality and strict comparison on natural words.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[capacity,threshold]`. -/
def bottleneckCapacityBody : Stmt :=
  .cond (.bin .eq (.reg 0) (.const 0)) (.ret (.const 0))
    (.cond (.bin .lt (.reg 0) (.reg 1)) (.ret (.const 0)) (.ret (.const 1)))

/-- The scalar bottleneck test occupies one procedure slot. -/
def bottleneckCapacityModule : List Stmt := [bottleneckCapacityBody]

/-- Exact unit-capacity predicate with unchanged memory. -/
def bottleneckCapacityContract (w capacity threshold : ℕ) : Contract where
  pre args _ := args = [capacity,threshold] ∧ 1 < 2^w
  post _ mem ret mem' := mem'=mem ∧ ret = if 0 < capacity ∧ threshold ≤ capacity then 1 else 0
  cost _ _ := 20

/-- The scalar test has no random instruction. -/
theorem bottleneckCapacityBody_noRand : bottleneckCapacityBody.NoRand := by
  simp only [bottleneckCapacityBody,Stmt.NoRand,and_self]

/-- The machine tests the exact active-edge predicate of the bottleneck
model, including its zero-capacity case, with constant cost. -/
theorem bottleneckCapacity_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b bottleneckCapacityModule) (capacity threshold : ℕ) :
    MeetsContract w p b (bottleneckCapacityContract w capacity threshold) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hw⟩ := hpre
  have hc : capacity < 2^w := hwords _ List.mem_cons_self
  have ht : threshold < 2^w := hwords _ (List.mem_cons_of_mem _ List.mem_cons_self)
  apply runs_start_le
  unfold bottleneckCapacityBody
  wram_step
  · have hz : capacity=0 := by simpa only [startState,List.getD_cons_zero] using hcond
    refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
    · exact ⟨rfl,by simp only [hz,lt_self_iff_false,false_and,↓reduceIte]; rfl⟩
    · simp only [bottleneckCapacityContract,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
  · have hpos : 0 < capacity := by
      have hh : capacity≠0 := by simpa only [startState,List.getD_cons_zero] using hcond
      omega
    wram_step
    · have hlt : capacity < threshold := by
        simpa only [startState,List.getD_cons_succ,List.getD_cons_zero] using hcond
      refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
      · exact ⟨rfl,by rw [ite_eq_right (by omega : ¬ (0 < capacity ∧ threshold ≤ capacity))]; rfl⟩
      · simp only [bottleneckCapacityContract,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega
    · have hle : threshold ≤ capacity := by
        have hh : ¬ capacity < threshold := by
          simpa only [startState,List.getD_cons_succ,List.getD_cons_zero] using hcond
        omega
      refine runs_ret_le (v := 1) (by eval_expr) ?_ ?_
      · exact ⟨rfl,(ite_eq_left ⟨hpos,hle⟩).symm⟩
      · simp only [bottleneckCapacityContract,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega

/-- Every capacity and threshold have simultaneous argument and constant
bounds at a finite word size. -/
theorem exists_bottleneckCapacity_pre (capacity threshold : ℕ) :
    ∃ w,(∀ x ∈ [capacity,threshold],x < 2^w) ∧
      (bottleneckCapacityContract w capacity threshold).pre [capacity,threshold] (fun _ => 0) := by
  let w := capacity+threshold+3
  have hw : capacity+threshold+3 < 2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,rfl,by omega⟩
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
