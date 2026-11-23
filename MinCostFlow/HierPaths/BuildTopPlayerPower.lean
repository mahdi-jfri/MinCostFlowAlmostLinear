module

public import WordRAM.Logic

/-!
# Computing the core inverse expansion

Repeated multiplication computes the integer power used by the router
scale. The final power bounds every intermediate power.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are a positive base and the core rank. -/
def buildTopPlayerPower : Stmt :=
  .assign 2 (.const 1) ;;
  forRange 3 (.const 0) (.reg 1) (.assign 2 (.bin .mul (.reg 2) (.reg 0))) ;;
  .ret (.reg 2)

theorem buildTopPlayerPower_noRand : buildTopPlayerPower.NoRand := by
  simp [buildTopPlayerPower, forRange, forUp, Stmt.NoRand]

/-- Compute the power without allocating or changing any memory. -/
theorem buildTopPlayerPower_meetsContract {w f base rank : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildTopPlayerPower) :
    MeetsContract w p f {
      pre := fun args _ => args = [base,rank] ∧ 0 < base ∧
        base ^ rank < 2 ^ w ∧ rank < 2 ^ w ∧ 1 < 2 ^ w
      post := fun _ mem v mem' => v = base ^ rank ∧ mem' = mem
      cost := fun _ _ => 13 * rank + 16 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl,hb,hpow,hrank,h1⟩ := hpre
  refine runs_start_le ?_
  unfold buildTopPlayerPower
  refine runs_seq_assign_le (v := 1) (Expr.eval_const h1) ?_
  let s := startState [base,rank] mem pos
  let J := fun i (t : State) => t.regs 0 = base ∧ t.regs 1 = rank ∧
    t.regs 2 = base ^ i ∧ t.regs 3 = i ∧ t.mem = mem
  have hl := Triple.forRange_le (w := w) (p := p) (r := 3)
    (lo := .const 0) (hi := .reg 1) (body := .assign 2 (.bin .mul (.reg 2) (.reg 0)))
    (P := fun t => t = { s with regs := Function.update s.regs 2 1 }) (Inv := J)
    (fun _ => 4) 0 rank (Nat.zero_le _) h1 (fun _ => hrank)
    (fun t ht => by subst t; exact ⟨Expr.eval_const (Nat.two_pow_pos _),
      rfl, rfl, by simp, by simp, rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1) ?_
  · refine runs_seq_triple_le hl rfl ?_
    intro t ⟨_,_,hval,_,hm⟩
    refine runs_ret_le (Expr.eval_reg_of_eq hval) ⟨rfl,hm⟩ ?_
    simp [Expr.size, rangeCost_const]
    omega
  intro i _ hi
  have hstep : base ^ i * base < 2 ^ w := by
    rw [← pow_succ]
    exact (Nat.pow_le_pow_right hb (Nat.succ_le_of_lt hi)).trans_lt hpow
  refine Triple.assign (P := J i) (val := fun _ => base ^ i * base) (fun t h =>
    Expr.eval_mul (Expr.eval_reg_of_eq h.2.2.1) (Expr.eval_reg_of_eq h.1) hstep) ?_
  · intro t ⟨r0,r1,r2,r3,hm⟩
    simp [J, Function.update_of_ne, pow_succ, r0,r1,r3,hm]

end MinCostFlow.HierPaths

end
