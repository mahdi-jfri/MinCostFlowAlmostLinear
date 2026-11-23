module

public import MinCostFlow.HierPaths.BuildTopPlayerBase
public import MinCostFlow.HierPaths.BuildTopPlayerPower

/-! # Computing the common router scale below the root -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The padded root exponent and core rank determine all non-root scales. -/
def buildTopPlayerScale (power : ℕ) : Stmt :=
  .assign 2 (buildTopCoreBaseExpr (.reg 0)) ;;
  .call 3 power [.reg 2, .reg 1] ;;
  .ret (.bin .mul (.const 4) (.reg 3))

theorem buildTopPlayerScale_noRand (power : ℕ) : (buildTopPlayerScale power).NoRand := by
  simp [buildTopPlayerScale, Stmt.NoRand]

/-- Compute the common scale in time linear in the core rank. -/
private theorem scaleFromBase {w f power x rank F : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopPlayerScale power))
    (hp : p.procs[power]? = some buildTopPlayerPower)
    (hpos : 0 < F)
    (heval : ∀ s : State, s.regs 0 = x → F < 2 ^ w →
      (buildTopCoreBaseExpr (.reg 0)).eval w s = some F) :
    MeetsContract w p f {
      pre := fun args _ => args = [x,rank] ∧ 0 < x ∧ 0 < rank ∧
        rank < 2 ^ w ∧ 4 * F ^ rank < 2 ^ w
      post := fun _ mem v mem' =>
        v = 4 * F ^ rank ∧ mem' = mem
      cost := fun _ _ => 13 * rank + 100 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl,hx,hr,hrw,hw⟩ := hpre
  have hpow : F ^ rank < 2 ^ w := (Nat.le_mul_of_pos_left _ (by decide)).trans_lt hw
  have hF : F < 2 ^ w := (Nat.le_self_pow (by omega : rank ≠ 0) F).trans_lt hpow
  have h4 : 4 < 2 ^ w :=
    (Nat.le_mul_of_pos_right _ (Nat.pow_pos hpos)).trans_lt hw
  have h1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildTopPlayerScale
  refine runs_seq_assign_le (v := F) (heval _ rfl hF) ?_
  refine runs_seq_call_le (buildTopPlayerPower_meetsContract hp) (vs := [F,rank])
    rfl ?_ ⟨rfl,hpos,hpow,hrw,h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hF
    · exact hrw
  intro v mem' pos' hpost
  have hv : v = F ^ rank := hpost.1
  have hm : mem' = mem := hpost.2
  refine runs_ret_le (v := 4 * F ^ rank) (Expr.eval_mul (Expr.eval_const h4)
    (Expr.eval_reg_of_eq (by simpa only [Function.update_self] using hv)) hw) ?_ ?_
  · exact ⟨show 4 * F ^ rank = 4 * F ^ rank from rfl, hm⟩
  · simp [Expr.size, argsSize, buildTopCoreBaseExpr, buildTopBaseMul, buildTopBaseSquare]
    omega

/-- Specialize the scale computation to the expansion loss of the padded root. -/
theorem buildTopPlayerScale_meetsContract {w f power x rank : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopPlayerScale power))
    (hp : p.procs[power]? = some buildTopPlayerPower) (hx : 0 < x) :
    MeetsContract w p f {
      pre := fun args _ => args = [x,rank] ∧ 0 < x ∧ 0 < rank ∧
        rank < 2 ^ w ∧ 4 * PParam ParamConfig.default (2 ^ x) rank < 2 ^ w
      post := fun _ mem v mem' =>
        v = 4 * PParam ParamConfig.default (2 ^ x) rank ∧ mem' = mem
      cost := fun _ _ => 13 * rank + 100 } := by
  unfold PParam
  apply scaleFromBase hf hp
  · rw [buildTopCoreFactor x hx]
    exact Nat.mul_pos (Nat.mul_pos (by decide) (Nat.pow_pos (by omega))) (Nat.succ_pos _)
  · intro s hs hF
    exact eval_buildTopCoreBaseExpr (Expr.eval_reg_of_eq hs) hx hF

end MinCostFlow.HierPaths

end
