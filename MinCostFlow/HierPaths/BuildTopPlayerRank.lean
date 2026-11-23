module

public import MinCostFlow.HierPaths.Params
public import WordRAM.Logic
public import MinCostFlow.HierPaths.BoundsProgBlocks

/-!
# Computing the core rank from the number of input edges

The rank is the least integer whose cube reaches the ceiling binary
logarithm of eight times the edge count plus eight.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The rank procedure takes the input edge count as its only argument. -/
def buildTopPlayerRank : Stmt :=
  .assign 20 (.bin .add (.bin .mul (.const 8) (.reg 0)) (.const 8)) ;;
  clogBlock ;;
  .assign 20 (.reg 21) ;;
  cbrtBlock ;;
  .ret (.reg 21)

theorem buildTopPlayerRank_noRand : buildTopPlayerRank.NoRand := by
  simp [buildTopPlayerRank, clogBlock_noRand, cbrtBlock_noRand, Stmt.NoRand]

/-- The rank procedure reuses the ceiling-logarithm and cube-root loops. -/
theorem buildTopPlayerRank_meetsContract {w f m : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildTopPlayerRank) :
    MeetsContract w p f {
      pre := fun args _ => args = [m] ∧ 8 * m + 8 < 2 ^ w ∧ depthOf m ^ 3 < 2 ^ w
      post := fun _ mem v mem' => v = depthOf m ∧ mem' = mem
      cost := fun _ _ => 13 * (Nat.log 2 (8 * m + 7) + 1) + 19 * depthOf m + 64 } := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hm, hpow⟩ := hpre
  have h8 : 8 < 2 ^ w := by omega
  have h4 : 4 ≤ 2 ^ w := by omega
  have hs : xOf m < 2 ^ w := by
    unfold xOf
    apply lt_of_le_of_lt _ hm
    rw [Nat.clog_le_iff_le_pow (by decide)]
    exact Nat.lt_two_pow_self.le
  have hpos : 1 ≤ xOf m := by
    unfold xOf
    apply Nat.succ_le_of_lt
    rw [Nat.lt_clog_iff_pow_lt (by decide)]
    simp only [pow_zero]; omega
  refine runs_start_le ?_
  unfold buildTopPlayerRank
  refine runs_seq_assign_le (v := 8 * m + 8)
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const h8) (Expr.eval_reg_of_eq (v := m) rfl)
      (by omega)) (Expr.eval_const h8) hm) ?_
  refine runs_seq_triple_le (clogBlock_triple (by omega) hm h4 _ (by rfl)) rfl ?_
  intro t ⟨ht, hmem, _, _⟩
  refine runs_seq_assign_le (v := xOf m) (Expr.eval_reg_of_eq ht) ?_
  refine runs_seq_triple_le (cbrtBlock_triple hpos hs hpow h4 _ (by rfl)) rfl ?_
  intro u ⟨hu, hum, _, _⟩
  refine runs_ret_le (v := depthOf m) (Expr.eval_reg_of_eq hu) ⟨rfl, hum.trans hmem⟩ ?_
  simp [Expr.size, depthOf]
  omega

end MinCostFlow.HierPaths

end
