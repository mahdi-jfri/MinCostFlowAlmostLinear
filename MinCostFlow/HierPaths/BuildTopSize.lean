module

public import MinCostFlow.HierPaths.BoundsProgBlocks
public import MinCostFlow.HierPaths.PortsHost

/-!
# The padded root size

The terminal count is the least power of two covering the two ports
of each input edge. The integer logarithm routine computes its exponent.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Given the number of input edges, return the bit count for the root terminals. -/
def buildTopSize : Stmt :=
  .assign 20 (.bin .add (.reg 0) (.reg 0)) ;;
  clogBlock ;;
  .ret (.reg 21)

theorem buildTopSize_noRand : buildTopSize.NoRand := by
  simp [buildTopSize, clogBlock_noRand, Stmt.NoRand]

def buildTopSizeContract (w : ℕ) : Contract where
  pre args _ := ∃ m, args = [m] ∧ 1 ≤ m ∧ 2 * m < 2 ^ w
  post args mem v mem' := v = Nat.clog 2 (2 * args.getD 0 0) ∧ mem' = mem
  cost args _ := 30 * args.getD 0 0 + 30

theorem buildTopSize_meetsContract {w f : ℕ} {p : Program}
    (hp : p.procs[f]? = some buildTopSize) :
    MeetsContract w p f (buildTopSizeContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨m, rfl, hm, hw⟩ := hpre
  have h4 : 4 ≤ 2 ^ w := by
    cases w with
    | zero => simp at hw; omega
    | succ w =>
      cases w with
      | zero => simp at hw; omega
      | succ w =>
        exact Nat.pow_le_pow_right (i := 2) (j := w + 1 + 1) (by decide : 0 < 2) (by omega)
  have he : m + m = 2 * m := by omega
  refine runs_start_le ?_
  unfold buildTopSize
  refine runs_seq_assign_le (v := 2 * m) (Expr.eval_eq_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (v := m) rfl) (Expr.eval_reg_of_eq (v := m) rfl)
      (by rwa [he])) he) ?_
  refine runs_seq_triple_le (clogBlock_triple (n := 2 * m) (by omega) hw h4 _ rfl) rfl ?_
  intro s ⟨hr, hmem, _, _⟩
  refine runs_ret_le (Expr.eval_reg_of_eq hr) ⟨rfl, hmem⟩ ?_
  have hl := Nat.log_le_self 2 (2 * m - 1)
  simp [buildTopSizeContract, Expr.size]
  omega

end MinCostFlow.HierPaths

end
