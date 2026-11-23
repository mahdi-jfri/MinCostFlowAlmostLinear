module

public import MinCostFlow.SparseCore.Program.AssemblyModel

/-!
# The first phase of a branch step: two bounds by the charge and the caps

The first phase of the step of a branch (`AsmBrCoreStepAt`, `AssemblyBranchStepIface.lean`) must
bound the work of P7's step by the charge of the model. This file proves two small facts that the
bounds of its post use.

* `batchEnc_U_S_le_branchStepCharge`: the encoding size of the output batch `U_S` is at most the
  step charge `branchStepCharge`. The charge has the term `S_cur.batchEnc U_S` times the log factor
  `bundleLogFactor`, and that factor is at least one.
* `log_two_mul_eCap_add_one_le`: when the caps meet the cap bound of the branch,
  `vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`, then `⌊log₂ (2 eCap + 1)⌋ ≤ capExp · (⌊log₂ (M + N + 2)⌋ + 1)`.
  The split lists of one step are paid with the factor `2 ⌊log₂ (2 eCap + 1)⌋` per leaving end
  (`OutSplitBound.lean`), and this turns that factor into the log factor of the interface.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.DynSpanner

/-- The log factor of the model is at least one. -/
theorem one_le_bundleLogFactor (M N : ℕ) : 1 ≤ bundleLogFactor M N := by
  unfold bundleLogFactor
  exact Nat.one_le_pow _ _ (Nat.succ_pos _)

/-- **The output batch is paid by the step charge.** The encoding size of the output batch `U_S`
of a step is at most the step charge `branchStepCharge`, since the charge holds the term
`S_cur.batchEnc U_S` times a log factor that is at least one. -/
theorem batchEnc_U_S_le_branchStepCharge {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord ord').U_S ≤
      branchStepCharge sparsify tr U ord ord' := by
  dsimp only [branchStepCharge]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ (one_le_bundleLogFactor _ _))
  omega

/-- **The log of the edge cap.** When the caps meet the cap bound of a branch,
`vCap + eCap + 2 ≤ (M + N + 2) ^ capExp`, the log of `2 eCap + 1` is at most `capExp` times the
log factor `⌊log₂ (M + N + 2)⌋ + 1`. -/
theorem log_two_mul_eCap_add_one_le {capExp vCap eCap M N : ℕ}
    (hcap : vCap + eCap + 2 ≤ (M + N + 2) ^ capExp) :
    Nat.log 2 (2 * eCap + 1) ≤ capExp * (Nat.log 2 (M + N + 2) + 1) := by
  set X := M + N + 2
  set l := Nat.log 2 X
  -- the exponent is not zero, since `X ^ 0 = 1 < vCap + eCap + 2`
  have hc : capExp ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcap
    omega
  -- `X < 2 ^ (l + 1)`, so `X ^ capExp < 2 ^ ((l + 1) capExp)`
  have hX : X < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by decide) X
  have hXc : X ^ capExp < 2 ^ ((l + 1) * capExp) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left hX hc
  -- so `2 eCap + 1 < 2 X ^ capExp < 2 ^ (capExp (l + 1) + 1)`
  have hlt : 2 * eCap + 1 < 2 ^ (capExp * (l + 1) + 1) := by
    rw [pow_succ, Nat.mul_comm capExp]
    omega
  exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hlt)

end MinCostFlow.SparseCore.Program
