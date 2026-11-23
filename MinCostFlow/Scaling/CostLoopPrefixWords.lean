module

public import MinCostFlow.Scaling.CostLoopContract

/-!
# Round-count words from the complete cost-loop reserve

Both round-count inputs and their padded logarithmic sum are bounded by
the common cost numerical base. The full power-524 reserve therefore
supplies every word premise of the exact round-count procedure.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- A single full cost-loop space premise also covers the exact round
count, both source increments, and the fixed arithmetic constant. -/
theorem costRounds_pre_of_loop_space {w : ℕ} (J : Circulation) (C U heap : ℕ) (mem : ℕ → ℕ)
    (hs : heap+J.m+2*J.n+3+(costRounds J.n C+1)*(costStepNumberBase J C U)^524<2^w) :
    (costRoundsContract w J.n C).pre [J.n,C] mem := by
  let D := costStepNumberBase J C U
  let N := D^524
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have h1N : D≤N := Nat.le_pow (by decide)
  have hNcells : N≤(costRounds J.n C+1)*N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤costRounds J.n C+1 by omega)
  have hnLog : Nat.clog 2 (J.n+1)≤J.n+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hcLog : Nat.clog 2 (C+1)≤C+1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hfuel : costRounds J.n C≤D := by change 1+Nat.clog 2 (C+1)+Nat.clog 2 (J.n+1)≤D; omega
  change heap+J.m+2*J.n+3+(costRounds J.n C+1)*N<2^w at hs
  refine ⟨rfl,?_,?_,?_,?_⟩ <;> omega

end MinCostFlow.Scaling.Machine
