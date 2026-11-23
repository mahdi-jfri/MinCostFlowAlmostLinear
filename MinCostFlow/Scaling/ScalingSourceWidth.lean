module

public import WordRAM.Entry

/-!
# Polynomial bounds on a chosen source width

A padded binary source logarithm addresses at most twice the source size
base. Consequently multiplier `c` addresses at most the `2*c` power of
that base. This upper bound lets the outer program reserve a constant
number of complete phase regions and then fit them at a larger fixed
multiplier on the original input.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The addressable region at source multiplier `c` is bounded by source
size-base power `2*c`, including multiplier zero. -/
theorem wordCapacity_le_source_power (c : ℕ) (input : List ℕ) :
    2^wordSize c input≤(input.length+input.foldr max 0+2)^(2*c) := by
  let B := input.length+input.foldr max 0+2
  have hB : 2≤B := by dsimp only [B]; omega
  have hlog : 2^(Nat.log 2 B+1)≤2*B := by
    rw [pow_succ]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2
      (Nat.pow_log_le_self 2 (show B≠0 by omega))
  have htwo : 2*B≤B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right B hB
  change 2^(c*(Nat.log 2 B+1))≤B^(2*c)
  rw [Nat.mul_comm c,pow_mul]
  simpa only [←pow_mul] using Nat.pow_le_pow_left (hlog.trans htwo) c

/-- Every positive padded source logarithm at multiplier at least four
has room for all small constants in the outer reduction programs. -/
theorem sixteen_le_source_capacity (c : ℕ) (input : List ℕ) (hc : 4≤c) :
    16≤2^wordSize c input := by
  have hw : c≤wordSize c input := by
    unfold wordSize
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left c
      (show 1≤Nat.log 2 (input.length+input.foldr max 0+2)+1 by omega)
  exact Nat.pow_le_pow_right (by decide : 0<2) (hc.trans hw)

end MinCostFlow.Scaling.Machine
