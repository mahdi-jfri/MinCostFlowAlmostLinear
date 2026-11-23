module

public import WordRAM.LinkDefs

/-!
# Addressable storage of a canonical guest

A multiplier-five guest word has five times the padded binary logarithm
of its encoding size base. The power of two at that width is at most the
fifth power of twice the base. This converts a bound on encoded numbers
into a polynomial host-memory reserve.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A multiplier-five canonical guest has polynomially many addressable
cells in its source encoding size base. -/
theorem canonicalGuest_space_le (input : List ℕ) :
    2^wordSize 5 input≤(2*(input.length+input.foldr max 0+2))^5 := by
  let B := input.length+input.foldr max 0+2
  have hpositive : 0<B := by dsimp only [B]; omega
  have hlog : 2^(Nat.log 2 B+1)≤2*B := by
    rw [pow_succ]
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (Nat.ne_of_gt hpositive))
  change 2^(5*(Nat.log 2 B+1))≤(2*B)^5
  rw [Nat.mul_comm 5,pow_mul]
  exact Nat.pow_le_pow_left hlog 5

end MinCostFlow.Scaling.Machine
