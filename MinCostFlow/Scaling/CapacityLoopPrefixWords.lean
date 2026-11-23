module

public import MinCostFlow.Scaling.CapacityLoopContract

/-!
# Round-count arithmetic from the full loop reserve

The uniform numerical base bounds the edge count, capacity bound, and
fixed constants. The full fresh-space reserve also bounds the prescribed
fuel because at least one cell is reserved per round. Thus computing the
round count needs no additional numerical premise from the caller.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The full capacity-loop reserve supplies every premise of the exact
round-count procedure on the same host word width. -/
theorem capacityRounds_pre_of_loop_space {w : ℕ} (J : Circulation) (C U heap : ℕ)
    (mem : ℕ → ℕ)
    (hspace : heap+J.m+2+(capacityRounds J.m U+1)*(capacityStepNumberBase J C U)^256<2^w) :
    (capacityRoundsContract w J.m U).pre [J.m,U] mem := by
  let D := capacityStepNumberBase J C U
  let N := D^256
  let fuel := capacityRounds J.m U
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have h16 : 16≤D^2 := Nat.pow_le_pow_left hD4 2
  have hfourD : 4*D≤D^2 := by simpa only [pow_two] using Nat.mul_le_mul_right D hD4
  have h2N : D^2≤N := Nat.pow_le_pow_right hDpos (by decide)
  have hN : 1≤N := by omega
  have hfuelCells : fuel+1≤(fuel+1)*N := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (fuel+1) hN
  have hNCells : N≤(fuel+1)*N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤fuel+1 by omega)
  change heap+J.m+2+(fuel+1)*N<2^w at hspace
  have hNWord : N<2^w := by omega
  refine ⟨rfl,?_,?_,?_,?_⟩
  · omega
  · omega
  · change fuel<2^w
    omega
  · omega

end MinCostFlow.Scaling.Machine
