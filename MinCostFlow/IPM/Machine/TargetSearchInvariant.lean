module

public import MinCostFlow.IPM.Machine.TargetSearchStep
public import MinCostFlow.IPM.Machine.TargetOffsetTestRun

/-!
# Invariant of the counted binary search

The live bracket contains the optimum offset. Its span halves
with each round, and the search preserves the original starting
flow and all fixed numerical inputs before its heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The half-open power bound for the inclusive interval's span
forces the two endpoints to coincide after the last round. -/
def TargetSearchInvariant {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (qp source heap limit radius tick space : ℕ)
    (mem : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  let rounds := targetSearchRounds radius
  let lo := st.regs 26
  let hi := st.regs 27
  let cur := st.regs 21
  st.regs 28=i ∧ st.regs 25=rounds ∧
  (∀ j<25,j≠6 → st.regs j=(targetOffsetPacket L F I 0 qp source cur limit radius).getD j 0) ∧
  lo≤tick ∧ tick≤hi ∧ hi≤2*radius ∧ hi-lo<2^(rounds-i) ∧
  heap≤cur ∧ cur≤heap+i*space ∧ (∀ b<heap,st.mem b=mem b) ∧ ZeroFrom st.mem cur

/-- The final bracket points at the unique optimal offset. -/
theorem targetSearch_final_offset {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (L : EpochLayout) (qp source heap limit radius tick space : ℕ)
    (mem : ℕ → ℕ) (st : State)
    (h : TargetSearchInvariant F I L qp source heap limit radius tick space mem (targetSearchRounds radius) st) :
    st.regs 26=tick ∧ st.regs 27=tick := by
  obtain ⟨_,_,_,hlo,hhi,_,hSpan,_⟩ := h
  rw [Nat.sub_self,pow_zero] at hSpan
  omega

end MinCostFlow.IPM.Machine
