module

public import MinCostFlow.IPM.Machine.TargetEpochStatic
public import MinCostFlow.IPM.Machine.TargetEpoch

/-!
# Word-fit for the startup and complete epoch packets

Every fixed address already appears in the target-stage arguments.
Fresh addresses lie below the separately reserved workspace endpoint.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Word-fit for the new copy, its residual and its coefficient heap
extends the incoming target-stage packet to the startup packet. -/
theorem targetEpoch_startup_words {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (old : EpochLayout) (tp qp source heap rp fp alloc initEnd : ℕ)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (hr : rp<2^w) (hf : fp<2^w) (ha : alloc<2^w) :
    ∀ z∈(old.next F I source rp fp alloc initEnd).startupPacket F I,z<2^w := by
  intro z hz
  simp only [EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first | exact hr | exact hf | exact ha | exact hwords _ (by simp [targetEpochPacket])

/-- The fixed complete-epoch packet adds only fresh addresses that
fit whenever the initialized endpoint fits. -/
theorem targetEpoch_complete_words {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (old : EpochLayout) (tp qp source heap rp fp alloc initEnd : ℕ)
    (hwords : ∀ z∈targetEpochPacket old F I tp qp source heap,z<2^w)
    (hr : rp<2^w) (hf : fp<2^w) (hi : initEnd<2^w)
    (hh : (old.next F I source rp fp alloc initEnd).handle≤ initEnd) :
    ∀ z∈(old.next F I source rp fp alloc initEnd).packet F I 0,z<2^w := by
  have hp : alloc+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent≤ initEnd := by
    change alloc+(_+_)≤ initEnd at hh
    omega
  change alloc+(Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+
    Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent)≤ initEnd at hh
  intro z hz
  simp only [EpochLayout.packet,EpochLayout.next,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hr | exact hf | exact hi | omega | exact hwords _ (by simp [targetEpochPacket])

end MinCostFlow.IPM.Machine
