module

public import MinCostFlow.Scaling.RoundedRecordProgram

/-!
# Calling rounded-cost arithmetic in successive scratch blocks

The rounded-cost arithmetic reads its operands from argument words. Its
precondition depends on memory only through the fresh zero tail. Moving
the call to another fitting fresh block preserves every arithmetic budget.
This fact allows an edge scan to reuse the scalar contract after each row.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Fresh scratch may move without changing any operand or arithmetic budget. -/
theorem roundedCost_pre_transfer {w : ℕ} {I : Circulation} {s : CostState I} {C : ℕ}
    {e : Fin (I.m+I.m)} {mem mem' : ℕ → ℕ} {heap heap' : ℕ}
    (hpre : (roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem)
    (hzero : ZeroFrom mem' heap') (hspace : heap'+12 < 2 ^ w) :
    (roundedCostContract w s C e).pre (roundedCostArguments s C e heap') mem' := by
  obtain ⟨⟨old, heq, hfactor, hcost, hxy, hpot, hsum, hadjust⟩, _, _⟩ := hpre
  refine ⟨⟨heap', rfl, hfactor, hcost, hxy, hpot, hsum, hadjust⟩, hzero, hspace⟩

/-- A larger word width and a fitting fresh block preserve every scalar
arithmetic budget as well as the zero-tail premise. -/
theorem roundedCost_pre_transfer_width {w w' : ℕ} {I : Circulation} {s : CostState I} {C : ℕ}
    {e : Fin (I.m+I.m)} {mem mem' : ℕ → ℕ} {heap heap' : ℕ}
    (hpre : (roundedCostContract w s C e).pre (roundedCostArguments s C e heap) mem)
    (hw : w ≤ w') (hzero : ZeroFrom mem' heap') (hspace : heap'+12 < 2 ^ w') :
    (roundedCostContract w' s C e).pre (roundedCostArguments s C e heap') mem' := by
  obtain ⟨⟨_, _, hfactor, hcost, hxy, hpot, hsum, hadjust⟩, _, _⟩ := hpre
  have hpow : 2 ^ w ≤ 2 ^ w' := Nat.pow_le_pow_right (by decide) hw
  exact ⟨⟨heap', rfl, hfactor.trans_le hpow, hcost.trans_le hpow, hxy.trans_le hpow,
    hpot.trans_le hpow, hsum.trans_le hpow, hadjust.trans_le hpow⟩, hzero, hspace⟩

end MinCostFlow.Scaling.Machine
