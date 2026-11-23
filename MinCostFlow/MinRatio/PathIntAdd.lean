module

public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Add

/-!
# Adding stored path numerators

The flow and length operations of Algorithm 2 (page 29) add
fixed-point numerators. These lemmas connect the library addition
procedure to path blocks when the signed result fits.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Prepare addition of two stored path numerators. -/
theorem addPathInt_pre {w h a d L heap : ℕ} {x y : ℤ} {mem : ℕ → ℕ}
    (hx : PathIntAt mem a h L x) (hy : PathIntAt mem d h L y)
    (ha : a + L ≤ heap) (hd : d + L ≤ heap) (hz : ZeroFrom mem heap)
    (hm : heap + L < 2 ^ w) :
    (Num.addContract w h).pre [a, d, L, heap] mem :=
  ⟨a, d, L, heap, rfl, ⟨⟨a, d, L, 0, heap, rfl, ha, hd, by decide, hx.1, hy.1⟩, hz, hm⟩⟩

/-- Interpret a fitting addition result as a path numerator. -/
theorem addPathInt_post {w h a d L heap ret : ℕ} {x y : ℤ} {mem mem' : ℕ → ℕ}
    (hx : PathIntAt mem a h L x) (hy : PathIntAt mem d h L y) (hfit : Num.Fits h L (x + y))
    (hout : (Num.addContract w h).post [a, d, L, heap] mem ret mem') :
    ret = heap + L ∧ (∀ z < heap, mem' z = mem z) ∧ ZeroFrom mem' ret ∧
      PathIntAt mem' heap h L (x + y) := by
  obtain ⟨hret, _, _, hframe, hz, hdigits⟩ := hout
  change ListAt mem' heap (Num.digits h L
    (Num.unsignedVal mem a h L + Num.unsignedVal mem d h L + 0)) at hdigits
  obtain ⟨hv, he⟩ := Num.addCarry_value hdigits
  rw [hx.2, hy.2, Int.natCast_zero, add_zero, Num.wrap_of_fits hfit] at he
  exact ⟨hret, hframe, hz, hv, he⟩

end MinCostFlow.MinRatio
