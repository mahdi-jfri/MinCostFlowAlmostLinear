module

public import MinCostFlow.MinRatio.QueryOutput
public import MinCostFlow.Chain.Algorithm2

/-!
# Connecting the Query output to the Algorithm 2 model

Section 6 (pages 29–30) keeps flow in the dynamic trees and reads a
coordinate on demand. The output procedure receives only one edge
value. If its original-direction flow represents that coordinate,
the scalar written to the old heap is the model's Query answer.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- A resolved edge value with a fitting original-direction flow
satisfies the numeric and address conditions of the output procedure. -/
theorem queryOutput_pre_of_pathEdge {w h L P a heap : ℕ} {mem : ℕ → ℕ} {value : PathEdgeValue}
    (hv : PathEdgeAt mem a h L (some value)) (hfit : Num.Fits h L value.originalFlow)
    (hsrc : a + 2 + 2 * L + L ≤ heap)
    (hz : ZeroFrom mem heap) (hroom : heap + L < 2 ^ w) :
    (queryOutputContract w h P).pre
      [a + 2 + 2 * L, (if value.forward then 1 else 0), L, heap] mem := by
  obtain ⟨_, _, _, _, hflow, _⟩ := hv
  refine ⟨⟨_, _, _, _, rfl, ?_, hsrc, hflow.1, ?_⟩, hz, hroom⟩
  · cases value.forward <;> decide
  · intro hd
    have hf : value.forward = false := by
      cases ha : value.forward <;> simp [ha] at hd ⊢
    rw [hflow.2]
    simpa only [PathEdgeValue.originalFlow, hf, Bool.false_eq_true, ↓reduceIte] using hfit

/-- When the edge-value layout represents the model coordinate, the
query output is the exact scalar required by Definition 4.5 (page 14). -/
theorem queryOutput_algorithm2_scalar {w h L P a heap ret e : ℕ}
    {cfg : Alg2Config} {st : Alg2State cfg} {mem mem' : ℕ → ℕ} {value : PathEdgeValue}
    (hv : PathEdgeAt mem a h L (some value))
    (hflow : (value.originalFlow : ℝ) / (2 : ℝ) ^ P = algorithm2_query cfg st e)
    (hout : (queryOutputContract w h P).post
      [a + 2 + 2 * L, (if value.forward then 1 else 0), L, heap] mem ret mem') :
    ScalarAt mem' heap h L P (algorithm2_query cfg st e) := by
  obtain ⟨_, _, _, _, hblock, _⟩ := hv
  have ho := hout.2.2.2.2.2
  change ScalarAt mem' heap h L P
    (if (if value.forward then 1 else 0 : ℕ) = 0 then
      -Num.fixVal mem (a + 2 + 2 * L) h L P else Num.fixVal mem (a + 2 + 2 * L) h L P) at ho
  rw [← hflow]
  cases hf : value.forward <;>
    simpa [Num.fixVal, PathEdgeValue.originalFlow, hf, hblock.2, Int.cast_neg, neg_div] using ho

end MinCostFlow.MinRatio
