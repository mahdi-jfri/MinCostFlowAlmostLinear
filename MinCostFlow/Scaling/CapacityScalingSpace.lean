module

public import MinCostFlow.Scaling.CapacityScalingContract
import MinCostFlow.Scaling.VertexCompressionSize
import MinCostFlow.Scaling.BottleneckGuestSpace

/-!
# Original-dimension bounds for the capacity wrapper

Compression keeps the edge arrays and never increases the vertex count.
Consequently its uniform loop reserve is at most the original reserve.
That reserve also bounds the source words and all small control constants.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Compressing vertex names cannot increase the uniform capacity-step reserve. -/
theorem capacityScaling_compressed_power_le (J : Circulation) (C U : ℕ) :
    (capacityStepNumberBase J.compress C U)^256≤(capacityStepNumberBase J C U)^256 := by
  apply Nat.pow_le_pow_left
  have hn := J.compress_vertices_le
  change J.compress.n+2*J.m+C+U+4≤J.n+2*J.m+C+U+4
  omega

/-- The wrapper's fresh-space premise supplies fitting source words and
control constants, including the empty-graph branch. -/
theorem capacityScaling_words_of_space {w : ℕ} (J : Circulation) (C U heap : ℕ)
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U)
    (hspace : heap+capacityScalingSpace J C U<2^w) :
    8<2^w ∧ (∀ x∈J.solverWords,x<2^w) := by
  let D := capacityStepNumberBase J C U
  let N := D^256
  have hD : J.n+2*J.m+C+U+4=D := rfl
  have hD4 : 4≤D := by omega
  have hDpos : 0<D := by omega
  have h16 : 16≤D^2 := Nat.pow_le_pow_left hD4 2
  have h2N : D^2≤N := Nat.pow_le_pow_right hDpos (by decide)
  have hD2 : D≤D^2 := Nat.le_pow (by decide)
  have hmax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D (by omega) (by omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hcells : N≤(capacityRounds J.m U+1)*N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤capacityRounds J.m U+1 by omega)
  change heap+(J.solverWords.length+J.n+2+J.m+2+(capacityRounds J.m U+1)*N+J.m)<2^w at hspace
  refine ⟨by omega,?_⟩
  intro x hx
  have h := Link.elem_le_foldr_max hx
  omega

end MinCostFlow.Scaling.Machine
