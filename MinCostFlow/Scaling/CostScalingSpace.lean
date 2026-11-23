module

public import MinCostFlow.Scaling.CostScalingContract
import MinCostFlow.Scaling.VertexCompressionSize
import MinCostFlow.Scaling.CapacityGraphSpaceBounds
import MinCostFlow.Scaling.BottleneckGuestSpace

/-!
# Original-dimension reserves for complete cost scaling

Compression does not increase vertex count, the numerical base, or the
prescribed cost-round count. The direct positive capacity call uses a
smaller reserve than one uniform cost round. That same reserve bounds the
original graph words and the polynomial branch threshold, including the
empty graph case.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

set_option exponentiation.threshold 1024 in
/-- Vertex compression cannot increase the cost loop's uniform round reserve. -/
theorem costScaling_compressed_power_le (J : Circulation) (C U : ℕ) :
    (costStepNumberBase J.compress C U)^524≤(costStepNumberBase J C U)^524 := by
  apply Nat.pow_le_pow_left
  have hn := J.compress_vertices_le
  change J.compress.n+4*J.m+(J.m+J.m)^10+C+U+8≤J.n+4*J.m+(J.m+J.m)^10+C+U+8
  omega

/-- Compression cannot increase the explicit cost-round count. -/
theorem costScaling_compressed_rounds_le (J : Circulation) (C : ℕ) :
    costRounds J.compress.n C≤costRounds J.n C := by
  have hn := Nat.clog_mono_right (b := 2) (Nat.add_le_add_right J.compress_vertices_le 1)
  exact Nat.add_le_add_left hn (1+Nat.clog 2 (C+1))

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- One uniform cost-round reserve also covers the direct positive
capacity-model branch on the compressed graph. -/
theorem costScaling_positive_space_le (J : Circulation) (C U : ℕ) :
    capacityPositiveSpace J.compress C U≤(costStepNumberBase J C U)^524 := by
  let D := costStepNumberBase J C U
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hn := J.compress_vertices_le
  have hbase : capacityGraphSpaceBase J.compress C U≤D := by
    change J.compress.n+2*J.m+C+U+8≤D
    omega
  have h260 : capacityPositiveSpace J.compress C U≤D^260 :=
    (capacityPositiveSpace_le J.compress C U).trans (Nat.pow_le_pow_left hbase 260)
  exact h260.trans (Nat.pow_le_pow_right (by omega : 0<D) (by decide))

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 2048 in
/-- The complete wrapper reserve supplies fitting source words, the
`m^10` threshold, and the small constants for every branch. -/
theorem costScaling_words_of_space {w : ℕ} (J : Circulation) (C U heap : ℕ)
    (hC : J.CostsBounded C) (hu : ∀ e,J.capacity e≤U)
    (hs : heap+costScalingSpace J C U<2^w) :
    8<2^w ∧ (∀ x∈J.solverWords,x<2^w) ∧ (∀ x∈J.compress.solverWords,x<2^w) ∧ J.m^10<2^w := by
  let D := costStepNumberBase J C U
  let N := D^524
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have h1N : D≤N := Nat.le_pow (by decide)
  have hNcells : N≤(costRounds J.n C+2)*N := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right N (show 1≤costRounds J.n C+2 by omega)
  change heap+(J.solverWords.length+J.n+2+J.m+2*J.n+3+(costRounds J.n C+2)*N+J.m+3)<2^w at hs
  have hmax : J.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J D (by omega) (by omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hcompN := J.compress_vertices_le
  have hmaxComp : J.compress.solverWords.foldr max 0≤D := solverWords_max_le_of_bounds J.compress D
    (by omega) (by change J.m≤D; omega)
    (fun e => (hu e).trans (by omega)) (fun e => (hC e).trans (by omega)) (by omega)
  have hpoly : J.m^10≤D := (Nat.pow_le_pow_left (show J.m≤J.m+J.m by omega) 10).trans (by omega)
  refine ⟨by omega,?_,?_,by omega⟩
  · intro x hx
    have h := Link.elem_le_foldr_max hx
    omega
  · intro x hx
    have h := Link.elem_le_foldr_max hx
    omega

end MinCostFlow.Scaling.Machine
