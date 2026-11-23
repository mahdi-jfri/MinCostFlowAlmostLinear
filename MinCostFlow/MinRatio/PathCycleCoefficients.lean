module

import MinCostFlow.MinRatio.PathNormalizationRange
public import MinCostFlow.Chain.Algorithm2
import MinCostFlow.Chain.WalkFlow
import MinCostFlow.LSF.Congestion

/-!
# Integer coefficients of the direction used by Algorithm 2

Algorithm 2 (page 29) routes the circulation returned by Algorithm 1.
It is the signed sum of the edges of an oriented walk, so each of its
coordinates is an integer. A gradient table at precision `P` therefore
gives a directional inner product at the same precision.
-/

public section

namespace MinCostFlow.MinRatio

open Chain

private theorem walkFlow_integral (walk : List (ℕ × Bool)) (e : ℕ) :
    ∃ z : ℤ, walkFlow walk e = (z : ℝ) := by
  induction walk with
  | nil => exact ⟨0, by simp [walkFlow_nil]⟩
  | cons x rest ih =>
    obtain ⟨z, hz⟩ := ih
    let c : ℤ := if x.1 = e then (if x.2 then 1 else -1) else 0
    refine ⟨c + z, ?_⟩
    rw [walkFlow_cons, hz, Int.cast_add]
    by_cases he : x.1 = e <;> cases hx : x.2 <;> simp [c, he, hx]

/-- Algorithm 1 returns an integral direction after translating back
to original edge names, including the zero direction for an empty choice. -/
theorem findCycle_lift_integral {T : SparseCoreRestartTool} {P : ChainParams}
    (s : ChainState T P) (G : MGraph) (f : ℕ → ℕ) (e : ℕ) :
    ∃ z : ℤ, liftEdgeFn G f (algorithm1_findCycle s).1 e = (z : ℝ) := by
  unfold liftEdgeFn algorithm1_findCycle
  dsimp only
  split
  · split
    · exact walkFlow_integral _ _
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

/-- The directional gradient inner product is the sum of the products of
the stored gradient numerators and integer circulation coefficients. -/
theorem pathFlow_inner_dyadic (G : MGraph) (g C : ℕ → ℝ)
    (P : ℕ) (gradient coefficient : ℕ → ℤ)
    (hg : ∀ e ∈ G.E, g e = ((gradient e : ℤ) : ℝ) / (2 : ℝ) ^ P)
    (hC : ∀ e ∈ G.E, C e = (coefficient e : ℝ)) :
    G.inner g C = ((∑ e ∈ G.E, gradient e * coefficient e : ℤ) : ℝ) / (2 : ℝ) ^ P := by
  unfold MGraph.inner
  rw [Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hg e he, hC e he, Int.cast_mul, div_mul_eq_mul_div]

/-- A returned direction passing the ratio test has the dyadic divisor
bound used by the normalization program. -/
theorem findCycle_lift_inner_lower {T : SparseCoreRestartTool} {P : ChainParams}
    (s : ChainState T P) (G : MGraph) (f : ℕ → ℕ) (g length : ℕ → ℝ)
    {r : ℝ} (E : ℕ) (hr : 1 / (2 : ℝ) ^ E ≤ r)
    (hl : ∀ e ∈ G.E, 1 / (2 : ℝ) ^ E ≤ length e) :
    let C := liftEdgeFn G f (algorithm1_findCycle s).1
    G.inner g C / G.lnorm length C ≤ -r → 1 / (2 : ℝ) ^ (2 * E) ≤ -G.inner g C := by
  dsimp only
  exact pathFlow_inner_dyadic_lower G g length _ E hr hl (fun e _ => findCycle_lift_integral s G f e)

/-- The exact weighted length uses the same precision as the edge
lengths. The integer coefficients contribute their absolute values. -/
theorem pathFlow_length_dyadic (G : MGraph) (length C : ℕ → ℝ)
    (P : ℕ) (len coefficient : ℕ → ℤ)
    (hl : ∀ e ∈ G.E, length e = (len e : ℝ) / (2 : ℝ) ^ P)
    (hC : ∀ e ∈ G.E, C e = (coefficient e : ℝ)) :
    G.lnorm length C = ((∑ e ∈ G.E, len e * |coefficient e| : ℤ) : ℝ) / (2 : ℝ) ^ P := by
  unfold MGraph.lnorm
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  rw [hl e he, hC e he, Int.cast_mul, Int.cast_abs, div_mul_eq_mul_div]

/-- The walk coefficients give a shared integer representation for
the gradient sum and exact weighted length of the lifted direction. -/
theorem findCycle_lift_dyadic_aggregates {T : SparseCoreRestartTool} {P : ChainParams}
    (s : ChainState T P) (G : MGraph) (f : ℕ → ℕ) (g length : ℕ → ℝ)
    (prec : ℕ) (ng nl : ℕ → ℤ)
    (hg : ∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ prec)
    (hl : ∀ e ∈ G.E, length e = (nl e : ℝ) / (2 : ℝ) ^ prec) :
    let C := liftEdgeFn G f (algorithm1_findCycle s).1
    ∃ coeff : ℕ → ℤ, (∀ e, C e = (coeff e : ℝ)) ∧
      G.inner g C = ((∑ e ∈ G.E, ng e * coeff e : ℤ) : ℝ) / (2 : ℝ) ^ prec ∧
      G.lnorm length C = ((∑ e ∈ G.E, nl e * |coeff e| : ℤ) : ℝ) / (2 : ℝ) ^ prec := by
  classical
  dsimp only
  choose coeff hcoeff using findCycle_lift_integral s G f
  exact ⟨coeff, hcoeff, pathFlow_inner_dyadic G g _ prec ng coeff hg (fun e _ => hcoeff e),
    pathFlow_length_dyadic G length _ prec nl coeff hl (fun e _ => hcoeff e)⟩

private theorem walkInner_dyadic (g : ℕ → ℝ) (ng : ℕ → ℤ) (prec : ℕ)
    (walk : List (ℕ × Bool))
    (hg : ∀ e ∈ walkEdges walk, g e = (ng e : ℝ) / (2 : ℝ) ^ prec) :
    ∃ z : ℤ, walkInner g walk = (z : ℝ) / (2 : ℝ) ^ prec := by
  classical
  choose coeff hcoeff using walkFlow_integral walk
  refine ⟨∑ e ∈ walkEdges walk, ng e * coeff e, ?_⟩
  unfold walkInner
  rw [Int.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  rw [hg e he, hcoeff e, Int.cast_mul, div_mul_eq_mul_div]

/-- The root potential of Definition 5.6 (page 18), in the repaired
core-gradient formula, keeps the input gradient's fixed-point precision. -/
theorem treeRootPot_dyadic {G : MGraph} (hforest : G.IsForest)
    (g : ℕ → ℝ) (ng : ℕ → ℤ) (prec v : ℕ)
    (hg : ∀ e ∈ G.E, g e = (ng e : ℝ) / (2 : ℝ) ^ prec) :
    ∃ z : ℤ, treeRootPot G g v = (z : ℝ) / (2 : ℝ) ^ prec :=
  walkInner_dyadic g ng prec _ fun e he => hg e (LSF.walkEdges_forestPath_sub_edges hforest he)

/-- The core gradient is computed by adding the head's integer potential
and subtracting the tail's, with the same denominator as the input (Definition 5.6, page 18). -/
theorem coreGrad_dyadic (G : MGraph) (forest : LSF) (g : ℕ → ℝ)
    (ng potential : ℕ → ℤ) (prec : ℕ) {e : ℕ}
    (hg : g e = (ng e : ℝ) / (2 : ℝ) ^ prec)
    (hpotential : ∀ v, treeRootPot forest.T g v = (potential v : ℝ) / (2 : ℝ) ^ prec) :
    coreGrad G forest g e =
      ((ng e + potential (G.head e) - potential (G.tail e) : ℤ) : ℝ) / (2 : ℝ) ^ prec := by
  unfold coreGrad
  rw [hg, hpotential, hpotential, Int.cast_sub, Int.cast_add, sub_div, add_div]

end MinCostFlow.MinRatio
