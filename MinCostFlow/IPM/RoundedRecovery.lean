module

public import MinCostFlow.Rounding.Lemma4_1
public import MinCostFlow.IPM.InitialOptimalAuxiliary
import MinCostFlow.IPM.IntegralOptimum
import MinCostFlow.IPM.InitialDomain
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Recovery after rounding an approximate augmented flow

Theorem 4.6 (page 15 of arXiv:2309.16629v1) supplies a half-unit
approximation. The existing rounding algorithm of Lemma 4.1 (page 13)
turns a rational feasible flow into an integral feasible flow without
increasing its cost. Since the optimum is integral, the rounded flow
is exactly optimal. On the augmented instance of Lemma 4.12 of Chen
et al., arXiv:2203.00671v2 (page 31 and Appendix B.1, page 92), the
proved recovery theorem then either returns an original optimum or
certifies infeasibility. This file applies the existing rounding
implementation and retains its dynamic-forest operation counts.
It does not assert that an arbitrary real IPM output is rational.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- An integral feasible flow within one half of an integral optimum
is optimal. Both costs are integers, so their nonnegative difference
cannot be strictly between zero and one. -/
theorem integral_near_optimal_isMinCostFlow (I : Instance) (hI : I.IsValid)
    (g : Fin I.m → ℝ) (hg : I.IsFeasible g) (hint : Rounding.IsIntegral g)
    (hclose : ∀ fstar, I.IsMinCostFlow fstar → I.cost g ≤ I.cost fstar+1/2) :
    I.IsMinCostFlow g := by
  obtain ⟨fstar, hs, hsint⟩ := exists_integral_minCostFlow I hI ⟨g, hg⟩
  obtain ⟨z, hz⟩ := integral_cost I g hint
  obtain ⟨zstar, hzstar⟩ := integral_cost I fstar hsint
  have hh := hclose fstar hs
  rw [hz, hzstar] at hh
  have hlt : (z : ℝ) < (zstar : ℝ)+1 := by linarith only [hh]
  have hltZ : z < zstar+1 := by exact_mod_cast hlt
  have hle : z ≤ zstar := Int.lt_add_one_iff.mp hltZ
  have hcost : I.cost g ≤ I.cost fstar := by
    rw [hz, hzstar]
    exact_mod_cast hle
  exact ⟨hg, fun f hf => hcost.trans (hs.2 f hf)⟩

/-- The existing rational rounding procedure applied to a half-unit
approximation returns an exact optimum. Its proved bounds are at most
`10m` dynamic-forest operations and `19m` other steps. -/
theorem roundFlow_near_optimal (D : Rounding.DynForest) (hD : D.IsSpec)
    (I : Instance) (hI : I.IsValid) (g : Fin I.m → ℚ)
    (hg : I.IsFeasible (fun e => (g e : ℝ)))
    (hclose : ∀ fstar, I.IsMinCostFlow fstar →
      I.cost (fun e => (g e : ℝ)) ≤ I.cost fstar+1/2) :
    let result := Rounding.roundFlow D I g
    I.IsMinCostFlow (fun e => (result.flowArr e : ℝ)) ∧
      result.counts.treeOps ≤ 10*I.m ∧ result.counts.otherSteps ≤ 19*I.m := by
  dsimp only
  have hr := Rounding.roundFlow_correct hD hI hg 0 0
  dsimp only at hr
  obtain ⟨_, _, hint, hfeas, hcost, htree, hother, _⟩ := hr
  refine ⟨integral_near_optimal_isMinCostFlow I hI _ hfeas hint ?_, htree, hother⟩
  intro fstar hs
  exact hcost.trans (hclose fstar hs)

/-- Round a rational half-unit approximation on the prescribed augmented
graph and apply Lemma 4.12's recovery map. This proves the original
optimum-or-infeasible conclusion using the existing rounding algorithm,
with its counts measured against the augmented edge count. -/
theorem rounded_initial_recovery (D : Rounding.DynForest) (hD : D.IsSpec)
    (I : Instance) (U : ℝ) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U)
    (hK : 0 ≤ (K : ℝ)) (hKlarge : 2*I.m*U < (K : ℝ))
    (g : Fin (initialInstance I K).m → ℚ)
    (hg : (initialInstance I K).IsFeasible (fun e => (g e : ℝ)))
    (hclose : ∀ fstar, (initialInstance I K).IsMinCostFlow fstar →
      (initialInstance I K).cost (fun e => (g e : ℝ)) ≤
        (initialInstance I K).cost fstar+1/2) :
    let result := Rounding.roundFlow D (initialInstance I K) g
    (I.IsMinCostFlow (recoverInitialFlow I K (fun e => (result.flowArr e : ℝ))) ∨
      ¬ ∃ f, I.IsFeasible f) ∧
      result.counts.treeOps ≤ 10*(initialInstance I K).m ∧
      result.counts.otherSteps ≤ 19*(initialInstance I K).m := by
  dsimp only
  have hr := roundFlow_near_optimal D hD (initialInstance I K)
    (initialInstance_valid I K hI) g hg hclose
  dsimp only at hr
  exact ⟨initial_optimum_recovery I U K hI hordered hU hnums hK hKlarge _ hr.1, hr.2⟩

/-- The fixed-point form of the recovery step. Lemma 4.1 (page 13)
constructs the rational input for its existing rounder from the supplied
dyadic flow, preserving every coordinate. Its integral output is an
augmented optimum and therefore satisfies Lemma 4.12's recovery theorem.
The operation bounds are the `20M` bounds in Lemma 4.1. -/
theorem dyadic_rounded_initial_recovery (D : Rounding.DynForest) (hD : D.IsSpec)
    (I : Instance) (U : ℝ) (K : ℤ) (hI : I.IsValid)
    (hordered : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U)
    (hK : 0 ≤ (K : ℝ)) (hKlarge : 2*I.m*U < (K : ℝ))
    (g : Fin (initialInstance I K).m → ℝ) (P : ℕ)
    (hg : (initialInstance I K).IsFeasible g)
    (hfixed : ∀ e, ∃ z : ℤ, g e = (z : ℝ)/(2 : ℝ)^P)
    (hclose : ∀ fstar, (initialInstance I K).IsMinCostFlow fstar →
      (initialInstance I K).cost g ≤ (initialInstance I K).cost fstar+1/2) :
    ∃ gQ : Fin (initialInstance I K).m → ℚ, (∀ e, (gQ e : ℝ) = g e) ∧
      let result := Rounding.roundFlow D (initialInstance I K) gQ
      (I.IsMinCostFlow (recoverInitialFlow I K (fun e => (result.flowArr e : ℝ))) ∨
        ¬ ∃ f, I.IsFeasible f) ∧
        result.counts.treeOps ≤ 20*(initialInstance I K).m ∧
        result.counts.otherSteps ≤ 20*(initialInstance I K).m := by
  obtain ⟨gQ, hcast, hint, hfeas, hcost, htree, hother, _⟩ :=
    Rounding.lemma_4_1 hD (initialInstance_valid I K hI) hg hfixed
  have hopt := integral_near_optimal_isMinCostFlow (initialInstance I K)
    (initialInstance_valid I K hI) _ hfeas hint
    (fun fstar hs => hcost.trans (hclose fstar hs))
  exact ⟨gQ, hcast,
    initial_optimum_recovery I U K hI hordered hU hnums hK hKlarge _ hopt, htree, hother⟩

/-- The rational rounding input conditions can hold together whenever
the original feasible set is nonempty. An integral optimum supplies
such an input, without assuming a rationality oracle. -/
theorem exists_roundFlow_near_optimal_input (I : Instance) (hI : I.IsValid)
    (hne : ∃ f, I.IsFeasible f) :
    ∃ g : Fin I.m → ℚ, I.IsFeasible (fun e => (g e : ℝ)) ∧
      (∀ fstar, I.IsMinCostFlow fstar →
        I.cost (fun e => (g e : ℝ)) ≤ I.cost fstar+1/2) := by
  obtain ⟨f, hf, hint⟩ := exists_integral_minCostFlow I hI hne
  choose z hz using hint
  let g : Fin I.m → ℚ := fun e => (z e : ℚ)
  have heq : (fun e => (g e : ℝ)) = f := by
    funext e
    simpa only [g, Rat.cast_intCast] using (hz e).symm
  refine ⟨g, heq.symm ▸ hf.1, ?_⟩
  intro fstar hs
  rw [heq]
  have hh := hf.2 fstar hs.1
  linarith only [hh]

end MinCostFlow.IPM
