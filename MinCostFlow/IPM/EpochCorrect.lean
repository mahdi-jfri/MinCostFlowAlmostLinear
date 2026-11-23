module

public import MinCostFlow.IPM.EpochInvariants
public import MinCostFlow.IPM.EpochAccounts
import MinCostFlow.IPM.IterationBound
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Correctness and operation counts of a full IPM epoch

The adapted Lemmas 9.1--9.4 of Chen et al., arXiv:2203.00671v2
(Section 9, pages 69--72), now imply the claims for a full causal epoch.
The proof establishes hidden stability of the actual input sequence,
feasibility of the returned flow, and its potential decrease. It also
bounds the actual Query count, total Detect output size, and primitive
coefficient-update size. The numbers of Update and Detect calls are the
epoch length by construction. A full final flow read adds `m` Queries.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- One full causal epoch of `m` updates has hidden stable inputs and
potential decrease `m(κ α/64)²/500`. It uses at most `5m` coordinate
Queries, returns at most `5m` total Detect edges, and refreshes at most
`10m` primitive updates. Reading its final flow costs `m` more Queries. The comparison flow
need only be feasible with cost at most the target, so this also covers
upper guesses in the cost search. -/
theorem epoch_correct (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hstart : (1/4 : ℝ) < residual I F base)
    (hpot : potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U))
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)) :
    let r := residual I F base
    let result := epochState I U κ r A base I.m
    I.IsFeasible (epochFlow I U κ r A base I.m) ∧
      StrictlyInside I (epochFlow I U κ r A base I.m) ∧
      0 < residual I F (epochFlow I U κ r A base I.m) ∧
      potential I (alpha I U) F (epochFlow I U κ r A base I.m) ≤
        potential I (alpha I U) F base-I.m*((κ*alpha I U/64)^2/500) ∧
      (epochInstance I U κ r A base).HiddenStable (2*I.m) (normalizedIpmAlpha I) (ipmPsi I U) ∧
      result.queries ≤ 5*I.m ∧ result.detected ≤ 5*I.m ∧ result.updateSize ≤ 10*I.m := by
  dsimp only
  let r := residual I F base
  have hinv := epoch_invariants I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
    hbase hroute hstart hpot hA
  dsimp only at hinv
  have hfull := hinv I.m le_rfl
  have hv := epoch_history_valid_prefix I U κ r A base (2*I.m) hI
    (by intro j hj; exact (hinv j (by omega)).2.2.2.1)
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have hcounts := epoch_refresh_counts I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
    (ipmDetectThreshold I U κ) A base (2*I.m) I.m hA hv le_rfl he.1 (by
      intro j hj
      have hh := (hfull.2.2.2.2.2.2.2 j hj).1
      exact hh.trans (by linarith only [he.1]))
  have hdet := epoch_detected_eq_queries I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
    (ipmDetectThreshold I U κ) A base (2*I.m) I.m hA hv le_rfl
  have hhidden := epoch_hiddenStable_of_numerical I U F κ r A base fstar (2*I.m)
    hm hU hsize hnums hk hk' hs hF hA hv
    (fun j hj => (hinv j (by omega)).2.2.2.1)
    (fun j hj => (hinv j (by omega)).2.1)
    (fun j hj => (hinv j (by omega)).1)
    (fun j hj => (hinv j (by omega)).2.2.2.2.2.2.1)
    (fun j hj => (hinv j (by omega)).2.2.2.2.1)
    (fun j hj => (hinv j (by omega)).2.2.2.2.2.1)
    (by intro j hj; exact (hfull.2.2.2.2.2.2.2 j (by omega)).1)
  have hdrop := potential_after_steps (fun j => potential I (alpha I U) F (epochFlow I U κ r A base j))
    ((κ*alpha I U/64)^2/500) I.m (fun j hj => (hfull.2.2.2.2.2.2.2 j hj).2)
  rw [epochFlow_zero I U κ r (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)
    A base hI hbase hA] at hdrop
  refine ⟨feasible_of_inside I _ hfull.1 hfull.2.1, hfull.2.1, hfull.2.2.1, hdrop,
    hhidden, hcounts.1, ?_, hcounts.2⟩
  rw [hdet]
  exact hcounts.1

end MinCostFlow.IPM
