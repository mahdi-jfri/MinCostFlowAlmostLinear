module

public import MinCostFlow.IPM.DataStructureTest
public import MinCostFlow.IPM.GuardedEpochCounts
import Mathlib.Tactic.Linarith

/-!
# The actual dynamic-instance transcript of a target run

Each attempted epoch contributes its input sequence together with the
prefix length actually evaluated before a guard fails. For an upper
target guess, the full epoch induction proves every such prefix hidden
stable. This file records that positive claim on the actual transcript.
It does not discard failed binary-search guesses from the whole search.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- The instance sequences and evaluated horizons of all guarded epochs
actually attempted by one bounded target run. -/
def boundedTargetInstances (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure) :
    ℕ → (Fin I.m → ℝ) → List (DynamicInstance × ℕ)
  | 0, _ => []
  | n+1, base => by
    classical
    exact if residual I F base ≤ 1/4 then [] else
      (epochInstance I U κ (residual I F base) A base,
        2*epochProcessed I U κ (residual I F base) A base I.m)::
      match epochFirstFailure I U κ (residual I F base) A base I.m with
      | some _ => []
      | none => boundedTargetInstances I U F κ A n (epochFlow I U κ (residual I F base) A base I.m)

/-- Every dynamic-instance prefix actually evaluated for an upper guess
is hidden stable with the normalized parameter and explicit magnitude
bound. Both properties are proved for the causal data structure calls. -/
theorem boundedTargetInstances_upper (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (fuel : ℕ) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hpot : 0 < residual I F base → potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U)) :
    ∀ p ∈ boundedTargetInstances I U F κ A fuel base,
      p.1.HiddenStable p.2 (normalizedIpmAlpha I) (ipmPsi I U) := by
  classical
  induction fuel generalizing base with
  | zero => intro p hp; exact False.elim (List.not_mem_nil hp)
  | succ fuel ih =>
    by_cases hstop : residual I F base ≤ 1/4
    · simp only [boundedTargetInstances, hstop, ↓reduceIte, List.not_mem_nil, false_implies, implies_true]
    · have hstart : (1/4 : ℝ) < residual I F base := lt_of_not_ge hstop
      have hpos : 0 < residual I F base := lt_trans (by norm_num) hstart
      have hscan := epochFirstFailure_upper I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
        hbase hroute hstart (hpot hpos) hA
      have hep := epoch_correct I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
        hbase hroute hstart (hpot hpos) hA
      dsimp only at hep
      have hpnew : potential I (alpha I U) F (epochFlow I U κ (residual I F base) A base I.m) ≤
          200*I.m*Real.log (I.m*U) := by
        have hnonneg : 0 ≤ (I.m : ℝ)*((κ*alpha I U/64)^2/500) :=
          mul_nonneg (Nat.cast_nonneg _) (div_nonneg (sq_nonneg _) (by norm_num))
        linarith only [hep.2.2.2.1, hpot hpos, hnonneg]
      have htail := ih _ hep.2.1 hep.1.1 (fun _ => hpnew)
      simp only [boundedTargetInstances, hstop, ↓reduceIte, hscan, epochProcessed,
        Option.getD_none, List.mem_cons]
      intro p hp
      rcases hp with rfl | hp
      · exact hep.2.2.2.2.1
      · exact htail p hp

end MinCostFlow.IPM
