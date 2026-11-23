module

public import MinCostFlow.Final.ChainToolBounds
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize
import Mathlib.Tactic

/-!
# The Section 5 model for the connected bounded solver

The geometric configuration uses the connected augmented size.
The numeric parameters use the same size and the original penalty.
-/

public noncomputable section
namespace MinCostFlow.Final
open IPM IPM.Machine Chain Scaling

/-- The Section 5 configuration on the augmented input. -/
@[expose] def QuantitativeChainTools.connectedConfig (T : QuantitativeChainTools) (J : Circulation)
    (hm : 0<J.m) (hp : ∀ e, 1≤J.capacity e) : Alg2Config :=
  ipmWidenedChainConfig (solverConnectedAugmented J) (solverPenalty J.m) T.budget
    (hm.trans_le (connectedInitial_circulation_m_ge J hp (solverPenalty J.m:ℤ))) T.core T.last T.coreParams T.lastParams T.averageStretch

/-- Theorem 5.1 (page 15) fills the widened model field at every
compressed input, with the same threshold the machine uses. -/
theorem QuantitativeChainTools.connectedModel_spec (T : QuantitativeChainTools) (J : Circulation)
    (hn : J.n≤2*J.m+1) (hm : 0<J.m) (hp : ∀ e, 1≤J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := integerQualityExponent T.budget I.m
    MinRatioSpecWithFailureUpTo (algorithm2_dsWithFailure (T.connectedConfig J hm hp)) (1/(2:ℝ)^k)
      (Num.IPM.alphaPrime I.m V/8)
      ((ipmQualityRangeExponent I.m V k+slackRangeExponent I.m V+6 : ℕ) : ℝ)
      ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m V/1024) I.m I.n := by
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  have hM : J.m ≤ I.m := connectedInitial_circulation_m_ge J hp (solverPenalty J.m:ℤ)
  have hN : I.n≤2*I.m+2 := by
    change J.n+1≤2*I.m+2
    change J.m≤I.m at hM
    omega
  have hV : 2≤V := by
    have hCap : 2≤solverCapacityBound J.m := le_max_left _ _
    have hPow : 0<(solverCapacityBound J.m)^2 := pow_pos (by omega) _
    have hh := Nat.le_mul_of_pos_right (4*J.m) hPow
    change 4*J.m≤V at hh
    omega
  have hSize : 2≤I.m*V := hV.trans (by
    have hh := Nat.mul_le_mul_right V (hm.trans_le hM)
    simpa only [Nat.one_mul] using hh)
  have hPenalty : V≤16*I.m^81 :=
    (solverPenalty_le J.m hm).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM _))
  exact (widened_chain_model_and_time I V (hm.trans_le hM) hN hSize hPenalty
    T.core T.last T.coreParams T.lastParams T.averageStretch T.constants
    T.coreParamsValid T.lastParamsValid T.coreSpec T.lastSpec T.averageStretchMono
    T.averageStretchNonneg T.mwu T.embedding T.noReinsert T.quantitative).1

end MinCostFlow.Final
