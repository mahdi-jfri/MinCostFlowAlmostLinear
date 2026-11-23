module

public import MinCostFlow.IPM.Machine.ConnectedPairOrder
public import MinCostFlow.IPM.Machine.RecoverPrefix
public import MinCostFlow.IPM.ConnectedInitialRecovery
import Mathlib.Tactic

/-!
# Recovering the circulation prefix from a connected optimum

Both blocks for zero deficits follow all of the original records.
The existing prefix read therefore recovers the original coordinates
after rounding the connected augmented flow.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open Scaling Rounding

/-- The original positive-capacity edges retain their input indices. -/
def connectedOriginalIndex (J : Circulation) (K : ℤ) (hp : ∀ e, 1 ≤ J.capacity e)
    (j : Fin J.m) : Fin (connectedInitialInstance J.toInstance K).m :=
  ⟨j.val,j.isLt.trans_le (connectedInitial_circulation_m_ge J hp K)⟩

/-- Removing all hub edges amounts to reading the input prefix. -/
theorem recoverConnectedInitialFlow_prefix (J : Circulation) (K : ℤ) (hp : ∀ e, 1 ≤ J.capacity e)
    (g : Fin (connectedInitialInstance J.toInstance K).m → ℝ) :
    recoverInitialFlow J.toInstance K (restrictConnectedInitialFlow J.toInstance K g) =
      J.inputFlow (fun e => g (connectedOriginalIndex J K hp e)) := by
  rw [recoverInitialFlow_prefix J K hp]
  funext e
  simp only [Circulation.inputFlow, restrictConnectedInitialFlow, flowOfArray, flowToArray]
  congr 1

/-- The first original coordinates of a rounded connected optimum
give nonnegative integral values of an optimal circulation. -/
theorem connectedRecoverPrefix_optimal (J : Circulation) (U : ℝ) (K : ℤ)
    (hp : ∀ e, 1 ≤ J.capacity e) (hU : 0 ≤ U) (hNums : NumbersBounded J.toInstance U)
    (hK : 2*J.toInstance.m*U^2 < (K:ℝ)) (hK' : 2*J.toInstance.m*U < (K:ℝ))
    (g : Fin (connectedInitialInstance J.toInstance K).m → ℚ)
    (hg : (connectedInitialInstance J.toInstance K).IsMinCostFlow (fun e => (g e:ℝ)))
    (hz : IsIntegral (fun e => (g e:ℝ))) :
    ∃ q : Fin J.m → ℕ,
      (∀ e, g (connectedOriginalIndex J K hp e) = (q e:ℚ)) ∧
      J.Optimal (fun e => (q e:ℝ)) ∧ ∀ e, q e ≤ J.capacity e := by
  let f : Fin J.m → ℝ := fun e => (g (connectedOriginalIndex J K hp e):ℝ)
  have hOrdered (e : Fin J.toInstance.m) :
      (J.toInstance.edge e).lower ≤ (J.toInstance.edge e).upper := by
    rw [Circulation.toInstance_edge]
    exact Int.natCast_nonneg _
  have hsome : ∃ f,J.toInstance.IsFeasible f :=
    ⟨_,(J.toInstance_feasible_iff _).mpr J.zero_feasible⟩
  have hOriginal : J.toInstance.IsMinCostFlow (J.inputFlow f) := by
    rw [← recoverConnectedInitialFlow_prefix J K hp (fun e => (g e:ℝ))]
    exact (connectedInitial_optimum_recovery J.toInstance U K J.toInstance_valid
      hU hNums hK hK' hOrdered _ hg hz).resolve_right (fun h => h hsome)
  have hOpt := (J.toInstance_minCostFlow_iff f).mp hOriginal
  have hInt : ∀ e : Fin J.m, ∃ n : ℤ, f e = n := fun e => hz (connectedOriginalIndex J K hp e)
  choose n hn using hInt
  let q := fun e => (n e).toNat
  have hq (e : Fin J.m) : f e = (q e:ℝ) := by
    have hNon : 0 ≤ (n e:ℝ) := (hn e) ▸ (hOpt.1.2 e).1
    have hh : 0 ≤ n e := by exact_mod_cast hNon
    have he : (q e:ℤ) = n e := Int.toNat_of_nonneg hh
    rw [hn e, ← he, Int.cast_natCast]
  refine ⟨q, ?_, (funext hq) ▸ hOpt, ?_⟩
  · intro e
    have he : (g (connectedOriginalIndex J K hp e):ℝ) = (q e:ℝ) := hq e
    exact_mod_cast he
  · intro e
    have h := (hOpt.1.2 e).2
    rw [hq e] at h
    exact_mod_cast h

end MinCostFlow.IPM.Machine
