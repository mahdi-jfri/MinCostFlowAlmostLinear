module

public import MinCostFlow.Final.IPMWorkspace
public import MinCostFlow.IPM.Machine.ConnectedSolverPolynomialSpace
import Mathlib.Tactic

/-!
# Scaling scratch for the connected bounded solver

The connected solver's augmented size is at most seven times the input
edge count. Its reciprocal-quality bound still gives polynomial scratch.
-/

public section
namespace MinCostFlow.Final
open IPM.Machine

/-- An edge-linear bound on reciprocal quality is enough for polynomial
scratch at widened runtime precision, with no uniform bound on the quality exponent. -/
theorem connectedIPMRuntimeWorkspace_polynomial (r : SolverRuntimeResources) (n m c d Ck : ℕ)
    (hk : ∀ M, 2^r.qualityExponent M ≤ Ck*(M+2))
    (hCycle : ∀ M ∈ Finset.Icc m (7*m), r.template.cycleSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestInit : ∀ M ∈ Finset.Icc m (7*m), r.template.forestInitSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestOp : ∀ M ∈ Finset.Icc m (7*m), r.template.forestOpSpace (n+1) M ≤ c*(n+m+2)^d) :
    connectedSolverRuntimeWorkspace r n m ≤
      (n+m+2)^(10*(Nat.clog 2 c+d+2*(Nat.clog 2 Ck+3)+240)) := by
  let B := n+m+2
  have hB : 2 ≤ B := by unfold B; omega
  have absorb (x d : ℕ) : x*B^d ≤ B^(Nat.clog 2 x+d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ ((Nat.le_pow_clog (by decide : 1 < 2) x).trans (Nat.pow_le_pow_left hB _))
  apply connectedSolverRuntimeWorkspace_polynomial r n m (Nat.clog 2 c+d) (Nat.clog 2 Ck+3)
  · intro M hM
    have hUpper := (Finset.mem_Icc.mp hM).2
    have hSmall : M+2 ≤ B^3 := by
      have hMb : m+2 ≤ B := by unfold B; omega
      have h7 : (7*(m:ℤ)+2 ≤ ((m:ℤ)+2)^3) := by
        have h : (0:ℤ) ≤ m := Int.natCast_nonneg _
        nlinarith [sq_nonneg (m:ℤ), pow_nonneg h 3]
      exact (show M+2 ≤ 7*m+2 by omega).trans
        ((by exact_mod_cast h7 : 7*m+2 ≤ (m+2)^3).trans (Nat.pow_le_pow_left hMb _))
    exact (hk M).trans ((Nat.mul_le_mul_left Ck hSmall).trans (absorb Ck 3))
  · exact fun M hM => (hCycle M hM).trans (absorb c d)
  · exact fun M hM => (hForestInit M hM).trans (absorb c d)
  · exact fun M hM => (hForestOp M hM).trans (absorb c d)

end MinCostFlow.Final
