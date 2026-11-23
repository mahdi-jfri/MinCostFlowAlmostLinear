module

public import MinCostFlow.IPM.Machine.SolverPolynomialSpace
public import MinCostFlow.Final.Scratch
import MinCostFlow.IPM.Machine.SolverInitialBounds
import WordRAM.Entry

/-!
# Scratch for the bounded IPM solver

The numeric guard and the allocation bound enter the same reservation.
A polynomial bound on reciprocal quality and polynomial bounds on the
three allocation envelopes give a uniform polynomial reservation.
-/

public section
namespace MinCostFlow.Final
open WordRAM Scaling IPM.Machine

/-- With fixed quality exponent, polynomial allocation envelopes give
polynomial IPM scratch. The operation rates enter only the time bound. -/
theorem ipmWorkspace_polynomial (r : SolverResources) (n m c d k : ℕ)
    (hk : r.qualityExponent ≤ k)
    (hCycle : ∀ M ∈ Finset.Icc m (3*m), r.cycleSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestInit : ∀ M ∈ Finset.Icc m (3*m), r.forestInitSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestOp : ∀ M ∈ Finset.Icc m (3*m), r.forestOpSpace (n+1) M ≤ c*(n+m+2)^d) :
    solverWorkspace r n m ≤ (n+m+2)^(10*(Nat.clog 2 c+d+2*k+240)) := by
  let B := n+m+2
  have hB : 2 ≤ B := by unfold B; omega
  have hc : c ≤ B^Nat.clog 2 c :=
    (Nat.le_pow_clog (by decide : 1 < 2) c).trans (Nat.pow_le_pow_left hB _)
  have hAbsorb : c*B^d ≤ B^(Nat.clog 2 c+d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hc
  exact (solverWorkspace_polynomial r n m (Nat.clog 2 c+d)
      (fun M hM => (hCycle M hM).trans hAbsorb)
      (fun M hM => (hForestInit M hM).trans hAbsorb)
      (fun M hM => (hForestOp M hM).trans hAbsorb)).trans
    (Nat.pow_le_pow_right (by omega : 0 < B) (by omega))

/-- An edge-linear bound on reciprocal quality is enough for polynomial
scratch at runtime, with no uniform bound on the quality exponent. -/
theorem ipmRuntimeWorkspace_polynomial (r : SolverRuntimeResources) (n m c d Ck : ℕ)
    (hk : ∀ M, 2^r.qualityExponent M ≤ Ck*(M+2))
    (hCycle : ∀ M ∈ Finset.Icc m (3*m), r.template.cycleSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestInit : ∀ M ∈ Finset.Icc m (3*m), r.template.forestInitSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestOp : ∀ M ∈ Finset.Icc m (3*m), r.template.forestOpSpace (n+1) M ≤ c*(n+m+2)^d) :
    solverRuntimeWorkspace r n m ≤
      (n+m+2)^(10*(Nat.clog 2 c+d+2*(Nat.clog 2 Ck+2)+240)) := by
  let B := n+m+2
  have hB : 2 ≤ B := by unfold B; omega
  have absorb (x d : ℕ) : x*B^d ≤ B^(Nat.clog 2 x+d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ ((Nat.le_pow_clog (by decide : 1 < 2) x).trans (Nat.pow_le_pow_left hB _))
  apply solverRuntimeWorkspace_polynomial r n m (Nat.clog 2 c+d) (Nat.clog 2 Ck+2)
  · intro M hM
    have hUpper := (Finset.mem_Icc.mp hM).2
    have hSmall : M+2 ≤ B*B := by
      have hMb : m+2 ≤ B := by unfold B; omega
      have hPair : (m+2)*(m+2) ≤ B*B := Nat.mul_le_mul hMb hMb
      exact (show M+2≤(m+2)*(m+2) by
        rw [Nat.add_mul, Nat.mul_add]
        omega).trans hPair
    exact (hk M).trans ((Nat.mul_le_mul_left Ck (by simpa only [pow_two] using hSmall)).trans (absorb Ck 2))
  · exact fun M hM => (hCycle M hM).trans (absorb c d)
  · exact fun M hM => (hForestInit M hM).trans (absorb c d)
  · exact fun M hM => (hForestOp M hM).trans (absorb c d)

/-- An edge-linear bound on reciprocal quality is enough for polynomial
scratch at widened runtime precision, with no uniform bound on the quality exponent. -/
theorem ipmQualityRuntimeWorkspace_polynomial (r : SolverRuntimeResources) (n m c d Ck : ℕ)
    (hk : ∀ M, 2^r.qualityExponent M ≤ Ck*(M+2))
    (hCycle : ∀ M ∈ Finset.Icc m (3*m), r.template.cycleSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestInit : ∀ M ∈ Finset.Icc m (3*m), r.template.forestInitSpace (n+1) M ≤ c*(n+m+2)^d)
    (hForestOp : ∀ M ∈ Finset.Icc m (3*m), r.template.forestOpSpace (n+1) M ≤ c*(n+m+2)^d) :
    solverQualityRuntimeWorkspace r n m ≤
      (n+m+2)^(10*(Nat.clog 2 c+d+2*(Nat.clog 2 Ck+2)+240)) := by
  let B := n+m+2
  have hB : 2 ≤ B := by unfold B; omega
  have absorb (x d : ℕ) : x*B^d ≤ B^(Nat.clog 2 x+d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ ((Nat.le_pow_clog (by decide : 1 < 2) x).trans (Nat.pow_le_pow_left hB _))
  apply solverQualityRuntimeWorkspace_polynomial r n m (Nat.clog 2 c+d) (Nat.clog 2 Ck+2)
  · intro M hM
    have hUpper := (Finset.mem_Icc.mp hM).2
    have hSmall : M+2 ≤ B*B := by
      have hMb : m+2 ≤ B := by unfold B; omega
      have hPair : (m+2)*(m+2) ≤ B*B := Nat.mul_le_mul hMb hMb
      exact (show M+2≤(m+2)*(m+2) by
        rw [Nat.add_mul, Nat.mul_add]
        omega).trans hPair
    exact (hk M).trans ((Nat.mul_le_mul_left Ck (by simpa only [pow_two] using hSmall)).trans (absorb Ck 2))
  · exact fun M hM => (hCycle M hM).trans (absorb c d)
  · exact fun M hM => (hForestInit M hM).trans (absorb c d)
  · exact fun M hM => (hForestOp M hM).trans (absorb c d)

private def unitLoop : Circulation where
  n := 1
  m := 1
  tail _ := 0
  head _ := 0
  capacity _ := 1
  cost _ := 0

/-- Even a one-edge bounded circulation needs more numerical word bits
than the original scaling adapter grants its guest solver. -/
theorem exists_ipm_width_above_original_guest :
    ∃ J : Circulation, J.CostsBounded (J.m^10) ∧
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) ∧
      wordSize 5 J.solverWords <
        ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m) := by
  refine ⟨unitLoop, ?_, ?_, ?_⟩
  · intro e
    change (0 : ℤ).natAbs ≤ 1
    decide
  · intro e
    change 1 ≤ 1 ∧ 1 ≤ 1
    decide
  · decide

end MinCostFlow.Final
