module

public import MinCostFlow.IPM.Machine.ConnectedSolverPolynomialSpace
import Mathlib.Tactic

/-!
# Scaling scratch for `SolverForestRuntimeResources`

Proves a polynomial bound on `forestConnectedSolverRuntimeWorkspace` when
`forestOpSpace L` grows polynomially in `(L + 1)` and `(n + m + 2)`.
-/

public section
namespace MinCostFlow.Final
open IPM.Machine

/-- Polynomial scratch degree for `SolverForestRuntimeResources`, absorbing the
limb factor `L + 1 ≤ (n + m + 2) ^ (Nat.clog 2 Ck + 52)` into the exponent. -/
@[expose] def forestScratchDegree (c d Ck : ℕ) : ℕ :=
  10 * (Nat.clog 2 c + d + Nat.clog 2 Ck + 52 + 2 * (Nat.clog 2 Ck + 3) + 240)

/-- An edge-linear bound on reciprocal quality together with `c * (n + m + 2)^d`
space bounds (`c * (L + 1) * (n + m + 2)^d` for `forestOpSpace`) suffices for
polynomial scratch in `forestConnectedSolverRuntimeWorkspace`. -/
theorem connectedForestIPMRuntimeWorkspace_polynomial (r : SolverForestRuntimeResources)
    (n m c d Ck : ℕ)
    (hk : ∀ M, 2 ^ r.qualityExponent M ≤ Ck * (M + 2))
    (hCycle : ∀ M ∈ Finset.Icc m (7 * m), r.template.cycleSpace (n + 1) M ≤ c * (n + m + 2) ^ d)
    (hForestInit : ∀ M ∈ Finset.Icc m (7 * m), r.template.forestInitSpace (n + 1) M ≤ c * (n + m + 2) ^ d)
    (hForestOp : ∀ M ∈ Finset.Icc m (7 * m),
      let L := ipmQualityLimbs M (solverPenalty m) (r.qualityExponent M)
      r.template.forestOpSpace L (n + 1) M ≤ c * (L + 1) * (n + m + 2) ^ d) :
    forestConnectedSolverRuntimeWorkspace r n m ≤
      (n + m + 2) ^ (forestScratchDegree c d Ck) := by
  let B := n + m + 2
  let q := Nat.clog 2 Ck + 3
  have hB : 2 ≤ B := by unfold B; omega
  have absorb (x e : ℕ) : x * B ^ e ≤ B ^ (Nat.clog 2 x + e) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ ((Nat.le_pow_clog (by decide : 1 < 2) x).trans (Nat.pow_le_pow_left hB _))
  have hQ : ∀ M ∈ Finset.Icc m (7 * m), 2 ^ r.qualityExponent M ≤ B ^ q := by
    intro M hM
    have hUpper := (Finset.mem_Icc.mp hM).2
    have hSmall : M + 2 ≤ B ^ 3 := by
      have hMb : m + 2 ≤ B := by unfold B; omega
      have h7 : (7 * (m : ℤ) + 2 ≤ ((m : ℤ) + 2) ^ 3) := by
        have h : (0 : ℤ) ≤ m := Int.natCast_nonneg _
        nlinarith [sq_nonneg (m : ℤ), pow_nonneg h 3]
      exact (show M + 2 ≤ 7 * m + 2 by omega).trans
        ((by exact_mod_cast h7 : 7 * m + 2 ≤ (m + 2) ^ 3).trans (Nat.pow_le_pow_left hMb _))
    exact (hk M).trans ((Nat.mul_le_mul_left Ck hSmall).trans (absorb Ck 3))
  let D := Nat.clog 2 c + d + q + 49
  have hD₁ : Nat.clog 2 c + d ≤ D := by dsimp [D]; omega
  unfold forestConnectedSolverRuntimeWorkspace
  split
  · exact Nat.zero_le _
  · rename_i hm
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    have hw := forestConnectedSolverRuntimeWorkspace_polynomial r n m D q hQ
      (fun M hM => (hCycle M hM).trans ((absorb c d).trans (Nat.pow_le_pow_right (by omega) hD₁)))
      (fun M hM => (hForestInit M hM).trans ((absorb c d).trans (Nat.pow_le_pow_right (by omega) hD₁)))
      (fun M hM => by
        obtain ⟨hLo, hHi⟩ := Finset.mem_Icc.mp hM
        have hLbd := ipmQualityLimbs_connected_poly n m M (r.qualityExponent M) q hm_pos hLo hHi (hQ M hM)
        have hL1 : ipmQualityLimbs M (solverPenalty m) (r.qualityExponent M) + 1 ≤
            B ^ (max 41 q + 8) := by
          have hp1 : 1 ≤ B ^ (max 41 q + 7) := Nat.one_le_pow _ _ (by omega)
          have h2 : B ^ (max 41 q + 7) + B ^ (max 41 q + 7) ≤ B * B ^ (max 41 q + 7) := by
            have := Nat.mul_le_mul_right (B ^ (max 41 q + 7)) hB
            omega
          calc _ ≤ B ^ (max 41 q + 7) + B ^ (max 41 q + 7) := Nat.add_le_add hLbd hp1
            _ ≤ B * B ^ (max 41 q + 7) := h2
            _ = B ^ (max 41 q + 8) := by rw [← pow_succ']
        have hL1' : ipmQualityLimbs M (solverPenalty m) (r.qualityExponent M) + 1 ≤ B ^ (q + 49) :=
          hL1.trans (Nat.pow_le_pow_right (by omega) (by omega))
        calc r.template.forestOpSpace (ipmQualityLimbs M (solverPenalty m) (r.qualityExponent M)) (n + 1) M
            ≤ c * (ipmQualityLimbs M (solverPenalty m) (r.qualityExponent M) + 1) * B ^ d := hForestOp M hM
          _ ≤ c * B ^ (q + 49) * B ^ d :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hL1')
          _ = c * B ^ (d + q + 49) := by rw [mul_assoc, ← pow_add, show q + 49 + d = d + q + 49 by omega]
          _ ≤ B ^ D := by simpa [D, add_assoc] using absorb c (d + q + 49))
    unfold forestConnectedSolverRuntimeWorkspace at hw
    rw [ite_eq_right hm] at hw
    exact hw

end MinCostFlow.Final