module

public import MinCostFlow.Final.AssemblyDryRunSCInitSpace
public import MinCostFlow.MinRatio.OrdSolverUpdateClauses
import Mathlib.Tactic

/-!
# Reduction of `hCapBounds` and `hEnv` to plain inequalities on `B` and `sz` (`AssemblyDryRunSCEnvelope`)

Reduces the two numeric and envelope obligations of `DrySCSolverHyps`
(`Final/AssemblyDryRunSC.lean`) to plain arithmetic inequalities on `B : OrdSolverInnerBounds`
and `sz : Circulation → Circulation → WiredInnerSizes`:

1. **`DryFixedPointCapBounds` (`dryFixedPointCapBounds_of_bounds`):**
   Using the IPM precision margin `4 * F.limbs ≥ F.fmt.precision + 92 * F.rangeExponent +
   12 * I.m.size + 1480`, all seven fixed-point capacity inequalities follow from six simple
   power-of-2 inequalities on `s.B_tree`, `s.B_bound`, `s.R_bound`, and `s.maxEdges + s.maxPaths`:
   * `2 ^ (P + 2 * E + 1) ≤ s.B_tree ≤ 2 ^ (P + 80 * E)`,
   * `2 ^ (P + 2 * E + 1) ≤ s.B_bound ≤ 2 ^ (P + 80 * E)`,
   * `s.R_bound ≤ 2 ^ (P + 80 * E)`,
   * `s.maxEdges + s.maxPaths < 2 ^ (3 * E + 20)`.

2. **`OrdSolverContractEnvelopeFullCredit` (`ordSolverContractEnvelopeFullCredit_of_ineqs`,
   `drySC_hEnv_of_ineqs`):**
   Discharges Init, Update (`op = 0`), Query (`op = 1`), and Detect (`op = 2`) from six plain
   arithmetic inequalities (`DryEnvelopeIneqs B hB sz`) together with the single reachability
   bound `tok.offReadyCount ≤ B.names I.m` (which does not follow from `OrdSolverReachedInv` alone,
   because `OrdSolverReachedInv` bounds `model.nextFresh` without upper-bounding `tok.intCap` or
   `tok.offReadyCount`). Inside Update (`op = 0`), `updateBudgetNoLoop_le_noIntCap` removes any
   dependence on `tok.intCap`, and `ceil_largeBatchEncCap_le` bounds `⌈largeBatchEncCap⌉₊` by
   `(40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40) * U.length` for `U.length ≤ 2 * I.m`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## Part 1: Reduction of `DryFixedPointCapBounds` to six plain power-of-2 bounds -/

/-- Six plain power-of-2 inequalities on `sz` that imply all seven clauses of
`DryFixedPointCapBounds`. -/
structure DryCapSimpleBounds (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop where
  hBounds : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let E := F.rangeExponent
      let P := F.fmt.precision
      let s := sz source J
      (2 : ℤ) ^ (P + 2 * E + 1) ≤ s.B_tree ∧
      s.B_tree ≤ (2 : ℤ) ^ (P + 80 * E) ∧
      (2 : ℤ) ^ (P + 2 * E + 1) ≤ s.B_bound ∧
      s.B_bound ≤ (2 : ℤ) ^ (P + 80 * E) ∧
      s.R_bound ≤ (2 : ℤ) ^ (P + 80 * E) ∧
      s.maxEdges + s.maxPaths < 2 ^ (3 * E + 20)

private theorem ipmQuality_four_limbs_ge (m V k : ℕ) :
    ipmQualityPrecision m V k + 92 * ipmQualityRangeExponent m V k + 12 * m.size + 1480 ≤
      4 * ipmQualityLimbs m V k := by
  dsimp only [ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits]
  omega

private theorem ipmQualityRangeExponent_ge_100 (m V k : ℕ) :
    100 ≤ ipmQualityRangeExponent m V k := by
  dsimp only [ipmQualityRangeExponent]; omega

private theorem capBounds_arith {P E L n msz maxEdges maxPaths : ℕ}
    {B_tree B_bound R_bound : ℤ}
    (h4L : P + 92 * E + 12 * msz + 1480 ≤ 4 * L)
    (hE100 : 100 ≤ E)
    (h2n1 : 2 * n + 1 < 2 ^ (msz + 3))
    (hn1 : n + 1 < 2 ^ (msz + 2))
    (hBtLo : (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_tree)
    (hBtHi : B_tree ≤ (2 : ℤ) ^ (P + 80 * E))
    (hBbLo : (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_bound)
    (hBbHi : B_bound ≤ (2 : ℤ) ^ (P + 80 * E))
    (hRbHi : R_bound ≤ (2 : ℤ) ^ (P + 80 * E))
    (hEP : maxEdges + maxPaths < 2 ^ (3 * E + 20)) :
    (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_bound ∧
    (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_tree ∧
    2 * ((2 * n + 1 : ℕ) : ℤ) * B_tree < (Num.capacity 4 L : ℤ) ∧
    maxEdges + maxPaths < 2 ^ (3 * E + 20) ∧
    2 * (((maxEdges + maxPaths * n : ℕ) : ℤ) * B_bound) < (Num.capacity 4 L : ℤ) ∧
    2 * ((2 * n + 1 : ℕ) : ℤ) *
      ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P))) <
      (Num.capacity 4 L : ℤ) ∧
    B_bound + (2 : ℤ) ^ (3 * E + 2 + P) < (Num.capacity 4 L : ℤ) := by
  have hCapEq : (Num.capacity 4 L : ℤ) = (2 : ℤ) ^ (4 * L) := by
    unfold Num.capacity Num.base
    rw [← pow_mul]
    push_cast
    rfl
  have h2n1Z : ((2 * n + 1 : ℕ) : ℤ) < (2 : ℤ) ^ (msz + 3) := by exact_mod_cast h2n1
  have hpowZ {a b : ℕ} (hab : a ≤ b) : (2 : ℤ) ^ a ≤ (2 : ℤ) ^ b :=
    pow_le_pow_right₀ (by norm_num) hab
  have hpowZ_lt {a b : ℕ} (hab : a < b) : (2 : ℤ) ^ a < (2 : ℤ) ^ b :=
    pow_lt_pow_right₀ (by norm_num) hab
  have h2pos {a : ℕ} : (0 : ℤ) < (2 : ℤ) ^ a := pow_pos (by norm_num) a
  have h2n1NN : (0 : ℤ) ≤ 2 * ((2 * n + 1 : ℕ) : ℤ) :=
    mul_nonneg (by norm_num) (Int.natCast_nonneg _)
  refine ⟨hBbLo, hBtLo, ?_, hEP, ?_, ?_, ?_⟩
  · -- Clause 3
    rw [hCapEq]
    have h1 : 2 * ((2 * n + 1 : ℕ) : ℤ) * B_tree ≤
        2 * ((2 * n + 1 : ℕ) : ℤ) * (2 : ℤ) ^ (P + 80 * E) :=
      mul_le_mul_of_nonneg_left hBtHi h2n1NN
    have h2 : 2 * ((2 * n + 1 : ℕ) : ℤ) * (2 : ℤ) ^ (P + 80 * E) <
        2 * (2 : ℤ) ^ (msz + 3) * (2 : ℤ) ^ (P + 80 * E) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h2n1Z (by norm_num)) h2pos
    have h3 : 2 * (2 : ℤ) ^ (msz + 3) * (2 : ℤ) ^ (P + 80 * E) =
        (2 : ℤ) ^ (P + 80 * E + msz + 4) := by
      calc 2 * (2 : ℤ) ^ (msz + 3) * (2 : ℤ) ^ (P + 80 * E)
          = (2 : ℤ) ^ 1 * (2 : ℤ) ^ (msz + 3) * (2 : ℤ) ^ (P + 80 * E) := by ring
        _ = (2 : ℤ) ^ (1 + (msz + 3) + (P + 80 * E)) := by rw [← pow_add, ← pow_add]
        _ = (2 : ℤ) ^ (P + 80 * E + msz + 4) := by congr 1; omega
    exact lt_of_lt_of_le (h1.trans_lt h2) (by rw [h3]; exact hpowZ (by omega))
  · -- Clause 5
    rw [hCapEq]
    have hprodN : maxEdges + maxPaths * n < 2 ^ (3 * E + msz + 22) := by
      have hle : maxEdges + maxPaths * n ≤ (maxEdges + maxPaths) * (n + 1) := by nlinarith
      calc maxEdges + maxPaths * n
          ≤ (maxEdges + maxPaths) * (n + 1) := hle
        _ < 2 ^ (3 * E + 20) * 2 ^ (msz + 2) := Nat.mul_lt_mul'' hEP hn1
        _ = 2 ^ (3 * E + msz + 22) := by rw [← pow_add]; congr 1; omega
    have hprodZ : ((maxEdges + maxPaths * n : ℕ) : ℤ) < (2 : ℤ) ^ (3 * E + msz + 22) := by
      exact_mod_cast hprodN
    have h1 : 2 * (((maxEdges + maxPaths * n : ℕ) : ℤ) * B_bound) ≤
        2 * (((maxEdges + maxPaths * n : ℕ) : ℤ) * (2 : ℤ) ^ (P + 80 * E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBbHi (Int.natCast_nonneg _)) (by norm_num)
    have h2 : 2 * (((maxEdges + maxPaths * n : ℕ) : ℤ) * (2 : ℤ) ^ (P + 80 * E)) <
        2 * ((2 : ℤ) ^ (3 * E + msz + 22) * (2 : ℤ) ^ (P + 80 * E)) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hprodZ h2pos) (by norm_num)
    have h3 : 2 * ((2 : ℤ) ^ (3 * E + msz + 22) * (2 : ℤ) ^ (P + 80 * E)) =
        (2 : ℤ) ^ (P + 83 * E + msz + 23) := by
      calc 2 * ((2 : ℤ) ^ (3 * E + msz + 22) * (2 : ℤ) ^ (P + 80 * E))
          = (2 : ℤ) ^ 1 * (2 : ℤ) ^ (3 * E + msz + 22) * (2 : ℤ) ^ (P + 80 * E) := by ring
        _ = (2 : ℤ) ^ (1 + (3 * E + msz + 22) + (P + 80 * E)) := by rw [← pow_add, ← pow_add]
        _ = (2 : ℤ) ^ (P + 83 * E + msz + 23) := by congr 1; omega
    exact lt_of_lt_of_le (h1.trans_lt h2) (by rw [h3]; exact hpowZ (by omega))
  · -- Clause 6
    rw [hCapEq]
    have hmp : (maxPaths : ℤ) ≤ (2 : ℤ) ^ (3 * E + 20) := by
      have : maxPaths ≤ 2 ^ (3 * E + 20) := by omega
      exact_mod_cast this
    have hmpTerm : (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P) ≤ (2 : ℤ) ^ (P + 80 * E) := by
      calc (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)
          ≤ (2 : ℤ) ^ (3 * E + 20) * (2 : ℤ) ^ (3 * E + 2 + P) :=
            mul_le_mul_of_nonneg_right hmp h2pos.le
        _ = (2 : ℤ) ^ (P + 6 * E + 22) := by rw [← pow_add]; congr 1; omega
        _ ≤ (2 : ℤ) ^ (P + 80 * E) := hpowZ (by omega)
    have hsum : (B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) ≤
        4 * (2 : ℤ) ^ (P + 80 * E) := by linarith
    have h1 : 2 * ((2 * n + 1 : ℕ) : ℤ) *
        ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) +
          (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P))) ≤
        2 * ((2 * n + 1 : ℕ) : ℤ) * (4 * (2 : ℤ) ^ (P + 80 * E)) :=
      mul_le_mul_of_nonneg_left hsum h2n1NN
    have h2 : 2 * ((2 * n + 1 : ℕ) : ℤ) * (4 * (2 : ℤ) ^ (P + 80 * E)) <
        2 * (2 : ℤ) ^ (msz + 3) * (4 * (2 : ℤ) ^ (P + 80 * E)) :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h2n1Z (by norm_num))
        (mul_pos (by norm_num) h2pos)
    have h3 : 2 * (2 : ℤ) ^ (msz + 3) * (4 * (2 : ℤ) ^ (P + 80 * E)) =
        (2 : ℤ) ^ (P + 80 * E + msz + 6) := by
      calc 2 * (2 : ℤ) ^ (msz + 3) * (4 * (2 : ℤ) ^ (P + 80 * E))
          = (2 : ℤ) ^ 3 * (2 : ℤ) ^ (msz + 3) * (2 : ℤ) ^ (P + 80 * E) := by ring
        _ = (2 : ℤ) ^ (3 + (msz + 3) + (P + 80 * E)) := by rw [← pow_add, ← pow_add]
        _ = (2 : ℤ) ^ (P + 80 * E + msz + 6) := by congr 1; omega
    exact lt_of_lt_of_le (h1.trans_lt h2) (by rw [h3]; exact hpowZ (by omega))
  · -- Clause 7
    rw [hCapEq]
    have hterm : (2 : ℤ) ^ (3 * E + 2 + P) ≤ (2 : ℤ) ^ (P + 80 * E) := hpowZ (by omega)
    have h1 : B_bound + (2 : ℤ) ^ (3 * E + 2 + P) ≤ (2 : ℤ) ^ (P + 80 * E + 1) := by
      rw [pow_succ]; linarith
    exact lt_of_le_of_lt h1 (hpowZ_lt (by omega))

/-- Discharges all seven clauses of `DryFixedPointCapBounds` from `DryCapSimpleBounds`. -/
theorem dryFixedPointCapBounds_of_bounds (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (h : DryCapSimpleBounds B hB sz) :
    DryFixedPointCapBounds dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) sz := by
  intro source J hJn hJm hCost hCap hw
  dsimp only
  obtain ⟨hBtLo, hBtHi, hBbLo, hBbHi, hRbHi, hEP⟩ := h.hBounds source J hJn hJm hCost hCap hw
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hImGeJm : J.m ≤ (solverConnectedAugmented J).m :=
    (solverConnectedAugmented_size J hJn hJm hCap1).1
  have hGnEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
    simp [namedInstance, MGraph.n]
  have hInLe : (solverConnectedAugmented J).n ≤ 2 * (solverConnectedAugmented J).m + 2 := by
    change J.n + 1 ≤ 2 * (solverConnectedAugmented J).m + 2; omega
  have hImLt : (solverConnectedAugmented J).m < 2 ^ (solverConnectedAugmented J).m.size :=
    Nat.lt_size_self _
  have h2m1 : 1 ≤ 2 ^ (solverConnectedAugmented J).m.size := Nat.one_le_pow _ _ (by decide)
  have h2Gn1 : 2 * (namedInstance (solverConnectedAugmented J)).n + 1 <
      2 ^ ((solverConnectedAugmented J).m.size + 3) := by
    rw [hGnEq, pow_add]; omega
  have hGn1 : (namedInstance (solverConnectedAugmented J)).n + 1 <
      2 ^ ((solverConnectedAugmented J).m.size + 2) := by
    rw [hGnEq, pow_add]; omega
  exact capBounds_arith (ipmQuality_four_limbs_ge _ _ _) (ipmQualityRangeExponent_ge_100 _ _ _)
    h2Gn1 hGn1 hBtLo hBtHi hBbLo hBbHi hRbHi hEP

/-! ## Part 2: Helper inequalities for `OrdSolverContractEnvelopeFullCredit` -/

/-- Bounds `updateBudgetNoLoop` without any upper bound on `intCap`, since the growth branch only
runs when `intCap < nextFresh + u`. -/
theorem updateBudgetNoLoop_le_noIntCap {L n intCap nextFresh u maxEdges maxPaths drainUnit rb nf ρ₀ ρ₁ : ℕ}
    (hnf : nextFresh ≤ nf) (hrb : rb ≤ ρ₀ + ρ₁ * u) :
    updateBudgetNoLoop L n intCap nextFresh u maxEdges maxPaths drainUnit rb ≤
      (136 * nf + 820 + 20 * L + ρ₀ + updateGoodBranchBudget L n maxEdges maxPaths drainUnit) +
        (536 + 34 * L + ρ₁) * u := by
  unfold updateBudgetNoLoop
  have h1 : (if intCap < nextFresh + u then 102 * intCap + 34 * (nextFresh + u) + 270 else 50) ≤
      136 * nf + 136 * u + 270 := by
    split_ifs <;> omega
  have h2 : (536 + 34 * L + ρ₁) * u = 136 * u + 300 * u + u * (34 * L + 100) + ρ₁ * u := by ring
  omega

/-- For `U.length ≤ 2 * m` and `m ≤ P.M₀`, `⌈largeBatchEncCap P U⌉₊` is linear in `U.length` with
a logarithmic factor `40 * Nat.clog 2 (3 * P.M₀ + 2) + 40`. -/
theorem ceil_largeBatchEncCap_le (P : ChainParams) {m : ℕ} (U : List Update)
    (hm : m ≤ P.M₀) (hU : U.length ≤ 2 * m) :
    ⌈largeBatchEncCap P U⌉₊ ≤ (40 * Nat.clog 2 (3 * P.M₀ + 2) + 40) * U.length := by
  unfold largeBatchEncCap
  split_ifs with hle
  · simp
  · have hsumLe : P.M₀ + U.length ≤ 2 * U.length := by omega
    have hsumM : P.M₀ + U.length + 2 ≤ 3 * P.M₀ + 2 := by omega
    have hclog : 3 * P.M₀ + 2 ≤ 2 ^ Nat.clog 2 (3 * P.M₀ + 2) :=
      Nat.le_pow_clog (by decide) _
    have hlogLe : Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) ≤
        (Nat.clog 2 (3 * P.M₀ + 2) : ℝ) := by
      have h1 : (P.M₀ : ℝ) + (U.length : ℝ) + 2 ≤ (2 : ℝ) ^ Nat.clog 2 (3 * P.M₀ + 2) := by
        exact_mod_cast le_trans hsumM hclog
      have h2 : (2 : ℝ) ^ Nat.clog 2 (3 * P.M₀ + 2) ≤ Real.exp (Nat.clog 2 (3 * P.M₀ + 2) : ℝ) := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc (2 : ℝ) ^ Nat.clog 2 (3 * P.M₀ + 2)
            ≤ (Real.exp 1) ^ Nat.clog 2 (3 * P.M₀ + 2) := pow_le_pow_left₀ (by norm_num) h2e _
          _ = Real.exp (Nat.clog 2 (3 * P.M₀ + 2) : ℝ) := by
              rw [← Real.exp_nat_mul, mul_one]
      have hpos : (0 : ℝ) < (P.M₀ : ℝ) + (U.length : ℝ) + 2 := by positivity
      calc Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2)
          ≤ Real.log (Real.exp (Nat.clog 2 (3 * P.M₀ + 2) : ℝ)) :=
            Real.log_le_log hpos (h1.trans h2)
        _ = (Nat.clog 2 (3 * P.M₀ + 2) : ℝ) := Real.log_exp _
    have hcap : 20 * ((P.M₀ : ℝ) + (U.length : ℝ)) * Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) ≤
        ((40 * Nat.clog 2 (3 * P.M₀ + 2) + 40) * U.length : ℕ) := by
      have hsumR : (P.M₀ : ℝ) + (U.length : ℝ) ≤ 2 * (U.length : ℝ) := by exact_mod_cast hsumLe
      have hlogNN : 0 ≤ Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) P.M₀, Nat.cast_nonneg (α := ℝ) U.length])
      push_cast
      have hmul : 20 * ((P.M₀ : ℝ) + (U.length : ℝ)) * Real.log ((P.M₀ : ℝ) + (U.length : ℝ) + 2) ≤
          20 * (2 * (U.length : ℝ)) * (Nat.clog 2 (3 * P.M₀ + 2) : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsumR (by norm_num)) hlogLe hlogNN (by positivity)
      have hU0 : (0 : ℝ) ≤ U.length := Nat.cast_nonneg _
      nlinarith
    exact Nat.ceil_le.mpr hcap

/-- Bounds `updateCreditCharge cfg toolMul treeMul U` linearly in `U.length` whenever
`U.length ≤ 2 * m` and `m ≤ cfg.P.M₀`. -/
theorem updateCreditCharge_le_linear (cfg : Alg2Config) {toolMul treeMul m : ℕ} (U : List Update)
    (hm : m ≤ cfg.P.M₀) (hU : U.length ≤ 2 * m) :
    updateCreditCharge cfg toolMul treeMul U ≤
      (toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
          (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
        treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0)) * U.length := by
  unfold updateCreditCharge
  have hlbe := ceil_largeBatchEncCap_le cfg.P U hm hU
  have h1 : toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length +
      ⌈largeBatchEncCap cfg.P U⌉₊) ≤
      toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
        (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) * U.length := by
    have hadd : runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length +
        ⌈largeBatchEncCap cfg.P U⌉₊ ≤
        (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
          (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) * U.length := by
      rw [Nat.add_mul]; exact Nat.add_le_add_left hlbe _
    calc toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length +
          ⌈largeBatchEncCap cfg.P U⌉₊)
        ≤ toolMul * ((runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
            (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) * U.length) :=
          Nat.mul_le_mul_left _ hadd
      _ = _ := by ring
  have h2 : treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 * U.length) =
      treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0) * U.length := by ring
  rw [Nat.add_mul, h2]
  exact Nat.add_le_add_right h1 _

/-! ## Generic envelope reduction lemma and dry-run specialization -/

/-- Generic reduction of `OrdSolverContractEnvelopeFullCredit` (all four clauses: Init, Update,
Query, Detect) to plain arithmetic inequalities on `B` and `s`, including `nfMax + 2 * m ≤ B.names m`.
Because `OrdSolverReachedInv` guarantees `tok.intCap = initTargetCap cfg G = nfMax + 2 * G.m`, the
table-growth branch in `Update` never runs (`updateBudgetNoLoop_le_noGrow`, charging only `50`) and
`tok.offReadyCount ≤ tok.intCap ≤ B.names m` holds automatically in `Detect`. -/
theorem ordSolverContractEnvelopeFullCredit_of_ineqs
    {w m nI V psi k epsExp : ℕ} {F : MinRatioFormat w} {cfg : Alg2Config} {G : MGraph}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {B : OrdSolverInnerBounds} {s : WiredInnerSizes}
    (hGm : G.E.card = m) (hmLeM0 : m ≤ cfg.P.M₀)
    (hLle : F.limbs ≤ B.limbs m)
    (hVle : G.n ≤ B.verts m)
    (hInitSp : s.initSpace' + initWiredExtraSpace cfg G ≤ B.initSpace m)
    (hInitBud :
      (s.initFixed + initWiredExtraCost cfg G) +
        cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220) *
          ((cfg.P.d + 1) * ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊) +
        s.toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
        s.treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0) ≤
      B.initBudget m)
    (hCoreMono : Monotone s.coreSpace)
    (hUpdSp :
      updateSpaceBound F.limbs m cfg.P.d
        (Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0) (2 * m)
        ((Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1))
        (6 + s.selectSpace + s.evalSpace) (max s.termSpace s.deepSpace)
        s.maxEdges s.maxPaths (cfg.P.d + (8 * (2 * m) + 1) + s.coreSpace (2 * m)) + 2 ≤
      B.updateSpace m)
    {ρ₀ ρ₁ : ℕ}
    (hCoreFix : ∀ u ≤ 2 * m, s.coreFixed u ≤ ρ₀ + ρ₁ * u)
    (hUpdRate :
      (600 + 20 * F.limbs +
          (ρ₀ + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 62 * (cfg.P.d + 1) + 240) +
          updateGoodBranchBudget F.limbs G.n s.maxEdges s.maxPaths
            (detectOffTreeDrainUnit F.limbs)) +
        (520 + 34 * F.limbs + ρ₁ +
          (s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
              (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
            s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0))) +
        cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220) +
        cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220) *
          fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 ≤
      B.updateRate m)
    (hNames : Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * m ≤ B.names m) :
    OrdSolverContractEnvelopeFullCredit F cfg G m V psi k epsExp
      (s.initSpace' + initWiredExtraSpace cfg G)
      (s.initFixed + initWiredExtraCost cfg G)
      (6 + s.selectSpace + s.evalSpace) (s.selectBudget + s.evalBudget + 90)
      (max s.termSpace s.deepSpace) (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
      s.maxEdges s.maxPaths s.toolMul s.treeMul
      (fun uLen => cfg.P.d + (8 * uLen + 1) + s.coreSpace uLen)
      (fun uLen => s.coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
        62 * (cfg.P.d + 1) + 240)
      Rcore B.cycleRate (B.cycleAllocation nI m) := by
  have hFixed := B.ordSolverRateAllocFixed_of_le (nI := nI) hLle hVle hInitSp hInitBud
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Init
    intro args _ _
    exact ⟨hFixed.1 args, hFixed.2.1⟩
  · -- Op 0 (`Update`)
    intro root batch g l eta heap mem model tok hrep hreach hpre _ U hBU
    obtain ⟨_, batch', _, _, _, _, U0, hargsEq, _, _, _, hBU0, _, _, _, _, _, _, _, _, _, _, _, hU0Le, _⟩ :=
      hpre.2
    injection hargsEq with _ hargsEq2
    injection hargsEq2 with hbatchEq _
    subst hbatchEq
    have hMemBatchU : mem batch = U.length := by simpa [IPM.Machine.BatchAt, batchWords] using hBU 0 (by simp [batchWords])
    have hMemBatchU0 : mem batch = U0.length := by simpa [IPM.Machine.BatchAt, batchWords] using hBU0 0 (by simp [batchWords])
    have hUlenLe : U.length ≤ 2 * m := by omega
    have hNfLe : model.nextFresh ≤ Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 :=
      hreach.2.2.1
    have hIntCapEq : tok.intCap = initTargetCap cfg G := hreach.2.2.2
    have hGm' : G.m = m := hGm
    have hNoGrow : model.nextFresh + U.length ≤ tok.intCap := by
      rw [hIntCapEq]; unfold initTargetCap; omega
    have hLoopLe : loopStepBound cfg (alg2PreLoopState cfg model U
        (readVector mem g 4 F.limbs F.fmt.precision m)
        (readVector mem l 4 F.limbs F.fmt.precision m)) ≤
        (Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1) :=
      le_trans (Nat.le_succ _) (loopStepBound_lt_pow cfg _)
    have hRefSpLe : cfg.P.d + (8 * U.length + 1) + s.coreSpace U.length ≤
        cfg.P.d + (8 * (2 * m) + 1) + s.coreSpace (2 * m) := by
      have hc := hCoreMono hUlenLe; omega
    constructor
    · dsimp only
      have hmono := updateSpaceBound_mono (L := F.limbs) (m := m) (d := cfg.P.d)
        (fs := 6 + s.selectSpace + s.evalSpace) (ss := max s.termSpace s.deepSpace)
        (me := s.maxEdges) (mp := s.maxPaths) hNfLe hUlenLe hLoopLe hRefSpLe
      exact le_trans (Nat.add_le_add_right hmono 2) hUpdSp
    · dsimp only
      have hrb : s.coreFixed U.length + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * U.length +
          62 * (cfg.P.d + 1) + 240 ≤
          (ρ₀ + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 62 * (cfg.P.d + 1) + 240) +
            (ρ₁ + 120) * U.length := by
        have hcf := hCoreFix U.length hUlenLe; rw [Nat.add_mul]; omega
      have hNoLoop := updateBudgetNoLoop_le_noGrow (L := F.limbs) (n := G.n)
        (intCap := tok.intCap) (maxEdges := s.maxEdges) (maxPaths := s.maxPaths)
        (drainUnit := detectOffTreeDrainUnit F.limbs) hNoGrow hrb
      have hCred := updateCreditCharge_le_linear cfg (toolMul := s.toolMul) (treeMul := s.treeMul)
        U hmLeM0 hUlenLe
      have hComb : updateBudgetNoLoop F.limbs G.n tok.intCap model.nextFresh U.length
            s.maxEdges s.maxPaths (detectOffTreeDrainUnit F.limbs)
            (s.coreFixed U.length + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * U.length +
              62 * (cfg.P.d + 1) + 240) +
          updateCreditCharge cfg s.toolMul s.treeMul U ≤
          (600 + 20 * F.limbs +
              (ρ₀ + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 62 * (cfg.P.d + 1) + 240) +
              updateGoodBranchBudget F.limbs G.n s.maxEdges s.maxPaths
                (detectOffTreeDrainUnit F.limbs)) +
            (520 + 34 * F.limbs + ρ₁ +
              (s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
                  (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
                s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0))) *
              U.length := by
        have heq : (520 + 34 * F.limbs + ρ₁ +
            (s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
                (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
              s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0))) * U.length =
            (400 + 34 * F.limbs + (ρ₁ + 120)) * U.length +
            (s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
                (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
              s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0)) * U.length := by
          ring
        rw [heq]; omega
      have hCharge := OrdSolverInnerBounds.update_charge_le_rate
        (Bc := cycleLoopIterBudget F.limbs cfg.P.d (s.selectBudget + s.evalBudget + 90)
          (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220))
        (W := fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0)
        hComb le_rfl le_rfl
      have hRateLe : B.updateRate m ≤ B.cycleRate m := by
        unfold OrdSolverInnerBounds.cycleRate
        exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
      have hMulRate := Nat.mul_le_mul_right (1 + U.length) (hUpdRate.trans hRateLe)
      rw [hMemBatchU]
      exact le_trans (by omega) (hCharge.trans hMulRate)
  · -- Op 1 (`Query`)
    intro root e heap mem model tok _ hreach _
    have hExtEq : model.extG = G := hreach.1.1.1
    refine ⟨query_space_of_fixed hFixed tok.tree.n _ [root, e, heap], ?_⟩
    rw [hExtEq]
    exact hFixed.2.2.2.1
  · -- Op 2 (`Detect`)
    intro root heap mem model tok hrep hreach _
    have hExtEq : model.extG = G := hreach.1.1.1
    have hCardLe : (algorithm2_detect cfg model).1.card ≤ m := by
      have hsub : (algorithm2_detect cfg model).1.card ≤ model.extG.E.card :=
        Finset.card_filter_le _ _
      rw [hExtEq] at hsub
      omega
    have hOffLe : tok.offReadyCount ≤ B.names m := by
      have hoffCap : tok.offReadyCount ≤ tok.intCap := hrep.2.2.2.2.2.2.2.2.2.1.1
      have hcapEq : tok.intCap = initTargetCap cfg G := hreach.2.2.2
      have hGm' : G.m = m := hGm
      unfold initTargetCap at hcapEq
      omega
    constructor
    · change 1 + m + ((algorithm2_detect cfg model).1.card + 1) * detectTreeRoundSpace F.limbs +
          tok.offReadyCount * (2 + 4 * F.limbs) ≤
        1 + m + (m + 1) * detectTreeRoundSpace (B.limbs m) + B.names m * (2 + 4 * B.limbs m)
      have hSpMono : detectTreeRoundSpace F.limbs ≤ detectTreeRoundSpace (B.limbs m) := by
        unfold detectTreeRoundSpace LinkCut.PathProg.treeLimbs; omega
      have h1 := Nat.mul_le_mul (Nat.add_le_add_right hCardLe 1) hSpMono
      have h2 := Nat.mul_le_mul hOffLe (by omega : 2 + 4 * F.limbs ≤ 2 + 4 * B.limbs m)
      omega
    · rw [hExtEq]
      exact detect_cost_of_step hFixed.2.2.2.2 _

/-- Six plain arithmetic inequalities on `B` and `sz` (with no reference to `Rrep`, `C.pre`,
`BatchAt`, `model`, or `tok`, and with no `136 * nfMax` table-growth term) that discharge
`OrdSolverContractEnvelopeFullCredit` together with the plain inequality `nfMax + 2 * I.m ≤ B.names I.m`. -/
structure DryEnvelopeIneqs (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes) : Prop where
  hIneqs : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
    fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let s := sz source J
      let findSp := 6 + s.selectSpace + s.evalSpace
      let findBud := s.selectBudget + s.evalBudget + 90
      let shiftSp := max s.termSpace s.deepSpace
      let shiftBud := max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220
      let B_iter := cycleLoopIterBudget F.limbs cfg.P.d findBud shiftBud
      let initBudFull :=
        (s.initFixed + initWiredExtraCost cfg G) +
        B_iter * ((cfg.P.d + 1) * ⌊(10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (cfg.P.d + 1)⌋₊) +
        s.toolMul * chainRebuildCap cfg (runtimeFactorNat cfg) (fun _ => 0) +
        s.treeMul * chainRebuildCap cfg (treeUpdateFactorNat cfg) (fun _ => 0)
      let nfMax := Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0
      let loopMax := (Chain.Ordered.loopDigitCap cfg + 1) ^ (cfg.P.d + 1)
      let creditPerEdge :=
        s.toolMul * (runtimeFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0 +
          (40 * Nat.clog 2 (3 * cfg.P.M₀ + 2) + 40)) +
        s.treeMul * (treeUpdateFactorNat cfg * capFwdWeight cfg (fwdGamma cfg) 0)
      F.limbs ≤ B.limbs I.m ∧
      G.n ≤ B.verts I.m ∧
      s.initSpace' + initWiredExtraSpace cfg G ≤ B.initSpace I.m ∧
      initBudFull ≤ B.initBudget I.m ∧
      Monotone s.coreSpace ∧
      updateSpaceBound F.limbs I.m cfg.P.d nfMax (2 * I.m) loopMax findSp shiftSp
        s.maxEdges s.maxPaths (cfg.P.d + (8 * (2 * I.m) + 1) + s.coreSpace (2 * I.m)) + 2 ≤
        B.updateSpace I.m ∧
      ∃ ρ₀ ρ₁ : ℕ,
        (∀ u ≤ 2 * I.m, s.coreFixed u ≤ ρ₀ + ρ₁ * u) ∧
        (600 + 20 * F.limbs +
            (ρ₀ + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 62 * (cfg.P.d + 1) + 240) +
            updateGoodBranchBudget F.limbs G.n s.maxEdges s.maxPaths
              (detectOffTreeDrainUnit F.limbs)) +
          (520 + 34 * F.limbs + ρ₁ + creditPerEdge) +
          B_iter + B_iter * fwdWeight cfg.P cfg.N₀ (alg2PsiGame cfg.Ψ cfg.P.M₀) (fwdGamma cfg) 0 ≤
          B.updateRate I.m

/-- **Dry-run reduction of `DrySCSolverHyps.hEnv` (`OrdSolverContractEnvelopeFullCredit`)**:
proves all four clauses (Init, Update, Query, Detect) from `DryEnvelopeIneqs B hB sz` plus the
plain arithmetic inequality `nfMax + 2 * I.m ≤ B.names I.m`. -/
theorem drySC_hEnv_of_ineqs (Psc : DrySparseCorePieces)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes)
    (hIneqs : DryEnvelopeIneqs B hB sz)
    (hNames : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun _source J _hw =>
        let I := solverConnectedAugmented J
        let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
        let G := namedInstance I
        Ordered.alg2NameBase cfg G + intRebuildThreshold cfg.P cfg.N₀ 0 + 2 * I.m ≤ B.names I.m) :
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffFull B hB) (dryAllocDeg B hB) source J hw
      let s := sz source J
      OrdSolverContractEnvelopeFullCredit F cfg (namedInstance I) I.m V ⌈cfg.Ψ⌉₊ k
        (k + Num.IPM.alphaExponent I.m V + 10)
        (s.initSpace' + initWiredExtraSpace cfg (namedInstance I))
        (s.initFixed + initWiredExtraCost cfg (namedInstance I))
        (6 + s.selectSpace + s.evalSpace) (s.selectBudget + s.evalBudget + 90)
        (max s.termSpace s.deepSpace) (max s.termFixed s.deepFixed + 28 * (cfg.P.d + 1) + 220)
        s.maxEdges s.maxPaths s.toolMul s.treeMul
        (fun uLen => cfg.P.d + (8 * uLen + 1) + s.coreSpace uLen)
        (fun uLen => s.coreFixed uLen + shiftQuotaWriterBudget cfg.P.d cfg.P.M₀ + 120 * uLen +
          62 * (cfg.P.d + 1) + 240)
        Rcore B.cycleRate (B.cycleAllocation I.n I.m) := by
  intro source J hJn hJm hCost hCap hw
  dsimp only
  obtain ⟨hLle, hVle, hInitSp, hInitBud, hCoreMono, hUpdSp, ρ₀, ρ₁, hCoreFix, hUpdRate⟩ :=
    hIneqs.hIneqs source J hJn hJm hCost hCap hw
  exact ordSolverContractEnvelopeFullCredit_of_ineqs
    (namedInstance_m (solverConnectedAugmented J)) (le_max_left _ _)
    hLle hVle hInitSp hInitBud hCoreMono hUpdSp hCoreFix hUpdRate
    (hNames source J hJn hJm hCost hCap hw)

end MinCostFlow.Final.DryRun

end
