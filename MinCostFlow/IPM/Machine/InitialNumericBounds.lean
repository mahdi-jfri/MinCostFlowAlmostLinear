module

public import MinCostFlow.IPM.Machine.InitialEncodedInstance
public import MinCostFlow.IPM.Initialization
public import MinCostFlow.Num.Encoding
import MinCostFlow.IPM.InitialNumbers
import MinCostFlow.IPM.GuessInitial
import Mathlib.Tactic.NormNum

/-!
# Numeric fit bounds for Lemma 4.12 initialization

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31,
Appendix B.1 page 92) uses penalty `4mU²` and bounds every augmented
capacity by the same number. These lemmas derive that bound on the
actual circulation input and transport signed fits from the bound to
every capacity and its fixed-point midpoint numerator. They do not
choose the precision or assume a correctly initialized flow.
-/

public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- The prescribed penalty as a nonnegative machine-word value. -/
@[expose] def initialPenaltyWord (J : Circulation) (U : ℕ) : ℕ := 4*J.m*U^2

/-- The machine word represents exactly the prescribed source penalty. -/
theorem initialPenaltyWord_cast (J : Circulation) (U : ℕ) :
    (initialPenaltyWord J U : ℤ) = initialPenalty J.toInstance U := by
  simp [initialPenaltyWord,initialPenalty,Circulation.toInstance_m]

/-- Every intermediate product of the penalty computation, and the total
capacity bound used by the endpoint scans, lie below that penalty. -/
theorem initialPenaltyWord_intermediates (J : Circulation) (U : ℕ)
    (hm : 0 < J.m) (hU : 2 ≤ U) :
    U^2 ≤ initialPenaltyWord J U ∧ 4*J.m ≤ initialPenaltyWord J U ∧
      J.m*U ≤ initialPenaltyWord J U := by
  have hU1 : 1 ≤ U := by omega
  have hpow1 : 1 ≤ U^2 := Nat.one_le_pow _ _ hU1
  have hpow : U ≤ U^2 := by
    simpa only [Nat.mul_one,pow_two] using Nat.mul_le_mul_left U hU1
  have h4m : 1 ≤ 4*J.m := by omega
  refine ⟨?_,?_,?_⟩
  · simpa only [initialPenaltyWord,Nat.one_mul] using Nat.mul_le_mul_right (U^2) h4m
  · simpa only [initialPenaltyWord,Nat.mul_one] using Nat.mul_le_mul_left (4*J.m) hpow1
  · exact (Nat.mul_le_mul_left J.m hpow).trans
      (Nat.mul_le_mul_right (U^2) (show J.m ≤ 4*J.m by omega))

/-- The unsigned endpoint accumulator's total-capacity fit follows from
the input capacity bound and the prescribed penalty's fit. -/
theorem total_capacity_le_penalty (J : Circulation) (U : ℕ) (hm : 0 < J.m) (hU : 2 ≤ U)
    (hcap : ∀ e, J.capacity e ≤ U) :
    (∑ e : Fin J.m, J.capacity e) ≤ initialPenaltyWord J U := by
  calc
    _ ≤ ∑ _ : Fin J.m, U := Finset.sum_le_sum (fun e _ => hcap e)
    _ = J.m*U := by simp
    _ ≤ _ := (initialPenaltyWord_intermediates J U hm hU).2.2

/-- Circulation data bounded by `U` satisfy the existing numerical input
predicate, with their zero demands and zero lower capacities. -/
theorem circulation_numbersBounded (J : Circulation) (U : ℕ)
    (hcap : ∀ e, J.capacity e ≤ U) (hcost : J.CostsBounded U) :
    NumbersBounded J.toInstance (U : ℝ) := by
  constructor
  · intro v
    simp [Instance.d]
  · intro e
    rw [Circulation.toInstance_edge]
    simp only [Circulation.inputEdge]
    refine ⟨?_,?_,?_⟩
    · simpa only [Int.cast_zero,abs_zero] using (Nat.cast_nonneg U : (0 : ℝ) ≤ U)
    · have hh : (J.capacity (J.inputIndex e) : ℝ) ≤ U := by
        exact_mod_cast hcap (J.inputIndex e)
      simpa only [Int.cast_natCast,abs_of_nonneg (show (0 : ℝ) ≤ J.capacity (J.inputIndex e) from Nat.cast_nonneg _)] using hh
    · have hh : ((J.cost (J.inputIndex e)).natAbs : ℤ) ≤ (U : ℤ) := by
        exact_mod_cast hcost (J.inputIndex e)
      rw [Int.natCast_natAbs] at hh
      exact_mod_cast hh

/-- The actual augmented unsigned capacities obey the source's penalty
bound. The proof applies the already proved Lemma 4.12 numeric estimate. -/
theorem initial_capacity_le_penalty (J : Circulation) (U : ℕ)
    (hm : 0 < J.m) (hU : 2 ≤ U) (hcap : ∀ e, J.capacity e ≤ U) (hcost : J.CostsBounded U)
    (e : Fin (initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).m) :
    ((initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper.toNat ≤ initialPenaltyWord J U := by
  have hnums := circulation_numbersBounded J U hcap hcost
  have heq : ((initialPenaltyWord J U : ℤ) : ℝ) = 4*J.toInstance.m*(U : ℝ)^2 := by
    simp [initialPenaltyWord,Circulation.toInstance_m]
  have hK : |((initialPenaltyWord J U : ℤ) : ℝ)| ≤ 4*J.toInstance.m*(U : ℝ)^2 := by
    rw [abs_of_nonneg (by exact_mod_cast (Nat.zero_le (initialPenaltyWord J U))),heq]
  have hn := augmented_numbersBounded J.toInstance (U : ℝ) (initialPenaltyWord J U : ℤ)
    (by simpa only [Circulation.toInstance_m] using hm)
    (by exact_mod_cast (show 1 ≤ U by omega)) hnums hK
  have hb : (((initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper : ℝ) ≤
      ((initialPenaltyWord J U : ℤ) : ℝ) := by
    rw [heq]
    exact (le_abs_self _).trans (hn.2 e).2.1
  have hbi : ((initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper ≤
      (initialPenaltyWord J U : ℤ) := by exact_mod_cast hb
  simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hbi

/-- A nonnegative integer below a fitting bound also fits. -/
theorem fits_of_nonneg_le (h L : ℕ) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : Num.Fits h L b) : Num.Fits h L a := by
  constructor
  · exact (neg_nonpos.mpr (Int.natCast_nonneg (Num.capacity h L))).trans (mul_nonneg (by decide) ha)
  · exact (mul_le_mul_of_nonneg_left hab (by decide : (0 : ℤ) ≤ 2)).trans_lt hb.2

/-- Fitting the source penalty and its scaled value suffices for every
capacity block needed by the initialized flow loader. -/
theorem initial_capacity_fits (J : Circulation) (U h L P : ℕ)
    (hm : 0 < J.m) (hU : 2 ≤ U) (hcap : ∀ e, J.capacity e ≤ U) (hcost : J.CostsBounded U)
    (hK : Num.Fits h L (initialPenaltyWord J U : ℤ))
    (hscaled : Num.Fits h L ((initialPenaltyWord J U : ℤ)*(2 : ℤ)^(P-1)))
    (e : Fin (initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).m) :
    let cap := ((initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper.toNat
    Num.Fits h L (cap : ℤ) ∧ Num.Fits h L ((cap : ℤ)*(2 : ℤ)^(P-1)) := by
  dsimp only
  have hle := initial_capacity_le_penalty J U hm hU hcap hcost e
  have hleZ : (((initialInstance J.toInstance (initialPenaltyWord J U : ℤ)).edge e).upper.toNat : ℤ) ≤
      (initialPenaltyWord J U : ℤ) := by exact_mod_cast hle
  constructor
  · exact fits_of_nonneg_le h L _ _ (Int.natCast_nonneg _) hleZ hK
  · exact fits_of_nonneg_le h L _ _
      (mul_nonneg (Int.natCast_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_right hleZ (by positivity)) hscaled

end MinCostFlow.IPM.Machine
