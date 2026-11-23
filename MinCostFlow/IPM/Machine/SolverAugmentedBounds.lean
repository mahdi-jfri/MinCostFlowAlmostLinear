module

public import MinCostFlow.IPM.Machine.SolverInitialBounds
public import MinCostFlow.IPM.GuessInitial
import MinCostFlow.IPM.InitialConstruction
import MinCostFlow.IPM.InitialDomain
import Mathlib.Tactic

/-!
# Numeric and encoding bounds for the solver's augmented graph

The penalty in Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31)
bounds costs and upper capacities. This gives one-word encodings of
the graph records and provides the strict penalty inequality needed
when deleting the auxiliary edges.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- The common numeric bound is the machine's exact penalty word. -/
theorem solverAugmented_numbers (J : Circulation) (hm : 0 < J.m)
    (hc : J.CostsBounded (J.m^10)) (hu : ∀ e, J.capacity e ≤ J.m^40) :
    let U := solverCapacityBound J.m
    let V := solverPenalty J.m
    NumbersBounded J.toInstance (U:ℝ) ∧ NumbersBounded (solverAugmented J) (V:ℝ) ∧
      2*J.toInstance.m*(U:ℝ) < (V:ℝ) := by
  dsimp only
  let U := solverCapacityBound J.m
  let V := solverPenalty J.m
  have hU : 2 ≤ U := le_max_left _ _
  have hUreal : (2:ℝ) ≤ U := by exact_mod_cast hU
  have hEq : (V:ℝ) = 4*J.toInstance.m*(U:ℝ)^2 := by
    simp [U,V,solverPenalty,Circulation.toInstance_m]
  obtain ⟨hCap,hCost⟩ := solverCapacityBound_input J hm hc hu
  have hNums := circulation_numbersBounded J U hCap hCost
  have hVn : (0:ℝ) ≤ V := Nat.cast_nonneg _
  have hPen : |((V:ℤ):ℝ)| ≤ 4*J.toInstance.m*(U:ℝ)^2 := by
    rw [Int.cast_natCast,abs_of_nonneg hVn,hEq]
  have hM : 0 < J.toInstance.m := by simpa only [Circulation.toInstance_m] using hm
  have hMreal : 0 < (J.toInstance.m:ℝ) := Nat.cast_pos.mpr hM
  refine ⟨hNums,hEq.symm ▸ augmented_numbersBounded J.toInstance (U:ℝ) (V:ℤ) hM
    (by linarith only [hUreal]) hNums hPen,?_⟩
  rw [hEq]
  have hStrict : 2*(U:ℝ) < 4*(U:ℝ)^2 := by nlinarith only [hUreal]
  nlinarith only [mul_lt_mul_of_pos_left hStrict hMreal]

/-- A valid row graph with bounded numbers fits its five-word record
layout as soon as its dimensions and numerical bound fit. -/
theorem zeroLowerWords_fit (I : Instance) (hI : I.IsValid) (V w : ℕ)
    (hNums : NumbersBounded I (V:ℝ)) (hn : I.n<2^w) (hm : I.m<2^w)
    (hV : V<2^w) (hOne : 1<2^w) :
    ∀ x∈zeroLowerWords I,x<2^w := by
  rw [←zeroLowerCirculation_words I hI]
  intro x hx
  simp only [Circulation.solverWords,List.mem_cons,List.mem_flatMap] at hx
  rcases hx with rfl | rfl | ⟨e,_,he⟩
  · exact hn
  · exact hm
  simp only [Circulation.solverEdgeWords,zeroLowerCirculation,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact (hI.1 _ (List.getElem_mem e.isLt)).1.trans hn
  · exact (hI.1 _ (List.getElem_mem e.isLt)).2.trans hn
  · refine (show (I.edge e).upper.toNat ≤ V from ?_).trans_lt hV
    have hl := (le_abs_self ((I.edge e).upper:ℝ)).trans (hNums.2 e).2.1
    have hInt : (I.edge e).upper ≤ (V:ℤ) := by exact_mod_cast hl
    simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hInt
  · change (if (I.edge e).cost < 0 then (1:ℕ) else 0)<2^w
    by_cases he : (I.edge e).cost < 0
    · rw [ite_eq_left he]; exact hOne
    · rw [ite_eq_right he]; omega
  · refine (show (I.edge e).cost.natAbs ≤ V from ?_).trans_lt hV
    have hInt : |(I.edge e).cost| ≤ (V:ℤ) := by exact_mod_cast (hNums.2 e).2.2
    rw [← Int.natCast_natAbs] at hInt
    exact_mod_cast hInt

end MinCostFlow.IPM.Machine
