module

public import MinCostFlow.IPM.TargetInstances
public import MinCostFlow.IPM.DataStructureSearch

/-!
# Dynamic instances evaluated by the full target search

The search proposed in Section 4 of Chen et al., arXiv:2203.00671v2
(page 24), invokes bounded target tests at the guesses recorded by
bisection and once more at its returned target. This file records every
evaluated dynamic-instance prefix, including prefixes of failed tests.
It is the input counterpart of the operation transcript in `SearchCounts`.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- All instance prefixes evaluated by the unknown-target search, in
call order. Failed target tests contribute their evaluated prefixes. -/
def dataStructureSearchInstances (I : Instance) (U κ : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (B : ℕ) : List (DynamicInstance × ℕ) :=
  let result := bisectCost (fun F => (dataStructureGuessTest I U F κ A base).isSome)
    (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))
  result.2.flatMap (fun (F : ℤ) => boundedTargetInstances I U F κ A (ipmEpochLimit I U κ) base) ++
    boundedTargetInstances I U result.1 κ A (ipmEpochLimit I U κ) base

/-- Every evaluated prefix of a tested target occurs in the full input
transcript, whether that target test accepts or rejects. -/
theorem mem_dataStructureSearchInstances_of_tested (I : Instance) (U κ : ℝ)
    (A : MinRatioDataStructure) (base : Fin I.m → ℝ) (B : ℕ) (F : ℤ)
    (p : DynamicInstance × ℕ)
    (hF : F ∈ (bisectCost (fun F => (dataStructureGuessTest I U F κ A base).isSome)
      (-(B : ℤ)) (2*B) (Nat.clog 2 (2*B+1))).2)
    (hp : p ∈ boundedTargetInstances I U F κ A (ipmEpochLimit I U κ) base) :
    p ∈ dataStructureSearchInstances I U κ A base B := by
  apply List.mem_append.mpr
  exact Or.inl (List.mem_flatMap.mpr ⟨F, hF, hp⟩)

end MinCostFlow.IPM
