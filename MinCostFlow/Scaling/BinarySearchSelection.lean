module

public import MinCostFlow.Scaling.BottleneckAcceptance

/-!
# Selection invariants of the counted binary search

The binary search in Lemma C.10 of Chen et al., arXiv:2203.00671v2,
Appendix C, retains the last negative unit optimum and rules out a suffix
of sorted capacity candidates. These elementary step lemmas refer to the
actual objective-sign test. Monotonicity is supplied by its proved
negative-walk characterization.
-/

@[expose] public section
namespace MinCostFlow.Scaling

private theorem getD_le_of_sorted (xs : List ℕ) (hs : xs.Pairwise (· ≤ ·))
    (i j : ℕ) (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    xs.getD i 0 ≤ xs.getD j 0 := by
  have hh := hs.rel_get_of_le (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  simpa only [List.getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some, List.get_eq_getElem] using hh

namespace BottleneckState
variable {I : Circulation}

/-- One step retains a genuine negative unit optimum at the predecessor of
its lower interval endpoint, or leaves the initial empty best value. -/
theorem step_best (solve : (J : Circulation) → Fin J.m → ℤ)
    (candidates : List ℕ) (s : BottleneckState I)
    (hbest : match s.best with
      | none => s.lower = 0
      | some (u, f) => 0 < s.lower ∧ u = candidates.getD (s.lower - 1) 0 ∧
          f = Circulation.solveWithZeroCapacities solve (I.bottleneckGraph u) ∧
          (I.bottleneckGraph u).integerObjective f < 0) :
    match (s.step solve candidates).value.best with
    | none => (s.step solve candidates).value.lower = 0
    | some (u, f) => 0 < (s.step solve candidates).value.lower ∧
        u = candidates.getD ((s.step solve candidates).value.lower - 1) 0 ∧
        f = Circulation.solveWithZeroCapacities solve (I.bottleneckGraph u) ∧
        (I.bottleneckGraph u).integerObjective f < 0 := by
  by_cases hi : s.lower < s.upper
  · simp only [step, hi, ↓reduceIte]
    by_cases hn : (I.bottleneckGraph (candidates.getD ((s.lower + s.upper) / 2) 0)).integerObjective
        (Circulation.solveWithZeroCapacities solve
          (I.bottleneckGraph (candidates.getD ((s.lower + s.upper) / 2) 0))) < 0
    · simp only [hn, ↓reduceIte]
      exact ⟨Nat.zero_lt_succ _, by simp, True.intro, True.intro⟩
    · simp only [hn, ↓reduceIte]
      exact hbest
  · simpa only [step, hi, ↓reduceIte] using hbest

/-- Rejecting a midpoint rejects the entire new suffix by sortedness and
monotonicity of the actual test. An accepted midpoint leaves the suffix intact. -/
theorem step_rejected_suffix (solve : (J : Circulation) → Fin J.m → ℤ)
    (candidates : List ℕ) (hsorted : candidates.Pairwise (· ≤ ·))
    (hmono : ∀ u v, u ≤ v → I.bottleneckAccepts solve v → I.bottleneckAccepts solve u)
    (s : BottleneckState I) (hs : s.lower ≤ s.upper ∧ s.upper ≤ candidates.length)
    (hreject : ∀ i, s.upper ≤ i → i < candidates.length →
      ¬ I.bottleneckAccepts solve (candidates.getD i 0)) :
    ∀ i, (s.step solve candidates).value.upper ≤ i → i < candidates.length →
      ¬ I.bottleneckAccepts solve (candidates.getD i 0) := by
  unfold step
  split
  · rename_i hinterval
    dsimp only
    split
    · exact hreject
    · rename_i hno
      intro i hi hilen hyes
      by_cases hold : s.upper ≤ i
      · exact hreject i hold hilen hyes
      · have hmidlen : (s.lower + s.upper) / 2 < candidates.length := by omega
        have hle := getD_le_of_sorted candidates hsorted _ i hmidlen hilen hi
        exact hno (hmono _ _ hle hyes)
  · exact hreject

end BottleneckState
end MinCostFlow.Scaling
