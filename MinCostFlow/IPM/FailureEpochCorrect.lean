module

public import MinCostFlow.IPM.FailureEpoch

/-!
# Upper-target epochs cannot fail

For every target at least the optimum, the adapted Lemmas 9.1--9.4
prove hidden stability of the full causal epoch. The failure clause
of the restated Definition 4.5 therefore forbids failure at each
Update. The existing numeric and Query-budget guards also pass.
Consequently the new first-failure scan preserves every upper-target
run of Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69).
-/

public section
namespace MinCostFlow.IPM

/-- Every upper-target epoch completes without explicit failure or a
failed local guard. This is proved from its hidden prefixes, not assumed
as a stronger data structure guarantee. -/
theorem epochFirstFailureWithAnswer_upper (I : Instance) (U F κ : ℝ)
    (A : MinRatioDataStructureWithFailure) (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hstart : (1/4 : ℝ) < residual I F base)
    (hpot : potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U))
    (hA : MinRatioSpecWithFailure A κ (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ)) :
    epochFirstFailureWithAnswer I U κ (residual I F base) A base I.m = none := by
  let B := A.eraseFailure
  let r := residual I F base
  have hguards := epochFirstFailure_upper I U F κ B base fstar hI hm hU hsize hnums
    hk hk' hs hF hbase hroute hstart hpot hA.1
  have hep := epoch_correct I U F κ B base fstar hI hm hU hsize hnums hk hk' hs hF
    hbase hroute hstart hpot hA.1
  dsimp only at hep
  obtain ⟨_, _, _, _, hhidden, _⟩ := hep
  have hinv := epoch_invariants I U F κ B base fstar hI hm hU hsize hnums hk hk' hs hF
    hbase hroute hstart hpot hA.1
  dsimp only at hinv
  have hvalid := epoch_history_valid_prefix I U κ r B base (2*I.m) hI
    (by intro j hj; exact (hinv j (by omega)).2.2.2.1)
  apply (epochFirstFailureWithAnswer_none_iff I U κ r A base I.m).mpr
  intro t ht
  refine ⟨?_, (epochFirstFailure_none_iff I U κ r B base I.m).mp hguards (t+1) (by omega)⟩
  rw [epochUpdateWithFailure_direction]
  have hprefix : (epochInstance I U κ r B base).HiddenStable (2*t+1)
      (normalizedIpmAlpha I) (ipmPsi I U) := by
    obtain ⟨c, w, hcw⟩ := hhidden
    exact ⟨c, w, fun j hj => hcw j (by omega)⟩
  have hop : epochIsUpdate (2*t+1) = true := by
    unfold epochIsUpdate
    apply decide_eq_true
    omega
  exact hA.2 _ (epochEta I U κ) epochIsUpdate (2*I.m) hvalid (2*t) (by omega) hop hprefix

/-- The failure-aware scanner agrees with the existing guarded scanner
when an implementation always reports success. -/
theorem epochFirstFailureWithAnswer_withFailureAnswer (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructure) (base : Fin I.m → ℝ) (n : ℕ) :
    epochFirstFailureWithAnswer I U κ r A.withFailureAnswer base n =
      epochFirstFailure I U κ r A base n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [epochFirstFailureWithAnswer, ih]
    have hs : (epochUpdateWithFailure I U κ r A.withFailureAnswer
        (epochState I U κ r A.withFailureAnswer.eraseFailure base n)).2.isSome = true := by
      rfl
    simp only [hs, ↓reduceIte, epochFirstFailure]
    cases A
    rfl

end MinCostFlow.IPM
