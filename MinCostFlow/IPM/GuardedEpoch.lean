module

public import MinCostFlow.IPM.EpochSafety
public import MinCostFlow.IPM.EpochCorrect
import Lean.Elab.Tactic.Omega

/-!
# Guarded epochs for arbitrary target guesses

The cost search of Section 4 of Chen et al., arXiv:2203.00671v2
(page 24), tests guesses that may lie below the optimum. Guard each
reported-coordinate refresh by a capacity check and cap the cumulative
coordinate Query count at `5m`. Stop immediately at the first failed
check. These checks inspect only the reported entries and the counter.
Every upper guess passes them by the epoch invariant and charging bound.
The feasibility theorem for a passed epoch requires no hidden witness.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- The two local checks after an Update--Detect pair: newly stored
coordinates are interior, and no more than `5m` Queries have been used. -/
def epochPasses (I : Instance) {A : MinRatioDataStructure} (s : IpmEpochState I A) : Prop :=
  epochStoredGuard I s ∧ s.queries ≤ 5*I.m

/-- Scan a causal epoch until its first failed check. A failed prefix
prevents evaluating any later iteration. `none` means every check passed. -/
def epochFirstFailure (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : ℕ → Option ℕ
  | 0 => none
  | n+1 => by
    classical
    exact match epochFirstFailure I U κ r A base n with
    | some k => some k
    | none => if epochPasses I (epochState I U κ r A base (n+1)) then none else some (n+1)

private theorem epoch_passes_zero (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : epochPasses I (epochState I U κ r A base 0) := by
  refine ⟨?_, Nat.zero_le _⟩
  intro e he
  exact False.elim (Finset.notMem_empty e he)

/-- A passed scan is exactly a prefix whose local checks all pass. -/
theorem epochFirstFailure_none_iff (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) :
    epochFirstFailure I U κ r A base n = none ↔
      ∀ j ≤ n, epochPasses I (epochState I U κ r A base j) := by
  classical
  induction n with
  | zero =>
    constructor
    · intro _ j hj
      have hj0 : j = 0 := by omega
      subst j
      exact epoch_passes_zero I U κ r A base
    · intro _; rfl
  | succ n ih =>
    simp only [epochFirstFailure]
    cases hp : epochFirstFailure I U κ r A base n with
    | some k =>
      simp only [Option.some_ne_none, false_iff]
      intro hall
      have hh := ih.mpr (fun j hj => hall j (Nat.le_succ_of_le hj))
      rw [hp] at hh
      contradiction
    | none =>
      have hprev := ih.mp hp
      split_ifs with hpass
      · simp only [true_iff]
        intro j hj
        by_cases he : j = n+1
        · subst j; exact hpass
        · exact hprev j (by omega)
      · simp only [false_iff]
        intro hall
        exact hpass (hall (n+1) le_rfl)

/-- A failure is at a positive stage within the scanned prefix, and every
preceding check passed. This makes the last failed iteration the only
possible overrun of the Query cap. -/
theorem epochFirstFailure_some_spec (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n k : ℕ)
    (hfail : epochFirstFailure I U κ r A base n = some k) :
    1 ≤ k ∧ k ≤ n ∧ ¬ epochPasses I (epochState I U κ r A base k) ∧
      ∀ j < k, epochPasses I (epochState I U κ r A base j) := by
  classical
  induction n with
  | zero => contradiction
  | succ n ih =>
    have hrec : epochFirstFailure I U κ r A base (n+1) =
        match epochFirstFailure I U κ r A base n with
        | some k => some k
        | none => if epochPasses I (epochState I U κ r A base (n+1)) then none else some (n+1) := by rfl
    rw [hrec] at hfail
    cases hp : epochFirstFailure I U κ r A base n with
    | some k' =>
      rw [hp] at hfail
      have heq := Option.some.inj hfail
      subst k'
      have hh := ih hp
      exact ⟨hh.1, Nat.le_succ_of_le hh.2.1, hh.2.2⟩
    | none =>
      rw [hp] at hfail
      dsimp only at hfail
      by_cases hpass : epochPasses I (epochState I U κ r A base (n+1))
      · rw [ite_eq_left hpass] at hfail
        cases hfail
      · rw [ite_eq_right hpass] at hfail
        have heq := Option.some.inj hfail
        subst k
        exact ⟨by omega, le_rfl, hpass,
          fun j hj => (epochFirstFailure_none_iff I U κ r A base n).mp hp j (by omega)⟩

/-- A successful guarded epoch returns a feasible flow on an arbitrary
target guess. It is safe to accept that flow if its cost meets the guess. -/
theorem guardedEpoch_feasible (I : Instance) (U κ r α Ψ ε : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (n : ℕ) (hI : I.IsValid) (hm : 0 < I.m)
    (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (he : 0 ≤ ε) (he' : ε ≤ 1/100) (hbase : StrictlyInside I base) (hroute : I.Routes base)
    (hA : MinRatioSpec A κ α Ψ ε)
    (hpass : epochFirstFailure I U κ r A base n = none) :
    I.IsFeasible (epochFlow I U κ r A base n) :=
  epoch_guards_feasible I U κ r α Ψ ε A base n hI hm hU hsize hnums he he' hbase hroute hA
    (fun j hj => ((epochFirstFailure_none_iff I U κ r A base n).mp hpass j hj).1)

/-- The full epoch of every upper target guess passes all local checks.
Thus guarding does not change the successful IPM run. -/
theorem epochFirstFailure_upper (I : Instance) (U F κ : ℝ) (A : MinRatioDataStructure)
    (base fstar : Fin I.m → ℝ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hbase : StrictlyInside I base) (hroute : I.Routes base) (hstart : (1/4 : ℝ) < residual I F base)
    (hpot : potential I (alpha I U) F base ≤ 200*I.m*Real.log (I.m*U))
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)) :
    epochFirstFailure I U κ (residual I F base) A base I.m = none := by
  let r := residual I F base
  have hinv := epoch_invariants I U F κ A base fstar hI hm hU hsize hnums hk hk' hs hF
    hbase hroute hstart hpot hA
  dsimp only at hinv
  have hv := epoch_history_valid_prefix I U κ r A base (2*I.m) hI
    (by intro j hj; exact (hinv j (by omega)).2.2.2.1)
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  apply (epochFirstFailure_none_iff I U κ r A base I.m).mpr
  intro j hj
  have hcounts := epoch_refresh_counts I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
    (ipmDetectThreshold I U κ) A base (2*I.m) j hA hv (by omega) he.1 (by
      intro t ht
      have hh := ((hinv j hj).2.2.2.2.2.2.2 t ht).1
      exact hh.trans (by linarith only [he.1]))
  refine ⟨?_, hcounts.1.trans (Nat.mul_le_mul_left _ hj)⟩
  intro e hem
  have heI := epoch_pending_mem I U κ r A base j e hem
  exact ⟨heI, (hinv j hj).2.2.2.1 ⟨e, heI⟩⟩

end MinCostFlow.IPM
