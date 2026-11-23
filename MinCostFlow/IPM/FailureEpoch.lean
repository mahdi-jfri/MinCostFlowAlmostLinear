module

public import MinCostFlow.IPM.GuardedEpochCounts
import Lean.Elab.Tactic.Omega

/-!
# Stopping an epoch at an explicit Update failure

The restated Definition 4.5 allows Update to fail on a non-hidden prefix.
This scanner inspects that answer before evaluating the next Detect or
Query. Successful iterations are the existing causal Update--Detect
pairs, and their capacity and Query-budget guards are unchanged.
The zero-increment projection is used only to describe those states and
to reuse the proved guarded-prefix bounds.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- The actual Update call with its success-or-failure answer. -/
def epochUpdateWithFailure (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (s : IpmEpochState I A.eraseFailure) : A.State × Option (ℕ → ℝ) :=
  A.update s.ds (refreshEdges (namedInstance I) s.pending.toList)
    (namedVector (epochGradient I U r s.stored))
    (namedVector (lengths I (alpha I U) s.stored))
    (ipmGradientScale I U*ipmStepEta I U κ)

/-- The optional answer agrees with the causal history of Definition 4.5. -/
theorem epochUpdateWithFailure_direction (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (t : ℕ) :
    (epochUpdateWithFailure I U κ r A (epochState I U κ r A.eraseFailure base t)).2 =
      minRatioFailureDirection A (epochInstance I U κ r A.eraseFailure base)
        (epochEta I U κ) epochIsUpdate (2*t) := by
  unfold minRatioFailureDirection
  change _ = (A.update (epochTrace I U κ r A.eraseFailure base (2*t)) _ _ _ _).2
  rw [(epochTrace_pair I U κ r A.eraseFailure base t).1]
  have hmod : (2*t+1)%2 = 1 := by omega
  have hidx : (2*t+1-1)/2 = t := by omega
  simp only [epochInstance, epochEta, hmod, hidx, ↓reduceIte, epochUpdateWithFailure]

/-- One iteration passes when Update succeeds and the original numeric
and Query-budget guards pass after its Detect and coordinate refreshes. -/
def failureEpochPasses (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) (t : ℕ) : Prop :=
  (epochUpdateWithFailure I U κ r A (epochState I U κ r A.eraseFailure base t)).2.isSome = true ∧
    epochPasses I (epochState I U κ r A.eraseFailure base (t+1))

/-- Scan until the first failed Update or local guard. The Update answer
is tested first. In the failure branch the expression for the next
Update--Detect state is not evaluated, so that test makes no further
Detect or Query call. A failure index counts the attempted Update. -/
def epochFirstFailureWithAnswer (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) : ℕ → Option ℕ
  | 0 => none
  | t+1 => by
    classical
    exact match epochFirstFailureWithAnswer I U κ r A base t with
    | some k => some k
    | none =>
      if (epochUpdateWithFailure I U κ r A (epochState I U κ r A.eraseFailure base t)).2.isSome = true then
        if epochPasses I (epochState I U κ r A.eraseFailure base (t+1)) then none else some (t+1)
      else some (t+1)

/-- A successful scan means each attempted Update succeeded and each
completed pair passed its local guards. -/
theorem epochFirstFailureWithAnswer_none_iff (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (n : ℕ) :
    epochFirstFailureWithAnswer I U κ r A base n = none ↔
      ∀ t < n, failureEpochPasses I U κ r A base t := by
  classical
  induction n with
  | zero => simp only [epochFirstFailureWithAnswer, Nat.not_lt_zero, false_implies, implies_true]
  | succ n ih =>
    simp only [epochFirstFailureWithAnswer]
    cases hp : epochFirstFailureWithAnswer I U κ r A base n with
    | some k =>
      simp only [Option.some_ne_none, false_iff]
      intro hall
      have hh := ih.mpr (fun t ht => hall t (Nat.lt_succ_of_lt ht))
      rw [hp] at hh
      contradiction
    | none =>
      have hprev := ih.mp hp
      by_cases hs : (epochUpdateWithFailure I U κ r A (epochState I U κ r A.eraseFailure base n)).2.isSome = true
      · by_cases hg : epochPasses I (epochState I U κ r A.eraseFailure base (n+1))
        · simp only [hs, hg, ↓reduceIte, true_iff]
          intro t ht
          by_cases he : t = n
          · subst t; exact ⟨hs, hg⟩
          · exact hprev t (by omega)
        · simp only [hs, hg, ↓reduceIte, Option.some_ne_none, false_iff]
          intro hall
          exact hg (hall n (Nat.lt_succ_self n)).2
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, Option.some_ne_none, false_iff]
        intro hall
        exact hs (hall n (Nat.lt_succ_self n)).1

/-- The initial numeric guard passes before any operation. -/
private theorem initial_epoch_passes (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : epochPasses I (epochState I U κ r A base 0) := by
  refine ⟨?_, Nat.zero_le _⟩
  intro e he
  exact False.elim (Finset.notMem_empty e he)

/-- Passing the failure-aware scan also passes the original guards. -/
theorem epochFirstFailureWithAnswer_none_old (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (n : ℕ)
    (h : epochFirstFailureWithAnswer I U κ r A base n = none) :
    epochFirstFailure I U κ r A.eraseFailure base n = none := by
  have hall := (epochFirstFailureWithAnswer_none_iff I U κ r A base n).mp h
  apply (epochFirstFailure_none_iff I U κ r A.eraseFailure base n).mpr
  intro j hj
  cases j with
  | zero => exact initial_epoch_passes I U κ r A.eraseFailure base
  | succ j => exact (hall j (by omega)).2

/-- A failed scan stops at a positive index within its requested length,
and every earlier iteration completed without failure. -/
theorem epochFirstFailureWithAnswer_some_spec (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (n k : ℕ)
    (h : epochFirstFailureWithAnswer I U κ r A base n = some k) :
    1 ≤ k ∧ k ≤ n ∧ ¬ failureEpochPasses I U κ r A base (k-1) ∧
      ∀ t < k-1, failureEpochPasses I U κ r A base t := by
  classical
  induction n with
  | zero => cases h
  | succ n ih =>
    simp only [epochFirstFailureWithAnswer] at h
    cases hp : epochFirstFailureWithAnswer I U κ r A base n with
    | some j =>
      rw [hp] at h
      have heq := Option.some.inj h
      subst j
      have hh := ih hp
      exact ⟨hh.1, Nat.le_succ_of_le hh.2.1, hh.2.2⟩
    | none =>
      rw [hp] at h
      have hprev := (epochFirstFailureWithAnswer_none_iff I U κ r A base n).mp hp
      by_cases hs : (epochUpdateWithFailure I U κ r A (epochState I U κ r A.eraseFailure base n)).2.isSome = true
      · by_cases hg : epochPasses I (epochState I U κ r A.eraseFailure base (n+1))
        · simp only [hs, hg, ↓reduceIte] at h
          cases h
        · simp only [hs, hg, ↓reduceIte] at h
          have heq := Option.some.inj h
          subst k
          simpa only [Nat.add_sub_cancel] using
            And.intro (show 1 ≤ n+1 by omega)
              (And.intro (le_refl (n+1)) (And.intro (fun hh => hg hh.2) hprev))
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
        have heq := Option.some.inj h
        subst k
        simpa only [Nat.add_sub_cancel] using
          And.intro (show 1 ≤ n+1 by omega)
            (And.intro (le_refl (n+1)) (And.intro (fun hh => hs hh.1) hprev))

/-- Number of attempted Updates in the failure-aware epoch. A failed
Update is included, although it is not followed by Detect or Query. -/
def epochProcessedWithAnswer (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructureWithFailure)
    (base : Fin I.m → ℝ) (n : ℕ) : ℕ :=
  (epochFirstFailureWithAnswer I U κ r A base n).getD n

/-- Explicit failure can only shorten the original guarded attempt.
Its original counters therefore give conservative bounds for this scan. -/
theorem epochProcessedWithAnswer_le (I : Instance) (U κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (n : ℕ) :
    epochProcessedWithAnswer I U κ r A base n ≤ epochProcessed I U κ r A.eraseFailure base n := by
  cases hn : epochFirstFailureWithAnswer I U κ r A base n with
  | none =>
    have ho := epochFirstFailureWithAnswer_none_old I U κ r A base n hn
    simp only [epochProcessedWithAnswer, epochProcessed, hn, ho, Option.getD_none, le_refl]
  | some k =>
    have hk := epochFirstFailureWithAnswer_some_spec I U κ r A base n k hn
    cases ho : epochFirstFailure I U κ r A.eraseFailure base n with
    | none => simpa only [epochProcessedWithAnswer, epochProcessed, hn, ho,
        Option.getD_some, Option.getD_none] using hk.2.1
    | some j =>
      have hj := epochFirstFailure_some_spec I U κ r A.eraseFailure base n j ho
      have hkj : k ≤ j := by
        by_contra hh
        have hpass := (hk.2.2.2 (j-1) (by omega)).2
        have heq : j-1+1 = j := Nat.sub_add_cancel hj.1
        rw [heq] at hpass
        exact hj.2.2.1 hpass
      simpa only [epochProcessedWithAnswer, epochProcessed, hn, ho, Option.getD_some] using hkj

end MinCostFlow.IPM
