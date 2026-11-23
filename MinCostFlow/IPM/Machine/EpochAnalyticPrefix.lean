module

public import MinCostFlow.IPM.Machine.EpochCertifiedDirection
public import MinCostFlow.IPM.Machine.EpochReportBalance
public import MinCostFlow.IPM.Machine.EpochInputFromCache
import Mathlib.Tactic.NormNum

/-!
# Analytic invariants of a certified epoch prefix

The prefix keeps the admissible steps, numerical accuracy of each
presented input, and two forms of movement accounting. The per-edge
bound guarantees accuracy at the next Detect. The total balance
guarantees that its report fits in the machine's remaining budget.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The analytic facts maintained at the current accepted point. -/
def EpochAnalyticPrefixAt {τ : Type} (I : Instance) (U R : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (i : ℕ) (P : EpochPoint τ) : Prop :=
  let a := Num.IPM.alphaPrime I.m U
  let q := κ*a/32
  let eps := κ*a/1024
  EpochDyadicPrefix I U target q A P.history P.eta P.op base i ∧ EpochDetectSchedule P.op i ∧
  EpochHistoryCacheStable I A P.history P.eta P.op (2*i) base ∧
  (∀ t≤2*i,EpochInputAccuracyAt I R target a r q A P.history P.eta P.op base t) ∧
  (∀ e<I.m,epochPendingMovement A.eraseFailure P.history P.eta P.op (2*i) e≤eps+eps/4) ∧
  EpochReportBalance A.eraseFailure I.m eps i P

/-- The analytic invariant at the original binary range. -/
def EpochAnalyticPrefix {τ : Type} (I : Instance) (U : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (i : ℕ) (P : EpochPoint τ) : Prop :=
  EpochAnalyticPrefixAt I U (ipmRangeExponent I.m U) target κ r A base i P

/-- The analytic invariants start with the initial input's numerical
accuracy, zero movement, and the actual five-reports-per-edge record. -/
theorem epochAnalyticPrefixAt_zero {τ : Type} (I : Instance) (U R : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (P : EpochPoint τ)
    (heps : 0≤κ*Num.IPM.alphaPrime I.m U/1024)
    (hbudget : P.machine.mem (P.machine.regs 8-3)=5*I.m)
    (hinput : EpochInputAccuracyAt I R target (Num.IPM.alphaPrime I.m U) r
      (κ*Num.IPM.alphaPrime I.m U/32) A P.history P.eta P.op base 0) :
    EpochAnalyticPrefixAt I U R target κ r A base 0 P := by
  refine ⟨fun j hj => (Nat.not_lt_zero j hj).elim,fun j hj => (Nat.not_lt_zero j hj).elim,
    epochHistoryCacheStable_zero I A P.history P.eta P.op base,?_,?_,epochReportBalance_zero _ _ _ _ hbudget⟩
  · intro t ht
    have h : t=0 := by omega
    subst t
    exact hinput
  · intro e _
    have h : 0≤κ*Num.IPM.alphaPrime I.m U/1024+(κ*Num.IPM.alphaPrime I.m U/1024)/4 :=
      add_nonneg heps (div_nonneg heps (by norm_num))
    simpa only [Nat.mul_zero,epochPendingMovement_zero] using h

/-- The analytic invariants start with the initial input's numerical
accuracy, zero movement, and the actual five-reports-per-edge record. -/
theorem epochAnalyticPrefix_zero {τ : Type} (I : Instance) (U : ℕ) (target κ r : ℝ)
    (A : MinRatioDataStructureWithFailure) (base : Fin I.m → ℝ) (P : EpochPoint τ)
    (heps : 0≤κ*Num.IPM.alphaPrime I.m U/1024)
    (hbudget : P.machine.mem (P.machine.regs 8-3)=5*I.m)
    (hinput : EpochInputAccuracy I U target (Num.IPM.alphaPrime I.m U) r
      (κ*Num.IPM.alphaPrime I.m U/32) A P.history P.eta P.op base 0) :
    EpochAnalyticPrefix I U target κ r A base 0 P :=
  epochAnalyticPrefixAt_zero I U _ target κ r A base P heps hbudget hinput

/-- The older certified inputs and the two actual numerical inputs
together account for every stage of the proposed history. -/
theorem epoch_input_accuracy_at_append (I : Instance) (R : ℕ) (target a r q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (i : ℕ) (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hold : ∀ t≤2*i,EpochInputAccuracyAt I R target a r q A D eta op base t)
    (hDetect : EpochInputAccuracyAt I R target a r q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base (2*i+1))
    (hUpdate : EpochInputAccuracyAt I R target a r q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base (2*i+1+1)) :
    ∀ t≤2*i+1+1,EpochInputAccuracyAt I R target a r q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base t := by
  intro t ht
  by_cases hOld : t≤2*i
  · exact (epochInputAccuracyAt_past I R target a r q A D eta op base (2*i) t hOld es g ell actual).mpr
      (hold t hOld)
  · by_cases h : t=2*i+1
    · exact h.symm ▸ hDetect
    · have h' : t=2*i+1+1 := by omega
      exact h'.symm ▸ hUpdate

/-- The older certified inputs and the two actual numerical inputs
together account for every stage of the proposed history. -/
theorem epoch_input_accuracy_append (I : Instance) (U : ℕ) (target a r q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (base : Fin I.m → ℝ) (i : ℕ) (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ)
    (hold : ∀ t≤2*i,EpochInputAccuracy I U target a r q A D eta op base t)
    (hDetect : EpochInputAccuracy I U target a r q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base (2*i+1))
    (hUpdate : EpochInputAccuracy I U target a r q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base (2*i+1+1)) :
    ∀ t≤2*i+1+1,EpochInputAccuracy I U target a r q A (appendHistoryIteration D (2*i) es g ell)
      (appendHistoryIterationEta eta (2*i) actual) (appendHistoryIterationOp op (2*i)) base t :=
  epoch_input_accuracy_at_append I _ target a r q A D eta op base i es g ell actual hold hDetect hUpdate

end MinCostFlow.IPM.Machine
