module

public import MinCostFlow.IPM.Machine.EpochHistoryCache
public import MinCostFlow.IPM.Machine.EpochHiddenWitness
import Mathlib.Tactic.Linarith

/-!
# Accuracy at each input of a fixed-point epoch

The flow for a min-ratio stage is the flow immediately before the
operation. The two stages of a machine iteration use the same flow,
even though only the second receives the refreshed coefficient table.
The analytic proof transports the old stages unchanged.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM.Machine

/-- The coefficients at stage zero, and at the following operation
inputs, are compared with the flow before the operation. -/
def epochInputFlow (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (t : ℕ)
    (base : Fin I.m → ℝ) : Fin I.m → ℝ :=
  epochHistoryFlow I A D eta op (t-1) base

/-- The coefficient and stale-coordinate estimates of Lemma 9.1 of
Chen et al., arXiv:2203.00671v2 (page 70), at one input stage. -/
def EpochInputAccuracyAt (I : Instance) (R : ℕ) (target a r q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ)
    (op : ℕ → Bool) (base : Fin I.m → ℝ) (t : ℕ) : Prop :=
  let f := epochInputFlow I A D eta op t base
  let stored := epochHistoryCache I A D eta op t base
  let g : Fin I.m → ℝ := fun e => D.g t e
  let ell : Fin I.m → ℝ := fun e => D.ℓ t e
  D.g t=namedVector g ∧ D.ℓ t=namedVector ell ∧
  ScalarApprox (1+q/4) r (residual I target f) ∧
  VectorApprox 2 ell (lengths I a f) ∧
  GradientTolerance (lengths I a f) (fun e => (r/residual I target f)*g e)
    (gradient I a target f) (q/16) ∧
  (∀ e, 1/(2:ℝ)^(R)≤ell e ∧ ell e≤(2:ℝ)^(R)) ∧
  ∀ e,|ell e*(f e-stored e)|≤1/2

/-- Accuracy at the original binary range. -/
def EpochInputAccuracy (I : Instance) (U : ℕ) (target a r q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ)
    (op : ℕ → Bool) (base : Fin I.m → ℝ) (t : ℕ) : Prop :=
  EpochInputAccuracyAt I (ipmRangeExponent I.m U) target a r q A D eta op base t

/-- Earlier inputs retain the same accuracy statements after appending
the next two operations. -/
theorem epochInputAccuracyAt_past (I : Instance) (R : ℕ) (target a r q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ)
    (op : ℕ → Bool) (base : Fin I.m → ℝ) (T t : ℕ) (ht : t≤T)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ) :
    EpochInputAccuracyAt I R target a r q A (appendHistoryIteration D T es g ell)
      (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) base t ↔
      EpochInputAccuracyAt I R target a r q A D eta op base t := by
  rw [EpochInputAccuracyAt,EpochInputAccuracyAt,
    epochHistoryCache_past I A D eta op T es g ell actual base t ht]
  have hflow : epochInputFlow I A (appendHistoryIteration D T es g ell)
      (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) t base =
        epochInputFlow I A D eta op t base := by
    funext e
    unfold epochInputFlow epochHistoryFlow
    rw [appendHistoryIteration_past_flow A.eraseFailure D eta op T es g ell actual _ _ (by omega)]
  rw [hflow]
  simp only [appendHistoryIteration,appendHistoryStage,Function.update_of_ne (by omega : t≠T+1),
    Function.update_of_ne (by omega : t≠T+1+1)]

/-- Earlier inputs retain the same accuracy statements after appending
the next two operations. -/
theorem epochInputAccuracy_past (I : Instance) (U : ℕ) (target a r q : ℝ)
    (A : MinRatioDataStructureWithFailure) (D : DynamicInstance) (eta : ℕ → ℝ)
    (op : ℕ → Bool) (base : Fin I.m → ℝ) (T t : ℕ) (ht : t≤T)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ) :
    EpochInputAccuracy I U target a r q A (appendHistoryIteration D T es g ell)
      (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) base t ↔
      EpochInputAccuracy I U target a r q A D eta op base t :=
  epochInputAccuracyAt_past I _ target a r q A D eta op base T t ht es g ell actual

/-- Both new operation inputs see the same pre-Update flow, since
Detect adds zero implicit circulation. -/
theorem epochInputFlow_append (I : Instance) (A : MinRatioDataStructureWithFailure)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (es : List ℕ) (g ell : ℕ → ℝ) (actual : ℝ) (base : Fin I.m → ℝ) :
    let D' := appendHistoryIteration D T es g ell
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    epochInputFlow I A D' eta' op' (T+1) base=epochHistoryFlow I A D eta op T base ∧
    epochInputFlow I A D' eta' op' (T+1+1) base=epochHistoryFlow I A D eta op T base := by
  dsimp only
  constructor <;> funext e <;> unfold epochInputFlow epochHistoryFlow
  · rw [Nat.add_sub_cancel,appendHistoryIteration_past_flow A.eraseFailure D eta op T es g ell actual T _ le_rfl]
  · rw [Nat.add_sub_cancel]
    unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
    rw [appendHistoryStage_past_flow A.eraseFailure _ _ _ (T+1) _ _ _ actual true _ _ le_rfl,
      appendHistoryStage_detect_flow A.eraseFailure D eta op T 0 e.val]

/-- The valid-history unchanged-edge condition extends over any
interval in which the edge remains present and is never inserted. -/
theorem epoch_length_constant (I : Instance) (D : DynamicInstance) (op : ℕ → Bool)
    (T : ℕ) (hv : MinRatioHistoryValid D op T)
    (hG : ∀ j≤T,D.G j=namedInstance I) {t u : ℕ} (htu : t≤u) (hu : u≤T)
    (e : Fin I.m) (hnot : D.NotInsertedBetween e t u) :
    D.ℓ u e=D.ℓ t e := by
  induction u with
  | zero =>
    have ht : t=0 := by omega
    rw [ht]
  | succ u ih =>
    by_cases h : t=u+1
    · rw [h]
    · have ht : t≤u := by omega
      have hbefore : D.NotInsertedBetween e t u :=
        fun j hj hj' => hnot j hj (hj'.trans (Nat.le_succ _))
      have he : e.val∈(D.G (u+1)).E := by rw [hG _ hu]; exact Finset.mem_range.mpr e.isLt
      have hlast : D.NotInsertedBetween e (u+1-1) (u+1) :=
        fun j hj hj' => hnot j (by omega) hj'
      have hs := (hv.2.2.2 _ (by omega) hu e he hlast).2
      exact hs.trans (ih ht (by omega) hbefore)

end MinCostFlow.IPM.Machine
