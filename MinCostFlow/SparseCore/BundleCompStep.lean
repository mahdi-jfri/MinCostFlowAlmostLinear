module

public import MinCostFlow.SparseCore.BundleRunsSpec

/-!
# The bundle step of one component

The spanner of a component of the initial graph runs on the bundle graph of that component. When the
input is ordered, the bundle step is the canonical step `bundleRunsStep`: it deletes the bundle
edges that the batch deletes and cuts every bundle into its maximal arcs in the core rotation after
the batch. When the input is not ordered the step does nothing. The specifications are in
`BundleStepDefs.lean`, and the proof that the canonical step meets them is `bundleRunsStep_spec`.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

/-- The bundle step of one component: the canonical step when the input is ordered, and no change
otherwise. -/
noncomputable def bundleCompStep (cs : CompLSFState) (B : BundleState) (k : ℕ)
    (ord ord' : ℕ → List End) (U : List Update) : List Update × BundleState :=
  open Classical in
  if BundleStepReady cs B k ord ord' U then bundleRunsStep cs B k ord' U else ([], B)

/-- On ordered input the bundle step is the canonical step. -/
theorem bundleCompStep_eq {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    bundleCompStep cs B k ord ord' U = bundleRunsStep cs B k ord' U := by
  unfold bundleCompStep
  rw [ite_eq_left h]

/-- The bundle step meets its specification on ordered input. -/
theorem bundleCompStep_spec {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    BundleStepSpec cs B k ord' U (bundleCompStep cs B k ord ord' U).1
      (bundleCompStep cs B k ord ord' U).2 := by
  rw [bundleCompStep_eq h]
  exact (bundleRunsStep_spec h).1

/-- The bundle step meets the local part of its specification on ordered input. -/
theorem bundleCompStep_localSpec {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : BundleStepReady cs B k ord ord' U) :
    BundleStepLocalSpec cs B U (bundleCompStep cs B k ord ord' U).1
      (bundleCompStep cs B k ord ord' U).2 := by
  rw [bundleCompStep_eq h]
  exact (bundleRunsStep_spec h).2

/-- Without ordered input the bundle step changes nothing. -/
theorem bundleCompStep_of_not {cs : CompLSFState} {B : BundleState} {k : ℕ}
    {ord ord' : ℕ → List End} {U : List Update} (h : ¬ BundleStepReady cs B k ord ord' U) :
    bundleCompStep cs B k ord ord' U = ([], B) := by
  unfold bundleCompStep
  rw [ite_eq_right h]

end MinCostFlow.SparseCore
