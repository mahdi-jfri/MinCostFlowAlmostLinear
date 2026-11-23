module

public import MinCostFlow.Scaling.AdjacencyScan
import Mathlib.Logic.Function.Basic

/-!
# A counted traversal for extracting distance labels

The dual-extraction reduction in Appendix C of Chen et al.,
arXiv:2203.00671v2, obtains a shortest-path tree from the positive-flow support
of an optimal routing. This file supplies its traversal as an integer function.
A newly reached vertex gets the parent's label minus the edge cost. Loading
its outgoing edges clears that adjacency list, so the total pending and stored
edge count drops by one per processed arc. This proves a linear operation bound
without any correctness assumption about the supplied flow.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Integer labels, visited flags, and the unprocessed directed edges. -/
structure LabelState (I : Circulation) where
  labels : Fin I.n → ℤ
  seen : Fin I.n → Bool
  outgoing : Fin I.n → List (Fin I.m)
  pending : List (Fin I.m)

namespace LabelState

/-- Number of arc entries still pending or stored in adjacency lists. -/
def remaining {I : Circulation} (s : LabelState I) : ℕ :=
  s.pending.length + I.adjacencyMass s.outgoing

/-- Process one pending edge, assigning a label only on first reaching its head.
The counter charges four operations for a skipped edge, or twelve plus two
per loaded adjacency entry for a newly reached vertex. -/
def step {I : Circulation} (s : LabelState I) : LabelState I × ℕ :=
  match s.pending with
  | [] => (s, 1)
  | e :: rest =>
    if s.seen (I.head e) then
      ({ s with pending := rest }, 4)
    else
      let entries := s.outgoing (I.head e)
      ({ labels := Function.update s.labels (I.head e) (s.labels (I.tail e) - I.cost e)
         seen := Function.update s.seen (I.head e) true
         outgoing := Function.update s.outgoing (I.head e) []
         pending := entries ++ rest }, 12 + 2 * entries.length)

/-- Every nonempty step consumes exactly one pending-or-stored edge entry. -/
theorem step_remaining {I : Circulation} (s : LabelState I) (hs : s.pending ≠ []) :
    s.step.1.remaining + 1 = s.remaining := by
  cases hp : s.pending with
  | nil => exact False.elim (hs hp)
  | cons e rest =>
    simp only [step, hp]
    split
    · simp only [remaining, hp, List.length_cons]
      omega
    · have hm := I.adjacencyMass_update s.outgoing (I.head e) []
      simp only [List.length_nil, Nat.add_zero] at hm
      simp only [remaining, hp, List.length_append, List.length_cons]
      omega

/-- The work of a step plus twice its remaining adjacency storage is bounded
by twelve plus twice the previous storage. This pays for copying loaded lists. -/
theorem step_work {I : Circulation} (s : LabelState I) :
    s.step.2 + 2 * I.adjacencyMass s.step.1.outgoing ≤
      12 + 2 * I.adjacencyMass s.outgoing := by
  cases hp : s.pending with
  | nil => simp only [step, hp]; omega
  | cons e rest =>
    simp only [step, hp]
    split
    · dsimp only
      omega
    · have hm := I.adjacencyMass_update s.outgoing (I.head e) []
      simp only [List.length_nil, Nat.add_zero] at hm
      dsimp only
      omega

/-- Run a bounded traversal, stopping as soon as no pending edges remain. -/
def run {I : Circulation} : ℕ → LabelState I → LabelState I × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    if s.pending = [] then (s, 1)
    else
      let next := s.step
      let result := run fuel next.1
      (result.1, next.2 + result.2)

/-- The traversal's work is at most twelve per allowed step plus twice the
initial adjacency storage. -/
theorem run_work {I : Circulation} (fuel : ℕ) (s : LabelState I) :
    (run fuel s).2 ≤ 12 * fuel + 2 * I.adjacencyMass s.outgoing := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      omega
    · dsimp only
      have h := ih s.step.1
      have hs := s.step_work
      omega

/-- A budget at least the initial pending-and-stored edge count completes the
traversal. Every nonempty step decreases that count by one. -/
theorem run_done {I : Circulation} (fuel : ℕ) (s : LabelState I)
    (hs : s.remaining ≤ fuel) : (run fuel s).1.pending = [] := by
  induction fuel generalizing s with
  | zero =>
    have hp : s.pending.length = 0 := by dsimp only [remaining] at hs; omega
    exact List.length_eq_zero_iff.mp hp
  | succ fuel ih =>
    rw [run]
    split
    · exact ‹s.pending = []›
    · dsimp only
      apply ih s.step.1
      have h := s.step_remaining ‹s.pending ≠ []›
      omega

end LabelState

/-- Initialize the root and move its outgoing edges into the pending list. -/
def initialLabelState (I : Circulation) (flow : Fin I.m → ℤ) (root : Fin I.n) :
    LabelState I :=
  let out := I.buildAdjacency flow
  { labels := fun _ => 0
    seen := fun v => decide (v = root)
    outgoing := Function.update out root []
    pending := out root }

/-- The initial pending-and-stored entry count is at most the number of edges. -/
theorem initialLabelState_remaining (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) : (I.initialLabelState flow root).remaining ≤ I.m := by
  have hm := I.adjacencyMass_update (I.buildAdjacency flow) root []
  simp only [List.length_nil, Nat.add_zero] at hm
  have hb := I.buildAdjacency_mass flow
  dsimp only [initialLabelState, LabelState.remaining]
  omega

/-- The label propagation model, including adjacency assembly and table
initialization. The flow and every computed label are integers. -/
def propagateLabels (I : Circulation) (flow : Fin I.m → ℤ) (root : Fin I.n) :
    LabelState I × ℕ :=
  let result := LabelState.run I.m (I.initialLabelState flow root)
  (result.1, 8 * I.m + 3 * I.n + 4 + result.2)

/-- The supplied `m`-step budget always exhausts the pending edges. -/
theorem propagateLabels_done (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) : (I.propagateLabels flow root).1.pending = [] :=
  LabelState.run_done I.m _ (I.initialLabelState_remaining flow root)

/-- Label propagation uses at most `22*m+3*n+4` counted integer/table operations.
The amortized term pays for every loaded adjacency entry once. -/
theorem propagateLabels_work (I : Circulation) (flow : Fin I.m → ℤ)
    (root : Fin I.n) : (I.propagateLabels flow root).2 ≤ 22 * I.m + 3 * I.n + 4 := by
  have h := LabelState.run_work I.m (I.initialLabelState flow root)
  have hm := I.initialLabelState_remaining flow root
  have hp : I.adjacencyMass (I.initialLabelState flow root).outgoing ≤ I.m := by
    dsimp only [LabelState.remaining] at hm
    omega
  dsimp only [propagateLabels]
  omega

end MinCostFlow.Scaling.Circulation
