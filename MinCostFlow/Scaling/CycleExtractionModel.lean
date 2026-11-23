module

public import MinCostFlow.Scaling.AdjacencyScan
import Mathlib.Logic.Function.Basic

/-!
# Counted cycle extraction from a unit circulation

Lemma C.10 of Chen et al., arXiv:2203.00671v2, detects a negative cycle by
solving a unit-capacity circulation. The function here follows unused
positive-flow arcs. When a vertex repeats, it removes the closed part of the
walk and returns it if its cost is negative. Nonnegative closed parts are
discarded and the walk continues. An explicit mode separates walking from
removing one edge of a closed part.

This file proves termination and a linear operation-counter bound for the
model. The circulation and negativity correctness arguments are separate.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The three traversal modes, plus a completed result. -/
inductive CycleMode (I : Circulation) where
  | choose
  | walk (vertex : Fin I.n)
  | peel (target : Fin I.n)
  | done
  deriving DecidableEq

/-- Integer data used by the positive-flow cycle scan. -/
structure CycleState (I : Circulation) where
  mode : CycleMode I
  outgoing : Fin I.n → List (Fin I.m)
  candidates : List (Fin I.m)
  stack : List (Fin I.m)
  onPath : Fin I.n → Bool
  cycleEdges : List (Fin I.m)
  cycleCost : ℤ
  result : Option (List (Fin I.m))

namespace CycleState

/-- A small mode rank pays for transitions between the three phases. -/
def rank {I : Circulation} : CycleMode I → ℕ
  | .choose => 0
  | .walk _ => 1
  | .peel _ => 2
  | .done => 0

/-- Remaining adjacency entries, candidate entries, and path edges pay for
walking, choosing a new start, and removing closed parts. -/
def potential {I : Circulation} (s : CycleState I) : ℕ :=
  4 * I.adjacencyMass s.outgoing + 2 * s.candidates.length +
    s.stack.length + rank s.mode

/-- Process one candidate, unused arc, or edge of a closed part. -/
def step {I : Circulation} (s : CycleState I) : CycleState I :=
  match s.mode with
  | .done => s
  | .choose =>
    match s.candidates with
    | [] => { s with mode := .done, result := none }
    | e :: rest =>
      let v := I.tail e
      if s.outgoing v = [] then
        { s with candidates := rest, stack := [] }
      else
        { s with mode := .walk v, candidates := rest, stack := [], onPath := Function.update s.onPath v true, cycleEdges := [], cycleCost := 0 }
  | .walk v =>
    match s.outgoing v with
    | [] => { s with mode := .choose, stack := [], onPath := Function.update s.onPath v false }
    | e :: rest =>
      let out := Function.update s.outgoing v rest
      if s.onPath (I.head e) then
        { s with mode := .peel (I.head e), outgoing := out, stack := e :: s.stack, cycleEdges := [], cycleCost := 0 }
      else
        { s with mode := .walk (I.head e), outgoing := out, stack := e :: s.stack, onPath := Function.update s.onPath (I.head e) true }
  | .peel target =>
    match s.stack with
    | [] => { s with mode := .done, result := none }
    | e :: rest =>
      let cost := s.cycleCost + I.cost e
      let edges := e :: s.cycleEdges
      let seen := if I.head e = target then s.onPath
        else Function.update s.onPath (I.head e) false
      if I.tail e = target then
        if cost < 0 then
          { s with mode := .done, stack := rest, onPath := seen, cycleEdges := edges, cycleCost := cost, result := some edges }
        else
          { s with mode := .walk target, stack := rest, onPath := seen, cycleEdges := [], cycleCost := 0 }
      else
        { s with stack := rest, onPath := seen, cycleEdges := edges, cycleCost := cost }


/-- Each unfinished step either completes the scan or decreases its natural
potential. This bound uses no circulation assumption on the supplied flow. -/
theorem step_progress {I : Circulation} (s : CycleState I) (hs : s.mode ≠ .done) :
    s.step.mode = .done ∨ s.step.potential + 1 ≤ s.potential := by
  rcases s with ⟨mode, out, candidates, stack, onPath, cycleEdges, cycleCost, result⟩
  cases mode with
  | done => exact False.elim (hs rfl)
  | choose =>
    cases hc : candidates with
    | nil => left; simp only [step]
    | cons e rest =>
      simp only [step]
      split
      · right
        simp only [potential, rank, List.length_cons, List.length_nil]
        omega
      · right
        simp only [potential, rank, List.length_cons, List.length_nil]
        omega
  | walk v =>
    cases ho : out v with
    | nil =>
      right
      simp only [step, ho, potential, rank, List.length_nil]
      omega
    | cons e rest =>
      have hu := I.adjacencyMass_update out v rest
      rw [ho, List.length_cons] at hu
      simp only [step, ho]
      split
      · right
        simp only [potential, rank, List.length_cons]
        omega
      · right
        simp only [potential, rank, List.length_cons]
        omega
  | peel target =>
    cases hk : stack with
    | nil => left; simp only [step]
    | cons e rest =>
      simp only [step]
      split
      · split
        · exact Or.inl rfl
        · right
          simp only [potential, rank, List.length_cons]
          omega
      · right
        simp only [potential, rank, List.length_cons]
        omega

/-- Run the scan with an explicit fuel budget and forty counted operations per
unfinished step. The final completion test costs one operation. -/
def run {I : Circulation} : ℕ → CycleState I → CycleState I × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    if s.mode = .done then (s, 1)
    else
      let r := run fuel s.step
      (r.1, 40 + r.2)

/-- A completed state stays completed for every fuel budget. -/
theorem run_of_done {I : Circulation} (fuel : ℕ) (s : CycleState I)
    (hs : s.mode = .done) : (run fuel s).1.mode = .done := by
  cases fuel with
  | zero => exact hs
  | succ fuel => simp only [run, hs, ↓reduceIte]

/-- The potential gives a sufficient linear fuel budget for completion. -/
theorem run_done {I : Circulation} (fuel : ℕ) (s : CycleState I)
    (hs : s.potential < fuel) : (run fuel s).1.mode = .done := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    rw [run]
    split
    · exact ‹s.mode = .done›
    · dsimp only
      rcases s.step_progress ‹_› with hd | hp
      · exact run_of_done fuel s.step hd
      · apply ih
        omega

/-- The scan's model counter is linear in its explicit fuel budget. -/
theorem run_work {I : Circulation} (fuel : ℕ) (s : CycleState I) :
    (run fuel s).2 ≤ 40 * fuel + 1 := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    rw [run]
    split
    · dsimp only
      omega
    · dsimp only
      have h := ih s.step
      omega

end CycleState

/-- Initial unused positive-flow arcs and an empty walk. -/
def cycleInitial (I : Circulation) (flow : Fin I.m → ℤ) : CycleState I where
  mode := .choose
  outgoing := I.buildAdjacency flow
  candidates := List.finRange I.m
  stack := []
  onPath := fun _ => false
  cycleEdges := []
  cycleCost := 0
  result := none

/-- The initial potential is at most six times the number of edges. -/
theorem cycleInitial_potential (I : Circulation) (flow : Fin I.m → ℤ) :
    (I.cycleInitial flow).potential ≤ 6 * I.m := by
  have h := I.buildAdjacency_mass flow
  simp only [cycleInitial, CycleState.potential, CycleState.rank, List.length_finRange,
    List.length_nil]
  omega

/-- Extract a negative closed part from a unit flow, using only explicit
integer loops, adjacency tables, and stack operations. -/
def extractCycleModel (I : Circulation) (flow : Fin I.m → ℤ) :
    CycleState I × ℕ :=
  let r := CycleState.run (6 * I.m + 1) (I.cycleInitial flow)
  (r.1, 9 * I.m + 2 * I.n + 4 + r.2)

/-- The cycle extraction always completes within its stated fuel budget. -/
theorem extractCycleModel_done (I : Circulation) (flow : Fin I.m → ℤ) :
    (I.extractCycleModel flow).1.mode = .done := by
  apply CycleState.run_done
  have h := I.cycleInitial_potential flow
  omega

/-- The extraction reserves at most `300*(m+n+1)` other integer operations. -/
theorem extractCycleModel_work (I : Circulation) (flow : Fin I.m → ℤ) :
    (I.extractCycleModel flow).2 ≤ 300 * (I.m + I.n + 1) := by
  have h := CycleState.run_work (6 * I.m + 1) (I.cycleInitial flow)
  dsimp only [extractCycleModel]
  omega

end MinCostFlow.Scaling.Circulation
