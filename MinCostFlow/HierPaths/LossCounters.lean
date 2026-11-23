module

public import MinCostFlow.HierPaths.Groups
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.List.Range

/-!
# The loss counters: the model

The lost sets of `HierPaths/Loss.lean` are defined from all directly failed terminals at once.
The data structure keeps them up to date one failure at a time, with integer counters. This file
writes that procedure as Lean functions; `HierPaths/LossCountersSpec.lean` proves it correct.

The state keeps, for each group `g` at each depth `j`:
* `own j g`, the size of the lost set of the group;
* `sum j g`, the sum of the sizes of the lost sets of its children (for groups above the leaves);

and also the set `failed` of directly failed terminals, the set `glob` of terminals marked
globally lost, and two operation counters: `updates` counts the counter updates and
`enumerated` counts the terminals enumerated when a group becomes wholly lost.

A first direct failure of `u` (`failStep`) adds one to the leaf count of `u` and enumerates `u`.
Then `climb` walks up the chain of groups of `u`. At each group it adds the change `Δ` coming
from below to `sum`, recomputes `own` by the rule of the lost sets (all members if
`4 · sum > size`, else `sum`), enumerates the members if the group has just become wholly lost,
and passes the change of `own` further up. It stops at the root or when the change is zero.
Enumerated terminals not yet marked are marked and output.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The state of the loss counters. -/
structure LossState where
  /-- The size of the lost set of each group, indexed by depth and group. -/
  own : ℕ → ℕ → ℕ
  /-- The sum of the sizes of the lost sets of the children of each group. -/
  sum : ℕ → ℕ → ℕ
  /-- The directly failed terminals. -/
  failed : Finset ℕ
  /-- The terminals marked globally lost. -/
  glob : Finset ℕ
  /-- The number of counter updates so far. -/
  updates : ℕ
  /-- The number of terminals enumerated so far. -/
  enumerated : ℕ

/-- The initial state: nothing failed. -/
def LossState.init : LossState := ⟨fun _ _ => 0, fun _ _ => 0, ∅, ∅, 0, 0⟩

/-- The array `f` with entry `(j, g)` set to `v`. -/
def setAt (f : ℕ → ℕ → ℕ) (j g v : ℕ) : ℕ → ℕ → ℕ :=
  fun i c => if i = j ∧ c = g then v else f i c

/-- The members of group `g` at depth `j`, in increasing order. -/
def memberList (x b j g : ℕ) : List ℕ := List.range' (g * groupSize x b j) (groupSize x b j)

/-- Enumerate the terminals of `l`: mark them globally lost and output those not marked before. -/
def enumerate (st : LossState) (l : List ℕ) : LossState × List ℕ :=
  (⟨st.own, st.sum, st.failed, st.glob ∪ l.toFinset, st.updates, st.enumerated + l.length⟩,
    l.filter (fun v => v ∉ st.glob))

/-- The new own count of a group at depth `j` whose children's counts sum to `s`: all members if
`4 s` exceeds the size, else `s`. -/
def newOwn (x b j s : ℕ) : ℕ := if groupSize x b j < 4 * s then groupSize x b j else s

/-- One level of the climb: update the counters of the group of `u` at depth `j` after a change
`Δ` of the lost set of its child. Returns the new state, the newly marked terminals and the
change to pass up. -/
def levelStep (x b u j Δ : ℕ) (st : LossState) : LossState × List ℕ × ℕ :=
  let X := groupOf x b j u
  let s := st.sum j X + Δ
  let o := st.own j X
  let o' := newOwn x b j s
  let st1 : LossState :=
    ⟨setAt st.own j X o', setAt st.sum j X s, st.failed, st.glob, st.updates + 1, st.enumerated⟩
  if o' = groupSize x b j ∧ o ≠ groupSize x b j then
    ((enumerate st1 (memberList x b j X)).1, (enumerate st1 (memberList x b j X)).2, o' - o)
  else (st1, [], o' - o)

/-- Walk up the chain of `u` from depth `j` (exclusive) to the root, passing the change `Δ`.
Stops when the change is zero. -/
def climb (x b u : ℕ) : ℕ → ℕ → LossState → LossState × List ℕ
  | 0, _, st => (st, [])
  | j + 1, Δ, st =>
    if Δ = 0 then (st, [])
    else
      ((climb x b u j (levelStep x b u j Δ st).2.2 (levelStep x b u j Δ st).1).1,
        (levelStep x b u j Δ st).2.1 ++
          (climb x b u j (levelStep x b u j Δ st).2.2 (levelStep x b u j Δ st).1).2)

/-- The step for a first direct failure of `u`. Returns the new state and the list of terminals
that became globally lost. -/
def failStep (x b u : ℕ) (st : LossState) : LossState × List ℕ :=
  let X := groupOf x b (leafDepth x b) u
  let st1 : LossState :=
    ⟨setAt st.own (leafDepth x b) X (st.own (leafDepth x b) X + 1), st.sum, insert u st.failed,
      st.glob, st.updates + 1, st.enumerated⟩
  ((climb x b u (leafDepth x b) 1 (enumerate st1 [u]).1).1,
    (enumerate st1 [u]).2 ++ (climb x b u (leafDepth x b) 1 (enumerate st1 [u]).1).2)

/-- The state after a list of first direct failures. -/
def runFailures (x b : ℕ) (l : List ℕ) : LossState :=
  l.foldl (fun st u => (failStep x b u st).1) LossState.init

end MinCostFlow.HierPaths
