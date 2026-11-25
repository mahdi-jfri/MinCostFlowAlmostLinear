module

public import MinCostFlow.Scaling.Residual
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Definitions for Gabow bit scaling on circulations

This file defines the doubled circulation instance, the capacity-capped phase
instance, integer residual projection and augmentation, and the phase-by-phase
bit-scaling model over `MinCostFlow.Scaling.Circulation`.

In bit scaling, capacities are introduced one bit at a time from most
significant to least significant. Starting from the zero flow at shift `T`
(the bit length of the largest capacity), phase `t + 1` (for `t < T`) forms
the doubled instance with capacities `I.capacity e / 2 ^ (T - (t + 1))`,
caps the residual capacities of twice the previous flow at `M = I.m + 1`,
solves that capped residual instance, and augments twice the previous flow by
the returned integral circulation.
-/

@[expose] public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- The doubled circulation instance with capacities `2 * I.capacity e + b e`,
keeping the same graph and edge costs. -/
abbrev doubled (I : Circulation) (b : Fin I.m → ℕ) : Circulation :=
  { I with capacity := fun e => 2 * I.capacity e + b e }

/-- Replace every edge capacity of `J` by its minimum with `M`. -/
abbrev capCapacities (J : Circulation) (M : ℕ) : Circulation :=
  { J with capacity := fun e => min (J.capacity e) M }

/-- The phase instance for bit scaling: the residual instance of `2 * g` in
the doubled instance `doubled I b`, with each capacity capped at `M`. -/
abbrev phaseInstance (I : Circulation) (b : Fin I.m → ℕ) (g : Fin I.m → ℤ)
    (M : ℕ) : Circulation :=
  capCapacities ((doubled I b).residual (fun e => 2 * g e)) M

/-- Integer projection of a residual circulation onto the original edges. -/
def intProject (m : ℕ) (d : Fin (m + m) → ℤ) (e : Fin m) : ℤ :=
  d (Fin.castAdd m e) - d (Fin.natAdd m e)

/-- Integer augmentation of a flow by a residual circulation. -/
def intAugment (m : ℕ) (f : Fin m → ℤ) (d : Fin (m + m) → ℤ) (e : Fin m) : ℤ :=
  f e + intProject m d e

/-- The maximum edge capacity of a circulation instance (`0` if `I.m = 0`). -/
def circMaxCapacity (I : Circulation) : ℕ :=
  Finset.univ.sup I.capacity

/-- The number of bit-scaling phases: the bit length `Nat.size` of the largest
edge capacity. -/
def bitScalingPhases (I : Circulation) : ℕ :=
  Nat.size (circMaxCapacity I)

/-- The instance obtained by dividing every capacity by `2 ^ k`. -/
abbrev truncInstance (I : Circulation) (k : ℕ) : Circulation :=
  { I with capacity := fun e => I.capacity e / 2 ^ k }

/-- Bit `k` of each edge capacity, `(I.capacity e / 2 ^ k) % 2`. -/
def capBit (I : Circulation) (k : ℕ) (e : Fin I.m) : ℕ :=
  (I.capacity e / 2 ^ k) % 2

/-- The capped residual phase instance for 0-based phase index `t` (i.e. phase
`t + 1` out of `T`) starting from previous flow `g`, with capacity cap
`M = I.m + 1`. -/
abbrev bitScalePhaseInstance (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ) :
    Circulation :=
  phaseInstance (truncInstance I (T - t)) (capBit I (T - (t + 1))) g (I.m + 1)

/-- The integral flow after `t` phases of bit scaling with total phase count
`T` and integral circulation solver `solve`. -/
def bitScaleFlow (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation)
    (T : ℕ) : ℕ → Fin I.m → ℤ
  | 0 => fun _ => 0
  | t + 1 =>
    let g := bitScaleFlow solve I T t
    intAugment I.m (fun e => 2 * g e) (solve (bitScalePhaseInstance I T t g))

/-- The phase instance passed to `solve` in 0-based phase `t` (phase `t + 1`). -/
abbrev bitScalePhaseCall (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (T t : ℕ) : Circulation :=
  bitScalePhaseInstance I T t (bitScaleFlow solve I T t)

/-- The integral residual flow returned by `solve` in 0-based phase `t`. -/
def bitScaleDelta (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation)
    (T t : ℕ) : Fin (I.m + I.m) → ℤ :=
  solve (bitScalePhaseCall solve I T t)

/-- The ordered list of `T` phase instances passed to `solve`. -/
def bitScaleCalls (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation)
    (T : ℕ) : List Circulation :=
  (List.range T).map (bitScalePhaseCall solve I T)

/-- Top-level bit-scaling model: runs `T = bitScalingPhases I` phases and
returns the final integral flow. -/
def bitScaleSolve (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : Fin I.m → ℤ :=
  bitScaleFlow solve I (bitScalingPhases I) (bitScalingPhases I)

/-- The list of phase instances invoked by `bitScaleSolve solve I`. -/
def bitScaleModelCalls (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) : List Circulation :=
  bitScaleCalls solve I (bitScalingPhases I)

/-- Exact forward residual capacity of edge `e` after `t` phases at flow `g`. -/
def phaseResidual (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ)
    (e : Fin I.m) : ℕ :=
  (((truncInstance I (T - t)).capacity e : ℤ) - g e).toNat

/-- Capped forward residual capacity of edge `e` after `t` phases at flow `g`. -/
def cappedResidual (I : Circulation) (T t : ℕ) (g : Fin I.m → ℤ) (M : ℕ)
    (e : Fin I.m) : ℕ :=
  min (phaseResidual I T t g e) M

/-- Capped flow (reverse residual capacity) of edge `e` at flow `g`. -/
def cappedFlow {m : ℕ} (g : Fin m → ℤ) (M : ℕ) (e : Fin m) : ℕ :=
  min (g e).toNat M

end MinCostFlow.Narrow
