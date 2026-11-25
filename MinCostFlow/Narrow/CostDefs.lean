module

public import MinCostFlow.Narrow.Defs
public import MinCostFlow.Scaling.ShortestRoutingModel
public import Mathlib.Data.Nat.Log

/-!
# Definitions for Stage 1 narrow-word cost scaling

This file defines the state, power-of-two units, clipping thresholds, freezing
flags, half-unit reduced-cost updates, small-data dual extraction, and the
Stage 1 cost-scaling loop over `MinCostFlow.Scaling.Circulation`.

Unlike `MinCostFlow.Scaling.CostState`, `NarrowCostState` stores no vertex
potentials. Per edge `e`, it keeps only a three-state freeze flag
(`FreezeState`), a small half-unit reduced cost `halfCost e` of magnitude
below `freezeThreshold I.m = O(m ^ 9)`, and the integral flow `flow e`.
Each round solves the rounded residual instance with Stage 2 (`bitScaleSolve`),
extracts the round's dual from the rounded costs and Stage 2's residual
presence flags (`extractDualFromFlags`), updates `halfCost` using one bit of
`I.cost e` and the round's dual, and freezes edges crossing `±freezeThreshold`.
-/

@[expose] public section

namespace MinCostFlow.Narrow

open MinCostFlow.Scaling

/-- Maximum absolute edge cost of a circulation instance (`0` if `I.m = 0`). -/
def circMaxCost (I : Circulation) : ℕ :=
  Finset.univ.sup (fun e => (I.cost e).natAbs)

/-- Bit length `L = Nat.size (circMaxCost I)`, satisfying `|I.cost e| < 2 ^ L`. -/
def costScaleBits (I : Circulation) : ℕ :=
  Nat.size (circMaxCost I)

/-- Power-of-two precision exponent `p = Nat.clog 2 ((2 * m) ^ 8)` so that
`2 ^ p ≥ (2 * m) ^ 8`. -/
def costPrecisionExp (m : ℕ) : ℕ :=
  Nat.clog 2 ((2 * m) ^ 8)

/-- Power-of-two vertex/edge scale exponent `q = Nat.clog 2 (2 * m)` so that
`2 * m ≤ 2 ^ q < 4 * m` for `m ≥ 1`. -/
def costClipExp (m : ℕ) : ℕ :=
  Nat.clog 2 (2 * m)

/-- Lower clipping magnitude `2 ^ p` (in round units `δ_j`). -/
def lowerClip (m : ℕ) : ℕ :=
  2 ^ costPrecisionExp m

/-- Upper clipping threshold `2 ^ (p + q)` (in round units `δ_j`). For every
`m ≥ 1` and `n ≤ 2 * m`, `n * lowerClip m ≤ upperClip m ≤ (2 * m) ^ 10`. -/
def upperClip (m : ℕ) : ℕ :=
  2 ^ (costPrecisionExp m + costClipExp m)

/-- Half-unit freezing threshold `Θ = 8 * upperClip m = 2 ^ (p + q + 3)`. -/
def freezeThreshold (m : ℕ) : ℕ :=
  8 * upperClip m

/-- Real optimality tolerance `ε_j = 2 ^ (L + p + 1 - j)` at round `j`. -/
noncomputable def stageEps (L p j : ℕ) : ℝ :=
  (2 : ℝ) ^ (((L + p + 1 : ℕ) : ℤ) - (j : ℤ))

/-- Real rounding unit `δ_j = ε_j / 2 ^ p = 2 ^ (L + 1 - j)` at round `j`. -/
noncomputable def stageDelta (L j : ℕ) : ℝ :=
  (2 : ℝ) ^ (((L + 1 : ℕ) : ℤ) - (j : ℤ))

/-- Integer floor `⌊c / 2 ^ k⌋` for any integer cost `c` and signed shift `k`. -/
def costScaled (c : ℤ) (k : ℤ) : ℤ :=
  if 0 ≤ k then c / (2 ^ k.toNat : ℤ) else c * (2 ^ (-k).toNat : ℤ)

/-- Bit `k` of a signed cost `c`: `(c / 2 ^ k) % 2` (floor division) when
`k ≥ 0`, and `0` when `k < 0`. -/
def costBit (c : ℤ) (k : ℤ) : ℤ :=
  if 0 ≤ k then (c / (2 ^ k.toNat : ℤ)) % 2 else 0

/-- Clamp an integer to `[lo, hi]`. -/
def clampInt (lo hi x : ℤ) : ℤ :=
  max lo (min x hi)

/-- Freezing status of an original edge in Stage 1:
- `none`: active (not frozen), reduced cost tracked in half units;
- `pos`: frozen with large positive reduced cost (`flow = 0` forever);
- `neg`: frozen with large negative reduced cost (`flow = capacity` forever). -/
inductive FreezeState where
  | none
  | pos
  | neg
deriving DecidableEq

/-- Forward residual slot cost derived solely from the freeze flag and half-unit
reduced cost `x`. -/
def roundedForwardCost (m : ℕ) (fr : FreezeState) (x : ℤ) : ℤ :=
  match fr with
  | .none => clampInt (-(lowerClip m : ℤ)) (upperClip m : ℤ) ((x + 1) / 2)
  | .pos => (upperClip m : ℤ)
  | .neg => -(lowerClip m : ℤ)

/-- Reverse residual slot cost derived solely from the freeze flag and half-unit
reduced cost `x`. -/
def roundedReverseCost (m : ℕ) (fr : FreezeState) (x : ℤ) : ℤ :=
  match fr with
  | .none => clampInt (-(lowerClip m : ℤ)) (upperClip m : ℤ) (-((x + 1) / 2))
  | .pos => -(lowerClip m : ℤ)
  | .neg => (upperClip m : ℤ)

/-- The `2 * I.m` rounded and clipped slot costs of a Stage 1 round. -/
def narrowRoundedCosts (I : Circulation) (fr : Fin I.m → FreezeState)
    (x : Fin I.m → ℤ) : Fin (I.m + I.m) → ℤ :=
  Fin.addCases (fun e => roundedForwardCost I.m (fr e) (x e))
    (fun e => roundedReverseCost I.m (fr e) (x e))

/-- One-round update of an edge's `(FreezeState, halfCost)` from its previous
value, the incoming cost bit, and the round's dual difference
`dy (tail e) - dy (head e)`. -/
def stepHalfCost (Θ : ℕ) (fr : FreezeState) (x bit dyDiff : ℤ) :
    FreezeState × ℤ :=
  match fr with
  | .none =>
    let x' := 2 * x + bit - 4 * dyDiff
    if (Θ : ℤ) ≤ x' then (.pos, 0)
    else if x' ≤ -(Θ : ℤ) then (.neg, 0)
    else (.none, x')
  | .pos => (.pos, 0)
  | .neg => (.neg, 0)

/-- Residual-presence graph built solely from the graph topology, small costs
of `J`, and boolean active flags `fwdActive` / `revActive` (never reading
`J.capacity`). -/
abbrev flagResidualGraph (J : Circulation)
    (fwdActive revActive : Fin J.m → Bool) : Circulation where
  n := J.n
  m := J.m + J.m
  tail := Fin.addCases J.tail J.head
  head := Fin.addCases J.head J.tail
  capacity := Fin.addCases (fun e => if fwdActive e then 1 else 0)
    (fun e => if revActive e then 1 else 0)
  cost := Fin.addCases J.cost (fun e => -J.cost e)

/-- Extract the round's integral dual potential using only the graph topology,
small rounded costs of `J`, and boolean residual-presence flags. -/
def extractDualFromFlags (solve : (K : Circulation) → Fin K.m → ℤ)
    (J : Circulation) (fwdActive revActive : Fin J.m → Bool) : Fin J.n → ℤ :=
  let R := flagResidualGraph J fwdActive revActive
  let S := R.shortestRoutingGraph
  let start := R.shortestRoutingStart
  let Q := S.residual start
  let delta := Circulation.solveWithZeroCapacities solve Q
  let routing : Fin S.m → ℤ := fun e =>
    start e + delta (Fin.castAdd S.m e) - delta (Fin.natAdd S.m e)
  let labels := S.propagateLabels routing (Fin.last J.n)
  fun v => labels.1.labels v.castSucc

/-- The single positive-capacity bounded-solver instance called by
`extractDualFromFlags`. -/
abbrev extractDualFromFlagsCall (J : Circulation)
    (fwdActive revActive : Fin J.m → Bool) : Circulation :=
  let R := flagResidualGraph J fwdActive revActive
  (R.shortestRoutingGraph.residual R.shortestRoutingStart).positiveInstance

/-- State of the Stage 1 narrow-word cost-scaling loop. No potentials are
stored. -/
structure NarrowCostState (I : Circulation) where
  flow : Fin I.m → ℤ
  frozen : Fin I.m → FreezeState
  halfCost : Fin I.m → ℤ
  round : ℕ

/-- Initial Stage 1 state: zero flow, no frozen edges, and `halfCost e` equal
to `-1` for negative costs and `0` for nonnegative costs. -/
def narrowCostInitial (I : Circulation) : NarrowCostState I where
  flow := fun _ => 0
  frozen := fun _ => .none
  halfCost := fun e => if I.cost e < 0 then -1 else 0
  round := 0

/-- The rounded residual circulation instance solved by Stage 2 in one Stage 1
round. -/
abbrev narrowRoundInstance (I : Circulation) (s : NarrowCostState I) :
    Circulation :=
  { I.residual s.flow with cost := narrowRoundedCosts I s.frozen s.halfCost }

/-- The integral augmentation computed by Stage 2 (`bitScaleSolve`) in one
Stage 1 round. -/
def narrowRoundDelta (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (s : NarrowCostState I) : Fin (I.m + I.m) → ℤ :=
  bitScaleSolve (Circulation.solveWithZeroCapacities solve) (narrowRoundInstance I s)

/-- Forward residual presence flags read from Stage 2's final capped residual. -/
def narrowRoundFwdFlags (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (s : NarrowCostState I) : Fin (I.m + I.m) → Bool :=
  let J := narrowRoundInstance I s
  let delta := narrowRoundDelta solve I s
  fun a => decide (0 < cappedResidual J (bitScalingPhases J) (bitScalingPhases J) delta (J.m + 1) a)

/-- Reverse residual presence flags read from Stage 2's final capped flow. -/
def narrowRoundRevFlags (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (s : NarrowCostState I) : Fin (I.m + I.m) → Bool :=
  let J := narrowRoundInstance I s
  let delta := narrowRoundDelta solve I s
  fun a => decide (0 < cappedFlow delta (J.m + 1) a)

/-- The round's integral dual potential extracted from the rounded costs and
Stage 2's residual presence flags. -/
def narrowRoundDual (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (s : NarrowCostState I) : Fin I.n → ℤ :=
  extractDualFromFlags solve (narrowRoundInstance I s)
    (narrowRoundFwdFlags solve I s) (narrowRoundRevFlags solve I s)

/-- One Stage 1 cost-scaling round. -/
def narrowCostStep (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L : ℕ) (s : NarrowCostState I) : NarrowCostState I :=
  let delta := narrowRoundDelta solve I s
  let dy := narrowRoundDual solve I s
  let nextPair (e : Fin I.m) : FreezeState × ℤ :=
    stepHalfCost (freezeThreshold I.m) (s.frozen e) (s.halfCost e)
      (costBit (I.cost e) ((L : ℤ) - ((s.round + 1 : ℕ) : ℤ)))
      (dy (I.tail e) - dy (I.head e))
  { flow := intAugment I.m s.flow delta
    frozen := fun e => (nextPair e).1
    halfCost := fun e => (nextPair e).2
    round := s.round + 1 }

/-- Stage 1 state after `j` rounds. -/
def narrowCostStateAt (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L : ℕ) : ℕ → NarrowCostState I
  | 0 => narrowCostInitial I
  | j + 1 => narrowCostStep solve I L (narrowCostStateAt solve I L j)

/-- Total number of Stage 1 cost-scaling rounds:
`L + p + 1 + Nat.size (I.n + 1)`. -/
def narrowCostRounds (I : Circulation) : ℕ :=
  costScaleBits I + costPrecisionExp I.m + 1 + Nat.size (I.n + 1)

/-- Final integral circulation returned by Stage 1. -/
def narrowCostSolve (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) : Fin I.m → ℤ :=
  (narrowCostStateAt solve I (costScaleBits I) (narrowCostRounds I)).flow

/-- Positive-capacity bounded-solver instances invoked during one Stage 1
round: Stage 2's phase calls (wrapped with `positiveInstance`) followed by
the single dual-extraction call. -/
def narrowRoundSolverCalls (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (s : NarrowCostState I) : List Circulation :=
  let J := narrowRoundInstance I s
  (bitScaleModelCalls (Circulation.solveWithZeroCapacities solve) J).map
      Circulation.positiveInstance ++
    [extractDualFromFlagsCall J (narrowRoundFwdFlags solve I s) (narrowRoundRevFlags solve I s)]

/-- All positive-capacity bounded-solver instances invoked across all
`narrowCostRounds I` rounds of Stage 1. -/
def narrowCostSolverCalls (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) : List Circulation :=
  (List.range (narrowCostRounds I)).flatMap
    (fun j => narrowRoundSolverCalls solve I (narrowCostStateAt solve I (costScaleBits I) j))

/-- Ghost integer potential (in units of `δ_j`) maintained only for the
mathematical proof, never stored in `NarrowCostState`. -/
def ghostPotential (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L : ℕ) : ℕ → Fin I.n → ℤ
  | 0 => fun _ => 0
  | j + 1 =>
    let y := ghostPotential solve I L j
    let dy := narrowRoundDual solve I (narrowCostStateAt solve I L j)
    fun v => 2 * (y v + dy v)

/-- Ghost real potential `δ_j * ghostPotential` at round `j`. -/
noncomputable def ghostRealPotential (solve : (K : Circulation) → Fin K.m → ℤ)
    (I : Circulation) (L : ℕ) (j : ℕ) (v : Fin I.n) : ℝ :=
  stageDelta L j * (ghostPotential solve I L j v : ℝ)

/-- Reduced-cost freezing margin `(2 ^ q + 4 * m) * ε_j` preserved across
all rounds once an edge is frozen. -/
noncomputable def freezeMargin (m L p j : ℕ) : ℝ :=
  (((2 ^ costClipExp m : ℕ) : ℝ) + 4 * (m : ℝ)) * stageEps L p j

end MinCostFlow.Narrow
