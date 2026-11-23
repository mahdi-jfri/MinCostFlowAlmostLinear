module

public import MinCostFlow.IPM.MinRatioSpec
public import MinCostFlow.IPM.NamedInstance
public import MinCostFlow.IPM.HiddenParameters
public import MinCostFlow.IPM.EdgeRefresh
public import MinCostFlow.IPM.GradientStability

/-!
# A single stored-residual epoch of the IPM

This is Algorithm 7 of Chen et al., arXiv:2203.00671v2 (Section 9,
page 69), adapted to the Update, Query and Detect operations in
Definition 4.5 (page 14 of arXiv:2309.16629v1). One data structure
maintains the entire increment from a fixed base flow. After each
Update, Detect reports the coordinates to query and refresh. The
residual estimate is fixed within an epoch. A full refresh between
epochs reads all coordinates and makes the current flow the next base.

The gradient is scaled to the hidden parameter `1/(8000 log(m+2))`.
The eta input is scaled by the same factor. The smaller explicit step
normalization below allows for the rescaling of the stored residual,
as proved in `StoredStep`. The epoch state stores only algorithm data
and operation counters, not correctness or stability conclusions.
-/

@[expose] public section
noncomputable section
namespace MinCostFlow.IPM

/-- Detect threshold for the single-flow interface. -/
def ipmDetectThreshold (I : Instance) (U κ : ℝ) : ℝ := κ*alpha I U/1000

/-- The unscaled-gradient normalization, before the fixed gradient scale.
The underlying parameter is `κ α / 32`. -/
def ipmStepEta (I : Instance) (U κ : ℝ) : ℝ := (κ*alpha I U/32)^2/50

/-- Stored coordinates, the abstract data structure state, the pending
coefficient refreshes, and counts of the operations already performed. -/
structure IpmEpochState (I : Instance) (A : MinRatioDataStructure) where
  ds : A.State
  stored : Fin I.m → ℝ
  pending : Finset ℕ
  queries : ℕ
  updateSize : ℕ
  detected : ℕ

/-- The scaled stored gradient, with the residual estimate fixed for the
epoch. Only coordinates returned by Detect change within an epoch. -/
def epochGradient (I : Instance) (U r : ℝ) (stored : Fin I.m → ℝ) : Fin I.m → ℝ :=
  fun e => ipmGradientScale I U*gradientWithResidual I (alpha I U) r stored e

/-- Initialize an epoch at the current feasible flow. The data structure
stores only the increment from this base and therefore starts at zero. -/
def epochInit (I : Instance) (U r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : IpmEpochState I A :=
  { ds := A.init (namedInstance I) (namedVector (epochGradient I U r base))
      (namedVector (lengths I (alpha I U) base)),
    stored := base, pending := ∅, queries := 0, updateSize := 0, detected := 0 }

/-- The Update call from the current stored coordinates. Every pending
coefficient change is passed as a deletion followed by an insertion. -/
def epochUpdate (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (s : IpmEpochState I A) : A.State × (ℕ → ℝ) :=
  A.update s.ds (refreshEdges (namedInstance I) s.pending.toList)
    (namedVector (epochGradient I U r s.stored))
    (namedVector (lengths I (alpha I U) s.stored))
    (ipmGradientScale I U*ipmStepEta I U κ)

/-- One Update, one Detect, and one Query for each reported graph edge.
Queries outside the original graph are never performed. For a data
structure satisfying the specification, the filtering leaves its Detect
output unchanged. -/
def epochNext (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (s : IpmEpochState I A) : IpmEpochState I A :=
  let updated := epochUpdate I U κ r A s
  let reported := A.detect updated.1
  let S := reported.1.filter fun e => e < I.m
  { ds := reported.2,
    stored := fun e => if (e : ℕ) ∈ S then base e+A.query reported.2 e else s.stored e,
    pending := S, queries := s.queries+S.card,
    updateSize := s.updateSize+2*s.pending.card,
    detected := s.detected+reported.1.card }

/-- The causal sequence of stored-residual epoch states. -/
def epochState (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : ℕ → IpmEpochState I A
  | 0 => epochInit I U r A base
  | t+1 => epochNext I U κ r A base (epochState I U κ r A base t)

/-- The exact flow represented by an epoch state. This is a mathematical
observation. Reading the whole vector explicitly requires `m` Queries,
which are counted separately when an epoch ends. -/
def epochFlow (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) (e : Fin I.m) : ℝ :=
  base e+A.query (epochState I U κ r A base t).ds e

/-- Input instance at the beginning and after every operation. Odd stages
are Updates, and positive even stages are Detections. A Detect has the
same coefficients as the preceding Update. -/
def epochInstance (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) : DynamicInstance where
  G _ := namedInstance I
  U t := if t % 2 = 1 then
    refreshEdges (namedInstance I) (epochState I U κ r A base ((t-1)/2)).pending.toList
    else []
  g t := namedVector (epochGradient I U r (epochState I U κ r A base ((t-1)/2)).stored)
  ℓ t := namedVector (lengths I (alpha I U) (epochState I U κ r A base ((t-1)/2)).stored)

/-- The interleaving of Update and Detect operations in an epoch. -/
def epochIsUpdate (t : ℕ) : Bool := decide (t%2 = 1)

/-- Only Update stages receive a nonzero eta input. -/
def epochEta (I : Instance) (U κ : ℝ) (t : ℕ) : ℝ :=
  if t%2 = 1 then ipmGradientScale I U*ipmStepEta I U κ else 0

end MinCostFlow.IPM
