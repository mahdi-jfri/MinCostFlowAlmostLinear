module

public import MinCostFlow.IPM.Machine.EpochLayout
public import MinCostFlow.IPM.Machine.EpochStart

/-!
# The next epoch layout

The graph, input coefficients and scalar constants keep their original
addresses. Only the base, held residual, mutable flow, new data
structure, its name list and coefficient tables receive new addresses.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The fixed packet for a new epoch, with its new initialized
workspace inserted at the addresses used by the machine calls. -/
def EpochLayout.next {w : ℕ} (old : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (base r flow heap names : ℕ) : EpochLayout :=
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
  { old with
    handle := heap+(la+ga)
    names := names
    base := base
    residual := r
    flow := flow
    lengths := heap
    gradient := heap+la
    sourceEnd := heap
    tableEnd := heap+(la+ga) }

/-- The same next epoch's fifteen startup arguments, with the new
consecutive arrays allocated from the fresh coefficient heap. -/
def EpochLayout.startPacket {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance) : List ℕ :=
  [I.m,L.cost,L.residual,L.lower,L.flow,L.upper,L.alpha,L.one,F.limbs,F.fmt.precision,L.exponent,
    Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision L.exponent,
    Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision L.exponent,L.sourceEnd,L.initGraph]

/-- The three constant blocks supply the full startup scan's limits. -/
def EpochLayout.startupPacket {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance) : List ℕ :=
  L.startPacket F I++[L.gradientMin,L.gradientMax,L.lengthMin]

end MinCostFlow.IPM.Machine
