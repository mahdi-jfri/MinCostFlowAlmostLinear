module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.Statement.Problem
import Mathlib.Tactic.IntervalCases

/-!
# Fixed addresses in the finite epoch loop

Algorithm 7 of Chen et al., arXiv:2203.00671v2 (page 69), keeps the base,
capacities, costs and shared numerical parameters fixed within an epoch.
The existing twenty-five-word machine packet also fixes the coefficient
table addresses and changes only its heap word. Record those addresses
as data, with no correctness, stability or progress fields. The last two
bounds describe caller-owned regions and are not runtime packet words.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine

/-- The fixed addresses and range exponent of the existing epoch packet.
All numerical values themselves remain in the shared fixed-point layout. -/
structure EpochLayout where
  handle : ℕ
  names : ℕ
  base : ℕ
  lower : ℕ
  upper : ℕ
  flow : ℕ
  cost : ℕ
  residual : ℕ
  alpha : ℕ
  one : ℕ
  slackMin : ℕ
  slackMax : ℕ
  exponent : ℕ
  lengths : ℕ
  gradient : ℕ
  /-- The five-word circulation rows read by the batch writer. -/
  graph : ℕ
  /-- The named graph read by data structure initialization. -/
  initGraph : ℕ
  request : ℕ
  gradientMin : ℕ
  gradientMax : ℕ
  lengthMin : ℕ
  sourceEnd : ℕ
  tableEnd : ℕ

/-- Exactly the existing iteration packet, with heap in word eight. -/
def EpochLayout.packet {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance) (heap : ℕ) : List ℕ :=
  [L.handle,L.names,I.m,L.base,L.lower,L.upper,L.flow,F.limbs,heap,L.cost,L.residual,L.alpha,
    L.one,L.slackMin,L.slackMax,F.fmt.precision,L.exponent,L.lengths,L.gradient,I.m,
    L.graph,L.request,L.gradientMin,L.gradientMax,L.lengthMin]

/-- The packet has twenty-five words, independent of the allocation endpoint. -/
theorem EpochLayout.packet_length {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance) (heap : ℕ) :
    (L.packet F I heap).length=25 := rfl

/-- The caller's heap register and the packet heap word agree. -/
theorem EpochLayout.packet_heap {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance) (heap : ℕ) :
    (L.packet F I heap).getD 8 0=heap := rfl

/-- Every other caller argument is unchanged when an iteration advances its heap. -/
theorem EpochLayout.packet_fixed {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (heap next j : ℕ) (hj : j<25) (h8 : j≠8) :
    (L.packet F I heap).getD j 0=(L.packet F I next).getD j 0 := by
  interval_cases j <;> simp_all [EpochLayout.packet]

/-- Word-fit of the fixed packet and a new heap gives the full next
argument list's word-fit, with no further numerical computation. -/
theorem EpochLayout.packet_words {w : ℕ} (L : EpochLayout) (F : MinRatioFormat w) (I : Instance)
    (heap : ℕ) (hfixed : ∀ z∈L.packet F I 0,z<2^w) (hheap : heap<2^w) :
    ∀ z∈L.packet F I heap,z<2^w := by
  intro z hz
  simp only [EpochLayout.packet,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst z
  all_goals first | exact hheap | exact hfixed _ (by simp [EpochLayout.packet])

end MinCostFlow.IPM.Machine
