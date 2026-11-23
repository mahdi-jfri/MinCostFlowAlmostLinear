module

public import MinCostFlow.IPM.Machine.EpochLayout
public import MinCostFlow.IPM.Machine.DetectRefresh

/-!
# Conditions at a successful prefix of the finite epoch loop

An epoch point contains the shared history, normalization choices,
operation choices, concrete credit witness and actual machine state.
The top-of-loop condition records the caller registers and remaining
budget together with the valid fixed-graph history and its exact cache.
It asserts the numerical input conditions needed for the next call, and that every
stage of the history so far has its lengths in the range the checked scan accepts.
Running time, hidden stability and progress are proved separately.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Data retained at one actual epoch prefix. The abstract DS state is
computed from the shared history at the current loop stage. -/
structure EpochPoint (τ : Type) where
  history : DynamicInstance
  eta : ℕ → ℝ
  op : ℕ → Bool
  credit : τ
  machine : State

/-- Current input conditions for the actual finite loop. Each completed
iteration appends Detect and Update, so counter `i` corresponds to shared
history stage `2*i`. The packet's sole changing argument is its heap. -/
def EpochConditions {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K : ℕ) (initialMem : ℕ → ℕ)
    (initialHeap space finish i : ℕ) (P : EpochPoint R.τ) : Prop :=
  let heap := P.machine.regs 8
  let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
  i≤finish ∧ P.machine.regs 25=finish ∧ P.machine.regs 26=i ∧
  (∀ j<25,P.machine.regs j=(L.packet F I heap).getD j 0) ∧
  heap ≤ initialHeap+i*space ∧ P.machine.mem (heap-3)≤5*I.m ∧
  (∀ z<L.flow,P.machine.mem z=initialMem z) ∧
  MinRatioHistoryValid P.history P.op (2*i) ∧
  (∀ j≤2*i,P.history.G j=namedInstance I) ∧
  (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s P.credit
    q K L.sourceEnd L.tableEnd).pre ((L.packet F I heap).take 20) P.machine.mem ∧
  readVector P.machine.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m=P.history.g (2*i) ∧
  readVector P.machine.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m=P.history.ℓ (2*i) ∧
  (∀ e<I.m,reportedCachePost F A
    (minRatioState A.eraseFailure P.history P.eta P.op (minRatioLast A.eraseFailure P.history P.eta P.op (2*i) e))
    I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e P.machine.mem) ∧
  (∀ e<I.m,Num.Valid P.machine.mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
    Num.Valid P.machine.mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
    |readVector P.machine.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
    (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector P.machine.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
    readVector P.machine.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) ∧
  HistoryLengthsWithin P.history (2*i) F.rangeExponent

/-- Naming the fixed graph preserves its dimensions throughout an epoch. -/
theorem namedHistory_bounded {D : DynamicInstance} {I : Instance} {T : ℕ}
    (hG : ∀ t ≤ T, D.G t = namedInstance I) :
    MinRatioHistoryBounded D T I.m I.n := by
  constructor
  · intro t ht
    rw [hG t ht, namedInstance_m]
  · intro t ht
    rw [hG t ht]
    exact (Finset.card_range I.n).le

/-- All graphs in an accepted machine epoch prefix fit the dimensions
of the instance on which the machine initialized the data structure. -/
theorem EpochConditions.history_bounded {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ}
    {initialHeap space finish i : ℕ} {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P) :
    MinRatioHistoryBounded P.history (2*i) I.m I.n :=
  namedHistory_bounded h.2.2.2.2.2.2.2.2.1

/-- Every stage of an accepted epoch prefix has its lengths in `[2^{-E}, 2^E]`,
`E = F.rangeExponent`. -/
theorem EpochConditions.history_lengths {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ}
    {initialHeap space finish i : ℕ} {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P) :
    HistoryLengthsWithin P.history (2*i) F.rangeExponent :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- A stage invariant admitted on the instance graph holds at every stage of an accepted
epoch prefix. -/
theorem EpochConditions.stages {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ}
    {initialHeap space finish i : ℕ} {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P)
    {S : MGraph → (ℕ → ℝ) → Prop} (hS : StageAdmits S (namedInstance I) F.rangeExponent) :
    ∀ j≤2*i,S (P.history.G j) (P.history.ℓ j) :=
  hS.history h.2.2.2.2.2.2.2.2.1 h.history_lengths

/-- The current budget is a fitting word whenever the initial five-edge
budget fits. No subtraction in the loop can increase it. -/
theorem EpochConditions.budget_word {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ} {initialHeap space finish i : ℕ}
    {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P)
    (hword : 5*I.m<2^w) : P.machine.mem (P.machine.regs 8-3)<2^w := by
  exact h.2.2.2.2.2.1.trans_lt hword

/-- The finite counter is within its endpoint on every successful prefix. -/
theorem EpochConditions.counter_le {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {L : EpochLayout} {q K : ℕ} {initialMem : ℕ → ℕ} {initialHeap space finish i : ℕ}
    {P : EpochPoint R.τ}
    (h : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i P) : i≤finish := h.1

end MinCostFlow.IPM.Machine
