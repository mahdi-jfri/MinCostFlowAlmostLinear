module

public import MinCostFlow.IPM.Machine.EpochConditions
public import MinCostFlow.IPM.Machine.BudgetedIterationResult
public import MinCostFlow.IPM.Machine.HistoryIteration

/-!
# Actual successful prefixes and stopping calls of an epoch

Each successful call appends its decoded Detect and Update to the shared
history. Its memory becomes the memory of the next point. The final call
may instead return failure. Record its actual result separately so the
analysis can show that this branch is unreachable on a promised target.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- One accepted call retains its concrete result and the rounded
normalization of its history extension. -/
def EpochAcceptedStep {w : ℕ} (F : MinRatioFormat w) (A : MinRatioDataStructureWithFailure)
    (I : Instance) (κ α : ℝ) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (L : EpochLayout) (q K i : ℕ) (P Q : EpochPoint R.τ) : Prop :=
  let heap := P.machine.regs 8
  let v := Q.machine.regs 8
  let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
  let s' := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*(i+1))
  Q.machine.mem (v-1)=1 ∧
  budgetedIterationResult F A I κ α rate allocation R L.handle s s' P.credit q K L.sourceEnd L.tableEnd
    (L.packet F I heap) P.machine.mem v Q.machine.mem ∧
  ∃ es actual cEnd cMem,
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s P.credit
      q K L.sourceEnd L.tableEnd).post ((L.packet F I heap).take 20) P.machine.mem cEnd cMem ∧
    cMem (cEnd-1)=1 ∧
    readVector Q.machine.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m=
      readVector cMem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
    readVector Q.machine.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m=
      readVector cMem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
    es.Nodup ∧ es.toFinset=(A.detect s).1 ∧
    Q.history=appendHistoryIteration P.history (2*i) es
      (readVector Q.machine.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector Q.machine.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
    Q.eta=appendHistoryIterationEta P.eta (2*i) actual ∧ Q.op=appendHistoryIterationOp P.op (2*i) ∧
    NormalizationWithin (Num.fixVal P.machine.mem L.request F.fmt.limbBits F.limbs F.fmt.precision) actual

/-- An indexed sequence of successful calls. Both ends are actual loop
points. The history, heap and cache conditions remain available at every
point in the sequence. -/
inductive EpochAcceptedPrefix {τ : Type} (Inv : ℕ → EpochPoint τ → Prop)
    (Step : ℕ → EpochPoint τ → EpochPoint τ → Prop) :
    ℕ → EpochPoint τ → ℕ → EpochPoint τ → Prop
  | nil {i P} : Inv i P → EpochAcceptedPrefix Inv Step i P i P
  | cons {i P Q j Z} : Inv i P → Step i P Q →
      EpochAcceptedPrefix Inv Step (i+1) Q j Z → EpochAcceptedPrefix Inv Step i P j Z

/-- The starting point of a prefix satisfies its input condition. -/
theorem EpochAcceptedPrefix.start_inv {τ : Type} {Inv : ℕ → EpochPoint τ → Prop}
    {Step : ℕ → EpochPoint τ → EpochPoint τ → Prop}
    {i j : ℕ} {P Q : EpochPoint τ} (h : EpochAcceptedPrefix Inv Step i P j Q) : Inv i P := by
  cases h with
  | nil h => exact h
  | cons h _ _ => exact h

/-- Induct along the realized prefix, using the maintained conditions
at both ends of each actual step. -/
theorem EpochAcceptedPrefix.propagate {τ : Type} {Inv Certified : ℕ → EpochPoint τ → Prop}
    {Step : ℕ → EpochPoint τ → EpochPoint τ → Prop}
    {i j : ℕ} {P Q : EpochPoint τ} (h : EpochAcceptedPrefix Inv Step i P j Q)
    (hstep : ∀ k X Y,Inv k X → Inv (k+1) Y → Step k X Y → Certified k X → Certified (k+1) Y)
    (hstart : Certified i P) : Certified j Q := by
  induction h with
  | nil _ => exact hstart
  | cons hX hXY htail ih => exact ih (hstep _ _ _ hX htail.start_inv hXY hstart)

/-- The endpoint satisfies the maintained loop condition. -/
theorem EpochAcceptedPrefix.end_inv {τ : Type} {Inv : ℕ → EpochPoint τ → Prop}
    {Step : ℕ → EpochPoint τ → EpochPoint τ → Prop}
    {i j : ℕ} {P Q : EpochPoint τ} (h : EpochAcceptedPrefix Inv Step i P j Q) : Inv j Q := by
  induction h with
  | nil h => exact h
  | cons _ _ _ ih => exact ih

/-- The actual stopping call retains the failure bit, report limit,
represented state and its footprint. -/
def EpochStoppedStep {w : ℕ} (F : MinRatioFormat w) (A : MinRatioDataStructureWithFailure)
    (I : Instance) (κ α : ℝ) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (L : EpochLayout) (q K i : ℕ) (P : EpochPoint R.τ)
    (v : ℕ) (st : State) (y : R.τ) : Prop :=
  let heap := P.machine.regs 8
  let s := minRatioState A.eraseFailure P.history P.eta P.op (2*i)
  st.mem (v-1)=0 ∧ v<2^w ∧
  ∃ s', budgetedIterationResult F A I κ α rate allocation R L.handle s s' P.credit q K L.sourceEnd L.tableEnd
      (L.packet F I heap) P.machine.mem v st.mem ∧ R.rep L.handle s' y st.mem ∧
    (∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ heap≤z)) ∧
    (A.detect s).1.card≤I.m

end MinCostFlow.IPM.Machine
