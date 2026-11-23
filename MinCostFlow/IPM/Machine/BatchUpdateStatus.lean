module

public import MinCostFlow.IPM.Machine.BatchUpdateOutput
public import MinCostFlow.IPM.Machine.ReportStatus
public import MinCostFlow.IPM.Machine.UpdateAllocationBound

/-!
# Returning the actual Update answer with a uniform last-word status

Read the report size before applying Update. It identifies the answer
header at the end of the prepared batch. After Update, copy that header's
bit and address into a fresh two-word record. The driver needs only the
last word to stop on failure, while a successful result also identifies
the effective normalization immediately after the saved answer address.
The report itself need not survive the Update call.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Read the count and save the actual Update answer header before the
core call, which may change the report's storage. -/
def batchUpdateStatusRead : Stmt :=
  .assign 8 (.load (.reg 2)) ;;
  .assign 9 (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 6) (.reg 8))))

/-- Copy the actual bit into a fresh uniform result record. -/
def batchUpdateStatusTail (record : ℕ) : Stmt :=
  .assign 11 (.load (.reg 9)) ;;
  .call 12 record [.reg 9,.reg 11,.reg 10] ;;
  .ret (.reg 12)

/-- The eight arguments are those of `batchUpdateBody`. The final record
contains `[answerHeader,successBit]`. Compute its header before Update. -/
def batchUpdateStatusBody (core record : ℕ) : Stmt :=
  batchUpdateStatusRead ;;
  .call 10 core [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7] ;;
  batchUpdateStatusTail record

/-- The final metadata record uses two extra words beyond the uniform
batch/Update bound. The effective scalar remains in its original output. -/
def batchUpdateStatusContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (S : Finset ℕ) : Contract where
  pre args mem := (batchUpdateContract F A I κ α rate allocation R b s x S).pre args mem ∧
    heapArg args+(1+6*S.card)+updateAllocationBound w b (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) allocation+
      (1+2*F.limbs)+2<2^w
  post args mem v mem' := ∃ coreEnd coreMem,
    (batchUpdateContract F A I κ α rate allocation R b s x S).post args mem coreEnd coreMem ∧
    (reportStatusContract w).post
      [heapArg args+(1+6*S.card),coreMem (heapArg args+(1+6*S.card)),coreEnd] coreMem v mem'
  cost _ mem := 180*S.card+rate I.m*(1+2*S.card)+R.phi b x mem+600

/-- Preparing the answer address and copying its actual bit are deterministic. -/
theorem batchUpdateStatusBody_noRand (core record : ℕ) : (batchUpdateStatusBody core record).NoRand := by
  simp [batchUpdateStatusBody,batchUpdateStatusRead,batchUpdateStatusTail,Stmt.NoRand]

/-- The original report count is the exact set size used by the batch
writer. This follows from its stored input, before Update can change it. -/
theorem batchUpdate_report_count {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem : ℕ → ℕ}
    (hpre : (batchUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem) : mem report=S.card := by
  obtain ⟨source',report',g',l',eta',heap',heq,hB,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨⟨source',report',heap',heq,_,_,hd,_⟩,_,_⟩ := hB
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  exact hd.count

end MinCostFlow.IPM.Machine
