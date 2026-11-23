module

public import MinCostFlow.IPM.Machine.MinRatioDetectProgram
public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.Machine.DetectSnapshot

/-!
# Detect followed by a stable caller-owned name list

Definition 4.5 (page 14) supplies Detect's reported set. Reserve the full
answer, snapshot its header and actual name order, then append the
snapshot's address in one metadata word. The target-test driver reads
this pointer at the returned endpoint minus one. The copied header and
names avoid the DS footprint even if the original answer did not.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Copy the reserved Detect answer and record its fresh snapshot address.
Register 3 contains the returned reserved endpoint. -/
def detectNamesTail (snapshot : ℕ) : Stmt :=
  .call 4 snapshot [.reg 2,.reg 3] ;;
  .store (.reg 4) (.reg 3) ;;
  .ret (.bin .add (.reg 4) (.const 1))

/-- Arguments `[handle,m,heap]`. Output's last word is the snapshot pointer;
that snapshot contains `[count,names...]` in Detect's actual order. -/
def detectNamesBody (detect snapshot : ℕ) : Stmt :=
  .call 3 detect [.reg 0,.bin .add (.reg 1) (.const 1),.reg 2] ;;
  detectNamesTail snapshot

/-- Detect, the snapshot call and pointer record contain no randomness. -/
theorem detectNamesBody_noRand (detect snapshot : ℕ) : (detectNamesBody detect snapshot).NoRand := by
  simp [detectNamesBody,detectNamesTail,Stmt.NoRand]

/-- Complete Detect/name-snapshot interface. The answer-cardinality input
condition is derived from Definition 4.5 on valid fixed-graph histories
by `minRatioDetect_card_le`; it is not an extra DS specification. -/
def detectNamesContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) : Contract :=
  let D := minRatioMachineContract F A G m κ α rate allocation
  let S := (A.detect s).1
  { pre := fun args mem => ∃ heap,args=[b,m,heap] ∧
      (minRatioDetectContract w R D b s x).pre [b,m+1,heap] mem ∧ S.card≤m ∧
      heap+D.space 2 s [b,heap] mem+2*(m+1)+1<2^w
    post := fun args mem v mem' => ∃ reserved detectMem snapshotEnd snapshotMem x',
      (minRatioDetectContract w R D b s x).post [b,m+1,heapArg args] mem reserved detectMem ∧
      (detectSnapshotContract w S).post [heapArg args,reserved] detectMem snapshotEnd snapshotMem ∧
      v=snapshotEnd+1 ∧ mem' (v-1)=reserved ∧
      (∀ z<snapshotEnd,mem' z=snapshotMem z) ∧ ZeroFrom mem' v ∧
      R.rep b (A.detect s).2 x' mem' ∧
      (∀ z,R.foot b x' z → z<v ∧ (R.foot b x z ∨ heapArg args≤z)) ∧
      (∀ i<1+S.card,¬ R.foot b x' (reserved+i)) ∧ ¬ R.foot b x' (v-1) ∧
      heapArg args≤v ∧ v≤heapArg args+D.space 2 s [b,heapArg args] mem+2*(m+1)+1 ∧
      (∀ z<heapArg args,¬ R.foot b x z → mem' z=mem z)
    cost := fun args mem => D.cost 2 s [b,heapArg args] mem+R.phi b x mem+17*S.card+200 }

end MinCostFlow.IPM.Machine
