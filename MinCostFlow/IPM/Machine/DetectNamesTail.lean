module

public import MinCostFlow.IPM.Machine.DetectNamesPointer
import WordRAM.Tactic

/-!
# Executing the stable-name continuation after Detect

Run the verified snapshot on the actual reserved answer, write its
pointer and return the fresh endpoint. The derived input conditions
justify every address and word bound. Both writes preserve the same
concrete DS representation and potential as after Detect.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual snapshot call and pointer record meet the combined output
condition while preserving the concrete post-Detect credit. -/
theorem detectNamesTail_runs {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {p : Program} {snapshot b heap reserved : ℕ} {s : A.State} {x mid : R.τ}
    {mem : ℕ → ℕ}
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (parent : State) (ω : ℕ → Bool)
    (hpre : (detectNamesContract F A G m κ α rate allocation R b s x).pre [b,m,heap] mem)
    (hdetect : (minRatioDetectContract w R
      (minRatioMachineContract F A G m κ α rate allocation) b s x).post
      [b,m+1,heap] mem reserved parent.mem)
    (hrep : R.rep b (A.detect s).2 mid parent.mem)
    (hmeta : ∀ z,R.foot b mid z → z<reserved ∧ (R.foot b x z ∨ heap≤z))
    (hheap : parent.regs 2=heap) (hreserved : parent.regs 3=reserved) :
    ∃ o st cost,Runs w p ω (detectNamesTail snapshot) parent o st cost ∧
      ((detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem o.value st.mem ∧
        R.rep b (A.detect s).2 mid st.mem ∧ R.phi b mid parent.mem=R.phi b mid st.mem ∧
        (∀ z,R.foot b mid z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
        (∀ z,R.foot b mid z → z<st.mem (o.value-1))) ∧
      cost≤17*(A.detect s).1.card+150 := by
  have hpreCopy := hpre
  obtain ⟨hSnapPre,hspace,_⟩ := detectNames_snapshot_pre F A G m κ α rate allocation R hpre hdetect
  obtain ⟨heap',heq,_,_,hbudget⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  subst heap'
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+2*(m+1)+1<2^w at hbudget
  have hheapW : heap<2^w := by omega
  have hrW : reserved<2^w := by omega
  have hw : 1<2^w := by omega
  apply runs_start_le
  unfold detectNamesTail
  refine runs_seq_call_le hsnapshot (vs:=[heap,reserved]) (by eval_expr) (by wram_words) hSnapPre ?_
  intro snapshotEnd snapshotMem snapshotPos hout
  have hend := hout.2
  change snapshotEnd=reserved+(1+(A.detect s).1.card) at hend
  have hEndW : snapshotEnd<2^w := by omega
  have hFinalW : snapshotEnd+1<2^w := by omega
  have hpost := detectNames_post_pointer F A G m κ α rate allocation R hlocal
    hpreCopy hdetect hout hrep hmeta
  wram_step
  simp only [hreserved]
  refine runs_ret_le (v:=snapshotEnd+1) (by eval_expr)
    ⟨hpost.1,hpost.2.1,hpost.2.2,?_,?_⟩ ?_
  · intro z hz
    change z<snapshotEnd+1 ∧ (R.foot b x z ∨ heap≤z)
    exact ⟨by have hh := (hmeta z hz).1; omega,(hmeta z hz).2⟩
  · intro z hz
    change z<Function.update snapshotMem snapshotEnd reserved (snapshotEnd+1-1)
    simpa only [Nat.add_sub_cancel,Function.update_self] using (hmeta z hz).1
  · simp only [detectSnapshotContract,heapContract,Expr.size_reg,Expr.size_const,Expr.size_bin,
      argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
