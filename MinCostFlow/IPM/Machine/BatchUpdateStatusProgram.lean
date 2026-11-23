module

public import MinCostFlow.IPM.Machine.BatchUpdateProgram
public import MinCostFlow.IPM.Machine.BatchUpdateStatusRead
public import MinCostFlow.IPM.Machine.BatchUpdateStatusTail
import MinCostFlow.IPM.Machine.MinRatioUpdateFrame
import WordRAM.Tactic

/-!
# Complete machine proof of the uniform Update result

Execute the two proved preparatory assignments, lift the actual
batch/Update procedure into its call, then execute the status
continuation. The explicit uniform allocation budget covers the final
two words. The exact same concrete credit cancels across that
continuation, so the bound remains linear in the reported set size.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual uniform-result entry meets its full output protocol and
retains the final concrete amortized credit on either Update answer. -/
theorem batchUpdateStatus_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update core record b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (s : A.State) (x : R.τ)
    (source report g l eta heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap],z<2^w)
    (hpre : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem) :
    ∃ o st cost s' final,Runs w p ω (batchUpdateStatusBody core record)
      (startState [b,source,report,g,l,eta,F.limbs,heap] mem pos) o st cost ∧
      (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∃ batchEnd batchMem,
        (detectBatchContract w I S).post [source,report,heap] mem batchEnd batchMem ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
          0 s [b,heap,g,l,eta,batchEnd] batchMem s' st.mem) ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤180*S.card+rate I.m*(1+2*S.card)+R.phi b x mem+600 := by
  obtain ⟨hCorePre,hspace⟩ := hpre
  change heap+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w at hspace
  have hcount := batchUpdate_report_count F A I κ α rate allocation R hCorePre
  have hheapWord : heap<2^w := by omega
  have hanswerWord : heap+(1+6*S.card)<2^w := by omega
  have hSix : 6<2^w := by
    have hd := F.divide_fits
    have hp := F.fmt.limbBits_pos
    have hw5 : 5≤w := by omega
    exact lt_of_lt_of_le (by decide : 6<2^5) (Nat.pow_le_pow_right (by decide) hw5)
  obtain ⟨oC,stC,cC,s',final,hrC,hCorePost,hrep,htransition,hmeta,hcost⟩ :=
    batchUpdate_runs_with_potential_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate
      s x source report g l eta heap mem pos ω hwords hCorePre
  have hend := batchUpdate_end_le F A I κ α rate allocation R hCorePost
  have halloc := update_allocation_le_bound (b:=b) (g:=g) (l:=l) (eta:=eta) allocation hheapWord hanswerWord
  have hfinalSpace : oC.value+2<2^w := by omega
  have hbefore : heap+(1+6*S.card)<oC.value := by omega
  have hbit := batchUpdate_answer_bit F A I κ α rate allocation R hCorePost
  let start := startState [b,source,report,g,l,eta,F.limbs,heap] mem pos
  let afterRead : State := ⟨mem,Function.update (Function.update start.regs 8 S.card) 9 (heap+(1+6*S.card)),pos⟩
  let afterCore : State := ⟨stC.mem,Function.update afterRead.regs 10 oC.value,stC.pos⟩
  have hread : Runs w p ω batchUpdateStatusRead start .normal afterRead 12 :=
    batchUpdateStatusRead_runs start ω (by simp [start,startState]) (by simp [start,startState]) hcount hSix hanswerWord
  have hcall : Runs w p ω
      (.call 10 core [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7]) afterRead .normal afterCore (8+cC+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,source,report,g,l,eta,F.limbs,heap],batchUpdateBody batch update,oC,stC,cC,
      by dsimp only [afterRead,start]; eval_expr,hcore,hrC,rfl,?_,rfl⟩
    cases stC
    rfl
  obtain ⟨o,st,cTail,hrTail,⟨hRecord,hrep',hphi,hfoot'⟩,hTailCost⟩ :=
    batchUpdateStatusTail_runs R himpl.1 hrecord afterCore ω
      (by simp [afterCore,afterRead]) (by simp [afterCore]) hbit hbefore hfinalSpace hend.2.2 hrep
      (fun z hz => (hmeta z hz).1)
  have hmeta' : ∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z) :=
    fun z hz => ⟨hfoot' z hz,(hmeta z hz).2⟩
  obtain ⟨batchEnd,batchMem,hBatch,hTransition⟩ := htransition
  have hframe : ∀ z<oC.value,st.mem z=stC.mem z := hRecord.1.2.2.1
  have hTransition' : (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
      0 s [b,heap,g,l,eta,batchEnd] batchMem s' st.mem :=  minRatioMachine_update_post_frozen F A (namedInstance I) I.m κ α rate allocation
    hTransition hframe (by
      have hv := hBatch.2
      change batchEnd=heap+(1+6*S.card) at hv
      omega)
  refine ⟨o,st,cC+cTail+23,s',final,?_,⟨oC.value,stC.mem,hCorePost,hRecord⟩,hrep',⟨batchEnd,batchMem,hBatch,hTransition'⟩,hmeta',?_⟩
  · unfold batchUpdateStatusBody
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterRead,12,(8+cC+1)+cTail+1,hread,?_,by omega⟩
    exact runs_seq_iff.mpr (Or.inr ⟨afterCore,8+cC+1,cTail,hcall,hrTail,rfl⟩)
  · rw [← hphi]
    dsimp only [afterCore]
    omega

theorem batchUpdateStatus_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update core record b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (s : A.State) (x : R.τ)
    (source report g l eta heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap],z<2^w)
    (hpre : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem) :
    ∃ o st cost s' final,Runs w p ω (batchUpdateStatusBody core record)
      (startState [b,source,report,g,l,eta,F.limbs,heap] mem pos) o st cost ∧
      (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∃ batchEnd batchMem,
        (detectBatchContract w I S).post [source,report,heap] mem batchEnd batchMem ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
          0 s [b,heap,g,l,eta,batchEnd] batchMem s' st.mem) ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤180*S.card+rate I.m*(1+2*S.card)+R.phi b x mem+600 :=
  batchUpdateStatus_runs_with_potential_at F A I κ α rate allocation R himpl S hbatchBody hbatch
    hupdate hcore hrecord s x source report g l eta heap mem pos ω hwords hpre

/-- The complete linked uniform Update entry has its explicit local
contract, for every tape and either model answer. -/
theorem batchUpdateStatus_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update core record entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (S : Finset ℕ) (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hp : p.procs[entry]?=some (batchUpdateStatusBody core record)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (batchUpdateStatusContract F A I κ α rate allocation R b s x S) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨source,report,g,l,eta,heap,rfl,_⟩ := hpre.1
  obtain ⟨o,st,cost,_,_,hr,hpost,_,_,_,hc⟩ := batchUpdateStatus_runs_with_potential_at F A I κ α rate allocation R
    himpl S hbatchBody hbatch hupdate hcore hrecord s x source report g l eta heap mem pos ω hwords hpreCopy
  exact ⟨o,st,cost,hr,hpost,(Nat.le_add_right cost _).trans hc⟩

theorem batchUpdateStatus_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update core record entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ) (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hp : p.procs[entry]?=some (batchUpdateStatusBody core record)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (batchUpdateStatusContract F A I κ α rate allocation R b s x S) :=
  batchUpdateStatus_meetsContract_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate
    hcore hrecord hp s x

end MinCostFlow.IPM.Machine
