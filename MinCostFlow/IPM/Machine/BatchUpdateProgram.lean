module

public import MinCostFlow.IPM.Machine.BatchUpdate
import WordRAM.Tactic

/-!
# Running batch preparation followed by the actual Update

Lift the verified batch writer into the first call. Its prefix frame
supplies the checked tables and normalization to the derived Update
input. Call the parameter's actual Update through its reserved-answer
wrapper, and return immediately. The same concrete intermediate credit
cancels, leaving linear reported-size work plus the Update charge.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual batch/Update entry meets its full relational output and
retains the final concrete amortized credit on both Update outcomes. -/
theorem batchUpdate_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (s : A.State) (x : R.τ)
    (source report g l eta heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap],z<2^w)
    (hpre : (batchUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem) :
    ∃ o st cost s' final,Runs w p ω (batchUpdateBody batch update)
      (startState [b,source,report,g,l,eta,F.limbs,heap] mem pos) o st cost ∧
      (batchUpdateContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∃ batchEnd batchMem,
        (detectBatchContract w I S).post [source,report,heap] mem batchEnd batchMem ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
          0 s [b,heap,g,l,eta,batchEnd] batchMem s' st.mem) ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤180*S.card+rate I.m*(1+2*S.card)+R.phi b x mem+500 := by
  obtain ⟨source',report',g',l',eta',heap',heq,hBpre,hrep,hfoot,hfit,hk,hprec,hq,
    hgEnd,hlEnd,heEnd,heValid,heLo,heHi,hvalid,hrange,hspace,hdetected⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hbWord := hwords b (by simp)
  have hsWord := hwords source (by simp)
  have hrWord := hwords report (by simp)
  have hgWord := hwords g (by simp)
  have hlWord := hwords l (by simp)
  have heWord := hwords eta (by simp)
  have hLWord := hwords F.limbs (by simp)
  have hhWord := hwords heap (by simp)
  obtain ⟨oB,stB,cB,hrB,hBpost,hBrep,hBfoot,hBcost⟩ :=
    detectBatch_runs_with_potential R himpl.1 hbatchBody hbatch pos ω (by wram_words) hBpre hrep hfoot
  have hvB := hBpost.2
  change oB.value=heap+(1+6*S.card) at hvB
  have hUspace : oB.value+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space
      0 s [b,heap,g,l,eta,oB.value] stB.mem+(1+2*F.limbs)<2^w := by
    simpa only [minRatioMachineContract,hvB] using hspace
  have hvBWord : oB.value<2^w := by omega
  have hpadding : 1+2*F.limbs<2^w := by omega
  have htwo : 2<2^w := by omega
  have hUpre := minRatioUpdate_pre_after_detectBatch F A I κ α rate allocation R himpl.1 hBpre hBpost
    hrep hfoot hfit hk hprec hq hgEnd hlEnd heEnd heValid heLo heHi hvalid hrange hdetected hUspace
  obtain ⟨oU,stU,cU,s',final,hrU,hUpost,hUrep,hDpost,hUmeta,hUcost⟩ :=
    minRatioUpdate_runs_with_potential R
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre)
      himpl s x heap g l eta (1+2*F.limbs) oB.value stB.mem stB.pos ω (by wram_words) hUpre
  have hDcost : (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre).cost
      0 s [b,heap,g,l,eta,oB.value] stB.mem = rate I.m*(1+2*S.card) :=
    minRatioUpdate_cost_after_detectBatch F A I κ α rate allocation
      (b:=b) (g:=g) (l:=l) (eta:=eta) (s:=s) hBpre hBpost hvBWord
  rw [hDcost] at hUcost
  let start := startState [b,source,report,g,l,eta,F.limbs,heap] mem pos
  let afterB : State := ⟨stB.mem,Function.update start.regs 8 oB.value,stB.pos⟩
  let afterU : State := ⟨stU.mem,Function.update afterB.regs 9 oU.value,stU.pos⟩
  have hcallB : Runs w p ω (.call 8 batch [.reg 1,.reg 2,.reg 7]) start .normal afterB
      (argsSize [.reg 1,.reg 2,.reg 7]+cB+1) := by
    apply runs_call_iff.mpr
    refine ⟨[source,report,heap],detectBatchBody batchWriter,oB,stB,cB,
      by dsimp only [start]; eval_expr,hbatchBody,hrB,rfl,?_,rfl⟩
    cases stB
    rfl
  have hcallU : Runs w p ω
      (.call 9 update [.reg 0,.reg 7,.reg 3,.reg 4,.reg 5,
        .bin .add (.const 1) (.bin .mul (.const 2) (.reg 6)),.reg 8]) afterB .normal afterU
      (argsSize [.reg 0,.reg 7,.reg 3,.reg 4,.reg 5,
        .bin .add (.const 1) (.bin .mul (.const 2) (.reg 6)),.reg 8]+cU+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,heap,g,l,eta,1+2*F.limbs,oB.value],minRatioUpdateBody (op 0),oU,stU,cU,
      by dsimp only [afterB,start]; eval_expr,hupdate,hrU,rfl,?_,rfl⟩
    cases stU
    rfl
  have hvUWord : oU.value<2^w := by
    obtain ⟨updateEnd,_,_,hv,_,hhi,_⟩ := hUpost
    change oU.value=updateEnd+(1+2*F.limbs) at hv
    change updateEnd≤oB.value+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space
      0 s [b,heap,g,l,eta,oB.value] stB.mem at hhi
    omega
  have hret : Runs w p ω (.ret (.reg 9)) afterU (.returned oU.value) afterU 2 := by
    exact runs_ret_iff.mpr ⟨oU.value,by dsimp only [afterU]; eval_expr,rfl,rfl,rfl⟩
  have hmeta : ∀ z,R.foot b final z → z<oU.value ∧ (R.foot b x z ∨ heap≤z) := by
    intro z hz
    refine ⟨(hUmeta z hz).1,?_⟩
    rcases (hUmeta z hz).2 with hold | hfresh
    · exact Or.inl hold
    · exact Or.inr (by omega)
  refine ⟨.returned oU.value,afterU,cB+cU+20,s',final,?_,?_,hUrep,⟨oB.value,stB.mem,hBpost,hDpost⟩,hmeta,?_⟩
  · unfold batchUpdateBody
    rw [runs_seq_iff]
    refine Or.inr ⟨afterB,_,
      argsSize [.reg 0,.reg 7,.reg 3,.reg 4,.reg 5,
        .bin .add (.const 1) (.bin .mul (.const 2) (.reg 6)),.reg 8]+cU+1+2+1,hcallB,?_,?_⟩
    · rw [runs_seq_iff]
      exact Or.inr ⟨afterU,_,2,hcallU,hret,rfl⟩
    · simp only [argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,Expr.size_const]
      omega
  · exact ⟨oB.value,stB.mem,s',final,hBpost,hUpost,hUrep,hDpost,hmeta⟩
  · dsimp only [afterU]
    omega

theorem batchUpdate_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (s : A.State) (x : R.τ)
    (source report g l eta heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,source,report,g,l,eta,F.limbs,heap],z<2^w)
    (hpre : (batchUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem) :
    ∃ o st cost s' final,Runs w p ω (batchUpdateBody batch update)
      (startState [b,source,report,g,l,eta,F.limbs,heap] mem pos) o st cost ∧
      (batchUpdateContract F A I κ α rate allocation R b s x S).post
        [b,source,report,g,l,eta,F.limbs,heap] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∃ batchEnd batchMem,
        (detectBatchContract w I S).post [source,report,heap] mem batchEnd batchMem ∧
        (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
          0 s [b,heap,g,l,eta,batchEnd] batchMem s' st.mem) ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤180*S.card+rate I.m*(1+2*S.card)+R.phi b x mem+500 :=
  batchUpdate_runs_with_potential_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate
    s x source report g l eta heap mem pos ω hwords hpre

/-- The complete linked batch/Update entry meets its explicit local
contract for every random tape, with all operation costs counted. -/
theorem batchUpdate_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init batch batchWriter update entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hp : p.procs[entry]?=some (batchUpdateBody batch update)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (batchUpdateContract F A I κ α rate allocation R b s x S) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨source,report,g,l,eta,heap,rfl,_⟩ := hpre
  obtain ⟨o,st,cost,_,_,hr,hpost,_,_,_,hc⟩ := batchUpdate_runs_with_potential_at F A I κ α rate allocation R
    himpl S hbatchBody hbatch hupdate s x source report g l eta heap mem pos ω hwords hpreCopy
  exact ⟨o,st,cost,hr,hpost,(Nat.le_add_right cost _).trans hc⟩

theorem batchUpdate_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init batch batchWriter update entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (S : Finset ℕ)
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I S))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (op 0)))
    (hp : p.procs[entry]?=some (batchUpdateBody batch update)) (s : A.State) (x : R.τ) :
    MeetsContract w p entry (batchUpdateContract F A I κ α rate allocation R b s x S) :=
  batchUpdate_meetsContract_at F A I κ α rate allocation R himpl S hbatchBody hbatch hupdate hp s x

end MinCostFlow.IPM.Machine
