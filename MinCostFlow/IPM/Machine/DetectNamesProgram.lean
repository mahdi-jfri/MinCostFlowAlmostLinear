module

public import MinCostFlow.IPM.Machine.DetectNamesTail
import WordRAM.Tactic

/-!
# Complete machine proof of Detect and stable-name preparation

Call the actual reserved Detect entry and then the verified snapshot
continuation. Detect's abstract state transition is exactly the model's
transition. The same concrete state supplies the final amortized credit,
which is preserved by the snapshot and metadata write. Own work is
linear in the actual report size, even when that report is empty.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The combined actual Detect/snapshot entry meets its full output
condition and retains the final concrete DS credit in its cost bound. -/
theorem detectNames_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init detect snapshot b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hdetect : p.procs[detect]?=some (minRatioDetectBody (op 2)))
    (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,m,heap],z<2^w)
    (hpre : (detectNamesContract F A G m κ α rate allocation R b s x).pre [b,m,heap] mem) :
    ∃ o st cost mid,Runs w p ω (detectNamesBody detect snapshot) (startState [b,m,heap] mem pos) o st cost ∧
      (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem o.value st.mem ∧
      R.rep b (A.detect s).2 mid st.mem ∧
      (∀ z,R.foot b mid z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      (∀ z,R.foot b mid z → z<st.mem (o.value-1)) ∧
      cost+R.phi b mid st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 2 s [b,heap] mem+
        R.phi b x mem+17*(A.detect s).1.card+200 := by
  have hpreCopy := hpre
  obtain ⟨heap',heq,hDpre,_,hbudget⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  subst heap'
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+2*(m+1)+1<2^w at hbudget
  have hm1 : m+1<2^w := by omega
  have hWrappedWords : ∀ z∈[b,m+1,heap],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hz | hz | hz
    all_goals subst z
    · exact hwords _ (by simp)
    · exact hm1
    · exact hwords _ (by simp)
  obtain ⟨oD,stD,cD,sD,mid,hrD,hDpost,hDrep,hDout,hDmeta,hDcost⟩ :=
    minRatioDetect_runs_with_potential R
      (minRatioMachineContractAt F A G m κ α rate allocation initPre)
      himpl s x (m+1) heap mem pos ω hWrappedWords hDpre
  change sD=(A.detect s).2 ∧ DetectAt stD.mem heap (A.detect s).1 ∧
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision sD at hDout
  rw [hDout.1] at hDrep
  let start := startState [b,m,heap] mem pos
  let afterDetect : State := ⟨stD.mem,Function.update start.regs 3 oD.value,stD.pos⟩
  have hcall : Runs w p ω
      (.call 3 detect [.reg 0,.bin .add (.reg 1) (.const 1),.reg 2]) start .normal afterDetect
      (argsSize [.reg 0,.bin .add (.reg 1) (.const 1),.reg 2]+cD+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,m+1,heap],minRatioDetectBody (op 2),oD,stD,cD,
      by dsimp only [start]; eval_expr,hdetect,hrD,rfl,?_,rfl⟩
    cases stD
    rfl
  obtain ⟨o,st,cTail,hrTail,⟨hpost,hrep,hphi,hmeta,hbefore⟩,hcTail⟩ :=
    detectNamesTail_runs F A G m κ α rate allocation R himpl.1 hsnapshot afterDetect ω
      hpreCopy hDpost hDrep hDmeta (by simp [afterDetect,start,startState]) (by simp [afterDetect])
  refine ⟨o,st,(argsSize [.reg 0,.bin .add (.reg 1) (.const 1),.reg 2]+cD+1)+cTail+1,
    mid,?_,hpost,hrep,hmeta,hbefore,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨afterDetect,_,cTail,hcall,hrTail,rfl⟩)
  · rw [← hphi]
    dsimp only [afterDetect]
    have hDcostEq : (minRatioMachineContractAt F A G m κ α rate allocation initPre).cost 2 s [b,heap] mem =
        (minRatioMachineContract F A G m κ α rate allocation).cost 2 s [b,heap] mem := rfl
    rw [hDcostEq] at hDcost
    simp only [argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_bin,Expr.size_const] at hDcost ⊢
    omega

theorem detectNames_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init detect snapshot b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hdetect : p.procs[detect]?=some (minRatioDetectBody (op 2)))
    (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (heap : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[b,m,heap],z<2^w)
    (hpre : (detectNamesContract F A G m κ α rate allocation R b s x).pre [b,m,heap] mem) :
    ∃ o st cost mid,Runs w p ω (detectNamesBody detect snapshot) (startState [b,m,heap] mem pos) o st cost ∧
      (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem o.value st.mem ∧
      R.rep b (A.detect s).2 mid st.mem ∧
      (∀ z,R.foot b mid z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      (∀ z,R.foot b mid z → z<st.mem (o.value-1)) ∧
      cost+R.phi b mid st.mem≤
        (minRatioMachineContract F A G m κ α rate allocation).cost 2 s [b,heap] mem+
        R.phi b x mem+17*(A.detect s).1.card+200 :=
  detectNames_runs_with_potential_at F A G m κ α rate allocation R himpl hdetect s x hsnapshot heap
    mem pos ω hwords hpre

/-- The actual linked Detect/name preparation procedure meets its stated
machine contract. Its snapshot component is the verified caller copy. -/
theorem detectNames_meetsContract_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init detect snapshot entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractAt F A G m κ α rate allocation initPre))
    (hdetect : p.procs[detect]?=some (minRatioDetectBody (op 2)))
    (hp : p.procs[entry]?=some (detectNamesBody detect snapshot)) (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1)) :
    MeetsContract w p entry (detectNamesContract F A G m κ α rate allocation R b s x) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  have hpreCopy := hpre
  obtain ⟨heap,heq,_⟩ := hpre
  subst args
  obtain ⟨o,st,cost,mid,hr,hpost,_,_,_,hc⟩ := detectNames_runs_with_potential_at F A G m κ α rate allocation R
    himpl hdetect s x hsnapshot heap mem pos ω hwords hpreCopy
  refine ⟨o,st,cost,hr,hpost,?_⟩
  change cost≤(minRatioMachineContract F A G m κ α rate allocation).cost 2 s [b,heap] mem+
    R.phi b x mem+17*(A.detect s).1.card+200
  omega

theorem detectNames_meetsContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init detect snapshot entry b : ℕ} {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A G m κ α rate allocation))
    (hdetect : p.procs[detect]?=some (minRatioDetectBody (op 2)))
    (hp : p.procs[entry]?=some (detectNamesBody detect snapshot)) (s : A.State) (x : R.τ)
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1)) :
    MeetsContract w p entry (detectNamesContract F A G m κ α rate allocation R b s x) :=
  detectNames_meetsContract_at F A G m κ α rate allocation R himpl hdetect hp s x hsnapshot

end MinCostFlow.IPM.Machine
