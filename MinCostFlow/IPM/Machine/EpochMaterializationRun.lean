module

public import MinCostFlow.IPM.Machine.EpochMaterializationInput
public import MinCostFlow.IPM.Machine.EpochMaterializationOutput
public import MinCostFlow.IPM.Machine.ReportedEdgesProgram

/-!
# The actual full-coordinate pass after a completed epoch

Run the existing reported-edge entry on all edge names after the
loop's success flag. The pass reuses the numerical source blocks and
the same min-ratio credit. Its cost is one Query and one refresh charge
per edge, plus constant control overhead.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- After the loop's success flag, the actual linked full pass preserves
the credited state and its complete numerical postcondition. -/
theorem epochMaterialization_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K i heap : ℕ) (Q : EpochPoint R.τ) (mem : ℕ → ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ} {p : Program}
    {init store query coefficient flag edge : ℕ} {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hQ : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i Q)
    (hrecord : (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem heap mem)
    (hrep : R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)) Q.credit mem)
    (hwords : ∀ z∈L.packet F I heap,z<2^w)
    (pos : ℕ) (ω : ℕ → Bool) :
    let args := (L.packet F I heap).take 20
    let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)
    let C := reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s Q.credit
      q K L.sourceEnd L.tableEnd
    ∃ o st cost credit,
      Runs w p ω (reportedEdgesBody edge flag) (startState args mem pos) o st cost ∧
      C.pre args mem ∧ (∀ e∈(namedInstance I).E,∃ j<I.m,mem (L.names+j)=e) ∧
      C.post args mem o.value st.mem ∧ R.rep L.handle s credit st.mem ∧
      (∀ z,R.foot L.handle credit z → z<o.value ∧ (R.foot L.handle Q.credit z ∨ heap≤z)) ∧
      cost+R.phi L.handle credit st.mem≤I.m*reportedEdgesCharge F I.m L.exponent rate+R.phi L.handle Q.credit mem+100 := by
  dsimp only
  obtain ⟨hpre,hcover⟩ := epoch_materialization_input F A I κ α rate allocation R L q K i heap Q mem
    hQ hrecord hrep
  have hArgs : ∀ z∈(L.packet F I heap).take 20,z<2^w :=
    fun z hz => hwords z (List.mem_of_mem_take hz)
  obtain ⟨o,st,cost,credit,hr,hout,hrep',hfoot,hcost⟩ :=
    reportedEdges_runs_with_potential_at F A (namedInstance I) I.m κ α rate allocation R
      himpl hstore hquery hcoefficient hflag hedge
      (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)) Q.credit L.names I.m L.base
      L.lower L.upper L.flow heap L.cost L.residual L.alpha L.one L.slackMin L.slackMax L.exponent
      L.lengths L.gradient mem pos ω hArgs hpre
  exact ⟨o,st,cost,credit,hr,hpre,hcover,hout,hrep',hfoot,hcost⟩

theorem epochMaterialization_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K i heap : ℕ) (Q : EpochPoint R.τ) (mem : ℕ → ℕ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ} {p : Program}
    {init store query coefficient flag edge : ℕ} {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hQ : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap space finish i Q)
    (hrecord : (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem heap mem)
    (hrep : R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)) Q.credit mem)
    (hwords : ∀ z∈L.packet F I heap,z<2^w)
    (pos : ℕ) (ω : ℕ → Bool) :
    let args := (L.packet F I heap).take 20
    let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*i)
    let C := reportedEdgesContract F A (namedInstance I) I.m rate allocation R L.handle s Q.credit
      q K L.sourceEnd L.tableEnd
    ∃ o st cost credit,
      Runs w p ω (reportedEdgesBody edge flag) (startState args mem pos) o st cost ∧
      C.pre args mem ∧ (∀ e∈(namedInstance I).E,∃ j<I.m,mem (L.names+j)=e) ∧
      C.post args mem o.value st.mem ∧ R.rep L.handle s credit st.mem ∧
      (∀ z,R.foot L.handle credit z → z<o.value ∧ (R.foot L.handle Q.credit z ∨ heap≤z)) ∧
      cost+R.phi L.handle credit st.mem≤I.m*reportedEdgesCharge F I.m L.exponent rate+R.phi L.handle Q.credit mem+100 :=
  epochMaterialization_runs_with_potential_at F A I κ α rate allocation R L q K i heap Q mem
    himpl hstore hquery hcoefficient hflag hedge hQ hrecord hrep hwords pos ω

end MinCostFlow.IPM.Machine
