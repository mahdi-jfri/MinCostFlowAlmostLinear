module

public import MinCostFlow.IPM.Machine.DetectBatchProgram
public import WordRAM.DataStructure

/-!
# Keeping the DS state while preparing an Update batch

The batch writer reads the fixed graph and the stable Detect report,
and writes above the incoming heap. Its old-prefix frame preserves the
same concrete DS representation and credit. Thus the linear batch cost
can be added between refresh and Update without losing amortized credit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Preparing the batch preserves a separated DS state and its exact
credit, and every newly written batch word avoids its footprint. -/
theorem detectBatch_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w source report heap v b : ℕ} {I : Instance} {S : Finset ℕ}
    {s : σ} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (detectBatchContract w I S).post [source,report,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' ∧
      (∀ z,R.foot b x z → z<v) ∧
      (∀ i<1+6*S.card,¬ R.foot b x (heap+i)) := by
  have hframe := hout.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hframe
  have hv := hout.2
  change v=heap+(1+6*S.card) at hv
  have hh := hlocal b s x mem mem' (fun z hz => (hframe z (hfoot z hz)).symm)
  refine ⟨hh.1 hrep,hh.2,?_,?_⟩
  · intro z hz
    have := hfoot z hz
    omega
  · intro i _ hi
    have := hfoot (heap+i) hi
    omega

/-- The actual batch writer retains the same concrete credit. Its own
cost is linear in the reported set, independently of the graph size. -/
theorem detectBatch_runs_with_potential {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w entry batch source report heap b : ℕ} {I : Instance} {S : Finset ℕ}
    {p : Program} (hproc : p.procs[entry]?=some (detectBatchBody batch))
    (hspec : MeetsContract w p entry (detectBatchContract w I S))
    {s : σ} {x : R.τ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[source,report,heap],z<2^w)
    (hpre : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    ∃ o st cost,Runs w p ω (detectBatchBody batch)
      (startState [source,report,heap] mem pos) o st cost ∧
      (detectBatchContract w I S).post [source,report,heap] mem o.value st.mem ∧
      R.rep b s x st.mem ∧ (∀ z,R.foot b x z → z<o.value) ∧
      cost+R.phi b x st.mem≤180*S.card+400+R.phi b x mem := by
  obtain ⟨body,hbody,o,st,cost,hr,hout,hcost⟩ := hspec _ _ pos ω hwords hpre
  have heq := Option.some.inj (hbody.symm.trans hproc)
  subst body
  have hs := detectBatch_preserves_state R hlocal hout hrep hfoot
  refine ⟨o,st,cost,hr,hout,hs.1,hs.2.2.1,?_⟩
  rw [← hs.2.1]
  change cost≤180*S.card+400 at hcost
  exact Nat.add_le_add_right hcost _

end MinCostFlow.IPM.Machine
