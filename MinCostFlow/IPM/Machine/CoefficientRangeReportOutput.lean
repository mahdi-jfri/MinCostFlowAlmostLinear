module

public import MinCostFlow.IPM.Machine.CoefficientRangeReport

/-!
# The checked coefficient report leaves all caller data intact

The range scan reads memory and the result record is fresh. Hence its
original report, numeric tables and normalization survive, while the
last word gives the actual scan bit. This frame connects the range
checks to batch preparation and Update without another coefficient scan.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the final checked-report result and retain the exact scan
postcondition, original Detect set and complete caller-prefix frame. -/
theorem coefficientRangeReport_output {w h report g l neg mx mn L heap v : ℕ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (coefficientRangeReportContract w h S).pre [report,g,l,neg,mx,mn,L,heap] mem)
    (hout : (coefficientRangeReportContract w h S).post [report,g,l,neg,mx,mn,L,heap] mem v mem') :
    mem' (v-2)=report ∧ mem' (v-1)≤1 ∧ DetectAt mem' report S ∧
      (coefficientRangeListContract w h).post [report+1,S.card,g,l,neg,mx,mn,L] mem (mem' (v-1)) mem ∧
      v=heap+2 ∧ ZeroFrom mem' v ∧ (∀ z<heap,mem' z=mem z) := by
  obtain ⟨report',g',l',neg',mx',mn',L',heap',heq,hDetect,hEnd,_⟩ := hpre
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨bit,hscan,hrecord⟩ := hout
  change (coefficientRangeListContract w h).post [report+1,S.card,g,l,neg,mx,mn,L] mem bit mem at hscan
  change (reportStatusContract w).post [report,bit,heap] mem v mem' at hrecord
  have hd := reportStatus_output hrecord
  have hv := hrecord.2
  change v=heap+2 at hv
  have hf := hrecord.1.2.2.1
  change ∀ z<heap,mem' z=mem z at hf
  have hbit : mem' (v-1)≤1 := by rw [hd.2]; exact hscan.2.1
  refine ⟨hd.1,hbit,?_,?_,hv,hrecord.1.2.2.2.1,hf⟩
  · obtain ⟨es,hnd,hset,hheader,hnames⟩ := hDetect
    have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
    refine ⟨es,hnd,hset,(hf report (by omega)).trans hheader,?_⟩
    intro i hi
    exact (hf (report+1+i) (by omega)).trans (hnames i hi)
  · rw [hd.2]
    exact hscan

/-- The actual checked-report procedure retains the same concrete DS
credit. Its only writes are the final fresh two-word status record. -/
theorem coefficientRangeReport_runs_with_potential {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w h entry range record report g l neg mx mn L heap b : ℕ} {S : Finset ℕ} {p : Program}
    (hproc : p.procs[entry]?=some (coefficientRangeReportBody range record))
    (hspec : MeetsContract w p entry (coefficientRangeReportContract w h S))
    {s : σ} {x : R.τ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ z∈[report,g,l,neg,mx,mn,L,heap],z<2^w)
    (hpre : (coefficientRangeReportContract w h S).pre [report,g,l,neg,mx,mn,L,heap] mem)
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    ∃ o st cost,Runs w p ω (coefficientRangeReportBody range record)
      (startState [report,g,l,neg,mx,mn,L,heap] mem pos) o st cost ∧
      (coefficientRangeReportContract w h S).post [report,g,l,neg,mx,mn,L,heap] mem o.value st.mem ∧
      R.rep b s x st.mem ∧ (∀ z,R.foot b x z → z<o.value) ∧
      cost+R.phi b x st.mem≤S.card*(164*L+500)+200+R.phi b x mem := by
  obtain ⟨body,hbody,o,st,cost,hr,hout,hcost⟩ := hspec _ _ pos ω hwords hpre
  have heq := Option.some.inj (hbody.symm.trans hproc)
  subst body
  have hs := coefficientRangeReport_preserves_state R hlocal hout hrep hfoot
  refine ⟨o,st,cost,hr,hout,hs.1,hs.2.2,?_⟩
  rw [← hs.2.1]
  change cost≤S.card*(164*L+500)+200 at hcost
  exact Nat.add_le_add_right hcost _

end MinCostFlow.IPM.Machine
