module

public import MinCostFlow.IPM.Machine.DetectRefreshDetectInput

/-!
# Composing Detect, refresh and the final report/status record

The actual call postconditions describe the stable report and checked
refresh. A fresh pointer/status record preserves the same final concrete
DS state and credit. Compose footprint growth and the three allocation
bounds to obtain the complete combined-stage output condition.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The final actual report/status write completes the combined-stage
postcondition and preserves the concrete state used in its credit bound. -/
theorem detectRefresh_post_record {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd dHeap rHeap v : ℕ}
    {s : A.State} {x detected refreshed : R.τ} {mem dMem rMem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hdetect : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem dHeap dMem)
    (hDrep : R.rep b (A.detect s).2 detected dMem)
    (hDmeta : ∀ z,R.foot b detected z → z<dHeap ∧ (R.foot b x z ∨ heap≤z))
    (hDbefore : ∀ z,R.foot b detected z → z<dMem (dHeap-1))
    (hrefresh : (reportedEdgesContract F A G m rate allocation R b (A.detect s).2 detected q K sourceEnd tableEnd).post
      [b,dMem (dHeap-1)+1,(A.detect s).1.card,base,lo,up,f,F.limbs,dHeap,c,r,a,one,mn,mx,
        F.fmt.precision,E,ld,gd,m] dMem rHeap rMem)
    (hRrep : R.rep b (A.detect s).2 refreshed rMem)
    (hRmeta : ∀ z,R.foot b refreshed z → z<rHeap ∧ (R.foot b detected z ∨ dHeap≤z))
    (hrecord : (reportStatusContract w).post [dMem (dHeap-1),rMem (rHeap-1),rHeap] rMem v mem') :
    (detectRefreshContract F A G m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem' ∧
    R.rep b (A.detect s).2 refreshed mem' ∧ R.phi b refreshed rMem=R.phi b refreshed mem' := by
  have hstate := reportStatus_preserves_state R hlocal hrecord hRrep (fun z hz => (hRmeta z hz).1)
  have hcard := (detectRefresh_detect_pre F A G m κ α rate allocation R hpre).2
  have hDcopy := hdetect
  have hRcopy := hrefresh
  obtain ⟨reserved,detectMem,snapshotEnd,snapshotMem,other,hDD,hDS,hvD,hPD,hFD,hZD,hRD,hMD,hND,hNPD,hLoD,hHiD,_⟩ := hdetect
  change heap≤dHeap at hLoD
  change dHeap≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+2*(m+1)+1 at hHiD
  simp only [reportedEdgesContract,List.getD_cons_zero,List.getD_cons_succ] at hrefresh
  obtain ⟨_,_,_,hLoR,hHiR,_⟩ := hrefresh
  have hv := hrecord.2
  change v=rHeap+2 at hv
  have hzero := hrecord.1.2.2.2.1
  change ZeroFrom mem' v at hzero
  have hmul := Nat.mul_le_mul_right (reportedEdgesScratch F m b E allocation) hcard
  refine ⟨?_,hstate.1,hstate.2⟩
  refine ⟨dHeap,dMem,detected,rHeap,rMem,refreshed,hDcopy,hDrep,hDmeta,hDbefore,hRcopy,hrecord,
    hstate.1,?_,hzero,?_,?_⟩
  · intro z hz
    refine ⟨by have hh := (hRmeta z hz).1; omega,?_⟩
    rcases (hRmeta z hz).2 with hold | hfresh
    · exact (hDmeta z hold).2
    · exact Or.inr (hLoD.trans hfresh)
  · change heap≤v
    omega
  · change v≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+
      2*(m+1)+m*reportedEdgesScratch F m b E allocation+4
    omega

end MinCostFlow.IPM.Machine
