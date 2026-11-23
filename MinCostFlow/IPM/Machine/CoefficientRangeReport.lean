module

public import MinCostFlow.IPM.Machine.CoefficientRangeList
public import MinCostFlow.IPM.Machine.ReportStatus
import WordRAM.Tactic

/-!
# Returning the stable report with its coefficient-check status

After a successful cache refresh, read the stable report's count and
check exactly its coefficient pairs. Append the same report pointer
and the new bit. The caller can use the uniform last-word status to
stop before batch preparation or Update. The only allocation is this
two-word record, and all earlier memory remains unchanged.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[report,gradientTable,lengthTable,negativeMaximum,maximum,
minimum,L,heap]`. The returned record contains the report pointer and bit. -/
def coefficientRangeReportBody (range record : ℕ) : Stmt :=
  .assign 8 (.load (.reg 0)) ;;
  .call 9 range [.bin .add (.reg 0) (.const 1),.reg 8,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6] ;;
  .call 10 record [.reg 0,.reg 9,.reg 7] ;;
  .ret (.reg 10)

/-- The actual scan result and fresh pointer/status record. Range checks
need valid represented inputs, without assuming their acceptance. -/
def coefficientRangeReportContract (w h : ℕ) (S : Finset ℕ) : Contract where
  pre args mem := ∃ report g l neg mx mn L heap,
    args=[report,g,l,neg,mx,mn,L,heap] ∧ DetectAt mem report S ∧
    report+1+S.card≤heap ∧
    (coefficientRangeListContract w h).pre [report+1,S.card,g,l,neg,mx,mn,L] mem ∧
    ZeroFrom mem heap ∧ heap+2<2^w
  post args mem v mem' := ∃ bit,
    (coefficientRangeListContract w h).post
      [args.getD 0 0+1,S.card,args.getD 1 0,args.getD 2 0,args.getD 3 0,args.getD 4 0,args.getD 5 0,args.getD 6 0]
      mem bit mem ∧
    (reportStatusContract w).post [args.getD 0 0,bit,args.getD 7 0] mem v mem'
  cost args _ := S.card*(164*args.getD 6 0+500)+200

/-- The count read, range scan and status record use no randomness. -/
theorem coefficientRangeReportBody_noRand (range record : ℕ) :
    (coefficientRangeReportBody range record).NoRand := by
  simp [coefficientRangeReportBody,Stmt.NoRand]

/-- Every input satisfying the full reported range-scan precondition has
an actual checked-record run, including rejection, with linear cost. -/
theorem coefficientRangeReport_meetsContract {w h entry range record : ℕ} {p : Program}
    (hrange : MeetsContract w p range (coefficientRangeListContract w h))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hp : p.procs[entry]?=some (coefficientRangeReportBody range record)) (S : Finset ℕ) :
    MeetsContract w p entry (coefficientRangeReportContract w h S) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨report,g,l,neg,mx,mn,L,heap,rfl,hreport,hend,hinput,hzero,hspace⟩ := hpre
  have hcount := hreport.count
  have hrWord := hwords report (by simp)
  have hgWord := hwords g (by simp)
  have hlWord := hwords l (by simp)
  have hnWord := hwords neg (by simp)
  have hxWord := hwords mx (by simp)
  have hmWord := hwords mn (by simp)
  have hLWord := hwords L (by simp)
  have hhWord := hwords heap (by simp)
  have hcWord : S.card<2^w := by omega
  have hnamesWord : report+1<2^w := by omega
  apply runs_start_le
  unfold coefficientRangeReportBody
  wram_step
  refine runs_seq_call_le hrange (vs:=[report+1,S.card,g,l,neg,mx,mn,L])
    (by eval_expr) (by wram_words) hinput ?_
  intro bit mem0 pos0 hscan
  have hsame := hscan.1
  change mem0=mem at hsame
  subst mem0
  have hbit := hscan.2.1
  have hbitWord : bit<2^w := by omega
  refine runs_seq_call_le hrecord (vs:=[report,bit,heap]) (by eval_expr) (by wram_words)
    ⟨⟨report,bit,heap,rfl,hbit⟩,hzero,hspace⟩ ?_
  intro v mem' pos' hout
  have hv := hout.2
  change v=heap+2 at hv
  have hvWord : v<2^w := by omega
  refine runs_ret_le (v:=v) (by eval_expr) ⟨bit,hscan,hout⟩ ?_
  simp only [coefficientRangeReportContract,coefficientRangeListContract,reportStatusContract,boundedStatusRecordContract,
    heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_load,
    Expr.size_bin,Expr.size_const,argsSize_cons,argsSize_nil]
  omega

/-- Only the final fresh record changes memory. Thus the exact concrete
DS state and credit survive the complete coefficient-check entry. -/
theorem coefficientRangeReport_preserves_state {σ : Type} (R : DSRep σ) (hlocal : R.Local)
    {w h report g l neg mx mn L heap v b : ℕ} {S : Finset ℕ}
    {s : σ} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (coefficientRangeReportContract w h S).post
      [report,g,l,neg,mx,mn,L,heap] mem v mem')
    (hrep : R.rep b s x mem) (hfoot : ∀ z,R.foot b x z → z<heap) :
    R.rep b s x mem' ∧ R.phi b x mem=R.phi b x mem' ∧
      (∀ z,R.foot b x z → z<v) := by
  obtain ⟨bit,_,hr⟩ := hout
  have hs := reportStatus_preserves_state R hlocal hr hrep hfoot
  have hv := hr.2
  change v=heap+2 at hv
  refine ⟨hs.1,hs.2,?_⟩
  intro z hz
  have := hfoot z hz
  omega

end MinCostFlow.IPM.Machine
