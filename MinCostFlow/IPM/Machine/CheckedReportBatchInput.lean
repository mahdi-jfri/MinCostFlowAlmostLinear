module

public import MinCostFlow.IPM.Machine.CoefficientRangeReportOutput
public import MinCostFlow.IPM.Machine.DetectBatchProgram
import WordRAM.Memory

/-!
# Batch preparation after the coefficient status record

The checked-report entry preserves the source graph and its report
while advancing the heap by two words. Its fresh suffix and prefix
frame therefore transfer the original fixed-graph batch-writer input
to the actual returned heap and pointer.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The checked-report record preserves every source needed by batch
preparation and supplies the new heap's complete input condition. -/
theorem detectBatch_pre_after_coefficientRangeReport {w h source report g l neg mx mn L heap v : ℕ}
    {I : Instance} {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hbatch : (detectBatchContract w I S).pre [source,report,heap] mem)
    (hpre : (coefficientRangeReportContract w h S).pre [report,g,l,neg,mx,mn,L,heap] mem)
    (hout : (coefficientRangeReportContract w h S).post [report,g,l,neg,mx,mn,L,heap] mem v mem')
    (hspace : v+(1+6*S.card)<2^w) :
    (detectBatchContract w I S).pre [source,mem' (v-2),v] mem' := by
  have hd := coefficientRangeReport_output hpre hout
  obtain ⟨⟨source',report',heap',heq,hI,hgraph,_,hsubset,hgEnd,hrEnd,hwords⟩,_,_⟩ := hbatch
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  have hgraph' := hgraph.of_agree_below hgEnd hd.2.2.2.2.2.2
  rw [hd.1]
  exact ⟨⟨source,report,v,rfl,hI,hgraph',hd.2.2.1,hsubset,
    by omega,by omega,hwords⟩,hd.2.2.2.2.2.1,hspace⟩

end MinCostFlow.IPM.Machine
