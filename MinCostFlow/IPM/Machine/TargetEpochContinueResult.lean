module

public import MinCostFlow.IPM.Machine.TargetEpochResult
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Decoding a target stage after initialization

The caller writes a rejection when startup or the complete epoch fails.
An accepted full read writes status two and the address of the exact
fixed-point flow for the next stage.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the post-startup status record. The checked full read
supplies feasible coordinates and the analytic trace supplies the
conditional progress bound. -/
theorem targetEpoch_continue_result {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U E : ℕ) (κ target : ℝ) (source heap current end_ out bit : ℕ)
    {mem epochMem final : ℕ → ℕ}
    (hframe : ∀ z<heap,epochMem z=mem z) (hend : heap≤end_) (hfit : out<2^w)
    (hbit : bit≤1)
    (hnonterminal : 1/4<residual I target (epochVector F I mem source))
    (hNo : bit=0 → ¬TargetStagePromise I U target (epochVector F I mem source))
    (hYes : bit=1 → TargetStageFlow F I E current end_ epochMem ∧
      (TargetStagePromise I U target (epochVector F I mem source) →
        potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I epochMem current)≤
          potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem source)-
            (I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000))
    (hrecord : (boundedStatusRecordContract w 2).post
      [current,2*bit,end_] epochMem out final) :
    TargetStageResult F I U E κ target source heap out mem final := by
  have hwrite := hrecord.1.2.2.1
  change ∀ z<end_,final z=epochMem z at hwrite
  have hzero := hrecord.1.2.2.2.1
  have hout : out=end_+2 := hrecord.2
  obtain ⟨hptr,hstatus⟩ := hrecord.1.2.2.2.2
  change final end_=current at hptr
  change final (end_+1)=2*bit at hstatus
  have hprefix : ∀ z<heap,final z=mem z :=
    fun z hz => (hwrite z (hz.trans_le hend)).trans (hframe z hz)
  have hout' : out-1=end_+1 := by omega
  have hptr' : out-2=end_ := by omega
  unfold TargetStageResult
  rw [hout',hptr',hptr,hstatus]
  refine ⟨by omega,hfit,hzero,hprefix,by omega,?_,by omega,?_⟩
  · exact fun hb => ⟨hnonterminal,hNo (by omega)⟩
  · intro hb
    have hOne : bit=1 := by omega
    obtain ⟨hflow,hprogress⟩ := hYes hOne
    have hf : epochVector F I final current=epochVector F I epochMem current := by
      funext e
      exact Num.IPM.fixVal_frozen hwrite ((reported_entry_end current F.limbs e.val I.m e.isLt).trans hflow.1)
    exact ⟨hflow.frozen hwrite (by omega),hnonterminal,by rw [hf]; exact hprogress⟩

end MinCostFlow.IPM.Machine
