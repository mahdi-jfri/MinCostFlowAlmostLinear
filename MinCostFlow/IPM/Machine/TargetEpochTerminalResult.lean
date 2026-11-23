module

public import MinCostFlow.IPM.Machine.TargetEpochResult
public import MinCostFlow.IPM.Machine.EpochGuardRanges
import MinCostFlow.IPM.Machine.ReportedTableLayout
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Decoding a terminal residual test

A small residual returns the original flow. A residual above the
numerical guard rejects it, which cannot happen under the potential
and upper-target promise.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Both terminal residual outcomes satisfy the target-stage
postcondition using the actual pointer and status record. -/
theorem targetEpoch_terminal_result {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U E : ℕ) (κ target : ℝ) (source heap end_ out : ℕ)
    {mem checked final : ℕ → ℕ}
    (hflow : TargetStageFlow F I E source heap mem)
    (hchecked : ∀ z<heap,checked z=mem z) (hend : heap≤end_)
    (hfit : out<2^w)
    {code : ℕ}
    (hcode : code=0 ∨ code=2)
    (hYes : code=0 → residual I target (epochVector F I mem source)≤1/4)
    (hNo : code=2 → 1/4<residual I target (epochVector F I mem source) ∧
      ¬TargetStagePromise I U target (epochVector F I mem source))
    (hrecord : (boundedStatusRecordContract w 2).post
      [source,if code=0 then 1 else 0,end_] checked out final) :
    TargetStageResult F I U E κ target source heap out mem final := by
  have hwrite := hrecord.1.2.2.1
  have hzero := hrecord.1.2.2.2.1
  have hout : out=end_+2 := hrecord.2
  obtain ⟨hptr,hstatus⟩ := hrecord.1.2.2.2.2
  change final end_=source at hptr
  change final (end_+1)=(if code=0 then 1 else 0) at hstatus
  have hframe : ∀ z<heap,final z=mem z :=
    fun z hz => (hwrite z (hz.trans_le hend)).trans (hchecked z hz)
  have hf : epochVector F I final source=epochVector F I mem source := by
    funext e
    exact Num.IPM.fixVal_frozen hframe ((reported_entry_end source F.limbs e.val I.m e.isLt).trans hflow.1)
  have hout' : out-1=end_+1 := by omega
  have hptr' : out-2=end_ := by omega
  unfold TargetStageResult
  rw [hout',hptr',hptr,hstatus]
  rcases hcode with rfl | rfl
  · refine ⟨by omega,hfit,hzero,hframe,by decide,by simp,?_,by simp⟩
    intro _
    exact ⟨hflow.frozen hframe (by omega),by rw [hf]; exact hYes rfl⟩
  · refine ⟨by omega,hfit,hzero,hframe,by decide,?_,by simp,by simp⟩
    exact fun _ => hNo rfl

/-- The potential and fixed instance bounds imply that a
nonterminal promised residual lies strictly within the machine range. -/
theorem targetEpoch_promised_residual_range {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (U E source heap : ℕ) (target : ℝ) (mem : ℕ → ℕ)
    (hflow : TargetStageFlow F I E source heap mem)
    (hE : E=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hr : 1/4<residual I target (epochVector F I mem source))
    (hp : TargetStagePromise I U target (epochVector F I mem source)) :
    1/(2:ℝ)^E<residual I target (epochVector F I mem source) ∧
      residual I target (epochVector F I mem source)<(2:ℝ)^E := by
  have hf : StrictlyInside I (epochVector F I mem source) := by
    intro e
    have hslack := (hflow.2.2 e).2
    have hpos : 0<1/(2:ℝ)^E := by positivity
    exact ⟨sub_pos.mp (hpos.trans hslack.2.1),sub_pos.mp (hpos.trans hslack.1.1)⟩
  have hroute : I.Routes (epochVector F I mem source) := hflow.2.1.1
  rw [hE]
  exact (epoch_strict_guard_ranges I U target _ hm hU hsize hnums hf hroute hp.2 hFlo
    (by linarith only [hr])).1

/-- The potential and fixed instance bounds imply that a
nonterminal promised residual lies strictly within the machine range. -/
theorem targetEpoch_promised_residual_range_at {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (U E source heap : ℕ) (target : ℝ) (mem : ℕ → ℕ)
    (hflow : TargetStageFlow F I E source heap mem)
    (hE : ipmRangeExponent I.m U≤E)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hr : 1/4<residual I target (epochVector F I mem source))
    (hp : TargetStagePromise I U target (epochVector F I mem source)) :
    1/(2:ℝ)^E<residual I target (epochVector F I mem source) ∧
      residual I target (epochVector F I mem source)<(2:ℝ)^E := by
  have hf : StrictlyInside I (epochVector F I mem source) := by
    intro e
    have hslack := (hflow.2.2 e).2
    have hpos : 0<1/(2:ℝ)^E := by positivity
    exact ⟨sub_pos.mp (hpos.trans hslack.2.1),sub_pos.mp (hpos.trans hslack.1.1)⟩
  have hroute : I.Routes (epochVector F I mem source) := hflow.2.1.1
  apply strict_guard_range_mono hE
  exact (epoch_strict_guard_ranges I U target _ hm hU hsize hnums hf hroute hp.2 hFlo
    (by linarith only [hr])).1

end MinCostFlow.IPM.Machine
