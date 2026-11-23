module

public import MinCostFlow.IPM.Machine.TargetEpochCompleteResult
public import MinCostFlow.IPM.Machine.TargetEpochAfterInit

/-!
# Returning the target stage after a complete epoch

The stage keeps the actual flow returned by the full read. The
two-word record preserves that flow and the caller's old data.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Connect a verified complete epoch to the actual stage return
instruction and its fixed-point result. -/
theorem targetEpoch_complete_tail {w complete record heap source finish cost : ℕ}
    {p : Program} {ω : ℕ → Bool} (before afterEpoch : State)
    {args : List ℕ} {body : Stmt} (hbody : p.procs[complete]?=some body)
    (hargs : evalArgs w before targetEpochCompleteArgs=some args)
    (hrun : Runs w p ω body (startState args before.mem before.pos) (.returned finish) afterEpoch cost)
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (F : MinRatioFormat w) (I : Instance) (U E flow : ℕ) (κ target : ℝ) (mem : ℕ → ℕ)
    (hflow : before.regs 23=flow) (hinit : before.regs 26=1)
    (hend : heap≤finish) (hFlow : flow<2^w) (hspace : finish+2<2^w)
    (hz : ZeroFrom afterEpoch.mem finish) (hbit : afterEpoch.mem (finish-1)≤1)
    (hframe : ∀ z<heap,afterEpoch.mem z=mem z)
    (hnonterminal : 1/4<residual I target (epochVector F I mem source))
    (hNo : afterEpoch.mem (finish-1)=0 → ¬TargetStagePromise I U target (epochVector F I mem source))
    (hYes : afterEpoch.mem (finish-1)=1 → TargetStageFlow F I E flow finish afterEpoch.mem ∧
      (TargetStagePromise I U target (epochVector F I mem source) →
        potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I afterEpoch.mem flow)≤
          potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem source)-
            (I.m:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/2000)) :
    ∃ out final c,
      Runs w p ω (targetEpochAfterInit complete record) before (.returned out) final c ∧
      TargetStageResult F I U E κ target source heap out mem final.mem ∧
      out=finish+2 ∧ c≤cost+argsSize targetEpochCompleteArgs+60 := by
  obtain ⟨out,final,c,hactual,hout,hWord,hcost⟩ :=
    targetEpochAfterInit_complete_runs before afterEpoch hbody hargs hrun hrecord
      hflow hinit hFlow hspace hz rfl hbit
  refine ⟨out,final,c,hactual,?_,hout.2,hcost⟩
  exact targetEpoch_continue_result F I U E κ target source heap flow finish out _
    hframe hend hWord hbit hnonterminal hNo hYes hout

end MinCostFlow.IPM.Machine
