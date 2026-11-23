module

public import MinCostFlow.IPM.Machine.TargetEpochTerminalResult
public import MinCostFlow.IPM.Machine.TargetEpochCopy

/-!
# Dispatching a target stage by its exact residual

Read the exact residual from the fixed-point source flow. Only the
branch that leaves a fresh copy enters the costly epoch. The other
branches immediately return the terminal result.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 450000 in
/-- Run the exact stage setup, then discharge its two terminal branches.
A continuation proof receives the actual fresh copy and residual
from this same run. -/
theorem targetEpoch_runs_of_continue {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U : ℕ) (κ target : ℝ) (L : EpochLayout) (tp qp source heap space price : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base startup complete record : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hwords : ∀ z∈targetEpochPacket L F I tp qp source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,tp,F.limbs,heap,L.slackMin,L.slackMax,qp] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hSpace : epochResidualEnd I.m F.limbs heap+2<2^w)
    (hEndSpace : epochResidualEnd I.m F.limbs heap+2≤heap+space)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hc : ∀ e : Fin I.m,Num.intVal mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost)
    (hT : Num.fixVal mem tp F.fmt.limbBits F.limbs F.fmt.precision=target)
    (hmnEnd : L.slackMin+F.limbs≤heap) (hmxEnd : L.slackMax+F.limbs≤heap) (hqEnd : qp+F.limbs≤heap)
    (hmn : ScalarAt mem L.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^L.exponent))
    (hmx : ScalarAt mem L.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^L.exponent))
    (hq : ScalarAt mem qp F.fmt.limbBits F.limbs F.fmt.precision (1/4))
    (hE : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hcontinue : ∀ checked : State,
      let r := residual I target (epochVector F I mem source)
      let flow := epochResidualEnd I.m F.limbs heap
      let coeffHeap := flow+I.m*F.limbs
      (∀ j<23,checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0) →
      checked.regs 30=coeffHeap → checked.regs 23=flow → 2<coeffHeap →
      (∀ z<heap,checked.mem z=mem z) → ZeroFrom checked.mem coeffHeap →
      1/4<r → 1/(2:ℝ)^L.exponent<r → r<(2:ℝ)^L.exponent →
      ScalarAt checked.mem (heap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r →
      (∀ e : Fin I.m,ScalarAt checked.mem (flow+e.val*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e)) →
      ∃ out final cost,
        Runs w p ω (targetEpochBranch startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50) :
    ∃ out final cost,
      Runs w p ω (targetEpochBody base startup complete record)
        (startState (targetEpochPacket L F I tp qp source heap) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤epochBaseCost I.m F.limbs+price+81 := by
  let flow := epochResidualEnd I.m F.limbs heap
  let r := residual I target (epochVector F I mem source)
  obtain ⟨v,checked,c,hsetup,hout,hcode,hNew,hfixed,hcost⟩ :=
    targetEpochSetup_runs F I L tp qp source heap mem pos ω hbase hwords hpre hL hEight (by omega)
  have hregs (j : ℕ) (hj : j<23) :
      checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0 := hfixed j hj
  have hsrc : checked.regs 20=source := hregs 20 (by decide)
  have hsrcWord := hwords source (by simp [targetEpochPacket])
  obtain ⟨hframe,hout'⟩ := epochBase_output_instance I (epochVector F I mem source) hout hL hflow.1
    hc (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hT hmnEnd hmxEnd hqEnd hmn hmx hq
  have terminal (hsmall : v=0 ∨ v=2) (hz : ZeroFrom checked.mem flow)
      (hYes : v=0 → r≤1/4)
      (hNo : v=2 → 1/4<r ∧ ¬TargetStagePromise I U target (epochVector F I mem source)) :
      ∃ out final cost,
        Runs w p ω (targetEpochBranch startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50 := by
    obtain ⟨out,final,c',hrun,hrecordOut,hfit,hcost'⟩ :=
      targetEpoch_terminal_runs checked ω hrecord hsmall hsrc hNew hcode hsrcWord (by omega) hSpace hz
    have hEnd : out=flow+2 := hrecordOut.2
    exact ⟨out,final,c',hrun,targetEpoch_terminal_result F I U L.exponent κ target source heap flow out
      hflow hframe (Nat.le_add_right _ _) hfit hsmall hYes hNo hrecordOut,by omega,by omega⟩
  have htail : ∃ out final cost,
      Runs w p ω (targetEpochBranch startup complete record) checked (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤price+50 := by
    change (if r≤1/4 then _ else _) at hout'
    by_cases hstop : r≤1/4
    · rw [ite_eq_left hstop] at hout'
      exact terminal (Or.inl hout'.1) hout'.2 (fun _ => hstop) (fun he => by omega)
    · rw [ite_eq_right hstop] at hout'
      have hnon := lt_of_not_ge hstop
      change (if 1/(2:ℝ)^L.exponent<r ∧ r<(2:ℝ)^L.exponent then _ else _) at hout'
      by_cases hRange : 1/(2:ℝ)^L.exponent<r ∧ r<(2:ℝ)^L.exponent
      · rw [ite_eq_left hRange] at hout'
        obtain ⟨hv,hbig,hzero,hR,hf⟩ := hout'
        exact hcontinue checked hregs (hcode.trans hv) hNew (hv ▸ hbig) hframe (hv ▸ hzero)
          hnon hRange.1 hRange.2 hR hf
      · rw [ite_eq_right hRange] at hout'
        exact terminal (Or.inr hout'.1) hout'.2 (fun he => by omega) (fun _ => ⟨hnon,fun hp =>
          hRange (targetEpoch_promised_residual_range F I U L.exponent source heap target mem
            hflow hE hm hU hsize hnums hFlo hnon hp)⟩)
  obtain ⟨out,final,c',hrun,hpost,hEnd,hcost'⟩ := htail
  exact ⟨out,final,c+c'+1,runs_seq_iff.mpr (Or.inr ⟨checked,c,c',hsetup,hrun,rfl⟩),
    hpost,hEnd,by omega⟩

/-- Run the exact stage setup, then discharge its two terminal branches.
A continuation proof receives the actual fresh copy and residual
from this same run. -/
theorem targetEpoch_runs_of_continue_at_range {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U : ℕ) (κ target : ℝ) (L : EpochLayout) (tp qp source heap space price : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base startup complete record : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hwords : ∀ z∈targetEpochPacket L F I tp qp source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,tp,F.limbs,heap,L.slackMin,L.slackMax,qp] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hSpace : epochResidualEnd I.m F.limbs heap+2<2^w)
    (hEndSpace : epochResidualEnd I.m F.limbs heap+2≤heap+space)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hc : ∀ e : Fin I.m,Num.intVal mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost)
    (hT : Num.fixVal mem tp F.fmt.limbBits F.limbs F.fmt.precision=target)
    (hmnEnd : L.slackMin+F.limbs≤heap) (hmxEnd : L.slackMax+F.limbs≤heap) (hqEnd : qp+F.limbs≤heap)
    (hmn : ScalarAt mem L.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^L.exponent))
    (hmx : ScalarAt mem L.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^L.exponent))
    (hq : ScalarAt mem qp F.fmt.limbBits F.limbs F.fmt.precision (1/4))
    (hE : ipmRangeExponent I.m U≤L.exponent)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hcontinue : ∀ checked : State,
      let r := residual I target (epochVector F I mem source)
      let flow := epochResidualEnd I.m F.limbs heap
      let coeffHeap := flow+I.m*F.limbs
      (∀ j<23,checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0) →
      checked.regs 30=coeffHeap → checked.regs 23=flow → 2<coeffHeap →
      (∀ z<heap,checked.mem z=mem z) → ZeroFrom checked.mem coeffHeap →
      1/4<r → 1/(2:ℝ)^L.exponent<r → r<(2:ℝ)^L.exponent →
      ScalarAt checked.mem (heap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r →
      (∀ e : Fin I.m,ScalarAt checked.mem (flow+e.val*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e)) →
      ∃ out final cost,
        Runs w p ω (targetEpochBranch startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50) :
    ∃ out final cost,
      Runs w p ω (targetEpochBody base startup complete record)
        (startState (targetEpochPacket L F I tp qp source heap) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤epochBaseCost I.m F.limbs+price+81 := by
  let flow := epochResidualEnd I.m F.limbs heap
  let r := residual I target (epochVector F I mem source)
  obtain ⟨v,checked,c,hsetup,hout,hcode,hNew,hfixed,hcost⟩ :=
    targetEpochSetup_runs F I L tp qp source heap mem pos ω hbase hwords hpre hL hEight (by omega)
  have hregs (j : ℕ) (hj : j<23) :
      checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0 := hfixed j hj
  have hsrc : checked.regs 20=source := hregs 20 (by decide)
  have hsrcWord := hwords source (by simp [targetEpochPacket])
  obtain ⟨hframe,hout'⟩ := epochBase_output_instance I (epochVector F I mem source) hout hL hflow.1
    hc (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hT hmnEnd hmxEnd hqEnd hmn hmx hq
  have terminal (hsmall : v=0 ∨ v=2) (hz : ZeroFrom checked.mem flow)
      (hYes : v=0 → r≤1/4)
      (hNo : v=2 → 1/4<r ∧ ¬TargetStagePromise I U target (epochVector F I mem source)) :
      ∃ out final cost,
        Runs w p ω (targetEpochBranch startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50 := by
    obtain ⟨out,final,c',hrun,hrecordOut,hfit,hcost'⟩ :=
      targetEpoch_terminal_runs checked ω hrecord hsmall hsrc hNew hcode hsrcWord (by omega) hSpace hz
    have hEnd : out=flow+2 := hrecordOut.2
    exact ⟨out,final,c',hrun,targetEpoch_terminal_result F I U L.exponent κ target source heap flow out
      hflow hframe (Nat.le_add_right _ _) hfit hsmall hYes hNo hrecordOut,by omega,by omega⟩
  have htail : ∃ out final cost,
      Runs w p ω (targetEpochBranch startup complete record) checked (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤price+50 := by
    change (if r≤1/4 then _ else _) at hout'
    by_cases hstop : r≤1/4
    · rw [ite_eq_left hstop] at hout'
      exact terminal (Or.inl hout'.1) hout'.2 (fun _ => hstop) (fun he => by omega)
    · rw [ite_eq_right hstop] at hout'
      have hnon := lt_of_not_ge hstop
      change (if 1/(2:ℝ)^L.exponent<r ∧ r<(2:ℝ)^L.exponent then _ else _) at hout'
      by_cases hRange : 1/(2:ℝ)^L.exponent<r ∧ r<(2:ℝ)^L.exponent
      · rw [ite_eq_left hRange] at hout'
        obtain ⟨hv,hbig,hzero,hR,hf⟩ := hout'
        exact hcontinue checked hregs (hcode.trans hv) hNew (hv ▸ hbig) hframe (hv ▸ hzero)
          hnon hRange.1 hRange.2 hR hf
      · rw [ite_eq_right hRange] at hout'
        exact terminal (Or.inr hout'.1) hout'.2 (fun he => by omega) (fun _ => ⟨hnon,fun hp =>
          hRange (targetEpoch_promised_residual_range_at F I U L.exponent source heap target mem
            hflow hE hm hU hsize hnums hFlo hnon hp)⟩)
  obtain ⟨out,final,c',hrun,hpost,hEnd,hcost'⟩ := htail
  exact ⟨out,final,c+c'+1,runs_seq_iff.mpr (Or.inr ⟨checked,c,c',hsetup,hrun,rfl⟩),
    hpost,hEnd,by omega⟩

private theorem targetEpochWithV_runs_of_continue_core {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U : ℕ) (κ target : ℝ) (L : EpochLayout) (tp qp source heap space price V : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base startup complete record : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hwords : ∀ z∈targetEpochPacket L F I tp qp source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,tp,F.limbs,heap,L.slackMin,L.slackMax,qp] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hSpace : epochResidualEnd I.m F.limbs heap+2<2^w)
    (hEndSpace : epochResidualEnd I.m F.limbs heap+2≤heap+space)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hc : ∀ e : Fin I.m,Num.intVal mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost)
    (hT : Num.fixVal mem tp F.fmt.limbBits F.limbs F.fmt.precision=target)
    (hmnEnd : L.slackMin+F.limbs≤heap) (hmxEnd : L.slackMax+F.limbs≤heap) (hqEnd : qp+F.limbs≤heap)
    (hmn : ScalarAt mem L.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^L.exponent))
    (hmx : ScalarAt mem L.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^L.exponent))
    (hq : ScalarAt mem qp F.fmt.limbBits F.limbs F.fmt.precision (1/4))
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hPromRange : 1/4 < residual I target (epochVector F I mem source) →
      TargetStagePromise I U target (epochVector F I mem source) →
      1/(2:ℝ)^L.exponent < residual I target (epochVector F I mem source) ∧
      residual I target (epochVector F I mem source) < (2:ℝ)^L.exponent)
    (hcontinue : ∀ checked : State,
      let r := residual I target (epochVector F I mem source)
      let flow := epochResidualEnd I.m F.limbs heap
      let coeffHeap := flow+I.m*F.limbs
      (∀ j<23,checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0) →
      checked.regs 30=coeffHeap → checked.regs 23=flow → checked.regs 29=V → 2<coeffHeap →
      (∀ z<heap,checked.mem z=mem z) → ZeroFrom checked.mem coeffHeap →
      1/4<r → 1/(2:ℝ)^L.exponent<r → r<(2:ℝ)^L.exponent →
      ScalarAt checked.mem (heap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r →
      (∀ e : Fin I.m,ScalarAt checked.mem (flow+e.val*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e)) →
      ∃ out final cost,
        Runs w p ω (targetEpochBranchWithV startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete record)
        (startState (targetEpochPacketWithV L F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤epochBaseCost I.m F.limbs+price+81 := by
  let flow := epochResidualEnd I.m F.limbs heap
  let r := residual I target (epochVector F I mem source)
  obtain ⟨v,checked,c,hsetup,hout,hcode,hNew,hVreg,hfixed,hcost⟩ :=
    targetEpochSetupWithV_runs F I L tp qp source heap V mem pos ω hbase hwords hpre hL hEight (by omega)
  have hregs (j : ℕ) (hj : j<23) :
      checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0 := by
    have hf := hfixed j hj
    change checked.regs j = (targetEpochPacket L F I tp qp source heap ++ [V]).getD j 0 at hf
    exact hf.trans (List.getD_append _ _ _ _ hj)
  have hsrc : checked.regs 20=source := hregs 20 (by decide)
  have hsrcWord := hwords source (by simp [targetEpochPacket])
  obtain ⟨hframe,hout'⟩ := epochBase_output_instance I (epochVector F I mem source) hout hL hflow.1
    hc (fun e => ⟨(hflow.2.2 e).1,rfl⟩) hT hmnEnd hmxEnd hqEnd hmn hmx hq
  have terminal (hsmall : v=0 ∨ v=2) (hz : ZeroFrom checked.mem flow)
      (hYes : v=0 → r≤1/4)
      (hNo : v=2 → 1/4<r ∧ ¬TargetStagePromise I U target (epochVector F I mem source)) :
      ∃ out final cost,
        Runs w p ω (targetEpochBranchWithV startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50 := by
    obtain ⟨out,final,c',hrun,hrecordOut,hfit,hcost'⟩ :=
      targetEpochWithV_terminal_runs checked ω hrecord hsmall hsrc hNew hcode hsrcWord (by omega) hSpace hz
    have hEnd : out=flow+2 := hrecordOut.2
    exact ⟨out,final,c',hrun,targetEpoch_terminal_result F I U L.exponent κ target source heap flow out
      hflow hframe (Nat.le_add_right _ _) hfit hsmall hYes hNo hrecordOut,by omega,by omega⟩
  have htail : ∃ out final cost,
      Runs w p ω (targetEpochBranchWithV startup complete record) checked (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤price+50 := by
    change (if r≤1/4 then _ else _) at hout'
    by_cases hstop : r≤1/4
    · rw [ite_eq_left hstop] at hout'
      exact terminal (Or.inl hout'.1) hout'.2 (fun _ => hstop) (fun he => by omega)
    · rw [ite_eq_right hstop] at hout'
      have hnon := lt_of_not_ge hstop
      change (if 1/(2:ℝ)^L.exponent<r ∧ r<(2:ℝ)^L.exponent then _ else _) at hout'
      by_cases hRange : 1/(2:ℝ)^L.exponent<r ∧ r<(2:ℝ)^L.exponent
      · rw [ite_eq_left hRange] at hout'
        obtain ⟨hv,hbig,hzero,hR,hf⟩ := hout'
        exact hcontinue checked hregs (hcode.trans hv) hNew hVreg (hv ▸ hbig) hframe (hv ▸ hzero)
          hnon hRange.1 hRange.2 hR hf
      · rw [ite_eq_right hRange] at hout'
        exact terminal (Or.inr hout'.1) hout'.2 (fun he => by omega)
          (fun _ => ⟨hnon, fun hp => hRange (hPromRange hnon hp)⟩)
  obtain ⟨out,final,c',hrun,hpost,hEnd,hcost'⟩ := htail
  exact ⟨out,final,c+c'+1,runs_seq_iff.mpr (Or.inr ⟨checked,c,c',hsetup,hrun,rfl⟩),
    hpost,hEnd,by omega⟩

/-- `V`-passing variant of `targetEpoch_runs_of_continue`. -/
theorem targetEpochWithV_runs_of_continue {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U : ℕ) (κ target : ℝ) (L : EpochLayout) (tp qp source heap space price V : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base startup complete record : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hwords : ∀ z∈targetEpochPacket L F I tp qp source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,tp,F.limbs,heap,L.slackMin,L.slackMax,qp] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hSpace : epochResidualEnd I.m F.limbs heap+2<2^w)
    (hEndSpace : epochResidualEnd I.m F.limbs heap+2≤heap+space)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hc : ∀ e : Fin I.m,Num.intVal mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost)
    (hT : Num.fixVal mem tp F.fmt.limbBits F.limbs F.fmt.precision=target)
    (hmnEnd : L.slackMin+F.limbs≤heap) (hmxEnd : L.slackMax+F.limbs≤heap) (hqEnd : qp+F.limbs≤heap)
    (hmn : ScalarAt mem L.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^L.exponent))
    (hmx : ScalarAt mem L.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^L.exponent))
    (hq : ScalarAt mem qp F.fmt.limbBits F.limbs F.fmt.precision (1/4))
    (hE : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hcontinue : ∀ checked : State,
      let r := residual I target (epochVector F I mem source)
      let flow := epochResidualEnd I.m F.limbs heap
      let coeffHeap := flow+I.m*F.limbs
      (∀ j<23,checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0) →
      checked.regs 30=coeffHeap → checked.regs 23=flow → checked.regs 29=V → 2<coeffHeap →
      (∀ z<heap,checked.mem z=mem z) → ZeroFrom checked.mem coeffHeap →
      1/4<r → 1/(2:ℝ)^L.exponent<r → r<(2:ℝ)^L.exponent →
      ScalarAt checked.mem (heap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r →
      (∀ e : Fin I.m,ScalarAt checked.mem (flow+e.val*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e)) →
      ∃ out final cost,
        Runs w p ω (targetEpochBranchWithV startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete record)
        (startState (targetEpochPacketWithV L F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤epochBaseCost I.m F.limbs+price+81 :=
  targetEpochWithV_runs_of_continue_core F I U κ target L tp qp source heap space price V
    mem pos ω hbase hrecord hwords hpre hL hEight hSpace hEndSpace hflow hc hT
    hmnEnd hmxEnd hqEnd hmn hmx hq hm hU hsize hnums hFlo
    (fun hnon hp => targetEpoch_promised_residual_range F I U L.exponent source heap target mem
      hflow hE hm hU hsize hnums hFlo hnon hp)
    hcontinue

/-- `V`-passing variant of `targetEpoch_runs_of_continue_at_range`. -/
theorem targetEpochWithV_runs_of_continue_at_range {w : ℕ} (F : MinRatioFormat w) (I : Instance)
    (U : ℕ) (κ target : ℝ) (L : EpochLayout) (tp qp source heap space price V : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) {p : Program} {base startup complete record : ℕ}
    (hbase : MeetsContract w p base (epochBaseContract w F.fmt.limbBits))
    (hrecord : MeetsContract w p record (boundedStatusRecordContract w 2))
    (hwords : ∀ z∈targetEpochPacket L F I tp qp source heap,z<2^w)
    (hpre : (epochBaseContract w F.fmt.limbBits).pre
      [L.cost,source,I.m,tp,F.limbs,heap,L.slackMin,L.slackMax,qp] mem)
    (hL : 0<F.limbs) (hEight : 8<2^w)
    (hSpace : epochResidualEnd I.m F.limbs heap+2<2^w)
    (hEndSpace : epochResidualEnd I.m F.limbs heap+2≤heap+space)
    (hflow : TargetStageFlow F I L.exponent source heap mem)
    (hc : ∀ e : Fin I.m,Num.intVal mem (L.cost+e.val*F.limbs) F.fmt.limbBits F.limbs=(I.edge e).cost)
    (hT : Num.fixVal mem tp F.fmt.limbBits F.limbs F.fmt.precision=target)
    (hmnEnd : L.slackMin+F.limbs≤heap) (hmxEnd : L.slackMax+F.limbs≤heap) (hqEnd : qp+F.limbs≤heap)
    (hmn : ScalarAt mem L.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^L.exponent))
    (hmx : ScalarAt mem L.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^L.exponent))
    (hq : ScalarAt mem qp F.fmt.limbBits F.limbs F.fmt.precision (1/4))
    (hE : ipmRangeExponent I.m U≤L.exponent)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hcontinue : ∀ checked : State,
      let r := residual I target (epochVector F I mem source)
      let flow := epochResidualEnd I.m F.limbs heap
      let coeffHeap := flow+I.m*F.limbs
      (∀ j<23,checked.regs j=(targetEpochPacket L F I tp qp source heap).getD j 0) →
      checked.regs 30=coeffHeap → checked.regs 23=flow → checked.regs 29=V → 2<coeffHeap →
      (∀ z<heap,checked.mem z=mem z) → ZeroFrom checked.mem coeffHeap →
      1/4<r → 1/(2:ℝ)^L.exponent<r → r<(2:ℝ)^L.exponent →
      ScalarAt checked.mem (heap+(8*I.m+3)*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision r →
      (∀ e : Fin I.m,ScalarAt checked.mem (flow+e.val*F.limbs)
        F.fmt.limbBits F.limbs F.fmt.precision (epochVector F I mem source e)) →
      ∃ out final cost,
        Runs w p ω (targetEpochBranchWithV startup complete record) checked (.returned out) final cost ∧
        TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
        out≤heap+space ∧ cost≤price+50) :
    ∃ out final cost,
      Runs w p ω (targetEpochBodyWithV base startup complete record)
        (startState (targetEpochPacketWithV L F I tp qp source heap V) mem pos) (.returned out) final cost ∧
      TargetStageResult F I U L.exponent κ target source heap out mem final.mem ∧
      out≤heap+space ∧ cost≤epochBaseCost I.m F.limbs+price+81 :=
  targetEpochWithV_runs_of_continue_core F I U κ target L tp qp source heap space price V
    mem pos ω hbase hrecord hwords hpre hL hEight hSpace hEndSpace hflow hc hT
    hmnEnd hmxEnd hqEnd hmn hmx hq hm hU hsize hnums hFlo
    (fun hnon hp => targetEpoch_promised_residual_range_at F I U L.exponent source heap target mem
      hflow hE hm hU hsize hnums hFlo hnon hp)
    hcontinue

end MinCostFlow.IPM.Machine
