module

public import MinCostFlow.IPM.Machine.EpochCompleteRun
public import MinCostFlow.IPM.Machine.EpochPromisedTrace

/-!
# Passing the verified lazy trace to the complete epoch

The same lazy run is passed to the full-coordinate caller for every
target. For a promised target its ending history carries the analytic
prefix certificate. A lower target may instead return the first failure.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Certify the complete caller's input trace using the actual finite
loop trace. Its stopping branch is retained even when the target is
below optimum. -/
theorem epoch_complete_trace_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance)
    (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hmem : P.machine.mem=mem) (hheap : P.machine.regs 8=heap)
    (hbudget : mem (heap-3)=5*I.m)
    (htrace :
      let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmErrorBits I.m U) K mem heap space finish
      let Step := EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmErrorBits I.m U) K
      if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
            (ipmErrorBits I.m U) K j Q v st credit) :
    let base := epochVector F I mem L.base
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K mem heap space finish
    (promised → st.mem (v-1)=1) ∧
      if st.mem (v-1)=1 then
        ∃ Q : EpochPoint R.τ,Inv finish Q ∧ credit=Q.credit ∧
          (promised → EpochAnalyticPrefix I U target κ r A base finish Q) ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else st.mem (v-1)=0 ∧ ∃ j<finish, ∃ Q : EpochPoint R.τ, Inv j Q ∧
        EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
          (ipmErrorBits I.m U) K j Q v st credit := by
  dsimp only
  by_cases hp : (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤200*I.m*Real.log (I.m*(U:ℝ))
  · obtain ⟨⟨fstar,hstar,hF⟩,hpot⟩ := hp
    obtain ⟨hbit,Q,hInv,hcert,hcredit,hflag,hrep⟩ := epoch_trace_promised_upTo F A I U κ target r rate allocation R
      hA L K heap space finish v P st credit capacity fstar mem hfinish hstatic hsource hlo hm hU hsize
      hnums hstar hF hFlo hκ hκ' hxlo hres hr hf hroute hpot hmem hheap hbudget htrace
    rw [ite_eq_left hbit]
    exact ⟨fun _ => hbit,Q,hInv,hcredit,fun _ => hcert,hflag,hrep⟩
  · refine ⟨fun h => (hp h).elim,?_⟩
    by_cases hb : st.mem (v-1)=1
    · rw [ite_eq_left hb] at htrace ⊢
      obtain ⟨Q,_,hInv,hcredit,hflag,hrep⟩ := htrace
      exact ⟨Q,hInv,hcredit,fun h => (hp h).elim,hflag,hrep⟩
    · rw [ite_eq_right hb] at htrace ⊢
      obtain ⟨j,hj,Q,_,hInv,hstop⟩ := htrace
      exact ⟨hstop.1,j,hj,Q,hInv,hstop⟩

/-- Certify the complete caller's input trace using the actual finite
loop trace. Its stopping branch is retained even when the target is
below optimum. -/
theorem epoch_complete_trace {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance)
    (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hmem : P.machine.mem=mem) (hheap : P.machine.regs 8=heap)
    (hbudget : mem (heap-3)=5*I.m)
    (htrace :
      let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmErrorBits I.m U) K mem heap space finish
      let Step := EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmErrorBits I.m U) K
      if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
            (ipmErrorBits I.m U) K j Q v st credit) :
    let base := epochVector F I mem L.base
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K mem heap space finish
    (promised → st.mem (v-1)=1) ∧
      if st.mem (v-1)=1 then
        ∃ Q : EpochPoint R.τ,Inv finish Q ∧ credit=Q.credit ∧
          (promised → EpochAnalyticPrefix I U target κ r A base finish Q) ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else st.mem (v-1)=0 ∧ ∃ j<finish, ∃ Q : EpochPoint R.τ, Inv j Q ∧
        EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
          (ipmErrorBits I.m U) K j Q v st credit :=
  epoch_complete_trace_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n) L K heap
    space finish v P st credit capacity mem hfinish hstatic hsource hlo hm hU hsize hnums hFlo
    hκ hκ' hxlo hres hr hf hroute hmem hheap hbudget htrace

/-- Certify the complete caller's input trace using the actual finite
loop trace. Its stopping branch is retained even when the target is
below optimum. -/
theorem epoch_complete_trace_widened_upTo_on {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance)
    (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hmem : P.machine.mem=mem) (hheap : P.machine.regs 8=heap)
    (hbudget : mem (heap-3)=5*I.m)
    (htrace :
      let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmQualityErrorBits I.m U k) K mem heap space finish
      let Step := EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmQualityErrorBits I.m U k) K
      if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
            (ipmQualityErrorBits I.m U k) K j Q v st credit) :
    let base := epochVector F I mem L.base
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K mem heap space finish
    (promised → st.mem (v-1)=1) ∧
      if st.mem (v-1)=1 then
        ∃ Q : EpochPoint R.τ,Inv finish Q ∧ credit=Q.credit ∧
          (promised → EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base finish Q) ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else st.mem (v-1)=0 ∧ ∃ j<finish, ∃ Q : EpochPoint R.τ, Inv j Q ∧
        EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
          (ipmQualityErrorBits I.m U k) K j Q v st credit := by
  dsimp only
  by_cases hp : (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤200*I.m*Real.log (I.m*(U:ℝ))
  · obtain ⟨⟨fstar,hstar,hF⟩,hpot⟩ := hp
    obtain ⟨hbit,Q,hInv,hcert,hcredit,hflag,hrep⟩ := epoch_trace_promised_widened_upTo_on F A I U k κ target r rate allocation R
      hA hPG L K heap space finish v P st credit capacity fstar mem hfinish hstatic hsource hlo hm hU hsize
      hnums hstar hF hFlo hκ hκ' hxlo hres hr hf hroute hpot hmem hheap hbudget htrace
    rw [ite_eq_left hbit]
    exact ⟨fun _ => hbit,Q,hInv,hcredit,fun _ => hcert,hflag,hrep⟩
  · refine ⟨fun h => (hp h).elim,?_⟩
    by_cases hb : st.mem (v-1)=1
    · rw [ite_eq_left hb] at htrace ⊢
      obtain ⟨Q,_,hInv,hcredit,hflag,hrep⟩ := htrace
      exact ⟨Q,hInv,hcredit,fun h => (hp h).elim,hflag,hrep⟩
    · rw [ite_eq_right hb] at htrace ⊢
      obtain ⟨j,hj,Q,_,hInv,hstop⟩ := htrace
      exact ⟨hstop.1,j,hj,Q,hInv,hstop⟩

/-- Certify the complete caller's input trace using the actual finite
loop trace. Its stopping branch is retained even when the target is
below optimum. -/
theorem epoch_complete_trace_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance)
    (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hmem : P.machine.mem=mem) (hheap : P.machine.regs 8=heap)
    (hbudget : mem (heap-3)=5*I.m)
    (htrace :
      let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmQualityErrorBits I.m U k) K mem heap space finish
      let Step := EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
        (ipmQualityErrorBits I.m U k) K
      if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
            (ipmQualityErrorBits I.m U k) K j Q v st credit) :
    let base := epochVector F I mem L.base
    let promised := (∃ fstar, I.IsFeasible fstar ∧ I.cost fstar≤target) ∧
      potential I (Num.IPM.alphaPrime I.m U) target base≤200*I.m*Real.log (I.m*(U:ℝ))
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K mem heap space finish
    (promised → st.mem (v-1)=1) ∧
      if st.mem (v-1)=1 then
        ∃ Q : EpochPoint R.τ,Inv finish Q ∧ credit=Q.credit ∧
          (promised → EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base finish Q) ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
      else st.mem (v-1)=0 ∧ ∃ j<finish, ∃ Q : EpochPoint R.τ, Inv j Q ∧
        EpochStoppedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
          (ipmQualityErrorBits I.m U k) K j Q v st credit :=
  epoch_complete_trace_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L K heap space finish v P st credit capacity mem
    hfinish hstatic hsource hlo hm hU hsize hnums hFlo hκ hκ' hxlo hres hr hf hroute hmem hheap
    hbudget htrace

end MinCostFlow.IPM.Machine
