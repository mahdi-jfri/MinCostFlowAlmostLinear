module

public import MinCostFlow.IPM.Machine.EpochAcceptedAnalytic
public import MinCostFlow.IPM.Machine.EpochStoppedAnalytic
public import MinCostFlow.IPM.Machine.EpochInitialAccuracy
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Certification of the complete finite epoch trace

Induct along the actual accepted prefix and preserve the fixed base
and scalar inputs. If the machine reports failure, the certified
condition at its stopping call forces that call's bit to be one.
Consequently a promised epoch completes all of its admissible steps.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 480000 in
/-- Algorithm 7's complete machine epoch (Chen et al., arXiv:2203.00671v2,
page 69) succeeds on upper targets. The resulting certified prefix
belongs to the same execution and final history as the loop's result. -/
theorem epoch_trace_promised_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
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
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K mem heap space finish
    st.mem (v-1)=1 ∧
      ∃ Q, Inv finish Q ∧ EpochAnalyticPrefix I U target κ r A (epochVector F I mem L.base) finish Q ∧
        credit=Q.credit ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
        R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem := by
  dsimp only at htrace ⊢
  let a := Num.IPM.alphaPrime I.m U
  let eps := κ*a/1024
  let Inv := EpochConditions F A I κ (a/8) rate allocation R L (ipmErrorBits I.m U) K mem heap space finish
  let Step := EpochAcceptedStep F A I κ (a/8) rate allocation R L (ipmErrorBits I.m U) K
  let base := epochVector F I mem L.base
  let Certified : ℕ → EpochPoint R.τ → Prop := EpochAnalyticPrefix I U target κ r A base
  have hstatic' := hstatic
  obtain ⟨_,_,_,_,_,harray,hscalars,_,_,_,_,_,_,_,_,_,_,_,_,_,hfmt,heps,_⟩ := hstatic'
  have hbase (j : ℕ) (Q : EpochPoint R.τ) (h : Inv j Q) :
      epochVector F I Q.machine.mem L.base=base := by
    have hframe := h.2.2.2.2.2.2.1
    funext e
    exact Num.IPM.fixVal_frozen hframe
      ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans (harray L.base (by simp)))
  have hcurrentStatic (j : ℕ) (Q : EpochPoint R.τ) (h : Inv j Q) :
      EpochStaticInputs F I U κ (a/8) eps L capacity ((25/32:ℝ)*(κ*a/32)^2/50) Q.machine.mem :=
    hstatic.frozen h.2.2.2.2.2.2.1
  have hcurrentSource (j : ℕ) (Q : EpochPoint R.τ) (h : Inv j Q) :
      epochSourcesAt F I L a r Q.machine.mem :=
    hsource.frozen h.2.2.2.2.2.2.1 harray ⟨hscalars L.residual (by simp),hscalars L.alpha (by simp)⟩
  have hInit : Inv 0 P := by
    by_cases hbit : st.mem (v-1)=1
    · obtain ⟨Q,hpath,_⟩ := ite_eq_left hbit ▸ htrace
      exact hpath.start_inv
    · obtain ⟨j,_,Q,hpath,_⟩ := ite_eq_right hbit ▸ htrace
      exact hpath.start_inv
  have hprefix : Certified 0 P := by
    have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
    have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
    have ha' : a≤alpha I U := (Num.IPM.alphaPrime_bounds I U hsize).2
    have haSmall := ha'.trans (alpha_le I U hsizeR)
    have hx : κ*a≤1 := by
      have hh := mul_le_mul_of_nonneg_right hκ' ha.le
      linarith only [hh,haSmall]
    obtain ⟨_,_,_,_,_,_,_,hv,hG,_,hg,hl,hcache,hRanges,_⟩ := hInit
    have hOld (e : Fin I.m) : 1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I mem L.lengths e ∧
        epochVector F I mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U) := by
      have hh := (hRanges e.val e.isLt).2.2.2
      simpa only [hmem,readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using hh
    have hAcc := epoch_initial_input_accuracy_upTo F A I U κ (a/8) (precisionHiddenPsi I.m U) (κ*a) target a r
      hA L mem P.history P.eta P.op hm hsizeR hnums ha.le ha' hxlo hx hsource (by linarith only [hr]) hres
      hv (hG 0 (by omega)) (by simpa only [hmem,Nat.mul_zero] using hg.symm)
      (by simpa only [hmem,Nat.mul_zero] using hl.symm) hOld
      (by simpa only [hmem,Nat.mul_zero,minRatioLast] using hcache)
    exact epochAnalyticPrefix_zero I U target κ r A base P heps.le (by rw [hmem,hheap,hbudget]) hAcc
  have hAdvance (j : ℕ) (X Y : EpochPoint R.τ) (hX : Inv j X) (hY : Inv (j+1) Y) (hXY : Step j X Y)
      (hCX : Certified j X) : Certified (j+1) Y := by
    have he := hbase j X hX
    have hC := epoch_accepted_analytic_upTo F A I U κ target r rate allocation R hA L K j X Y capacity fstar
      hX hY hXY (he.symm ▸ hCX) (hcurrentStatic j X hX) (hcurrentSource j X hX)
      hm (hX.counter_le.trans hfinish) hU hsize hnums hstar hF hκ hκ' hxlo
      (he.symm ▸ hres) hr (he.symm ▸ hf) (he.symm ▸ hroute) (he.symm ▸ hpot)
    change EpochAnalyticPrefix I U target κ r A base (j+1) Y
    simpa only [he] using hC.1
  by_cases hbit : st.mem (v-1)=1
  · rw [ite_eq_left hbit] at htrace
    obtain ⟨Q,hpath,hQ,hCred,hRecord,hRep⟩ := htrace
    exact ⟨hbit,Q,hQ,hpath.propagate hAdvance hprefix,hCred,hRecord,hRep⟩
  · rw [ite_eq_right hbit] at htrace
    obtain ⟨j,hj,Q,hpath,hQ,hStop⟩ := htrace
    have hAq := hpath.propagate hAdvance hprefix
    have he := hbase j Q hQ
    obtain ⟨_,_,s',hout,_⟩ := hStop
    have hone := epoch_iteration_promised_accepts_upTo F A I U κ target r rate allocation R hA L K j v
      Q st.mem s' capacity fstar hQ (he.symm ▸ hAq) (hcurrentStatic j Q hQ) (hcurrentSource j Q hQ) hlo
      hm (hj.le.trans hfinish) hU hsize hnums hstar hF hFlo hκ hκ' hxlo
      (he.symm ▸ hres) hr (he.symm ▸ hf) (he.symm ▸ hroute) (he.symm ▸ hpot) hout
    exact False.elim (hbit hone)

/-- Algorithm 7's complete machine epoch (Chen et al., arXiv:2203.00671v2,
page 69) succeeds on upper targets. The resulting certified prefix
belongs to the same execution and final history as the loop's result. -/
theorem epoch_trace_promised {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
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
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K mem heap space finish
    st.mem (v-1)=1 ∧
      ∃ Q, Inv finish Q ∧ EpochAnalyticPrefix I U target κ r A (epochVector F I mem L.base) finish Q ∧
        credit=Q.credit ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
        R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem :=
  epoch_trace_promised_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n) L K heap
    space finish v P st credit capacity fstar mem hfinish hstatic hsource hlo hm hU hsize hnums
    hstar hF hFlo hκ hκ' hxlo hres hr hf hroute hpot hmem hheap hbudget htrace

/-- Algorithm 7's complete machine epoch (Chen et al., arXiv:2203.00671v2,
page 69) succeeds on upper targets. The resulting certified prefix
belongs to the same execution and final history as the loop's result. -/
theorem epoch_trace_promised_widened_upTo_on {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
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
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K mem heap space finish
    st.mem (v-1)=1 ∧
      ∃ Q, Inv finish Q ∧ EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I mem L.base) finish Q ∧
        credit=Q.credit ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
        R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem := by
  dsimp only at htrace ⊢
  let a := Num.IPM.alphaPrime I.m U
  let eps := κ*a/1024
  let Inv := EpochConditions F A I κ (a/8) rate allocation R L (ipmQualityErrorBits I.m U k) K mem heap space finish
  let Step := EpochAcceptedStep F A I κ (a/8) rate allocation R L (ipmQualityErrorBits I.m U k) K
  let base := epochVector F I mem L.base
  let Certified : ℕ → EpochPoint R.τ → Prop := EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base
  have hstatic' := hstatic
  obtain ⟨_,_,_,_,_,harray,hscalars,_,_,_,_,_,_,_,_,_,_,_,_,_,hfmt,heps,_⟩ := hstatic'
  have hbase (j : ℕ) (Q : EpochPoint R.τ) (h : Inv j Q) :
      epochVector F I Q.machine.mem L.base=base := by
    have hframe := h.2.2.2.2.2.2.1
    funext e
    exact Num.IPM.fixVal_frozen hframe
      ((reported_entry_end L.base F.limbs e.val I.m e.isLt).trans (harray L.base (by simp)))
  have hcurrentStatic (j : ℕ) (Q : EpochPoint R.τ) (h : Inv j Q) :
      EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (a/8) eps L capacity ((25/32:ℝ)*(κ*a/32)^2/50) Q.machine.mem :=
    hstatic.frozen h.2.2.2.2.2.2.1
  have hcurrentSource (j : ℕ) (Q : EpochPoint R.τ) (h : Inv j Q) :
      epochSourcesAt F I L a r Q.machine.mem :=
    hsource.frozen h.2.2.2.2.2.2.1 harray ⟨hscalars L.residual (by simp),hscalars L.alpha (by simp)⟩
  have hInit : Inv 0 P := by
    by_cases hbit : st.mem (v-1)=1
    · obtain ⟨Q,hpath,_⟩ := ite_eq_left hbit ▸ htrace
      exact hpath.start_inv
    · obtain ⟨j,_,Q,hpath,_⟩ := ite_eq_right hbit ▸ htrace
      exact hpath.start_inv
  have hprefix : Certified 0 P := by
    have hsizeR : 2≤(I.m:ℝ)*U := by exact_mod_cast hsize
    have ha : 0<a := by unfold a Num.IPM.alphaPrime; positivity
    have ha' : a≤alpha I U := (Num.IPM.alphaPrime_bounds I U hsize).2
    have haSmall := ha'.trans (alpha_le I U hsizeR)
    have hx : κ*a≤1 := by
      have hh := mul_le_mul_of_nonneg_right hκ' ha.le
      linarith only [hh,haSmall]
    have hPD0 := hInit.stages hPG 0 (Nat.zero_le _)
    obtain ⟨_,_,_,_,_,_,_,hv,hG,_,hg,hl,hcache,hRanges,_⟩ := hInit
    have hOld (e : Fin I.m) : 1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I mem L.lengths e ∧
        epochVector F I mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
      have hh := (hRanges e.val e.isLt).2.2.2
      simpa only [hmem,readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using hh
    have hAcc := epoch_initial_input_accuracy_widened_upTo_on F A I U k κ (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) (κ*a) target a r
      hA L mem P.history P.eta P.op hm hsizeR hnums ha.le ha' hxlo hx hsource (by linarith only [hr]) hres
      hv (hG 0 (by omega)) hPD0 (by simpa only [hmem,Nat.mul_zero] using hg.symm)
      (by simpa only [hmem,Nat.mul_zero] using hl.symm) hOld
      (by simpa only [hmem,Nat.mul_zero,minRatioLast] using hcache)
    exact epochAnalyticPrefixAt_zero I U (ipmQualityRangeExponent I.m U k) target κ r A base P heps.le (by rw [hmem,hheap,hbudget]) hAcc
  have hAdvance (j : ℕ) (X Y : EpochPoint R.τ) (hX : Inv j X) (hY : Inv (j+1) Y) (hXY : Step j X Y)
      (hCX : Certified j X) : Certified (j+1) Y := by
    have he := hbase j X hX
    have hC := epoch_accepted_analytic_widened_upTo_on F A I U k κ target r rate allocation R hA hPG L K j X Y capacity fstar
      hX hY hXY (he.symm ▸ hCX) (hcurrentStatic j X hX) (hcurrentSource j X hX)
      hm (hX.counter_le.trans hfinish) hU hsize hnums hstar hF hκ hκ' hxlo
      (he.symm ▸ hres) hr (he.symm ▸ hf) (he.symm ▸ hroute) (he.symm ▸ hpot)
    change EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A base (j+1) Y
    simpa only [he] using hC.1
  by_cases hbit : st.mem (v-1)=1
  · rw [ite_eq_left hbit] at htrace
    obtain ⟨Q,hpath,hQ,hCred,hRecord,hRep⟩ := htrace
    exact ⟨hbit,Q,hQ,hpath.propagate hAdvance hprefix,hCred,hRecord,hRep⟩
  · rw [ite_eq_right hbit] at htrace
    obtain ⟨j,hj,Q,hpath,hQ,hStop⟩ := htrace
    have hAq := hpath.propagate hAdvance hprefix
    have he := hbase j Q hQ
    obtain ⟨_,_,s',hout,_⟩ := hStop
    have hone := epoch_iteration_promised_accepts_widened_upTo_on F A I U k κ target r rate allocation R hA hPG L K j v
      Q st.mem s' capacity fstar hQ (he.symm ▸ hAq) (hcurrentStatic j Q hQ) (hcurrentSource j Q hQ) hlo
      hm (hj.le.trans hfinish) hU hsize hnums hstar hF hFlo hκ hκ' hxlo
      (he.symm ▸ hres) hr (he.symm ▸ hf) (he.symm ▸ hroute) (he.symm ▸ hpot) hout
    exact False.elim (hbit hone)

/-- Any call to the budgeted loop starting from a promised input (with widened numeric bounds)
page 69) succeeds on upper targets. The resulting certified prefix
belongs to the same execution and final history as the loop's result. -/
theorem epoch_trace_promised_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K heap space finish v : ℕ) (P : EpochPoint R.τ)
    (st : State) (credit : R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ) (mem : ℕ → ℕ)
    (hfinish : finish≤I.m)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hlo : L.exponent=ipmQualityRangeExponent I.m U k)
    (hm : 0<I.m) (hU : 0<U) (hsize : 2≤I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (hκ : 0<κ) (hκ' : κ≤1) (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I mem L.base)) (hroute : I.Routes (epochVector F I mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ)))
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
    let Inv := EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K mem heap space finish
    st.mem (v-1)=1 ∧
      ∃ Q, Inv finish Q ∧ EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I mem L.base) finish Q ∧
        credit=Q.credit ∧ (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
        R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem :=
  epoch_trace_promised_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L K heap space finish v P st credit capacity fstar
    mem hfinish hstatic hsource hlo hm hU hsize hnums hstar hF hFlo hκ hκ' hxlo hres hr hf hroute
    hpot hmem hheap hbudget htrace

end MinCostFlow.IPM.Machine
