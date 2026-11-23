module

public import MinCostFlow.IPM.Machine.EpochCertifiedIteration

/-!
# Analytic invariants advance on the actual successful trace

The successful trace records the exact post-refresh memory and the
new history it supplied. Certify the history using that memory. The
same realized movement then pays for the next per-edge cache bound
and the reduction in the machine's remaining report allowance.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 350000 in
/-- Advance the analytic invariant along a successful machine step of
Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69). The current
hidden witness uses only the old progress and the newly read inputs. -/
theorem epoch_accepted_analytic_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K i : ℕ) (P Q : EpochPoint R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hP : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish i P)
    (hQ : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish (i+1) Q)
    (hstep : EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K i P Q)
    (hanalytic : EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ))) :
    EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) (i+1) Q ∧
      Q.history.HiddenStable (2*(i+1)) (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U) := by
  let a := Num.IPM.alphaPrime I.m U
  let eps := κ*a/1024
  have hstepData := hstep
  obtain ⟨_,_,es,actual,cEnd,cMem,hCpost,hCbit,hgSame,hlSame,_,hset,hist,heta,hop,hnorm⟩ := hstepData
  rw [hgSame,hlSame] at hist
  have hq' := hQ
  have hp' := hP
  obtain ⟨_,_,_,_,_,hbudget,_,hvalidP,_,_,_,_,_,_⟩ := hp'
  obtain ⟨_,_,_,_,_,_,_,hvalidQ,_,_,_,_,_,hrangesQ,_⟩ := hq'
  have hindex : 2*i+1+1=2*(i+1) := by omega
  have hvalid := hvalidQ
  rw [← hindex,hist,hop] at hvalid
  have hstatic' := hstatic
  obtain ⟨_,_,_,_,_,_,_,_,hreq,_,_,_,_,_,_,_,_,_,_,_,hfmt,heps,_⟩ := hstatic'
  rw [hreq.2] at hnorm
  have hnewRange (e : Fin I.m) : 1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I cMem L.lengths e ∧
      epochVector F I cMem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U) := by
    have h := (hrangesQ e.val e.isLt).2.2.2
    rw [hlSame] at h
    simpa only [readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using h
  obtain ⟨hc,hinput,hhidden,_,hs,hsched,hmove⟩ :=
    epoch_certified_iteration_upTo F A I U κ target r rate allocation R hA L K i cEnd P cMem es actual capacity
      fstar hP hanalytic hstatic hsource hm hi hU hsize hnums hstar hF hκ hκ' hxlo hres hr hf hroute hpot
      hCpost hCbit hset hnorm hnewRange hvalid
  rw [← hist,← heta,← hop] at hc hinput hs hmove
  rw [hindex] at hc hinput hmove
  rw [← hop] at hsched
  rw [← hist,hindex] at hhidden
  have hHist := hP.history_bounded
  have hDetect := (hA
    (appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i)))
    (Function.update P.eta (2*i+1) 0) (Function.update P.op (2*i+1) false) (2*i+1)
    (appendHistoryStage_valid_detect P.history P.op (2*i) hvalidP)
    (appendHistoryStage_bounded [] _ _ hHist)).1
  have hbalance := epochReportBalance_step_on F A I κ (a/8) (precisionHiddenPsi I.m U) eps rate allocation R
    L (ipmErrorBits I.m U) K i P Q hDetect heps.le hvalidP hvalidQ hbudget hanalytic.2.2.2.2.2 hstep hmove
  have hcharge := (epoch_iteration_movement_charge_on A.eraseFailure P.history P.eta P.op (2*i) κ (a/8)
    (precisionHiddenPsi I.m U) eps hDetect hvalidP heps.le es _ _ actual hset hvalid).2
  rw [← hist,← heta,← hop,hindex] at hcharge
  refine ⟨⟨hs,hsched,hc,hinput,?_,hbalance⟩,hhidden⟩
  intro e he
  have hG := hQ.2.2.2.2.2.2.2.2.1 _ le_rfl
  have hmem : e∈(Q.history.G (2*(i+1))).E := by rw [hG]; exact Finset.mem_range.mpr he
  exact (hcharge e hmem).trans (add_le_add_right hmove eps)

/-- Advance the analytic invariant along a successful machine step of
Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69). The current
hidden witness uses only the old progress and the newly read inputs. -/
theorem epoch_accepted_analytic {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U)
      (κ*Num.IPM.alphaPrime I.m U/1024))
    (L : EpochLayout) (K i : ℕ) (P Q : EpochPoint R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hP : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish i P)
    (hQ : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K initialMem initialHeap space finish (i+1) Q)
    (hstep : EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmErrorBits I.m U) K i P Q)
    (hanalytic : EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputs F I U κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ))) :
    EpochAnalyticPrefix I U target κ r A (epochVector F I P.machine.mem L.base) (i+1) Q ∧
      Q.history.HiddenStable (2*(i+1)) (Num.IPM.alphaPrime I.m U/8) (precisionHiddenPsi I.m U) :=
  epoch_accepted_analytic_upTo F A I U κ target r rate allocation R (hA.upTo I.m I.n) L K i P Q
    capacity fstar hP hQ hstep hanalytic hstatic hsource hm hi hU hsize hnums hstar hF hκ hκ'
    hxlo hres hr hf hroute hpot

/-- Advance the analytic invariant along a successful machine step of
Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69). The current
hidden witness uses only the old progress and the newly read inputs. -/
theorem epoch_accepted_analytic_widened_upTo_on {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (K i : ℕ) (P Q : EpochPoint R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hP : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish i P)
    (hQ : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish (i+1) Q)
    (hstep : EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K i P Q)
    (hanalytic : EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ))) :
    EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) (i+1) Q ∧
      Q.history.HiddenStable (2*(i+1)) (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) := by
  let a := Num.IPM.alphaPrime I.m U
  let eps := κ*a/1024
  have hstepData := hstep
  obtain ⟨_,_,es,actual,cEnd,cMem,hCpost,hCbit,hgSame,hlSame,_,hset,hist,heta,hop,hnorm⟩ := hstepData
  rw [hgSame,hlSame] at hist
  have hq' := hQ
  have hp' := hP
  obtain ⟨_,_,_,_,_,hbudget,_,hvalidP,hGP,_,_,_,_,_⟩ := hp'
  obtain ⟨_,_,_,_,_,_,_,hvalidQ,_,_,_,_,_,hrangesQ,_⟩ := hq'
  have hindex : 2*i+1+1=2*(i+1) := by omega
  have hvalid := hvalidQ
  rw [← hindex,hist,hop] at hvalid
  have hstatic' := hstatic
  obtain ⟨_,_,_,_,_,_,_,_,hreq,_,_,_,_,_,_,_,_,_,_,_,hfmt,heps,_⟩ := hstatic'
  rw [hreq.2] at hnorm
  have hnewRange (e : Fin I.m) : 1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I cMem L.lengths e ∧
      epochVector F I cMem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k) := by
    have h := (hrangesQ e.val e.isLt).2.2.2
    rw [hlSame] at h
    simpa only [readVector,e.isLt,ite_true,epochVector,hfmt,zpow_neg,zpow_natCast,one_div] using h
  obtain ⟨hc,hinput,hhidden,_,hs,hsched,hmove⟩ :=
    epoch_certified_iteration_widened_upTo_on F A I U k κ target r rate allocation R hA hPG L K i cEnd P cMem es actual capacity
      fstar hP hanalytic hstatic hsource hm hi hU hsize hnums hstar hF hκ hκ' hxlo hres hr hf hroute hpot
      hCpost hCbit hset hnorm hnewRange hvalid
  rw [← hist,← heta,← hop] at hc hinput hs hmove
  rw [hindex] at hc hinput hmove
  rw [← hop] at hsched
  rw [← hist,hindex] at hhidden
  have hHist := hP.history_bounded
  have hDetect := (hA
    (appendHistoryStage P.history (2*i) [] (P.history.g (2*i)) (P.history.ℓ (2*i)))
    (Function.update P.eta (2*i+1) 0) (Function.update P.op (2*i+1) false) (2*i+1)
    (appendHistoryStage_valid_detect P.history P.op (2*i) hvalidP)
    (appendHistoryStage_bounded [] _ _ hHist)
    (appendHistoryStage_stage_on [] _ _ (hP.stages hPG) (hP.stages hPG _ le_rfl))).1
  have hbalance := epochReportBalance_step_on F A I κ (a/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) eps rate allocation R
    L (ipmQualityErrorBits I.m U k) K i P Q hDetect heps.le hvalidP hvalidQ hbudget hanalytic.2.2.2.2.2 hstep hmove
  have hcharge := (epoch_iteration_movement_charge_on A.eraseFailure P.history P.eta P.op (2*i) κ (a/8)
    ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) eps hDetect hvalidP heps.le es _ _ actual hset hvalid).2
  rw [← hist,← heta,← hop,hindex] at hcharge
  refine ⟨⟨hs,hsched,hc,hinput,?_,hbalance⟩,hhidden⟩
  intro e he
  have hG := hQ.2.2.2.2.2.2.2.2.1 _ le_rfl
  have hmem : e∈(Q.history.G (2*(i+1))).E := by rw [hG]; exact Finset.mem_range.mpr he
  exact (hcharge e hmem).trans (add_le_add_right hmove eps)

/-- Advance the analytic invariant along a successful machine step of
Algorithm 7 (Chen et al., arXiv:2203.00671v2, page 69). The current
hidden witness uses only the old progress and the newly read inputs. -/
theorem epoch_accepted_analytic_widened_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U k : ℕ) (κ target r : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ)
      (κ*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (L : EpochLayout) (K i : ℕ) (P Q : EpochPoint R.τ) (capacity : ℝ) (fstar : Fin I.m → ℝ)
    {initialMem : ℕ → ℕ} {initialHeap space finish : ℕ}
    (hP : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish i P)
    (hQ : EpochConditions F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K initialMem initialHeap space finish (i+1) Q)
    (hstep : EpochAcceptedStep F A I κ (Num.IPM.alphaPrime I.m U/8) rate allocation R L
      (ipmQualityErrorBits I.m U k) K i P Q)
    (hanalytic : EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) i P)
    (hstatic : EpochStaticInputsAt F I U (ipmQualityRangeExponent I.m U k) κ (Num.IPM.alphaPrime I.m U/8) (κ*Num.IPM.alphaPrime I.m U/1024)
      L capacity ((25/32:ℝ)*(κ*Num.IPM.alphaPrime I.m U/32)^2/50) P.machine.mem)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r P.machine.mem)
    (hm : 0<I.m) (hi : i≤ I.m) (hU : 0<U) (hsize : 2≤ I.m*U) (hnums : NumbersBounded I U)
    (hstar : I.IsFeasible fstar) (hF : I.cost fstar≤target) (hκ : 0<κ) (hκ' : κ≤1)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤κ*Num.IPM.alphaPrime I.m U)
    (hres : r=residual I target (epochVector F I P.machine.mem L.base)) (hr : 1/4<r)
    (hf : StrictlyInside I (epochVector F I P.machine.mem L.base))
    (hroute : I.Routes (epochVector F I P.machine.mem L.base))
    (hpot : potential I (Num.IPM.alphaPrime I.m U) target (epochVector F I P.machine.mem L.base)≤
      200*I.m*Real.log (I.m*(U:ℝ))) :
    EpochAnalyticPrefixAt I U (ipmQualityRangeExponent I.m U k) target κ r A (epochVector F I P.machine.mem L.base) (i+1) Q ∧
      Q.history.HiddenStable (2*(i+1)) (Num.IPM.alphaPrime I.m U/8) ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) :=
  epoch_accepted_analytic_widened_upTo_on F A I U k κ target r rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L K i P Q capacity fstar hP hQ hstep hanalytic
    hstatic hsource hm hi hU hsize hnums hstar hF hκ hκ' hxlo hres hr hf hroute hpot

end MinCostFlow.IPM.Machine
