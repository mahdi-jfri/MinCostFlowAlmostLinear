module

public import MinCostFlow.IPM.Machine.SolverSearchLink
import MinCostFlow.Num.ModulePlacement
import Mathlib.Tactic

/-!
# Verification of `solverSearchModuleWithV`

The `V`-passing bisection module mirrors `solverSearchModule_runs_*`
with `minRatioMachineContractWithV` and `V` passed in index 26.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
/-- `V`-passing variant of `solverSearchModule_runs_upTo`. -/
theorem solverSearchModuleWithV_runs_upTo {w b init : ℕ} {p : Program} {op : ℕ → ℕ}
    (I : Instance) (U k V : ℕ) (hw : ipmParameterWordBits I.m U≤w)
    (A : MinRatioDataStructureWithFailure) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (hp : p.HasAt b (solverSearchModuleWithV b init op))
    (hA : MinRatioSpecWithFailureUpTo A (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8)
      (precisionHiddenPsi I.m U) ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (himpl : R.Implements w p init op (minRatioMachineContractWithV (ipmMinRatioFormat I.m U hw)
      A (namedInstance I) I.m V (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (old : EpochLayout) (qp source heap B : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs (ipmMinRatioFormat I.m U hw) I old qp qp heap (1/4)
      ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow (ipmMinRatioFormat I.m U hw) I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector (ipmMinRatioFormat I.m U hw) I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector (ipmMinRatioFormat I.m U hw) I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old (ipmMinRatioFormat I.m U hw) I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace (ipmMinRatioFormat I.m U hw) I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0 < I.m) (hU : 0 < U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let F := ipmMinRatioFormat I.m U hw
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV (b+1))
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate := by
  let F := ipmMinRatioFormat I.m U hw
  let q := ipmErrorBits I.m U
  let K := gradientCoefficientExponent I.m U
  let κ := (1:ℝ)/(2:ℝ)^k
  have hCtl := Num.hasAt_append_left hp
  have hLen : (solverSearchControlWithV b init op).length=33 := rfl
  have atCtl (j : Fin 33) : p.procs[b+j.val]?=
      some ((solverSearchControlWithV b init op)[j.val]'(by rw [hLen]; exact j.isLt)) :=
    hCtl _ _
  let residual := b+33
  let store := residual+(epochResidualModule residual 4).length
  let status := store+(storeCoordinateModule store 4).length
  let batch := status+(coefficientStatusModule status 4).length
  let scalarRange := batch+(detectBatchModule batch).length
  let refreshArrays := scalarRange+(coefficientRangeGuardModule scalarRange 4).length
  let integer := refreshArrays+(coefficientRefreshModule refreshArrays 4).length
  have aux := Num.hasAt_append_right hp
  change p.HasAt residual (solverSearchAux residual) at aux
  unfold solverSearchAux at aux
  have hAux₁ := Num.hasAt_append_right aux
  have hAux₂ := Num.hasAt_append_right hAux₁
  have hAux₃ := Num.hasAt_append_right hAux₂
  have hAux₄ := Num.hasAt_append_right hAux₃
  have hAux₅ := Num.hasAt_append_right hAux₄
  have hAux₆ := Num.hasAt_append_right hAux₅
  have hResidualAt : p.HasAt residual (epochResidualModule residual 4) := Num.hasAt_append_left aux
  have hStoreAt : p.HasAt store (storeCoordinateModule store 4) := Num.hasAt_append_left hAux₁
  have hStatusAt : p.HasAt status (coefficientStatusModule status 4) := Num.hasAt_append_left hAux₂
  have hBatchAt : p.HasAt batch (detectBatchModule batch) := Num.hasAt_append_left hAux₃
  have hGuardAt : p.HasAt scalarRange (coefficientRangeGuardModule scalarRange 4) := Num.hasAt_append_left hAux₄
  have hRefreshAt : p.HasAt refreshArrays (coefficientRefreshModule refreshArrays 4) := Num.hasAt_append_left hAux₅
  have hIntegerAt : p.HasAt integer (fixedIntegerBlockModule integer 4) := hAux₆
  have hw14 := (ipm_parameter_words_fit I.m U hw).1
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hw14)
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  have h4 : 0 < (4:ℕ) := by decide
  have h10 : 2*4+2≤w := by omega
  have hBase : Num.base 4<2^w := h16
  have hCopyAt : p.HasAt (b+30) [copyWords] := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+30]?=some copyWords; exact atCtl ⟨30,by decide⟩
  have hCopy := copyWords_meetsContract (w:=w) hCopyAt
  have hFlowCopy := epochFlowCopy_meetsContract (atCtl 31) hCopy
  have hResidual := epochResidualModule_meetsContract h4 h10 h2 hBase hResidualAt
  have hEpochBase := epochBase_meetsContract (atCtl 4) hResidual hFlowCopy
  have hStore := storeCoordinate_meetsContract h4 h10 hStoreAt
  have hStatus := coefficientStatus_meetsContract (q:=q) (K:=K) h4 hw14 hStatusAt
  have hFlagAt : p.HasAt (b+32) flagRecordModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+32]?=some flagRecordBody; exact atCtl ⟨32,by decide⟩
  have hFlag := flagRecord_meetsContract (w:=w) hFlagAt
  have hRecord := reportStatus_meetsContract (w:=w) (atCtl 11)
  have hRecord₂ := boundedStatusRecord_meetsContract (w:=w) (limit:=2) (atCtl 11)
  have hSnapshot (s : A.State) := detectSnapshot_meetsContract hCopy (atCtl 7) (A.detect s).1
  have hBatch (s : A.State) := detectBatch_meetsContract (by omega : 5<2^w) I (A.detect s).1 hBatchAt
  have hRange := coefficientRangeGuard_meetsContract h4 h1 hBase hGuardAt
  have hFullScan := coefficientRangeFull_meetsContract hRange (atCtl 23)
  have hList := coefficientRangeList_meetsContract hRange (atCtl 27)
  have hReport (s : A.State) := coefficientRangeReport_meetsContract hList hRecord (atCtl 16) (A.detect s).1
  have hBudget := epochBudgetRecord_meetsContract (atCtl 18) hRecord
  have hArrays := coefficientRefresh_meetsContract (q:=q) (K:=K) h4 hw14 hRefreshAt
  have hNamesAt : p.HasAt (b+25) vertexNamesModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+25]?=some vertexNamesBody; exact atCtl ⟨25,by decide⟩
  have hNames := vertexNames_meetsContract h1 hNamesAt
  have hInitBudget := epochBudgetInit_meetsContract (atCtl 26) hBudget
  have hInteger := fixedIntegerBlock_meetsContract h4 h10 hIntegerAt
  have hGuess := targetGuess_meetsContract (atCtl 29) hInteger h1
  exact targetSearch_runs_withV_upTo I U k V hw A rate allocation R F q K κ hA hEpochBase himpl
    (atCtl 5) (atCtl 6) hStore (atCtl 8) hStatus hFlag (atCtl 9) (atCtl 10) hRecord
    (atCtl 12) hSnapshot hBatchAt.head hBatch (atCtl 13) (atCtl 14) (atCtl 15) (atCtl 16)
    hReport (atCtl 17) hBudget (atCtl 19) (atCtl 20) (atCtl 21) hRecord₂ hArrays
    hFullScan (atCtl 22) (atCtl 24) hNames hInitBudget (atCtl 28)
    (atCtl 3) (atCtl 2) hGuess (atCtl 1)
    old qp source heap B mem pos ω rfl rfl rfl rfl hE hfixed hflow hhalf hwords hV
    hRadius hRound halloc hLimit hspace hz hm hU hsize hk hI hnums hLower

/-- `V`-passing variant of `solverSearchModule_runs`. -/
theorem solverSearchModuleWithV_runs {w b init : ℕ} {p : Program} {op : ℕ → ℕ}
    (I : Instance) (U k V : ℕ) (hw : ipmParameterWordBits I.m U≤w)
    (A : MinRatioDataStructureWithFailure) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (hp : p.HasAt b (solverSearchModuleWithV b init op))
    (hA : MinRatioSpecWithFailure A (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8)
      (precisionHiddenPsi I.m U) ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/1024))
    (himpl : R.Implements w p init op (minRatioMachineContractWithV (ipmMinRatioFormat I.m U hw)
      A (namedInstance I) I.m V (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (old : EpochLayout) (qp source heap B : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hE : old.exponent=ipmRangeExponent I.m U)
    (hfixed : TargetFixedInputs (ipmMinRatioFormat I.m U hw) I old qp qp heap (1/4)
      ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow (ipmMinRatioFormat I.m U hw) I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector (ipmMinRatioFormat I.m U hw) I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector (ipmMinRatioFormat I.m U hw) I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old (ipmMinRatioFormat I.m U hw) I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace (ipmMinRatioFormat I.m U hw) I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0 < I.m) (hU : 0 < U) (hsize : 2≤I.m*U)
    (hk : k≤slackRangeExponent I.m U) (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let F := ipmMinRatioFormat I.m U hw
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV (b+1))
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate :=
  solverSearchModuleWithV_runs_upTo I U k V hw A rate allocation R hp
    (hA.upTo I.m I.n) himpl old qp source heap B mem pos ω hE hfixed
    hflow hhalf hwords hV hRadius hRound halloc hLimit hspace hz hm hU hsize hk hI hnums hLower

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- `V`-passing variant of `solverSearchModule_runs_widened_upTo_on`. -/
theorem solverSearchModuleWithV_runs_widened_upTo_on {w b init : ℕ} {p : Program} {op : ℕ → ℕ}
    {P : MGraph → (ℕ → ℝ) → Prop} (I : Instance) (U k V : ℕ) (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (hp : p.HasAt b (solverSearchModuleWithV b init op))
    (hA : MinRatioSpecWithFailureUpToOn P A (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (hP : StageAdmits P (namedInstance I) (ipmQualityRangeExponent I.m U k))
    (himpl : R.Implements w p init op (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m U k hw)
      A (namedInstance I) I.m V (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (old : EpochLayout) (qp source heap B : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs (ipmQualityMinRatioFormat I.m U k hw) I old qp qp heap (1/4)
      ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow (ipmQualityMinRatioFormat I.m U k hw) I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old (ipmQualityMinRatioFormat I.m U k hw) I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace (ipmQualityMinRatioFormat I.m U k hw) I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0 < I.m) (hU : 0 < U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let F := ipmQualityMinRatioFormat I.m U k hw
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV (b+1))
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate := by
  let F := ipmQualityMinRatioFormat I.m U k hw
  let q := ipmQualityErrorBits I.m U k
  let K := gradientCoefficientExponent I.m U
  let κ := (1:ℝ)/(2:ℝ)^k
  have hCtl := Num.hasAt_append_left hp
  have hLen : (solverSearchControlWithV b init op).length=33 := rfl
  have atCtl (j : Fin 33) : p.procs[b+j.val]?=
      some ((solverSearchControlWithV b init op)[j.val]'(by rw [hLen]; exact j.isLt)) :=
    hCtl _ _
  let residual := b+33
  let store := residual+(epochResidualModule residual 4).length
  let status := store+(storeCoordinateModule store 4).length
  let batch := status+(coefficientStatusModule status 4).length
  let scalarRange := batch+(detectBatchModule batch).length
  let refreshArrays := scalarRange+(coefficientRangeGuardModule scalarRange 4).length
  let integer := refreshArrays+(coefficientRefreshModule refreshArrays 4).length
  have aux := Num.hasAt_append_right hp
  change p.HasAt residual (solverSearchAux residual) at aux
  unfold solverSearchAux at aux
  have hAux₁ := Num.hasAt_append_right aux
  have hAux₂ := Num.hasAt_append_right hAux₁
  have hAux₃ := Num.hasAt_append_right hAux₂
  have hAux₄ := Num.hasAt_append_right hAux₃
  have hAux₅ := Num.hasAt_append_right hAux₄
  have hAux₆ := Num.hasAt_append_right hAux₅
  have hResidualAt : p.HasAt residual (epochResidualModule residual 4) := Num.hasAt_append_left aux
  have hStoreAt : p.HasAt store (storeCoordinateModule store 4) := Num.hasAt_append_left hAux₁
  have hStatusAt : p.HasAt status (coefficientStatusModule status 4) := Num.hasAt_append_left hAux₂
  have hBatchAt : p.HasAt batch (detectBatchModule batch) := Num.hasAt_append_left hAux₃
  have hGuardAt : p.HasAt scalarRange (coefficientRangeGuardModule scalarRange 4) := Num.hasAt_append_left hAux₄
  have hRefreshAt : p.HasAt refreshArrays (coefficientRefreshModule refreshArrays 4) := Num.hasAt_append_left hAux₅
  have hIntegerAt : p.HasAt integer (fixedIntegerBlockModule integer 4) := hAux₆
  have hw14 := (ipm_quality_parameter_words_fit I.m U k hw).1
  have h16 : 16<2^w := (by decide : 16<2^14).trans_le (Nat.pow_le_pow_right (by decide) hw14)
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  have h4 : 0 < (4:ℕ) := by decide
  have h10 : 2*4+2≤w := by omega
  have hBase : Num.base 4<2^w := h16
  have hCopyAt : p.HasAt (b+30) [copyWords] := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+30]?=some copyWords; exact atCtl ⟨30,by decide⟩
  have hCopy := copyWords_meetsContract (w:=w) hCopyAt
  have hFlowCopy := epochFlowCopy_meetsContract (atCtl 31) hCopy
  have hResidual := epochResidualModule_meetsContract h4 h10 h2 hBase hResidualAt
  have hEpochBase := epochBase_meetsContract (atCtl 4) hResidual hFlowCopy
  have hStore := storeCoordinate_meetsContract h4 h10 hStoreAt
  have hStatus := coefficientStatus_meetsContract (q:=q) (K:=K) h4 hw14 hStatusAt
  have hFlagAt : p.HasAt (b+32) flagRecordModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+32]?=some flagRecordBody; exact atCtl ⟨32,by decide⟩
  have hFlag := flagRecord_meetsContract (w:=w) hFlagAt
  have hRecord := reportStatus_meetsContract (w:=w) (atCtl 11)
  have hRecord₂ := boundedStatusRecord_meetsContract (w:=w) (limit:=2) (atCtl 11)
  have hSnapshot (s : A.State) := detectSnapshot_meetsContract hCopy (atCtl 7) (A.detect s).1
  have hBatch (s : A.State) := detectBatch_meetsContract (by omega : 5<2^w) I (A.detect s).1 hBatchAt
  have hRange := coefficientRangeGuard_meetsContract h4 h1 hBase hGuardAt
  have hFullScan := coefficientRangeFull_meetsContract hRange (atCtl 23)
  have hList := coefficientRangeList_meetsContract hRange (atCtl 27)
  have hReport (s : A.State) := coefficientRangeReport_meetsContract hList hRecord (atCtl 16) (A.detect s).1
  have hBudget := epochBudgetRecord_meetsContract (atCtl 18) hRecord
  have hArrays := coefficientRefresh_meetsContract (q:=q) (K:=K) h4 hw14 hRefreshAt
  have hNamesAt : p.HasAt (b+25) vertexNamesModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+25]?=some vertexNamesBody; exact atCtl ⟨25,by decide⟩
  have hNames := vertexNames_meetsContract h1 hNamesAt
  have hInitBudget := epochBudgetInit_meetsContract (atCtl 26) hBudget
  have hInteger := fixedIntegerBlock_meetsContract h4 h10 hIntegerAt
  have hGuess := targetGuess_meetsContract (atCtl 29) hInteger h1
  exact targetSearch_runs_withV_widened_upTo_on I U k V hw A rate allocation R F q K κ hA hP hEpochBase himpl
    (atCtl 5) (atCtl 6) hStore (atCtl 8) hStatus hFlag (atCtl 9) (atCtl 10) hRecord
    (atCtl 12) hSnapshot hBatchAt.head hBatch (atCtl 13) (atCtl 14) (atCtl 15) (atCtl 16)
    hReport (atCtl 17) hBudget (atCtl 19) (atCtl 20) (atCtl 21) hRecord₂ hArrays
    hFullScan (atCtl 22) (atCtl 24) hNames hInitBudget (atCtl 28)
    (atCtl 3) (atCtl 2) hGuess (atCtl 1)
    old qp source heap B mem pos ω rfl rfl rfl rfl hE hfixed hflow hhalf hwords hV
    hRadius hRound halloc hLimit hspace hz hm hU hsize hI hnums hLower

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- `V`-passing variant of `solverSearchModule_runs_widened_upTo`. -/
theorem solverSearchModuleWithV_runs_widened_upTo {w b init : ℕ} {p : Program} {op : ℕ → ℕ}
    (I : Instance) (U k V : ℕ) (hw : ipmQualityParameterWordBits I.m U k≤w)
    (A : MinRatioDataStructureWithFailure) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    (R : DSRep A.State) (hp : p.HasAt b (solverSearchModuleWithV b init op))
    (hA : MinRatioSpecWithFailureUpTo A (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8)
      ((ipmQualityRangeExponent I.m U k+slackRangeExponent I.m U+6 : ℕ) : ℝ) ((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/1024) I.m I.n)
    (himpl : R.Implements w p init op (minRatioMachineContractWithV (ipmQualityMinRatioFormat I.m U k hw)
      A (namedInstance I) I.m V (1/(2:ℝ)^k) (Num.IPM.alphaPrime I.m U/8) rate allocation))
    (old : EpochLayout) (qp source heap B : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hE : old.exponent=ipmQualityRangeExponent I.m U k)
    (hfixed : TargetFixedInputs (ipmQualityMinRatioFormat I.m U k hw) I old qp qp heap (1/4)
      ((25/32:ℝ)*((1/(2:ℝ)^k)*Num.IPM.alphaPrime I.m U/32)^2/50) (Num.IPM.alphaPrime I.m U) mem)
    (hflow : TargetStageFlow (ipmQualityMinRatioFormat I.m U k hw) I old.exponent source heap mem)
    (hhalf : ∀ e, (1/2:ℝ)≤epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e-(I.edge e).lower ∧
      (1/2:ℝ)≤(I.edge e).upper-epochVector (ipmQualityMinRatioFormat I.m U k hw) I mem source e)
    (hwords : ∀ z∈targetOffsetPacket old (ipmQualityMinRatioFormat I.m U k hw) I 0 qp source heap (targetTestLimit I.m U k) (I.m*U^2),z<2^w)
    (hV : V<2^w)
    (hRadius : 2*(I.m*U^2)<2^w)
    (hRound : targetSearchRounds (I.m*U^2)<2^w)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hLimit : targetTestLimit I.m U k<2^w)
    (hspace : heap+targetSearchSpace (ipmQualityMinRatioFormat I.m U k hw) I.m U k old.exponent B<2^w)
    (hz : ZeroFrom mem heap) (hm : 0 < I.m) (hU : 0 < U) (hsize : 2≤I.m*U)
    (hI : I.IsValid) (hnums : NumbersBounded I U)
    (hLower : ∀ e : Fin I.m,0≤(I.edge e).lower) :
    let F := ipmQualityMinRatioFormat I.m U k hw
    let limit := targetTestLimit I.m U k
    let radius := I.m*U^2
    ∃ v final cost, ∃ z : ℤ, ∃ fstar,
      Runs w p ω (targetSearchBodyWithV (b+1))
        (startState (targetOffsetPacket old F I 0 qp source heap limit radius++[targetSearchRounds radius,V]) mem pos)
        (.returned v) final cost ∧
      I.IsMinCostFlow fstar ∧ I.cost fstar=(z:ℝ) ∧
      TargetOffsetResult F I old.exponent heap v z z mem final.mem ∧ final.mem (v-1)=1 ∧
      v≤heap+targetSearchSpace F I.m U k old.exponent B ∧
      cost≤targetSearchCost F I.m U k old.exponent rate :=
  solverSearchModuleWithV_runs_widened_upTo_on I U k V hw A rate allocation R hp
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) himpl old qp source heap B mem pos ω hE hfixed
    hflow hhalf hwords hV hRadius hRound halloc hLimit hspace hz hm hU hsize hI hnums hLower

end MinCostFlow.IPM.Machine