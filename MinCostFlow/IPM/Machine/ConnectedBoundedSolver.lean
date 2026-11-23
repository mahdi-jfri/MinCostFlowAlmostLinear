module

public import MinCostFlow.IPM.Machine.BoundedSolver
public import MinCostFlow.IPM.Machine.ConnectedSolverModule
public import MinCostFlow.IPM.Machine.ConnectedSolverPositive
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import MinCostFlow.IPM.Machine.RoundCleanupProgram
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The bounded solver on connected graphs

Positive compressed inputs run the connected initializer and the
linked solver. The empty input branch returns immediately.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

private theorem connectedSolverNumericWidthAt_fits (r : SolverForestResources) (J : Circulation) {w : ℕ}
    (hs : 2^solverQualityForestNumericWidthAt r J.m (solverConnectedAugmented J).m<2^w) :
    let M := (solverConnectedAugmented J).m
    let V := solverPenalty J.m
    ipmQualityParameterWordBits M V r.qualityExponent≤w ∧ 2*(M*V^2)<2^w ∧
      targetTestLimit M V r.qualityExponent<2^w ∧ M.size+V.size<2^w ∧ r.qualityExponent<2^w := by
  dsimp only
  let M := (solverConnectedAugmented J).m
  let V := solverPenalty J.m
  let k := r.qualityExponent
  have hw : solverQualityForestNumericWidthAt r J.m M≤w := by
    by_contra hh
    have hge := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_of_not_ge hh)
    exact (not_lt_of_ge hge) hs
  change max (ipmQualityParameterWordBits M V r.qualityExponent) (max (2*(M*V^2)).size
    (max (targetTestLimit M V k).size (max (M.size+V.size).size k.size)))≤w at hw
  obtain ⟨hF,hh⟩ := max_le_iff.mp hw
  obtain ⟨hB,hh⟩ := max_le_iff.mp hh
  obtain ⟨hT,hh⟩ := max_le_iff.mp hh
  obtain ⟨hS,hK⟩ := max_le_iff.mp hh
  exact ⟨hF,Nat.size_le.mp hB,Nat.size_le.mp hT,Nat.size_le.mp hS,Nat.size_le.mp hK⟩

private theorem boundedConnectedIPMRuntime_unpack (withV : Bool) {b : ℕ} {p : Program}
    (e : SolverDispatch)
    (hModule : p.HasAt b (cond withV (boundedConnectedIPMRuntimeModuleWithV b e)
      (boundedConnectedIPMRuntimeModule b e))) :
    let graph := b+14
    let alpha := graph+(connectedGraphModule graph).length
    let flow := alpha+(qualityPrecisionAlphaModule alpha).length
    let named := flow+(initialFlowModule flow 4).length
    let coefficients := named+(namedGraphModule named).length
    let signed := coefficients+(coefficientTablesModule coefficients 4).length
    let norm := signed+(signedGuardConstantsModule signed).length
    let search := norm+(normalizationModule norm).length
    let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
    p.procs[b]?=some (boundedIPMBody (b+1)) ∧
      p.procs[b+1]?=some (solverPositiveRuntimeBody e.quality (b+2) (b+13) (b+3)) ∧
      p.procs[b+2]?=some solverPenaltyBody ∧
      p.procs[b+4]?=some (solverSearchSetupBody named coefficients (b+5)) ∧
      p.procs[b+5]?=some (solverGuardTablesBody signed norm) ∧
      p.procs[b+6]?=some workspaceBody ∧
      p.procs[b+7]?=some (solverLimitsBody (b+11) (b+8) (b+9)) ∧
      p.procs[b+8]?=some (targetTestLimitBody (b+12)) ∧
      p.procs[b+9]?=some (targetSearchRoundsBody (b+11)) ∧
      p.procs[b+11]?=some (Num.IPM.bitLengthBody (b+11)) ∧
      p.procs[b+12]?=some iterationBudgetBody ∧
      p.procs[b+13]?=some (solverQualityInitializeBody e.quality (b+2) graph alpha flow) ∧
      p.HasAt graph (connectedGraphModule graph) ∧
      p.HasAt alpha (qualityPrecisionAlphaModule alpha) ∧
      p.HasAt flow (initialFlowModule flow 4) ∧
      p.HasAt named (namedGraphModule named) ∧
      p.HasAt coefficients (coefficientTablesModule coefficients 4) ∧
      p.HasAt signed (signedGuardConstantsModule signed) ∧
      p.HasAt norm (normalizationModule norm) ∧
      p.HasAt recover (solverRoundModule recover e.forestInit e.forestOp) ∧
      (withV = false →
        p.procs[b+3]?=some (solverAfterInitBody (b+4) (b+6) (b+7) (b+10)) ∧
        p.procs[b+10]?=some (solverSearchRecoverBody search recover) ∧
        p.HasAt search (solverSearchModule search e.cycleInit e.cycleOp)) ∧
      (withV = true →
        p.procs[b+3]?=some (solverAfterInitBodyWithV (b+4) (b+6) (b+7) (b+10)) ∧
        p.procs[b+10]?=some (solverSearchRecoverBodyWithV search recover) ∧
        p.HasAt search (solverSearchModuleWithV search e.cycleInit e.cycleOp)) := by
  dsimp only
  cases withV
  · change p.HasAt b (boundedConnectedIPMRuntimeModule b e) at hModule
    have hCtl := Num.hasAt_append_left hModule
    have hAux := Num.hasAt_append_right hModule
    unfold connectedSolverOwnModules at hAux
    have hInitAt := (Num.hasAt_append_left hAux).head
    have hAux₀ := Num.hasAt_append_right hAux
    have hAux₁ := Num.hasAt_append_right hAux₀
    have hAux₂ := Num.hasAt_append_right hAux₁
    have hAux₃ := Num.hasAt_append_right hAux₂
    have hAux₄ := Num.hasAt_append_right hAux₃
    have hAux₅ := Num.hasAt_append_right hAux₄
    have hAux₆ := Num.hasAt_append_right hAux₅
    have hAux₇ := Num.hasAt_append_right hAux₆
    have hAux₈ := Num.hasAt_append_right hAux₇
    exact ⟨hCtl 0 (by change 0 < 13; decide), hCtl 1 (by change 1 < 13; decide),
      hCtl 2 (by change 2 < 13; decide), hCtl 4 (by change 4 < 13; decide),
      hCtl 5 (by change 5 < 13; decide), hCtl 6 (by change 6 < 13; decide),
      hCtl 7 (by change 7 < 13; decide), hCtl 8 (by change 8 < 13; decide),
      hCtl 9 (by change 9 < 13; decide), hCtl 11 (by change 11 < 13; decide),
      hCtl 12 (by change 12 < 13; decide), hInitAt,
      Num.hasAt_append_left hAux₀, Num.hasAt_append_left hAux₁, Num.hasAt_append_left hAux₂,
      Num.hasAt_append_left hAux₃, Num.hasAt_append_left hAux₄, Num.hasAt_append_left hAux₅,
      Num.hasAt_append_left hAux₆, hAux₈,
      (fun _ => ⟨hCtl 3 (by change 3 < 13; decide), hCtl 10 (by change 10 < 13; decide),
        Num.hasAt_append_left hAux₇⟩),
      (fun hEq => by cases hEq)⟩
  · change p.HasAt b (boundedConnectedIPMRuntimeModuleWithV b e) at hModule
    have hCtl := Num.hasAt_append_left hModule
    have hAux := Num.hasAt_append_right hModule
    unfold connectedSolverOwnModulesWithV at hAux
    have hInitAt := (Num.hasAt_append_left hAux).head
    have hAux₀ := Num.hasAt_append_right hAux
    have hAux₁ := Num.hasAt_append_right hAux₀
    have hAux₂ := Num.hasAt_append_right hAux₁
    have hAux₃ := Num.hasAt_append_right hAux₂
    have hAux₄ := Num.hasAt_append_right hAux₃
    have hAux₅ := Num.hasAt_append_right hAux₄
    have hAux₆ := Num.hasAt_append_right hAux₅
    have hAux₇ := Num.hasAt_append_right hAux₆
    have hAux₈ := Num.hasAt_append_right hAux₇
    exact ⟨hCtl 0 (by change 0 < 13; decide), hCtl 1 (by change 1 < 13; decide),
      hCtl 2 (by change 2 < 13; decide), hCtl 4 (by change 4 < 13; decide),
      hCtl 5 (by change 5 < 13; decide), hCtl 6 (by change 6 < 13; decide),
      hCtl 7 (by change 7 < 13; decide), hCtl 8 (by change 8 < 13; decide),
      hCtl 9 (by change 9 < 13; decide), hCtl 11 (by change 11 < 13; decide),
      hCtl 12 (by change 12 < 13; decide), hInitAt,
      Num.hasAt_append_left hAux₀, Num.hasAt_append_left hAux₁, Num.hasAt_append_left hAux₂,
      Num.hasAt_append_left hAux₃, Num.hasAt_append_left hAux₄, Num.hasAt_append_left hAux₅,
      Num.hasAt_append_left hAux₆, hAux₈,
      (fun hEq => by cases hEq),
      (fun _ => ⟨hCtl 3 (by change 3 < 13; decide), hCtl 10 (by change 10 < 13; decide),
        Num.hasAt_append_left hAux₇⟩)⟩

set_option maxHeartbeats 900000 in
private theorem boundedConnectedIPMRuntime_meetsForestContract_core (withV : Bool) {w b : ℕ} {p : Program}
    (r : SolverForestRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (cond withV (boundedConnectedIPMRuntimeModuleWithV b e)
      (boundedConnectedIPMRuntimeModule b e)))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          cond withV
            (SolverQualityForestDataStructuresWithVAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)
            (SolverQualityForestDataStructuresAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD)) :
    MeetsContract w p b { Scaling.Machine.solverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)).pre args mem ∧
          (Scaling.Machine.solverDimensions args mem).1 ≤ 2 *
            (Scaling.Machine.solverDimensions args mem).2 + 1 } := by
  let graph := b+14
  let alpha := graph+(connectedGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  obtain ⟨hEntry, hPosAt, hPenAt, hSetupAt, hGuardsAt, hWorkAt0, hLimitsAt, hLimitAt, hRoundsAt,
    hBitsAt0, hBudgetAt0, hInitAt, hGraphAt, hAlphaAt, hFlowAt, hNamedAt, hCoeffAt, hSignedAt, hNormAt,
    hRecoverAt, hFalse, hTrue⟩ := boundedConnectedIPMRuntime_unpack withV e hModule
  have hPenalty := solverPenalty_meetsContract (w:=w) hPenAt
  have hGuards := solverQualityGuardTables_meetsContract (w:=w) hGuardsAt hSignedAt hNormAt
  have hWorkAt : p.HasAt (b+6) workspaceModule := fun j hj => by
    have : j = 0 := by change j < 1 at hj; omega
    subst this; exact hWorkAt0
  have hBitsAt : p.HasAt (b+11) (Num.IPM.bitLengthModule (b+11)) := fun j hj => by
    have : j = 0 := by change j < 1 at hj; omega
    subst this; exact hBitsAt0
  have hBudgetAt : p.HasAt (b+12) iterationBudgetModule := fun j hj => by
    have : j = 0 := by change j < 1 at hj; omega
    subst this; exact hBudgetAt0
  have hBudget := iterationBudget_meetsContract (w:=w) hBudgetAt
  apply meetsContract_of_runs hEntry
  intro args mem pos ω hWordsIn hpre
  obtain ⟨⟨a,h,rfl,J,hat,hend,hWords,hCost,hSpace,hCap⟩,hZero,_⟩ := hpre.1
  change ZeroFrom mem h at hZero
  have hSize := J.solverWords_length
  have hReadM := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  have hOne : 1<2^w := by omega
  have ha1 : a+1<2^w := by omega
  have hDimensions := Scaling.Machine.solverDimensions_of_at J mem a h hat
  let st := startState [a,h] mem pos
  have hTest : Expr.eval w st (.load (.bin .add (.reg 0) (.const 1)))=some J.m :=
    Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hOne) ha1) hReadM
  by_cases hm : J.m=0
  · have hr : Runs w p ω (.ret (.reg 1)) st (.returned h) st 2 :=
      runs_ret_iff.mpr ⟨h,rfl,rfl,rfl,rfl⟩
    have hRun : Runs w p ω (boundedIPMBody (b+1)) st (.returned h) st 7 := by
      apply runs_cond_iff.mpr
      exact ⟨J.m,2,hTest,by rw [ite_eq_left hm]; exact hr,rfl⟩
    refine ⟨.returned h,st,7,hRun,⟨?_,?_,?_,hZero,?_⟩,?_⟩
    · exact le_rfl
    · change h≤h+_
      exact Nat.le_add_right _ _
    · intro _ _
      rfl
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact emptyCirculation_optimal K hm _
    · change 7≤forestConnectedSolverRuntimeTime r _ _
      rw [hDimensions]
      unfold forestConnectedSolverRuntimeTime
      omega
  · have hm' : 0 < J.m := Nat.pos_of_ne_zero hm
    have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
    have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
    let M := (solverConnectedAugmented J).m
    let res := r.forSize M
    let k := r.qualityExponent M
    have hAllowed := hpre.2
    change (Scaling.Machine.solverDimensions [a,h] mem).1 ≤ 2 *
      (Scaling.Machine.solverDimensions [a,h] mem).2 + 1 at hAllowed
    rw [hDimensions] at hAllowed
    obtain ⟨hWS,hWidth,hTS⟩ := forestConnectedSolverRuntimeWorkspace_covers r J hAllowed hm' hp
    obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ :=
      connectedSolverNumericWidthAt_fits (w:=w) res J (hWidth.trans_lt (by omega))
    obtain ⟨C,RC,RD,hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
    have h14 := (ipm_quality_parameter_words_fit (solverConnectedAugmented J).m (solverPenalty J.m) k hw).1
    have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
    have hTwo : 2<2^w := by omega
    have hWork := workspace_meetsContract h409 hWorkAt
    have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
    have hLimitProc := targetTestLimit_meetsContract hLimitAt hBudget hOne
    have hRoundsProc := targetSearchRounds_meetsContract hRoundsAt hBit hTwo
    have hLimitsProc := solverLimits_meetsContract hLimitsAt hBit hLimitProc hRoundsProc
    have hInit := connectedSolverInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J r.qualityExponent r.qualityCost hQuality hkW
    have hSetup := solverQualitySearchSetup_meetsContract hSetupAt hNamedAt hCoeffAt hGuards
      (solverConnectedAugmented J) (solverPenalty J.m) k
    have hSpace' : h+J.m+forestConnectedSolverWorkspaceAt res J.n J.m (solverConnectedAugmented J).m<2^w := by
      exact (Nat.add_le_add_left hWS _).trans_lt hSpace
    obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :
        ∃ out final c, Runs w p ω (solverPositiveRuntimeBody e.quality (b+2) (b+13) (b+3))
          (startState [a,h] mem pos) (.returned out) final c ∧
          J.Optimal (fun e => (J.readSolverFlow final.mem h e:ℝ)) ∧ h+J.m≤out ∧
          out≤h+J.m+forestConnectedSolverWorkspaceAt res J.n J.m (solverConnectedAugmented J).m ∧
          ZeroFrom final.mem out ∧ (∀ x<h,final.mem x=mem x) ∧
          c+12≤forestConnectedSolverTimeAt res J.n J.m (solverConnectedAugmented J).m + 2 * r.qualityCost (solverConnectedAugmented J).m := by
      cases withV
      · obtain ⟨hAfterAt, hFinishAt, hSearchAt⟩ := hFalse rfl
        exact connectedForestSolverPositive_runs_on res e C D hD RC RD J r.qualityExponent r.qualityCost hQuality rfl hm' hp hCost hu hw hDS hSearchAt hRecoverAt
          hFinishAt hAfterAt hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
          hat hend hWords hZero hRadius hLimit hBits hkW hSpace'
      · obtain ⟨hAfterAt, hFinishAt, hSearchAt⟩ := hTrue rfl
        exact connectedForestSolverPositiveWithV_runs_on res e C D hD RC RD J r.qualityExponent r.qualityCost hQuality rfl hm' hp hCost hu hw hDS hSearchAt hRecoverAt
          hFinishAt hAfterAt hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
          hat hend hWords hZero hRadius hLimit hBits hkW hSpace'
    have hCall := round_returning_call (dst:=2) hPosAt
      (show evalArgs w st [.reg 0,.reg 1]=some [a,h] from rfl) hRun
    let final' : State := ⟨final.mem,Function.update st.regs 2 out,final.pos⟩
    have hret : Runs w p ω (.ret (.reg 2)) final' (.returned out) final' 2 :=
      runs_ret_iff.mpr ⟨out,rfl,rfl,rfl,rfl⟩
    have hPositive : Runs w p ω (.call 2 (b+1) [.reg 0,.reg 1] ;; .ret (.reg 2))
        st (.returned out) final' (c+6) :=
      runs_seq_iff.mpr (Or.inr ⟨final',2+c+1,2,hCall,hret,by omega⟩)
    have hAll : Runs w p ω (boundedIPMBody (b+1)) st (.returned out) final' (c+11) := by
      apply runs_cond_iff.mpr
      exact ⟨J.m,c+6,hTest,by rw [ite_eq_right hm]; exact hPositive,by
        simp only [Expr.size_load,Expr.size_bin,Expr.size_reg,Expr.size_const]; omega⟩
    refine ⟨.returned out,final',c+11,hAll,⟨?_,?_,hFrame,hFresh,?_⟩,?_⟩
    · exact (Nat.le_add_right _ _).trans hLo
    · change out≤h+((Scaling.Machine.solverDimensions [a,h] mem).2+
        forestConnectedSolverRuntimeWorkspace r (Scaling.Machine.solverDimensions [a,h] mem).1
          (Scaling.Machine.solverDimensions [a,h] mem).2)
      rw [hDimensions]
      change out≤h+(J.m+forestConnectedSolverRuntimeWorkspace r J.n J.m)
      change out ≤ h+J.m+forestConnectedSolverWorkspaceAt (r.forSize (solverConnectedAugmented J).m) J.n J.m (solverConnectedAugmented J).m at hHi
      exact hHi.trans (by omega)
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact hOpt
    · change c+11≤forestConnectedSolverRuntimeTime r _ _
      rw [hDimensions]
      exact ((show c+11≤c+12 by omega).trans hTime).trans hTS

/-- The bounded IPM with runtime quality meets the shared solver contract
for `SolverForestRuntimeResources` and the quality procedure at dispatched addresses. -/
private theorem boundedConnectedIPMRuntime_meetsForestContract_on {w b : ℕ} {p : Program}
    (r : SolverForestRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityForestDataStructuresAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b { Scaling.Machine.solverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)).pre args mem ∧
          (Scaling.Machine.solverDimensions args mem).1 ≤ 2 *
            (Scaling.Machine.solverDimensions args mem).2 + 1 } :=
  boundedConnectedIPMRuntime_meetsForestContract_core false r e D hD hModule hQuality hSupported

private theorem boundedConnectedIPMRuntimeWithV_meetsForestContract_on {w b : ℕ} {p : Program}
    (r : SolverForestRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityForestDataStructuresWithVAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b { Scaling.Machine.solverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)).pre args mem ∧
          (Scaling.Machine.solverDimensions args mem).1 ≤ 2 *
            (Scaling.Machine.solverDimensions args mem).2 + 1 } :=
  boundedConnectedIPMRuntime_meetsForestContract_core true r e D hD hModule hQuality hSupported

/-- The bounded IPM with runtime quality meets the compressed solver contract
for `L`- and `w`-aware forest data structures (`SolverForestRuntimeResources`). -/
theorem boundedConnectedIPMRuntime_meetsForestCompressedContract {w b : ℕ} {p : Program}
    (r : SolverForestRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityForestDataStructuresAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)) :=
  boundedConnectedIPMRuntime_meetsForestContract_on r e D hD hModule hQuality hSupported

/-- The bounded IPM with runtime quality meets the compressed solver contract
for connected data structures and the quality procedure at the dispatched addresses. -/
theorem boundedConnectedIPMRuntime_meetsConnectedCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityConnectedDataStructuresAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (connectedSolverRuntimeTime r) (connectedSolverRuntimeWorkspace r)) :=
  boundedConnectedIPMRuntime_meetsForestCompressedContract r.toForest e D hD hModule hQuality
    (fun J hAllowed hm' hCost hCap hw =>
      let ⟨C, RC, RD, hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
      ⟨C, RC, RD, hDS.toForest⟩)

/-- The bounded IPM with runtime quality meets the compressed solver contract
for the data structures and quality procedure at the dispatched addresses. -/
theorem boundedConnectedIPMRuntime_meetsCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (connectedSolverRuntimeTime r) (connectedSolverRuntimeWorkspace r)) :=
  boundedConnectedIPMRuntime_meetsConnectedCompressedContract r e D hD hModule hQuality
    (fun J hAllowed hm' hCost hCap hw =>
      let ⟨C, RC, RD, hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
      ⟨C, RC, RD, hDS.toConnected⟩)

/-- `V`-passing variant of `boundedConnectedIPMRuntime_meetsForestCompressedContract`. -/
theorem boundedConnectedIPMRuntimeWithV_meetsForestCompressedContract {w b : ℕ} {p : Program}
    (r : SolverForestRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityForestDataStructuresWithVAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (forestConnectedSolverRuntimeTime r) (forestConnectedSolverRuntimeWorkspace r)) :=
  boundedConnectedIPMRuntimeWithV_meetsForestContract_on r e D hD hModule hQuality hSupported

/-- `V`-passing variant of `boundedConnectedIPMRuntime_meetsConnectedCompressedContract`. -/
theorem boundedConnectedIPMRuntimeWithV_meetsConnectedCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityConnectedDataStructuresWithVAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (connectedSolverRuntimeTime r) (connectedSolverRuntimeWorkspace r)) :=
  boundedConnectedIPMRuntimeWithV_meetsForestCompressedContract r.toForest e D hD hModule hQuality
    (fun J hAllowed hm' hCost hCap hw =>
      let ⟨C, RC, RD, hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
      ⟨C, RC, RD, hDS.toForest⟩)

/-- `V`-passing variant of `boundedConnectedIPMRuntime_meetsCompressedContract`. -/
theorem boundedConnectedIPMRuntimeWithV_meetsCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedConnectedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverConnectedAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresWithVAt w p e (r.forSize (solverConnectedAugmented J).m) (solverConnectedAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (connectedSolverRuntimeTime r) (connectedSolverRuntimeWorkspace r)) :=
  boundedConnectedIPMRuntimeWithV_meetsConnectedCompressedContract r e D hD hModule hQuality
    (fun J hAllowed hm' hCost hCap hw =>
      let ⟨C, RC, RD, hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
      ⟨C, RC, RD, hDS.toConnected⟩)

end MinCostFlow.IPM.Machine
