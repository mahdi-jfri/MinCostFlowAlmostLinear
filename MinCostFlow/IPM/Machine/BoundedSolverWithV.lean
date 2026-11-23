module

public import MinCostFlow.IPM.Machine.BoundedSolver
public import MinCostFlow.IPM.Machine.SolverPositiveWithV
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic
import MinCostFlow.IPM.Machine.RoundCleanupProgram
import Mathlib.Tactic

/-!
# `V`-passing WordRAM bounded solver contracts

Companion to `BoundedSolver.lean` for modules whose min-ratio initializer
receives `[graph, g, l, limbs, precision, V, heap]`.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

private theorem boundedIPMWithV_driver_wrap {w b : ℕ} {p : Program}
    {timeFn spaceFn : ℕ → ℕ → ℕ} {allowed : ℕ → ℕ → Prop} {posBody : Stmt}
    (hEntry : p.procs[b]?=some (boundedIPMBody (b+1)))
    (hPosAt : p.procs[b+1]?=some posBody)
    (hZeroTime : ∀ n m, 7 ≤ timeFn n m)
    (hPosCase : ∀ (J : Circulation) (a h : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      allowed J.n J.m → 0 < J.m →
      ListAt mem a J.solverWords → a + J.solverWords.length ≤ h →
      (∀ x ∈ J.solverWords, x < 2^w) → J.CostsBounded (J.m^10) →
      h + J.m + spaceFn J.n J.m < 2^w → (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m^40) →
      ZeroFrom mem h → (Scaling.Machine.solverContract w timeFn spaceFn).pre [a, h] mem →
      ∃ out final c, Runs w p ω posBody (startState [a, h] mem pos) (.returned out) final c ∧
        J.Optimal (fun e => (J.readSolverFlow final.mem h e : ℝ)) ∧ h + J.m ≤ out ∧
        out ≤ h + J.m + spaceFn J.n J.m ∧ ZeroFrom final.mem out ∧
        (∀ x < h, final.mem x = mem x) ∧ c + 11 ≤ timeFn J.n J.m) :
    MeetsContract w p b { Scaling.Machine.solverContract w timeFn spaceFn with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w timeFn spaceFn).pre args mem ∧
          allowed (Scaling.Machine.solverDimensions args mem).1
            (Scaling.Machine.solverDimensions args mem).2 } := by
  apply meetsContract_of_runs hEntry
  intro args mem pos ω hWordsIn hpre
  obtain ⟨⟨a, h, rfl, J, hat, hend, hWords, hCost, hSpace, hCap⟩, hZero, _⟩ := hpre.1
  change ZeroFrom mem h at hZero
  have hSize := J.solverWords_length
  have hReadM := ((Scaling.Machine.solverWords_at_iff J mem a).mp hat).2.1
  have hOne : 1 < 2^w := by omega
  have ha1 : a + 1 < 2^w := by omega
  have hDimensions := Scaling.Machine.solverDimensions_of_at J mem a h hat
  let st := startState [a, h] mem pos
  have hTest : Expr.eval w st (.load (.bin .add (.reg 0) (.const 1))) = some J.m :=
    Expr.eval_load_of_eq (Expr.eval_add rfl (Expr.eval_const hOne) ha1) hReadM
  by_cases hm : J.m = 0
  · have hr : Runs w p ω (.ret (.reg 1)) st (.returned h) st 2 :=
      runs_ret_iff.mpr ⟨h, rfl, rfl, rfl, rfl⟩
    have hRun : Runs w p ω (boundedIPMBody (b+1)) st (.returned h) st 7 := by
      apply runs_cond_iff.mpr
      exact ⟨J.m, 2, hTest, by rw [ite_eq_left hm]; exact hr, rfl⟩
    refine ⟨.returned h, st, 7, hRun, ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl, hZero, ?_⟩, ?_⟩
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact emptyCirculation_optimal K hm _
    · change 7 ≤ timeFn _ _
      rw [hDimensions]
      exact hZeroTime J.n J.m
  · have hm' : 0 < J.m := Nat.pos_of_ne_zero hm
    have hAllowed := hpre.2
    change allowed (Scaling.Machine.solverDimensions [a, h] mem).1
      (Scaling.Machine.solverDimensions [a, h] mem).2 at hAllowed
    rw [hDimensions] at hAllowed
    obtain ⟨out, final, c, hRun, hOpt, hLo, hHi, hFresh, hFrame, hTime⟩ :=
      hPosCase J a h mem pos ω hAllowed hm' hat hend hWords hCost hSpace hCap hZero hpre.1
    have hCall := round_returning_call (dst := 2) hPosAt
      (show evalArgs w st [.reg 0, .reg 1] = some [a, h] from rfl) hRun
    let final' : State := ⟨final.mem, Function.update st.regs 2 out, final.pos⟩
    have hret : Runs w p ω (.ret (.reg 2)) final' (.returned out) final' 2 :=
      runs_ret_iff.mpr ⟨out, rfl, rfl, rfl, rfl⟩
    have hPositive : Runs w p ω (.call 2 (b+1) [.reg 0, .reg 1] ;; .ret (.reg 2))
        st (.returned out) final' (c + 6) :=
      runs_seq_iff.mpr (Or.inr ⟨final', 2 + c + 1, 2, hCall, hret, by omega⟩)
    have hAll : Runs w p ω (boundedIPMBody (b+1)) st (.returned out) final' (c + 11) := by
      apply runs_cond_iff.mpr
      exact ⟨J.m, c + 6, hTest, by rw [ite_eq_right hm]; exact hPositive, by
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega⟩
    refine ⟨.returned out, final', c + 11, hAll, ⟨?_, ?_, hFrame, hFresh, ?_⟩, ?_⟩
    · exact (Nat.le_add_right _ _).trans hLo
    · change out ≤ h + ((Scaling.Machine.solverDimensions [a, h] mem).2 +
        spaceFn (Scaling.Machine.solverDimensions [a, h] mem).1
          (Scaling.Machine.solverDimensions [a, h] mem).2)
      rw [hDimensions]
      exact hHi.trans (Nat.le_of_eq (Nat.add_assoc _ _ _))
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact hOpt
    · change c + 11 ≤ timeFn _ _
      rw [hDimensions]
      exact hTime

private theorem solverOwnModulesWithV_unpack {b : ℕ} {p : Program}
    (choose : Stmt) (e : SolverDispatch)
    (hModule : p.HasAt b (solverControlWithV b choose e ++ solverOwnModulesWithV b e)) :
    let graph := b+14
    let alpha := graph+(initialGraphModule graph).length
    let flow := alpha+(precisionAlphaModule alpha).length
    let named := flow+(initialFlowModule flow 4).length
    let coefficients := named+(namedGraphModule named).length
    let signed := coefficients+(coefficientTablesModule coefficients 4).length
    let norm := signed+(signedGuardConstantsModule signed).length
    let search := norm+(normalizationModule norm).length
    let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
    p.procs[b]?=some (boundedIPMBody (b+1)) ∧
      p.procs[b+1]?=some (solverPositiveBodyWith choose (b+2) (b+13) (b+3)) ∧
      p.procs[b+2]?=some solverPenaltyBody ∧
      p.procs[b+3]?=some (solverAfterInitBodyWithV (b+4) (b+6) (b+7) (b+10)) ∧
      p.procs[b+4]?=some (solverSearchSetupBody named coefficients (b+5)) ∧
      p.procs[b+5]?=some (solverGuardTablesBody signed norm) ∧
      p.procs[b+6]?=some workspaceBody ∧
      p.procs[b+7]?=some (solverLimitsBody (b+11) (b+8) (b+9)) ∧
      p.procs[b+8]?=some (targetTestLimitBody (b+12)) ∧
      p.procs[b+9]?=some (targetSearchRoundsBody (b+11)) ∧
      p.procs[b+10]?=some (solverSearchRecoverBodyWithV search recover) ∧
      p.procs[b+11]?=some (Num.IPM.bitLengthBody (b+11)) ∧
      p.procs[b+12]?=some iterationBudgetBody ∧
      p.procs[b+13]?=some (solverInitializeBody (b+2) graph alpha flow) ∧
      p.HasAt graph (initialGraphModule graph) ∧
      p.HasAt alpha (precisionAlphaModule alpha) ∧
      p.HasAt flow (initialFlowModule flow 4) ∧
      p.HasAt named (namedGraphModule named) ∧
      p.HasAt coefficients (coefficientTablesModule coefficients 4) ∧
      p.HasAt signed (signedGuardConstantsModule signed) ∧
      p.HasAt norm (normalizationModule norm) ∧
      p.HasAt search (solverSearchModuleWithV search e.cycleInit e.cycleOp) ∧
      p.HasAt recover (solverRoundModule recover e.forestInit e.forestOp) := by
  dsimp only
  have hCtl := Num.hasAt_append_left hModule
  have atCtl (j : Fin 13) : p.procs[b+j.val]?=some
      ((solverControlWithV b choose e)[j.val]'(by change j.val < 13; exact j.isLt)) := hCtl _ _
  have hAux := Num.hasAt_append_right hModule
  unfold solverOwnModulesWithV at hAux
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
  exact ⟨atCtl ⟨0, by decide⟩, atCtl ⟨1, by decide⟩, atCtl ⟨2, by decide⟩, atCtl ⟨3, by decide⟩,
    atCtl ⟨4, by decide⟩, atCtl ⟨5, by decide⟩, atCtl ⟨6, by decide⟩, atCtl ⟨7, by decide⟩,
    atCtl ⟨8, by decide⟩, atCtl ⟨9, by decide⟩, atCtl ⟨10, by decide⟩, atCtl ⟨11, by decide⟩,
    atCtl ⟨12, by decide⟩, hInitAt, Num.hasAt_append_left hAux₀, Num.hasAt_append_left hAux₁,
    Num.hasAt_append_left hAux₂, Num.hasAt_append_left hAux₃, Num.hasAt_append_left hAux₄,
    Num.hasAt_append_left hAux₅, Num.hasAt_append_left hAux₆, Num.hasAt_append_left hAux₇, hAux₈⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 530000 in
/-- `V`-passing variant of `boundedIPM_meetsContract_by_instance`. -/
theorem boundedIPMWithV_meetsContract_by_instance {w b : ℕ} {p : Program}
    (r : SolverResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMModuleWithV b r.qualityExponent e))
    (hSupported : ∀ J : Circulation,0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresWithVAt w p e r (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r)) := by
  let k := r.qualityExponent
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  obtain ⟨hEntry, hPosAt, hPenAt, hAfterAt, hSetupAt, hGuardsAt, hWorkAt0, hLimitsAt,
    hLimitAt, hRoundsAt, hFinishAt, hBitsAt0, hBudgetAt0, hInitAt, hGraphAt, hAlphaAt, hFlowAt,
    hNamedAt, hCoeffAt, hSignedAt, hNormAt, hSearchAt, hRecoverAt⟩ :=
    solverOwnModulesWithV_unpack (.assign 24 (.const k)) e hModule
  have hPenalty := solverPenalty_meetsContract (w:=w) hPenAt
  have hGuards := solverGuardTables_meetsContract (w:=w) hGuardsAt hSignedAt hNormAt
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
  have hWrap : MeetsContract w p b { Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r)).pre args mem ∧
          True } := by
    refine boundedIPMWithV_driver_wrap (w:=w) (timeFn:=solverTime r) (spaceFn:=solverWorkspace r)
      (allowed:=fun _ _ => True) hEntry hPosAt (fun _ _ => by unfold solverTime; omega) ?_
    intro J a h mem pos ω _ hm' hat hend hWords hCost hSpace hCap hZero _
    have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
    have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
    obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ := solverNumericWidth_fits (w:=w) r J hm' hp (by omega)
    obtain ⟨hk,C,RC,RD,hDS⟩ := hSupported J hm' hCost hCap hw
    obtain ⟨hWS,_,hTS⟩ := solverWorkspace_covers r J hm' hp
    have h14 := (ipm_parameter_words_fit (solverAugmented J).m (solverPenalty J.m) hw).1
    have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
    have hOne : 1<2^w := by omega
    have hTwo : 2<2^w := by omega
    have hWork := workspace_meetsContract h409 hWorkAt
    have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
    have hLimitProc := targetTestLimit_meetsContract hLimitAt hBudget hOne
    have hRoundsProc := targetSearchRounds_meetsContract hRoundsAt hBit hTwo
    have hLimitsProc := solverLimits_meetsContract hLimitsAt hBit hLimitProc hRoundsProc
    have hInit := solverInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J
    have hSetup := solverSearchSetup_meetsContract hSetupAt hNamedAt hCoeffAt hGuards
      (solverAugmented J) (solverPenalty J.m) k
    have hSpace' : h+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m<2^w :=
      (Nat.add_le_add_left hWS _).trans_lt hSpace
    obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :=
      solverPositiveWithV_runs r e C D hD RC RD J hm' hp hCost hu hw hDS hSearchAt hRecoverAt
        hFinishAt hAfterAt hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
        hat hend hWords hZero hRadius hLimit hBits hkW hk hSpace'
    exact ⟨out,final,c,by simpa [solverPositiveBody] using hRun,hOpt,hLo,
      hHi.trans (Nat.add_le_add_left hWS (h+J.m)),hFresh,hFrame,
      ((show c+11≤c+12 by omega).trans hTime).trans hTS⟩
  intro args mem pos ω hWords hpre
  exact hWrap args mem pos ω hWords ⟨hpre, trivial⟩

/-- `V`-passing variant of `boundedIPM_meetsContract`. -/
theorem boundedIPMWithV_meetsContract {w b : ℕ} {p : Program}
    (r : SolverResources) (e : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMModuleWithV b r.qualityExponent e))
    (hSupported : ∀ J : Circulation,0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresWithVAt w p e r (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r)) :=
  boundedIPMWithV_meetsContract_by_instance r e D hD hModule fun J hm hcost hcap hw =>
    let ⟨hk, RC, RD, hDS⟩ := hSupported J hm hcost hcap hw
    ⟨hk, C, RC, RD, hDS⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 530000 in
/-- `V`-passing variant of `boundedIPMRuntime_meetsContract_on`. -/
private theorem boundedIPMRuntimeWithV_meetsContract_on {w b : ℕ} {p : Program}
    (allowed : ℕ → ℕ → Prop) (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,allowed J.n J.m → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent (solverAugmented J).m≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresWithVAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b { Scaling.Machine.solverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r)).pre args mem ∧
          allowed (Scaling.Machine.solverDimensions args mem).1
            (Scaling.Machine.solverDimensions args mem).2 } := by
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  obtain ⟨hEntry, hPosAt, hPenAt, hAfterAt, hSetupAt, hGuardsAt, hWorkAt0, hLimitsAt,
    hLimitAt, hRoundsAt, hFinishAt, hBitsAt0, hBudgetAt0, hInitAt, hGraphAt, hAlphaAt, hFlowAt,
    hNamedAt, hCoeffAt, hSignedAt, hNormAt, hSearchAt, hRecoverAt⟩ :=
    solverOwnModulesWithV_unpack (.call 24 e.quality [.reg 8]) e hModule
  have hPenalty := solverPenalty_meetsContract (w:=w) hPenAt
  have hGuards := solverGuardTables_meetsContract (w:=w) hGuardsAt hSignedAt hNormAt
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
  refine boundedIPMWithV_driver_wrap (w:=w) (timeFn:=solverRuntimeTime r) (spaceFn:=solverRuntimeWorkspace r)
    (allowed:=allowed) hEntry (by simpa [solverPositiveRuntimeBody] using hPosAt)
    (fun _ _ => by unfold solverRuntimeTime; omega) ?_
  intro J a h mem pos ω hAllowed hm' hat hend hWords hCost hSpace hCap hZero _
  have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
  have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
  let M := (solverAugmented J).m
  let res := r.forSize M
  let k := r.qualityExponent M
  obtain ⟨hWS,hWidth,hTS⟩ := solverRuntimeWorkspace_covers r J hm' hp
  obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ :=
    solverNumericWidthAt_fits (w:=w) res J (hWidth.trans_lt (by omega))
  obtain ⟨hk,C,RC,RD,hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
  have h14 := (ipm_parameter_words_fit (solverAugmented J).m (solverPenalty J.m) hw).1
  have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hWork := workspace_meetsContract h409 hWorkAt
  have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
  have hLimitProc := targetTestLimit_meetsContract hLimitAt hBudget hOne
  have hRoundsProc := targetSearchRounds_meetsContract hRoundsAt hBit hTwo
  have hLimitsProc := solverLimits_meetsContract hLimitsAt hBit hLimitProc hRoundsProc
  have hInit := solverInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J
  have hSetup := solverSearchSetup_meetsContract hSetupAt hNamedAt hCoeffAt hGuards
    (solverAugmented J) (solverPenalty J.m) k
  have hSpace' : h+J.m+solverWorkspaceAt res J.n J.m (solverAugmented J).m<2^w :=
    (Nat.add_le_add_left hWS _).trans_lt hSpace
  obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :=
    solverPositiveRuntimeWithV_runs res e C D hD RC RD J r.qualityExponent r.qualityCost hQuality rfl hm' hp hCost hu hw hDS hSearchAt hRecoverAt
      hFinishAt hAfterAt hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
      hat hend hWords hZero hRadius hLimit hBits hkW hk hSpace'
  exact ⟨out,final,c,hRun,hOpt,hLo,
    hHi.trans (Nat.add_le_add_left hWS (h+J.m)),hFresh,hFrame,
    ((show c+11≤c+12 by omega).trans hTime).trans hTS⟩

/-- `V`-passing variant of `boundedIPMRuntime_meetsContract`. -/
theorem boundedIPMRuntimeWithV_meetsContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent (solverAugmented J).m≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresWithVAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.solverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r)) := by
  have h := boundedIPMRuntimeWithV_meetsContract_on (fun _ _ => True) r e D hD hModule hQuality
    (fun J _ => hSupported J)
  intro args mem pos ω hwords hpre
  exact h args mem pos ω hwords ⟨hpre, trivial⟩

/-- `V`-passing variant of `boundedIPMRuntimeFixedPrecision_meetsCompressedContract`. -/
theorem boundedIPMRuntimeFixedPrecisionWithV_meetsCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent (solverAugmented J).m≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresWithVAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r)) :=
  boundedIPMRuntimeWithV_meetsContract_on (fun n m => n ≤ 2*m+1) r e D hD hModule hQuality hSupported

set_option maxHeartbeats 900000 in
/-- `V`-passing variant of `boundedIPMQualityRuntime_meetsContract_on`. -/
private theorem boundedIPMQualityRuntimeWithV_meetsContract_on {w b : ℕ} {p : Program}
    (allowed : ℕ → ℕ → Prop) (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMQualityRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,allowed J.n J.m → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresWithVAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b { Scaling.Machine.solverContract w (solverQualityRuntimeTime r) (solverQualityRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (solverQualityRuntimeTime r) (solverQualityRuntimeWorkspace r)).pre args mem ∧
          allowed (Scaling.Machine.solverDimensions args mem).1
            (Scaling.Machine.solverDimensions args mem).2 } := by
  have hCtl := Num.hasAt_append_left hModule
  have atCtl (j : Fin 13) : p.procs[b+j.val]?=some
      ((solverRuntimeControlWithV b e)[j.val]'(by change j.val<13; exact j.isLt)) := hCtl _ _
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModuleWithV search e.cycleInit e.cycleOp).length
  have hAux := Num.hasAt_append_right hModule
  change p.HasAt (b+13) (solverQualityOwnModulesWithV b e) at hAux
  unfold solverQualityOwnModulesWithV at hAux
  have hInitAt : p.procs[b+13]?=some (solverQualityInitializeBody e.quality (b+2) graph alpha flow) :=
    (Num.hasAt_append_left hAux).head
  have hAux₀ := Num.hasAt_append_right hAux
  have hAux₁ := Num.hasAt_append_right hAux₀
  have hAux₂ := Num.hasAt_append_right hAux₁
  have hAux₃ := Num.hasAt_append_right hAux₂
  have hAux₄ := Num.hasAt_append_right hAux₃
  have hAux₅ := Num.hasAt_append_right hAux₄
  have hAux₆ := Num.hasAt_append_right hAux₅
  have hAux₇ := Num.hasAt_append_right hAux₆
  have hAux₈ := Num.hasAt_append_right hAux₇
  have hGraphAt : p.HasAt graph (initialGraphModule graph) := Num.hasAt_append_left hAux₀
  have hAlphaAt : p.HasAt alpha (qualityPrecisionAlphaModule alpha) := Num.hasAt_append_left hAux₁
  have hFlowAt : p.HasAt flow (initialFlowModule flow 4) := Num.hasAt_append_left hAux₂
  have hNamedAt : p.HasAt named (namedGraphModule named) := Num.hasAt_append_left hAux₃
  have hCoeffAt : p.HasAt coefficients (coefficientTablesModule coefficients 4) := Num.hasAt_append_left hAux₄
  have hSignedAt : p.HasAt signed (signedGuardConstantsModule signed) := Num.hasAt_append_left hAux₅
  have hNormAt : p.HasAt norm (normalizationModule norm) := Num.hasAt_append_left hAux₆
  have hSearchAt : p.HasAt search (solverSearchModuleWithV search e.cycleInit e.cycleOp) := Num.hasAt_append_left hAux₇
  have hRecoverAt : p.HasAt recover (solverRoundModule recover e.forestInit e.forestOp) := hAux₈
  have hPenalty := solverPenalty_meetsContract (w:=w) (atCtl 2)
  have hGuards := solverQualityGuardTables_meetsContract (w:=w) (atCtl 5) hSignedAt hNormAt
  have hWorkAt : p.HasAt (b+6) workspaceModule := fun j hj => by
    have : j = 0 := by change j < 1 at hj; omega
    subst this; exact atCtl ⟨6, by decide⟩
  have hBitsAt : p.HasAt (b+11) (Num.IPM.bitLengthModule (b+11)) := fun j hj => by
    have : j = 0 := by change j < 1 at hj; omega
    subst this; exact atCtl ⟨11, by decide⟩
  have hBudgetAt : p.HasAt (b+12) iterationBudgetModule := fun j hj => by
    have : j = 0 := by change j < 1 at hj; omega
    subst this; exact atCtl ⟨12, by decide⟩
  have hBudget := iterationBudget_meetsContract (w:=w) hBudgetAt
  refine boundedIPMWithV_driver_wrap (w:=w) (timeFn:=solverQualityRuntimeTime r) (spaceFn:=solverQualityRuntimeWorkspace r)
    (allowed:=allowed) (atCtl ⟨0, by decide⟩)
    (by simpa [solverPositiveRuntimeBody] using atCtl ⟨1, by decide⟩)
    (fun _ _ => by unfold solverQualityRuntimeTime; omega) ?_
  intro J a h mem pos ω hAllowed hm' hat hend hWords hCost hSpace hCap hZero _
  have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
  have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
  let M := (solverAugmented J).m
  let res := r.forSize M
  let k := r.qualityExponent M
  obtain ⟨hWS,hWidth,hTS⟩ := solverQualityRuntimeWorkspace_covers r J hm' hp
  obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ :=
    solverQualityNumericWidthAt_fits (w:=w) res J (hWidth.trans_lt (by omega))
  obtain ⟨C,RC,RD,hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
  have h14 := (ipm_quality_parameter_words_fit (solverAugmented J).m (solverPenalty J.m) k hw).1
  have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
  have hOne : 1<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hWork := workspace_meetsContract h409 hWorkAt
  have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
  have hLimitProc := targetTestLimit_meetsContract (atCtl 8) hBudget hOne
  have hRoundsProc := targetSearchRounds_meetsContract (atCtl 9) hBit hTwo
  have hLimitsProc := solverLimits_meetsContract (atCtl 7) hBit hLimitProc hRoundsProc
  have hInit := solverQualityInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J r.qualityExponent r.qualityCost hQuality hkW
  have hSetup := solverQualitySearchSetup_meetsContract (atCtl 4) hNamedAt hCoeffAt hGuards
    (solverAugmented J) (solverPenalty J.m) k
  have hSpace' : h+J.m+solverQualityWorkspaceAt res J.n J.m (solverAugmented J).m<2^w :=
    (Nat.add_le_add_left hWS _).trans_lt hSpace
  obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :=
    solverPositiveQualityRuntimeWithV_runs res e C D hD RC RD J r.qualityExponent r.qualityCost hQuality rfl hm' hp hCost hu hw hDS hSearchAt hRecoverAt
      (atCtl 10) (atCtl 3) hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
      hat hend hWords hZero hRadius hLimit hBits hkW hSpace'
  exact ⟨out,final,c,hRun,hOpt,hLo,
    hHi.trans (Nat.add_le_add_left hWS (h+J.m)),hFresh,hFrame,
    ((show c+11≤c+12 by omega).trans hTime).trans hTS⟩

/-- `V`-passing variant of `boundedIPMRuntime_meetsCompressedContract`. -/
theorem boundedIPMRuntimeWithV_meetsCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMQualityRuntimeModuleWithV b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresWithVAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (solverQualityRuntimeTime r) (solverQualityRuntimeWorkspace r)) :=
  boundedIPMQualityRuntimeWithV_meetsContract_on (fun n m => n ≤ 2*m+1) r e D hD hModule hQuality hSupported

end MinCostFlow.IPM.Machine
