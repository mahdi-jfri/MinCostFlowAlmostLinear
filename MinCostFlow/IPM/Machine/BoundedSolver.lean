module

public import MinCostFlow.IPM.Machine.SolverModule
public import MinCostFlow.IPM.Machine.SolverPositive
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Scaling.SolverInputLayout
import WordRAM.Tactic
import MinCostFlow.IPM.Machine.RoundCleanupProgram
import Mathlib.Tactic

/-!
# A WordRAM procedure meeting the bounded circulation contract

Appendix C, Lemma C.1 of Chen et al. (arXiv:2203.00671v2) calls
a bounded numerical solver. At this entry the Lemma 4.12 initializer,
verified repeated IPM tests and forest rounding act on the same
heap. The output is an exact integral optimum in the original edge
order, with independent time and space bounds.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- Feasibility and objective on an empty edge set are constant. -/
theorem emptyCirculation_optimal (J : Circulation) (h : J.m=0)
    (flow : Fin J.m → ℝ) : J.Optimal flow := by
  have : IsEmpty (Fin J.m) := by rw [h]; infer_instance
  refine ⟨⟨fun _ => by simp [Circulation.balance],fun e => isEmptyElim e⟩,?_⟩
  intro g _
  simp [Circulation.objective]

/-- The solver's numerical word size requirements follow from its
workspace precondition for every legal positive-size call. -/
theorem solverNumericWidthAt_fits (r : SolverResources) (J : Circulation) {w : ℕ}
    (hs : 2^solverNumericWidthAt r J.m (solverAugmented J).m<2^w) :
    let M := (solverAugmented J).m
    let V := solverPenalty J.m
    ipmParameterWordBits M V≤w ∧ 2*(M*V^2)<2^w ∧
      targetTestLimit M V r.qualityExponent<2^w ∧ M.size+V.size<2^w ∧ r.qualityExponent<2^w := by
  dsimp only
  let M := (solverAugmented J).m
  let V := solverPenalty J.m
  let k := r.qualityExponent
  have hw : solverNumericWidthAt r J.m M≤w := by
    by_contra hh
    have hge := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_of_not_ge hh)
    exact (not_lt_of_ge hge) hs
  change max (ipmParameterWordBits M V) (max (2*(M*V^2)).size
    (max (targetTestLimit M V k).size (max (M.size+V.size).size k.size)))≤w at hw
  obtain ⟨hF,hh⟩ := max_le_iff.mp hw
  obtain ⟨hB,hh⟩ := max_le_iff.mp hh
  obtain ⟨hT,hh⟩ := max_le_iff.mp hh
  obtain ⟨hS,hK⟩ := max_le_iff.mp hh
  exact ⟨hF,Nat.size_le.mp hB,Nat.size_le.mp hT,Nat.size_le.mp hS,Nat.size_le.mp hK⟩

/-- The solver's numerical word size requirements follow from its
workspace precondition for every legal positive-size call. -/
theorem solverNumericWidth_fits (r : SolverResources) (J : Circulation) {w : ℕ}
    (hm : 0 < J.m) (hp : ∀ e,1≤J.capacity e)
    (hs : solverWorkspace r J.n J.m<2^w) :
    let M := (solverAugmented J).m
    let V := solverPenalty J.m
    ipmParameterWordBits M V≤w ∧ 2*(M*V^2)<2^w ∧
      targetTestLimit M V r.qualityExponent<2^w ∧ M.size+V.size<2^w ∧ r.qualityExponent<2^w :=
  solverNumericWidthAt_fits r J ((solverWorkspace_covers r J hm hp).2.1.trans_lt hs)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 530000 in
/-- The linked bounded IPM meets the shared solver contract. Its only
procedure parameters are the min-ratio data structure with failure
and the dynamic forest. The quality exponent must be in the common
fixed-point range on inputs covered by the data structures. Each
representation describes states of its own format, as supplied to Init. -/
theorem boundedIPM_meetsContract_by_instance {w b : ℕ} {p : Program}
    (r : SolverResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMModule b r.qualityExponent e))
    (hSupported : ∀ J : Circulation,0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresAt w p e r (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r)) := by
  let k := r.qualityExponent
  have hCtl := Num.hasAt_append_left hModule
  have atCtl (j : Fin 13) : p.procs[b+j.val]?=some
      ((solverControl b k e)[j.val]'(by change j.val<13; exact j.isLt)) := hCtl _ _
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  have hAux := Num.hasAt_append_right hModule
  change p.HasAt (b+13) (solverOwnModules b e) at hAux
  unfold solverOwnModules at hAux
  have hInitAt : p.procs[b+13]?=some (solverInitializeBody (b+2) graph alpha flow) :=
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
  have hAlphaAt : p.HasAt alpha (precisionAlphaModule alpha) := Num.hasAt_append_left hAux₁
  have hFlowAt : p.HasAt flow (initialFlowModule flow 4) := Num.hasAt_append_left hAux₂
  have hNamedAt : p.HasAt named (namedGraphModule named) := Num.hasAt_append_left hAux₃
  have hCoeffAt : p.HasAt coefficients (coefficientTablesModule coefficients 4) := Num.hasAt_append_left hAux₄
  have hSignedAt : p.HasAt signed (signedGuardConstantsModule signed) := Num.hasAt_append_left hAux₅
  have hNormAt : p.HasAt norm (normalizationModule norm) := Num.hasAt_append_left hAux₆
  have hSearchAt : p.HasAt search (solverSearchModule search e.cycleInit e.cycleOp) := Num.hasAt_append_left hAux₇
  have hRecoverAt : p.HasAt recover (solverRoundModule recover e.forestInit e.forestOp) := hAux₈
  have hPenalty := solverPenalty_meetsContract (w:=w) (atCtl 2)
  have hGuards := solverGuardTables_meetsContract (w:=w) (atCtl 5) hSignedAt hNormAt
  have hWorkAt : p.HasAt (b+6) workspaceModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+6]?=some workspaceBody
    exact atCtl ⟨6,by decide⟩
  have hBitsAt : p.HasAt (b+11) (Num.IPM.bitLengthModule (b+11)) := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+11]?=some (Num.IPM.bitLengthBody (b+11))
    exact atCtl ⟨11,by decide⟩
  have hBudgetAt : p.HasAt (b+12) iterationBudgetModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+12]?=some iterationBudgetBody
    exact atCtl ⟨12,by decide⟩
  have hBudget := iterationBudget_meetsContract (w:=w) hBudgetAt
  have hEntry : p.procs[b]?=some (boundedIPMBody (b+1)) := atCtl ⟨0,by decide⟩
  apply meetsContract_of_runs hEntry
  intro args mem pos ω hWordsIn hpre
  obtain ⟨⟨a,h,rfl,J,hat,hend,hWords,hCost,hSpace,hCap⟩,hZero,_⟩ := hpre
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
    · change 7≤solverTime r _ _
      rw [hDimensions]
      unfold solverTime
      omega
  · have hm' : 0 < J.m := Nat.pos_of_ne_zero hm
    have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
    have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
    obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ := solverNumericWidth_fits (w:=w) r J hm' hp (by omega)
    obtain ⟨hk,C,RC,RD,hDS⟩ := hSupported J hm' hCost hCap hw
    obtain ⟨hWS,_,hTS⟩ := solverWorkspace_covers r J hm' hp
    have h14 := (ipm_parameter_words_fit (solverAugmented J).m (solverPenalty J.m) hw).1
    have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
    have hTwo : 2<2^w := by omega
    have hWork := workspace_meetsContract h409 hWorkAt
    have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
    have hLimitProc := targetTestLimit_meetsContract (atCtl 8) hBudget hOne
    have hRoundsProc := targetSearchRounds_meetsContract (atCtl 9) hBit hTwo
    have hLimitsProc := solverLimits_meetsContract (atCtl 7) hBit hLimitProc hRoundsProc
    have hInit := solverInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J
    have hSetup := solverSearchSetup_meetsContract (atCtl 4) hNamedAt hCoeffAt hGuards
      (solverAugmented J) (solverPenalty J.m) k
    have hSpace' : h+J.m+solverWorkspaceAt r J.n J.m (solverAugmented J).m<2^w := by
      exact (Nat.add_le_add_left hWS _).trans_lt hSpace
    obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :=
      solverPositive_runs r e C D hD RC RD J hm' hp hCost hu hw hDS hSearchAt hRecoverAt
        (atCtl 10) (atCtl 3) hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
        hat hend hWords hZero hRadius hLimit hBits hkW hk hSpace'
    have hCallAt : p.procs[b+1]?=some (solverPositiveBody k (b+2) (b+13) (b+3)) :=
      atCtl ⟨1,by decide⟩
    have hCall := round_returning_call (dst:=2) hCallAt
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
        solverWorkspace r (Scaling.Machine.solverDimensions [a,h] mem).1
          (Scaling.Machine.solverDimensions [a,h] mem).2)
      rw [hDimensions]
      change out≤h+(J.m+solverWorkspace r J.n J.m)
      exact hHi.trans (by omega)
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact hOpt
    · change c+11≤solverTime r _ _
      rw [hDimensions]
      exact ((show c+11≤c+12 by omega).trans hTime).trans hTS

set_option maxRecDepth 4096 in
set_option maxHeartbeats 530000 in
/-- The bounded IPM with runtime quality meets the shared solver contract
for the data structures and quality procedure at the dispatched addresses. -/
private theorem boundedIPMRuntime_meetsContract_on {w b : ℕ} {p : Program}
    (allowed : ℕ → ℕ → Prop) (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,allowed J.n J.m → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent (solverAugmented J).m≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b { Scaling.Machine.solverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r)).pre args mem ∧
          allowed (Scaling.Machine.solverDimensions args mem).1
            (Scaling.Machine.solverDimensions args mem).2 } := by
  have hCtl := Num.hasAt_append_left hModule
  have atCtl (j : Fin 13) : p.procs[b+j.val]?=some
      ((solverRuntimeControl b e)[j.val]'(by change j.val<13; exact j.isLt)) := hCtl _ _
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(precisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  have hAux := Num.hasAt_append_right hModule
  change p.HasAt (b+13) (solverOwnModules b e) at hAux
  unfold solverOwnModules at hAux
  have hInitAt : p.procs[b+13]?=some (solverInitializeBody (b+2) graph alpha flow) :=
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
  have hAlphaAt : p.HasAt alpha (precisionAlphaModule alpha) := Num.hasAt_append_left hAux₁
  have hFlowAt : p.HasAt flow (initialFlowModule flow 4) := Num.hasAt_append_left hAux₂
  have hNamedAt : p.HasAt named (namedGraphModule named) := Num.hasAt_append_left hAux₃
  have hCoeffAt : p.HasAt coefficients (coefficientTablesModule coefficients 4) := Num.hasAt_append_left hAux₄
  have hSignedAt : p.HasAt signed (signedGuardConstantsModule signed) := Num.hasAt_append_left hAux₅
  have hNormAt : p.HasAt norm (normalizationModule norm) := Num.hasAt_append_left hAux₆
  have hSearchAt : p.HasAt search (solverSearchModule search e.cycleInit e.cycleOp) := Num.hasAt_append_left hAux₇
  have hRecoverAt : p.HasAt recover (solverRoundModule recover e.forestInit e.forestOp) := hAux₈
  have hPenalty := solverPenalty_meetsContract (w:=w) (atCtl 2)
  have hGuards := solverGuardTables_meetsContract (w:=w) (atCtl 5) hSignedAt hNormAt
  have hWorkAt : p.HasAt (b+6) workspaceModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+6]?=some workspaceBody
    exact atCtl ⟨6,by decide⟩
  have hBitsAt : p.HasAt (b+11) (Num.IPM.bitLengthModule (b+11)) := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+11]?=some (Num.IPM.bitLengthBody (b+11))
    exact atCtl ⟨11,by decide⟩
  have hBudgetAt : p.HasAt (b+12) iterationBudgetModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+12]?=some iterationBudgetBody
    exact atCtl ⟨12,by decide⟩
  have hBudget := iterationBudget_meetsContract (w:=w) hBudgetAt
  have hEntry : p.procs[b]?=some (boundedIPMBody (b+1)) := atCtl ⟨0,by decide⟩
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
    · change 7≤solverRuntimeTime r _ _
      rw [hDimensions]
      unfold solverRuntimeTime
      omega
  · have hm' : 0 < J.m := Nat.pos_of_ne_zero hm
    have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
    have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
    let M := (solverAugmented J).m
    let res := r.forSize M
    let k := r.qualityExponent M
    obtain ⟨hWS,hWidth,hTS⟩ := solverRuntimeWorkspace_covers r J hm' hp
    obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ :=
      solverNumericWidthAt_fits (w:=w) res J (hWidth.trans_lt (by omega))
    have hAllowed := hpre.2
    change allowed (Scaling.Machine.solverDimensions [a,h] mem).1
      (Scaling.Machine.solverDimensions [a,h] mem).2 at hAllowed
    rw [hDimensions] at hAllowed
    obtain ⟨hk,C,RC,RD,hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
    have h14 := (ipm_parameter_words_fit (solverAugmented J).m (solverPenalty J.m) hw).1
    have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
    have hTwo : 2<2^w := by omega
    have hWork := workspace_meetsContract h409 hWorkAt
    have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
    have hLimitProc := targetTestLimit_meetsContract (atCtl 8) hBudget hOne
    have hRoundsProc := targetSearchRounds_meetsContract (atCtl 9) hBit hTwo
    have hLimitsProc := solverLimits_meetsContract (atCtl 7) hBit hLimitProc hRoundsProc
    have hInit := solverInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J
    have hSetup := solverSearchSetup_meetsContract (atCtl 4) hNamedAt hCoeffAt hGuards
      (solverAugmented J) (solverPenalty J.m) k
    have hSpace' : h+J.m+solverWorkspaceAt res J.n J.m (solverAugmented J).m<2^w := by
      exact (Nat.add_le_add_left hWS _).trans_lt hSpace
    obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :=
      solverPositiveRuntime_runs res e C D hD RC RD J r.qualityExponent r.qualityCost hQuality rfl hm' hp hCost hu hw hDS hSearchAt hRecoverAt
        (atCtl 10) (atCtl 3) hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
        hat hend hWords hZero hRadius hLimit hBits hkW hk hSpace'
    have hCallAt : p.procs[b+1]?=some (solverPositiveRuntimeBody e.quality (b+2) (b+13) (b+3)) :=
      atCtl ⟨1,by decide⟩
    have hCall := round_returning_call (dst:=2) hCallAt
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
        solverRuntimeWorkspace r (Scaling.Machine.solverDimensions [a,h] mem).1
          (Scaling.Machine.solverDimensions [a,h] mem).2)
      rw [hDimensions]
      change out≤h+(J.m+solverRuntimeWorkspace r J.n J.m)
      change out ≤ h+J.m+solverWorkspaceAt (r.forSize (solverAugmented J).m) J.n J.m (solverAugmented J).m at hHi
      exact hHi.trans (by omega)
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact hOpt
    · change c+11≤solverRuntimeTime r _ _
      rw [hDimensions]
      exact ((show c+11≤c+12 by omega).trans hTime).trans hTS

/-- The bounded IPM with runtime quality meets the shared solver contract
for the data structures and quality procedure at the dispatched addresses. -/
theorem boundedIPMRuntime_meetsContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent (solverAugmented J).m≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.solverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r)) := by
  have h := boundedIPMRuntime_meetsContract_on (fun _ _ => True) r e D hD hModule hQuality
    (fun J _ => hSupported J)
  intro args mem pos ω hwords hpre
  exact h args mem pos ω hwords ⟨hpre, trivial⟩

/-- The bounded IPM with runtime quality meets the compressed solver contract
for the data structures and quality procedure at the dispatched addresses. -/
theorem boundedIPMRuntimeFixedPrecision_meetsCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent (solverAugmented J).m≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (solverRuntimeTime r) (solverRuntimeWorkspace r)) :=
  boundedIPMRuntime_meetsContract_on (fun n m => n ≤ 2*m+1) r e D hD hModule hQuality hSupported

/-- A fixed model is a special case of the instance-dependent solver. -/
theorem boundedIPM_meetsContract {w b : ℕ} {p : Program}
    (r : SolverResources) (e : SolverDispatch)
    (C : MinRatioDataStructureWithFailure) (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMModule b r.qualityExponent e))
    (hSupported : ∀ J : Circulation,0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmParameterWordBits (solverAugmented J).m (solverPenalty J.m)≤w,
        r.qualityExponent≤slackRangeExponent (solverAugmented J).m (solverPenalty J.m) ∧
        ∃ (RC : DSRep C.State) (RD : DSRep D.State),
          SolverDataStructuresAt w p e r (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.solverContract w (solverTime r) (solverWorkspace r)) := by
  apply boundedIPM_meetsContract_by_instance r e D hD hModule
  intro J hm hcost hcap hw
  obtain ⟨hk, RC, RD, hDS⟩ := hSupported J hm hcost hcap hw
  exact ⟨hk, C, RC, RD, hDS⟩


theorem solverQualityNumericWidthAt_fits (r : SolverResources) (J : Circulation) {w : ℕ}
    (hs : 2^solverQualityNumericWidthAt r J.m (solverAugmented J).m<2^w) :
    let M := (solverAugmented J).m
    let V := solverPenalty J.m
    ipmQualityParameterWordBits M V r.qualityExponent≤w ∧ 2*(M*V^2)<2^w ∧
      targetTestLimit M V r.qualityExponent<2^w ∧ M.size+V.size<2^w ∧ r.qualityExponent<2^w := by
  dsimp only
  let M := (solverAugmented J).m
  let V := solverPenalty J.m
  let k := r.qualityExponent
  have hw : solverQualityNumericWidthAt r J.m M≤w := by
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

set_option maxHeartbeats 900000 in
/-- The bounded IPM with runtime quality meets the shared solver contract
for the data structures and quality procedure at the dispatched addresses. -/
private theorem boundedIPMQualityRuntime_meetsContract_on {w b : ℕ} {p : Program}
    (allowed : ℕ → ℕ → Prop) (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMQualityRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,allowed J.n J.m → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b { Scaling.Machine.solverContract w (solverQualityRuntimeTime r) (solverQualityRuntimeWorkspace r) with
      pre := fun args mem =>
        (Scaling.Machine.solverContract w (solverQualityRuntimeTime r) (solverQualityRuntimeWorkspace r)).pre args mem ∧
          allowed (Scaling.Machine.solverDimensions args mem).1
            (Scaling.Machine.solverDimensions args mem).2 } := by
  have hCtl := Num.hasAt_append_left hModule
  have atCtl (j : Fin 13) : p.procs[b+j.val]?=some
      ((solverRuntimeControl b e)[j.val]'(by change j.val<13; exact j.isLt)) := hCtl _ _
  let graph := b+14
  let alpha := graph+(initialGraphModule graph).length
  let flow := alpha+(qualityPrecisionAlphaModule alpha).length
  let named := flow+(initialFlowModule flow 4).length
  let coefficients := named+(namedGraphModule named).length
  let signed := coefficients+(coefficientTablesModule coefficients 4).length
  let norm := signed+(signedGuardConstantsModule signed).length
  let search := norm+(normalizationModule norm).length
  let recover := search+(solverSearchModule search e.cycleInit e.cycleOp).length
  have hAux := Num.hasAt_append_right hModule
  change p.HasAt (b+13) (solverQualityOwnModules b e) at hAux
  unfold solverQualityOwnModules at hAux
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
  have hSearchAt : p.HasAt search (solverSearchModule search e.cycleInit e.cycleOp) := Num.hasAt_append_left hAux₇
  have hRecoverAt : p.HasAt recover (solverRoundModule recover e.forestInit e.forestOp) := hAux₈
  have hPenalty := solverPenalty_meetsContract (w:=w) (atCtl 2)
  have hGuards := solverQualityGuardTables_meetsContract (w:=w) (atCtl 5) hSignedAt hNormAt
  have hWorkAt : p.HasAt (b+6) workspaceModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+6]?=some workspaceBody
    exact atCtl ⟨6,by decide⟩
  have hBitsAt : p.HasAt (b+11) (Num.IPM.bitLengthModule (b+11)) := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+11]?=some (Num.IPM.bitLengthBody (b+11))
    exact atCtl ⟨11,by decide⟩
  have hBudgetAt : p.HasAt (b+12) iterationBudgetModule := by
    intro j hj
    change j<1 at hj
    have he : j=0 := by omega
    subst j
    change p.procs[b+12]?=some iterationBudgetBody
    exact atCtl ⟨12,by decide⟩
  have hBudget := iterationBudget_meetsContract (w:=w) hBudgetAt
  have hEntry : p.procs[b]?=some (boundedIPMBody (b+1)) := atCtl ⟨0,by decide⟩
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
    · change 7≤solverQualityRuntimeTime r _ _
      rw [hDimensions]
      unfold solverQualityRuntimeTime
      omega
  · have hm' : 0 < J.m := Nat.pos_of_ne_zero hm
    have hp : ∀ e,1≤J.capacity e := fun e => (hCap e).1
    have hu : ∀ e,J.capacity e≤J.m^40 := fun e => (hCap e).2
    let M := (solverAugmented J).m
    let res := r.forSize M
    let k := r.qualityExponent M
    obtain ⟨hWS,hWidth,hTS⟩ := solverQualityRuntimeWorkspace_covers r J hm' hp
    obtain ⟨hw,hRadius,hLimit,hBits,hkW⟩ :=
      solverQualityNumericWidthAt_fits (w:=w) res J (hWidth.trans_lt (by omega))
    have hAllowed := hpre.2
    change allowed (Scaling.Machine.solverDimensions [a,h] mem).1
      (Scaling.Machine.solverDimensions [a,h] mem).2 at hAllowed
    rw [hDimensions] at hAllowed
    obtain ⟨C,RC,RD,hDS⟩ := hSupported J hAllowed hm' hCost hCap hw
    have h14 := (ipm_quality_parameter_words_fit (solverAugmented J).m (solverPenalty J.m) k hw).1
    have h409 : 409<2^w := (by decide : 409<2^14).trans_le (Nat.pow_le_pow_right (by decide) h14)
    have hTwo : 2<2^w := by omega
    have hWork := workspace_meetsContract h409 hWorkAt
    have hBit := Num.IPM.bitLength_meetsContract hTwo hBitsAt
    have hLimitProc := targetTestLimit_meetsContract (atCtl 8) hBudget hOne
    have hRoundsProc := targetSearchRounds_meetsContract (atCtl 9) hBit hTwo
    have hLimitsProc := solverLimits_meetsContract (atCtl 7) hBit hLimitProc hRoundsProc
    have hInit := solverQualityInitialize_meetsContract hInitAt hPenalty hGraphAt hAlphaAt hFlowAt J r.qualityExponent r.qualityCost hQuality hkW
    have hSetup := solverQualitySearchSetup_meetsContract (atCtl 4) hNamedAt hCoeffAt hGuards
      (solverAugmented J) (solverPenalty J.m) k
    have hSpace' : h+J.m+solverQualityWorkspaceAt res J.n J.m (solverAugmented J).m<2^w := by
      exact (Nat.add_le_add_left hWS _).trans_lt hSpace
    obtain ⟨out,final,c,hRun,hOpt,hLo,hHi,hFresh,hFrame,hTime⟩ :=
      solverPositiveQualityRuntime_runs res e C D hD RC RD J r.qualityExponent r.qualityCost hQuality rfl hm' hp hCost hu hw hDS hSearchAt hRecoverAt
        (atCtl 10) (atCtl 3) hInit hPenalty hSetup hWork hLimitsProc a h mem pos ω
        hat hend hWords hZero hRadius hLimit hBits hkW hSpace'
    have hCallAt : p.procs[b+1]?=some (solverPositiveRuntimeBody e.quality (b+2) (b+13) (b+3)) :=
      atCtl ⟨1,by decide⟩
    have hCall := round_returning_call (dst:=2) hCallAt
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
        solverQualityRuntimeWorkspace r (Scaling.Machine.solverDimensions [a,h] mem).1
          (Scaling.Machine.solverDimensions [a,h] mem).2)
      rw [hDimensions]
      change out≤h+(J.m+solverQualityRuntimeWorkspace r J.n J.m)
      change out ≤ h+J.m+solverQualityWorkspaceAt (r.forSize (solverAugmented J).m) J.n J.m (solverAugmented J).m at hHi
      exact hHi.trans (by omega)
    · intro K hK
      change ListAt mem a K.solverWords at hK
      obtain rfl := solverWordsAt_unique K J mem a hK hat
      exact hOpt
    · change c+11≤solverQualityRuntimeTime r _ _
      rw [hDimensions]
      exact ((show c+11≤c+12 by omega).trans hTime).trans hTS

/-- The bounded IPM with runtime quality meets the compressed solver contract
for the data structures and quality procedure at the dispatched addresses. -/
theorem boundedIPMRuntime_meetsCompressedContract {w b : ℕ} {p : Program}
    (r : SolverRuntimeResources) (e : SolverDispatch)
    (D : Rounding.DynForest) (hD : D.IsSpec)
    (hModule : p.HasAt b (boundedIPMQualityRuntimeModule b e))
    (hQuality : MeetsContract w p e.quality (solverQualityContract w r.qualityExponent r.qualityCost))
    (hSupported : ∀ J : Circulation,J.n ≤ 2*J.m+1 → 0 < J.m → J.CostsBounded (J.m^10) →
      (∀ e,1≤J.capacity e ∧ J.capacity e≤J.m^40) →
      ∀ hw : ipmQualityParameterWordBits (solverAugmented J).m (solverPenalty J.m) (r.qualityExponent (solverAugmented J).m)≤w,
        ∃ (C : MinRatioDataStructureWithFailure) (RC : DSRep C.State) (RD : DSRep D.State),
          SolverQualityDataStructuresAt w p e (r.forSize (solverAugmented J).m) (solverAugmented J) (solverPenalty J.m) hw C D RC RD) :
    MeetsContract w p b (Scaling.Machine.compressedSolverContract w (solverQualityRuntimeTime r) (solverQualityRuntimeWorkspace r)) :=
  boundedIPMQualityRuntime_meetsContract_on (fun n m => n ≤ 2*m+1) r e D hD hModule hQuality hSupported

end MinCostFlow.IPM.Machine
